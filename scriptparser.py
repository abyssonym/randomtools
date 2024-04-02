from .utils import fake_yaml as yaml
from collections import OrderedDict
from io import BytesIO
from sys import argv


class TrackedPointer:
    def __init__(self, pointer, virtual_address, parser):
        self.virtual_address = virtual_address
        self.pointer = pointer
        self.parser = parser
        assert self.pointer - self.virtual_address >= 0

    def __repr__(self):
        return f'{self}'

    def __format__(self, format_spec):
        return self.parser.format_pointer(self, format_spec)

    def __eq__(self, other):
        if self.parser is not other.parser:
            return False
        return self is other

    def __lt__(self, other):
        return self.pointer < other.pointer

    def __hash__(self):
        return self.pointer

    @property
    def converted(self):
        return self.parser.convert_pointer(self)

    @property
    def bytecode(self):
        return self.parser.pointer_to_bytecode(self)


class Instruction:
    def __init__(self, script):
        self.script = script
        self.read_from_data()
        self.script.instructions.append(self)
        self.parser.update_format_length(self)

    def __repr__(self):
        format_length = self.parser.format_length
        s = ('{0:%s}   # {1}' % format_length).format(self.format,
                                                      self.comment)
        if not self.text_parameters:
            return s

        for parameter_name, text in self.text_parameters.items():
            s = f'{s}\n{self.parser.format_text(parameter_name, text)}'
        s = s.replace('\n', '\n  ')
        return s

    def read_from_data(self):
        self.start_address = self.parser.data.tell()
        opcode = self.parser.data.read(self.parser.config['opcode_size'])
        opcode = int.from_bytes(opcode,
                                byteorder=self.parser.config['byte_order'])
        self.opcode = opcode

        if self.opcode not in self.parser.config['instructions']:
            import pdb; pdb.set_trace()

        if 'parameters' not in self.manifest:
            parameter_order = []
        elif len(self.manifest['parameters']) <= 1:
            parameter_order = list(self.manifest['parameters'].keys())
        else:
            parameter_order = self.manifest['parameter_order']

        parameters = OrderedDict()
        text_parameters = OrderedDict()
        for parameter_name in parameter_order:
            pmani = self.manifest['parameters'][parameter_name]
            length = pmani['length']
            value = self.parser.data.read(length)
            value = int.from_bytes(value,
                                   byteorder=self.parser.config['byte_order'])
            if 'track_pointer' in pmani and pmani['track_pointer']:
                value = self.parser.get_tracked_pointer(
                        value, pmani['virtual_address'])
                is_text = 'is_text' in pmani and pmani['is_text']
                if is_text:
                    address = self.parser.data.tell()
                    text_parameters[parameter_name] = \
                            self.parser.get_text(value)
                    self.parser.data.seek(address)
                if value not in self.parser.script_pointers and not is_text:
                    self.parser.script_pointers.add(value)
            assert parameter_name not in parameters
            parameters[parameter_name] = value
        self.parameters = parameters
        self.text_parameters = text_parameters
        self.end_address = self.parser.data.tell()

    @property
    def format(self):
        parameters = []
        for parameter_name in self.parameters:
            parameters.append(
                    self.parser.format_parameter(self, parameter_name))
        parameters = ','.join(parameters)
        opcode = self.parser.format_opcode(self.opcode)
        return f'{opcode}:{parameters}'

    @property
    def comment(self):
        parameters = dict(self.parameters)
        for parameter_name in set(parameters.keys()):
            pmani = self.manifest['parameters'][parameter_name]
            if 'prettify' in pmani:
                value = parameters[parameter_name]
                if value in pmani['prettify']:
                    prettified = pmani['prettify'][value].format(**parameters)
                else:
                    prettified = pmani['prettify'][-1].format(**parameters)
                parameters[f'_pretty_{parameter_name}'] = prettified
        return self.manifest['comment'].format(**parameters)

    @property
    def parser(self):
        return self.script.parser

    @property
    def manifest(self):
        return self.parser.config['instructions'][self.opcode]

    @property
    def references(self):
        return [v for (k, v) in self.parameters.items()
                if isinstance(v, TrackedPointer)]

    @property
    def is_terminator(self):
        return self.opcode in self.parser.config['terminators']


class Script:
    def __init__(self, pointer, parser):
        self.pointer = pointer
        self.parser = parser
        self.instructions = []

    def __repr__(self):
        header = self.parser.format_pointer(self.pointer)
        lines = [header]
        start_addresses = [f'{i.start_address:x}' for i in self.instructions]
        address_length = max(len(addr) for addr in start_addresses)

        for instruction in self.instructions:
            line = '{0:0>%sx}. {1}' % address_length
            lines.append(line.format(instruction.start_address, instruction))
        s = '\n'.join(lines)
        s = s.replace('\n', '\n  ')
        return s

    def __eq__(self, other):
        if self.parser is not other.parser:
            return False
        return self is other

    def __lt__(self, other):
        return self.pointer < other.pointer

    def __hash__(self):
        return (self.parser.__hash__(), self.pointer.__hash__()).__hash__()

    @property
    def references(self):
        return {r for i in self.instructions for r in i.references}

    @property
    def referenced_scripts(self):
        references = {r.pointer for r in self.references}
        references.add(self.pointer.pointer)
        return {v for (k, v) in self.parser.scripts.items()
                if k in references}


class Parser:
    Script = Script
    Instruction = Instruction
    TrackedPointer = TrackedPointer

    def __init__(self, config_filename, data, pointers):
        with open(config_filename) as f:
            self.config = yaml.safe_load(f.read())
        if not isinstance(data, bytes):
            assert isinstance(data, str)
            with open(data, 'r+b') as f:
                data = f.read()
        self.data = BytesIO(data)
        self.pointers = {}
        self.script_pointers = set()
        for p in pointers:
            self.add_pointer(p, script=True)
        self.get_text_decode_table()
        self.read_scripts()

    def get_tracked_pointer(self, pointer, virtual_address=None, script=False):
        if pointer in self.pointers:
            return self.pointers[pointer]
        if virtual_address is None:
            virtual_address = self.config['virtual_address']
        tracked_pointer = self.TrackedPointer(pointer, virtual_address, self)
        self.pointers[pointer] = tracked_pointer
        if script:
            self.script_pointers.add(tracked_pointer)
        return tracked_pointer

    add_pointer = get_tracked_pointer

    def convert_pointer(self, pointer):
        return pointer.pointer - pointer.virtual_address

    def pointer_to_bytecode(self, pointer):
        return pointer.pointer.to_bytes(length=self.config['pointer_size'],
                                        byteorder=self.config['byte_order'])

    def get_text_decode_table(self):
        self.text_decode_table = {}
        self.text_encode_table = {}
        if 'text_decode_table' not in self.config:
            return
        for codepoint, value in self.config['text_decode_table'].items():
            if isinstance(value, str):
                value = value.replace(r'\n', '\n')
                assert codepoint not in self.text_decode_table
                self.text_decode_table[codepoint] = value
                self.text_encode_table[value] = codepoint
                continue

            expansion = value['expansion']
            increment = value['increment']
            for i, character in enumerate(expansion):
                excodepoint = codepoint + (i*increment)
                assert excodepoint not in self.text_decode_table
                self.text_decode_table[excodepoint] = character
                self.text_encode_table[character] = excodepoint

    def get_text(self, pointer):
        raise NotImplementedError

    def format_opcode(self, opcode):
        length = self.config['opcode_size'] * 2
        return ('{0:0>%sx}' % length).format(opcode)

    def format_parameter(self, instruction, parameter_name):
        pmani = instruction.manifest['parameters'][parameter_name]
        value = instruction.parameters[parameter_name]
        if isinstance(value, int):
            length = pmani['length'] * 2
            parameter = ('{0:0>%sx}' % length).format(value)
        else:
            parameter = str(value)
        return parameter

    def format_pointer(self, pointer, format_spec=None):
        if not format_spec:
            format_spec = 'x'
        return ('@{0:%s}' % format_spec).format(pointer.pointer)

    def format_text(self, parameter_name, text):
        name_length = len(parameter_name)
        lines = text.split('\n')
        lines = [f'|{line}|' for line in lines]
        first_line = f'{parameter_name}: {lines[0]}'
        other_lines = [('{0:%s}  {1}' % name_length).format('', line)
                       for line in lines[1:]]
        return '\n'.join([first_line] + other_lines)

    def interpret_opcode(self, opcode):
        raise NotImplementedError

    def interpret_parameter(self, parameter):
        raise NotImplementedError

    def interpret_pointer(self, pointer):
        raise NotImplementedError

    def interpret_text(self, text):
        raise NotImplementedError

    def update_format_length(self, instruction):
        length = len(instruction.format)
        if hasattr(self, 'format_length'):
            self.format_length = max(length, self.format_length)
        else:
            self.format_length = length

    def read_script(self, pointer):
        script = self.Script(pointer=pointer, parser=self)
        self.data.seek(pointer.converted)
        while True:
            instruction = self.Instruction(script=script)
            if instruction.is_terminator:
                break
        return script

    def read_scripts(self):
        if not hasattr(self, 'scripts'):
            self.scripts = {}
        while True:
            old_pointers = frozenset(self.pointers)
            updated = False
            for p, pointer in sorted(self.pointers.items()):
                if p in self.scripts:
                    continue
                if pointer not in self.script_pointers:
                    continue
                updated = True
                self.scripts[p] = self.read_script(pointer)
                if self.pointers != old_pointers:
                    break
            if not updated:
                break


if __name__ == '__main__':
    config_filename, data_filename = argv[1:]
    p = Parser(config_filename)
