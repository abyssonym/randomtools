from .utils import cached_property, fake_yaml as yaml
from collections import OrderedDict, defaultdict
from copy import deepcopy
from io import BytesIO, SEEK_END
from sys import argv


OPTIMIZE = False


def hexify(s):
    result = []
    while s:
        w = s[:4]
        s = s[4:]
        w = ' '.join('{0:0>2x}'.format(c) for c in w)
        result.append(w)
    return ' '.join(result)


def length_to_num_bits(length):
    length = int(round(length * 10))
    length_bytes = length // 10
    length_bits = length % 10
    assert 0 <= length_bits <= 7
    num_bits = (length_bytes * 8) + length_bits
    return num_bits


def reverse_byte_order(value, length=None, mask=None):
    if mask is None:
        mask = (2**(length*8)) - 1
    assert mask
    while not mask & 1:
        mask >>= 1

    reverse_value = 0
    assert mask & 1
    while True:
        reverse_value <<= 8
        reverse_value |= value & 0xff
        value >>= 8
        mask >>= 8
        if not mask:
            break
    return reverse_value


def mask_shift_left(value, mask):
    assert mask
    count = 0
    while not mask & 1:
        mask >>= 1
        count += 1
    return value << count


class TrackedPointer:
    def __init__(self, pointer, virtual_address, parser):
        self.virtual_address = virtual_address
        self.pointer = pointer
        self.old_pointer = pointer
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
    def converted_repointer(self):
        return self.parser.convert_pointer(self, repointed=True)

    @property
    def converted_smart(self):
        if hasattr(self, 'repointer') and self.repointer is not None:
            return self.converted_repointer
        else:
            return self.converted


class Instruction:
    def __init__(self, script=None, opcode=None, parameters=None, parser=None,
                 start_address=None, end_address=None):
        self.start_address, self.end_address = start_address, end_address
        self.script = None
        self.context = None
        self.parameters = None
        self.text_parameters = None
        if script is not None:
            self.set_script(script)
        if self.script is not None:
            self._parser = self.script.parser
        elif parser is not None:
            self._parser = parser
        self.context = self.script.context
        if opcode is None and parameters is None:
            self.read_from_data()
        if opcode is not None and parameters is not None:
            self.opcode = opcode
            self.set_parameters(**parameters)
        if 'context' in self.manifest:
            self.script.context = self.manifest['context']
        #self.parser.update_format_length(self)

    def __repr__(self):
        if not hasattr(self.parser, 'format_length'):
            self.parser.update_format_length()
        format_length = self.parser.format_length
        s = ('{0:%s}   # {1}' % format_length).format(self.format,
                                                      self.comment)
        if not self.text_parameters:
            return s

        for parameter_name, text in self.text_parameters.items():
            s = f'{s}\n{self.parser.format_text(parameter_name, text)}'
        s = s.replace('\n', '\n  ')
        return s

    def set_script(self, script):
        if self.script is not None and self in self.script.instructions:
            return
        self.script = script
        if self.start_address is None:
            if self.script.instructions:
                self.start_address = max(i.start_address
                                         for i in self.script.instructions) + 1
            else:
                self.start_address = 1
        self.script.instructions.append(self)
        if self.context is None:
            self.context = self.script.context

    def read_from_data(self):
        self.start_address = self.parser.data.tell()
        header_size = self.parser.config['opcode_size']
        header = self.parser.data.read(header_size)
        header_size = len(header)
        header = int.from_bytes(header, byteorder='big')
        self.parser.data.seek(self.start_address)

        instructions = self.parser.get_instructions(context=self.context)
        originals = self.parser.config['contexts'][self.context]['_original']
        valid_opcodes, inherited_opcodes = set(), set()
        for opcode in instructions:
            opcode_size = instructions[opcode]['opcode_size']
            if header_size < opcode_size:
                continue
            mask = instructions[opcode]['mask']
            tempcode = header >> ((header_size - opcode_size) * 8)
            if tempcode & mask == opcode:
                if opcode in originals:
                    valid_opcodes.add(opcode)
                else:
                    inherited_opcodes.add(opcode)

        if not valid_opcodes:
            valid_opcodes = inherited_opcodes

        if len(valid_opcodes) == 0:
            msg = (f'Undefined opcode at @{self.start_address:x}: '
                   f'{header:x} (context {self.context})')
            print(msg)
            import pdb; pdb.set_trace()
            raise Exception(msg)
        if len(valid_opcodes) >= 2:
            msg = (f'Multiple opcode conflict at @{self.start_address:x}: '
                   f'{header:x} (context {self.context})')
            print(msg)
            import pdb; pdb.set_trace()
            raise Exception(msg)
        self.opcode = list(valid_opcodes)[0]

        if self.manifest['length'] == 'variable':
            self.read_variable_length()

        parameters = OrderedDict()
        parameter_order = self.manifest['parameter_order']
        self.parser.data.seek(self.start_address)
        data = self.parser.data.read(self.manifest['length'])

        data = int.from_bytes(data, byteorder='big')
        for parameter_name in parameter_order:
            field = self.manifest['fields'][parameter_name]
            value = data & field['mask']
            tempmask = field['mask']
            while not tempmask & 1:
                tempmask >>= 1
                value >>= 1
            if 'byteorder' in field and field['byteorder'] == 'little':
                value = reverse_byte_order(value, mask=tempmask)
            if 'is_pointer' in field and field['is_pointer']:
                virtual_address = None
                if 'virtual_address' in field:
                    virtual_address = field['virtual_address']
                value = self.parser.get_tracked_pointer(
                        value, virtual_address)
                self.parser.script_pointers.add(value)
            parameters[parameter_name] = value

        self.parameters = parameters
        self.end_address = self.parser.data.tell()
        self.parser.log_read_data(self.start_address, self.end_address)

    def set_parameters(self, **kwargs):
        if not hasattr(self, 'parameters') or self.parameters is None:
            self.parameters = {}
        if not hasattr(self, 'text_parameters') or \
                self.text_parameters is None:
            self.text_parameters = {}
        for parameter_name, value in kwargs.items():
            assert value is not None
            pmani = self.manifest['fields'][parameter_name]
            is_text = 'is_text' in pmani and pmani['is_text']
            if is_text and isinstance(value, str):
                self.text_parameters[parameter_name] = value
                continue
            if not is_text:
                if 'is_pointer' in pmani and pmani['is_pointer']:
                    assert isinstance(value, self.parser.TrackedPointer)
                else:
                    assert not isinstance(value, self.parser.TrackedPointer)
            self.parameters[parameter_name] = value
            if is_text and parameter_name not in self.text_parameters:
                self.text_parameters[parameter_name] = None

    def update_text(self, text, parameter_name=None):
        if parameter_name is None:
            if hasattr(self, 'previous_text_update'):
                parameter_name = self.previous_text_update
            else:
                return False
        if parameter_name not in self.text_parameters:
            return False
        old_text = self.text_parameters[parameter_name]
        if old_text is None:
            self.text_parameters[parameter_name] = text
        else:
            self.text_parameters[parameter_name] = '\n'.join([old_text, text])
        return True

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
            pmani = self.manifest['fields'][parameter_name]
            prettified = None
            prettify_table = None
            if 'prettify' in pmani:
                prettify_table = pmani['prettify']
            if prettify_table is None and 'prettify' in self.parser.config \
                    and parameter_name in self.parser.config['prettify']:
                prettify_table = self.parser.config['prettify'][parameter_name]
            if prettify_table is not None:
                value = parameters[parameter_name]
                if value not in prettify_table:
                    value = -1
                prettified = prettify_table[value].format(**parameters)
            if prettified is not None:
                parameters[f'_pretty_{parameter_name}'] = prettified
        if 'comment' not in self.manifest:
            return f'Unknown {self.opcode:0>2x}'
        return self.manifest['comment'].format(**parameters)

    @property
    def parser(self):
        if hasattr(self, '_parser'):
            if self.script is not None:
                assert self.script.parser is self._parser
            return self._parser
        return self.script.parser

    @cached_property
    def manifest(self):
        instructions = self.parser.get_instructions(context=self.context)
        manifest = instructions[self.opcode]
        assert 'inherit' not in manifest
        return manifest

    @property
    def references(self):
        return [v for (k, v) in self.parameters.items()
                if isinstance(v, self.parser.TrackedPointer)]

    @property
    def referenced_scripts(self):
        return [self.parser.scripts[r.pointer] for r in self.references
                if r.pointer in self.parser.scripts]

    @property
    def is_terminator(self):
        return self.opcode in self.parser.config['terminators']

    @property
    def bytecode(self):
        bytecode = self.parser.instruction_to_bytecode(self)
        assert len(bytecode) == self.bytecode_length
        return bytecode

    @property
    def bytecode_length(self):
        length = self.manifest['length']
        if length == 'variable':
            raise NotImplementedError
        return length


class Script:
    def __init__(self, pointer, parser):
        self.pointer = pointer
        self.parser = parser
        self.instructions = []
        self.parser.set_context(self)
        self.joined_before, self.joined_after = None, None

    def __repr__(self):
        header = self.parser.format_pointer(self.pointer)
        lines = [header]
        start_addresses = [f'{i.start_address:x}' for i in self.instructions]
        address_length = 0
        if start_addresses:
            address_length = max(len(addr) for addr in start_addresses)

        for instruction in self.instructions:
            line = '{0:0>%sx}. {1}' % address_length
            try:
                lines.append(line.format(instruction.start_address,
                                         instruction))
            except TypeError:
                lines.append(line.format(instruction.start_address,
                                         'UNKNOWN'))
        if self.joined_after:
            after = self.joined_after
            line = f'{after.pointer.pointer:x}. {after.pointer}'
            lines.append(line)
        s = '\n'.join(lines)
        s = s.replace('\n', '\n  ')
        return s.strip()

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
        scripts = {v for (k, v) in self.parser.scripts.items()
                   if k in references}
        return scripts

    @property
    def bytecode(self):
        bytecode = self.parser.script_to_bytecode(self)
        assert len(bytecode) == self.bytecode_length
        return bytecode

    @property
    def bytecode_length(self):
        bytecode_length = sum([i.bytecode_length for i in self.instructions])
        return bytecode_length

    @property
    def joined_start(self):
        before = self
        while before.joined_before:
            before = before.joined_before
        return before

    @property
    def joined_bytecode(self):
        after = self.joined_start
        bytecode = after.bytcode
        while after.joined_after:
            after = after.joined_after
            bytecode += after.bytecode
        return bytecode

    @property
    def joined_bytecode_length(self):
        after = self.joined_start
        bytecode_length = after.bytecode_length
        while after.joined_after is not None:
            after = after.joined_after
            bytecode_length += after.bytecode_length
        return bytecode_length

    @property
    def joined_references(self):
        after = self.joined_start
        references = set(after.references)
        chain = {self.pointer}
        while after.joined_after is not None:
            after = after.joined_after
            chain.add(after.pointer)
            references |= after.references
        return references - chain

    @property
    def joined_referenced_scripts(self):
        references = {r.pointer for r in self.joined_references}
        references.add(self.joined_start.pointer.pointer)
        scripts = {v for (k, v) in self.parser.scripts.items()
                   if k in references}
        return scripts

    def insert_instruction(self, index, text):
        instruction = self.parser.interpret_instruction(text, self)
        instruction.start_address = 0
        self.instructions.insert(index, instruction)

    def append_instruction(self, text):
        self.insert_instruction(len(self.instructions), text)

    def prepend_instruction(self, text):
        self.insert_instruction(0, text)

    def register_external_references(self):
        raise NotImplementedError
        internal_addresses = {i.start_address for i in self.instructions}
        for p in self.references:
            if p.converted not in internal_addresses:
                self.parser.script_pointers.add(p)

    def split(self, pointer):
        ever_after = self.joined_after
        new_script = self.parser.Script(pointer=pointer,
                                        parser=self.parser)
        after_instructions = [i for i in self.instructions
                              if pointer.converted <= i.start_address]
        self.instructions = [i for i in self.instructions
                             if i not in after_instructions]
        new_script.instructions = after_instructions
        if ever_after is not None:
            assert ever_after.joined_before is self
            self.joined_after = None
            ever_after.joined_before = new_script
            new_script.joined_after = ever_after
        self.join(new_script)
        return self, new_script

    def join(self, script):
        if self.joined_after:
            assert self.joined_after is script
        if script.joined_before:
            assert script.joined_before is self
        self.joined_after = script
        script.joined_before = self
        assert self.joined_after.joined_before is self
        assert script.joined_before.joined_after is script


class Parser:
    Script = Script
    Instruction = Instruction
    TrackedPointer = TrackedPointer

    def __init__(self, config, data, pointers, log_reads=False):
        if isinstance(config, dict):
            self.config = config
        else:
            with open(config, encoding='utf8') as f:
                self.config = yaml.safe_load(f.read())
        self.clean_config()
        if not isinstance(data, bytes):
            assert isinstance(data, str)
            with open(data, 'r+b') as f:
                data = f.read()
        self.data = BytesIO(data)
        self.original_data = self.data.read()
        self.max_address = self.data.tell()
        self.data.seek(0)
        self.log_reads = log_reads
        self.readlog = None
        if self.log_reads:
            self.readlog = BytesIO(bytes(len(self.original_data)))
        self.pointers = {}
        self.script_pointers = set()
        for p in pointers:
            self.add_pointer(p, script=True)
        self.get_text_decode_table()
        self.read_scripts()

    def clean_config(self):
        for conname, context in self.config['contexts'].items():
            instructions = context['instructions']
            if '_original' not in context:
                context['_original'] = deepcopy(instructions)
            if 'inherit' in context:
                incontexts = context['inherit']
                incontexts = incontexts.split(',')
                for incontext in incontexts:
                    inconin = self.config['contexts'][incontext]
                    for opcode, v in inconin['instructions'].items():
                        if opcode not in instructions:
                            instructions[opcode] = v
                del(context['inherit'])

            for opcode, inconf in instructions.items():
                while 'inherit' in inconf:
                    incode = inconf['inherit']
                    del(inconf['inherit'])
                    for key in instructions[incode]:
                        if key in inconf:
                            inconf[key] = deepcopy(instructions[incode][key])

                assert 'parameters' not in inconf
                if 'mask' not in inconf:
                    if opcode == 0:
                        mask = 0xff
                    else:
                        mask = 0
                        while True:
                            mask <<= 8
                            mask |= 0xff
                            if mask & opcode == opcode:
                                break
                    inconf['mask'] = mask
                else:
                    mask = inconf['mask']
                maskmask = 0
                opcode_size = 0
                while True:
                    opcode_size += 1
                    maskmask <<= 8
                    maskmask |= 0xff
                    if mask & maskmask == mask:
                        break
                inconf['opcode_size'] = opcode_size

                if 'length' not in inconf:
                    inconf['length'] = opcode_size

                if inconf['length'] == 'variable':
                    continue

                if 'fields' not in inconf:
                    length = inconf['length']
                    fieldmask = (1 << (length * 8)) - 1
                    fieldmask ^= inconf['mask'] << ((length-opcode_size)*8)
                    if fieldmask:
                        fields = {'_unknown': {'mask': fieldmask,
                                               'byteorder': 'big',
                                               'is_pointer': False}}
                    else:
                        fields = {}
                    inconf['fields'] = fields

                if 'parameter_order' not in inconf:
                    inconf['parameter_order'] = [k for k in inconf['fields']]

    def log_read_data(self, start, finish):
        if not self.log_reads:
            return
        assert start <= finish
        self.readlog.seek(start)
        self.readlog.write(b'\xff' * (finish-start))
        assert self.readlog.tell() == finish
        self.readlog.seek(0)

    def get_unread_data(self):
        self.readlog.seek(0)
        data = BytesIO(self.original_data)
        data.seek(0)
        unread_data = {}
        current_segment = b''
        current_pointer = 0
        while True:
            peek = self.readlog.read(1)
            if len(peek) == 0:
                break
            if peek == b'\x00':
                if not current_segment:
                    current_pointer = self.readlog.tell() - 1
                data.seek(self.readlog.tell() - 1)
                current_segment += data.read(1)
            elif peek == b'\xff':
                if current_segment:
                    unread_data[current_pointer] = current_segment
                    current_segment = b''
        if current_segment:
            unread_data[current_pointer] = current_segment
            current_segment = b''
        return unread_data

    def set_context(self, script):
        script.context = self.config['default_context']

    def get_instructions(self, context=None):
        return self.config['contexts'][context]['instructions']

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

    def convert_pointer(self, pointer, repointed=False):
        if repointed:
            return pointer.repointer - pointer.virtual_address
        else:
            return pointer.pointer - pointer.virtual_address

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

    def decode(self, pointer, data=None):
        if data is None:
            data = self.data
        if isinstance(data, bytes):
            data = BytesIO(data)
        address = data.tell()
        data.seek(pointer)
        decoded = ''
        char_size = self.config['text_char_size']
        while True:
            value = data.read(char_size)
            if len(value) < char_size:
                decoded += '{EOF}'
                break
            value = int.from_bytes(value, byteorder=self.config['byte_order'])
            if value in self.text_decode_table:
                decoded += self.text_decode_table[value]
            else:
                word = ('{0:0>%sx}' % (char_size*2)).format(value)
                decoded += '{%s}' % word
            if value in self.config['text_terminators']:
                break
        self.log_read_data(pointer, data.tell())
        data.seek(address)
        return decoded

    def encode(self, text):
        original_text = text
        bytecode = b''
        char_size = self.config['text_char_size']
        byteorder = self.config['byte_order']
        encode_order = sorted(self.text_encode_table,
                              key=lambda w: (-len(w), w))
        while True:
            if not text:
                break
            value = None
            if text.startswith('{'):
                index = text.index('}')
                word = text[0:index+1]
                if word == '{EOF}':
                    break
                elif word in self.text_encode_table:
                    value = self.text_encode_table[word]
                else:
                    value = int(word[1:-1], 0x10)
                text = text[index+1:]
            else:
                for word in encode_order:
                    if '{' in word:
                        continue
                    if text.startswith(word):
                        value = self.text_encode_table[word]
                        text = text[len(word):]
                        break
            if value is None:
                raise Exception(f'Unable to encode "{text}".')
            bytecode += value.to_bytes(length=char_size,
                                       byteorder=byteorder)
        if value not in self.config['text_terminators']:
            print(f'WARNING: "{original_text}" not terminated properly.')
        return bytecode

    def get_text(self, value, instruction):
        raise NotImplementedError

    def read_variable_length(self, instruction, parameters):
        raise NotImplementedError

    def get_next_instruction(self, script, start_address=None):
        if start_address is None and script.instructions:
            end_address = script.instructions[-1].end_address
            if end_address == self.data.tell():
                start_address = end_address
        if start_address == self.max_address:
            return None
        instruction = self.Instruction(script=script,
                                       start_address=start_address)
        return instruction

    def read_script(self, pointer):
        if self.scripts:
            nearest = max({s for s in self.scripts.values()
                           if s.pointer < pointer or s.pointer == pointer})
            assert nearest.pointer != pointer
            for i in nearest.instructions:
                if i.start_address == pointer.converted:
                    a, b = nearest.split(pointer)
                    assert b.pointer == pointer
                    return b
        script = self.Script(pointer=pointer, parser=self)
        self.data.seek(pointer.converted)
        #print(hex(self.data.tell()))
        while True:
            instruction = self.get_next_instruction(script=script)
            #print(instruction)
            if instruction is None or instruction.is_terminator:
                break
        #script.register_external_references()
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
        #self.update_format_length()

    def format_opcode(self, opcode):
        length = self.config['opcode_size'] * 2
        opcode = f'{opcode:x}'
        while len(opcode) % 2:
            opcode = f'0{opcode}'
        assert len(opcode) <= length
        return ('{0:<%s}' % length).format(opcode)

    def format_parameter(self, instruction, parameter_name):
        value = instruction.parameters[parameter_name]
        if isinstance(value, int):
            mask = instruction.manifest['fields'][parameter_name]['mask']
            while not mask & 1:
                mask >>= 1
            length = len(f'{mask:x}')
            if length < 2:
                length += 1
            parameter = ('{0:0>%sx}' % length).format(value)
        elif isinstance(value, bytes):
            if parameter_name in instruction.text_parameters:
                parameter = parameter_name
            else:
                parameter = ''.join(f'{c:0>2x}' for c in value)
        elif isinstance(value, list):
            if not value:
                raise NotImplementedError
            parameter_list = []
            for v in value:
                if isinstance(v, int):
                    parameter_list.append(f'{v:x}')
                elif isinstance(v, bytes):
                    parameter_list.append(''.join(f'{c:0>2x}' for c in v))
                else:
                    parameter_list.append(str(v))
            parameter = ','.join(parameter_list)
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

    def update_format_length(self, instruction=None):
        lengths = []
        if instruction is not None:
            new_length = len(instruction.format)
            if not hasattr(self, 'format_length'):
                self.format_length = new_length
            if new_length <= self.format_length:
                return
            lengths.append(new_length)
        for script in self.scripts.values():
            for i in script.instructions:
                lengths.append(len(i.format))
        mean = sum(lengths) / len(lengths)
        median = sorted(lengths)[len(lengths) >> 1]
        deviation = sum((l-mean)**2 for l in lengths) / len(lengths)
        threshold = mean + (2 * deviation)
        self.format_length = max(l for l in lengths if l <= threshold)

    def interpret_opcode(self, opcode, context):
        if context is None:
            context = self.config['default_context']
        opcode = int(opcode, 0x10)
        instructions = self.config['contexts'][context]['instructions']
        if opcode in instructions:
            return opcode
        return None

    def interpret_parameter(self, parameter):
        if parameter.startswith('@'):
            return self.interpret_pointer(parameter)
        else:
            try:
                return int(parameter, 0x10)
            except ValueError:
                return None

    def interpret_pointer(self, pointer):
        pointer = pointer.split('#')[0].strip()
        if pointer.startswith('@'):
            try:
                pointer = int(pointer[1:], 0x10)
                return self.get_tracked_pointer(pointer)
            except ValueError:
                return None

    def interpret_instruction(self, line, script=None):
        if script is not None:
            context = script.context
        else:
            context = self.config['default_context']
        line = line.split('#')[0].strip()
        if line.count(':') > 1:
            return None
        line_number = None
        if '.' in line:
            line_number, line = line.split('.')
            line_number = int(line_number.strip(), 0x10)
            line = line.strip()
        if line.count(':') == 0:
            assert line.startswith('@')
            script_pointer = int(line[1:], 0x10)
            joined_script = self.scripts[script_pointer]
            if script.joined_after is None:
                script.join(joined_script)
            assert script.joined_after == joined_script
            return True
        opcode, parameters = line.split(':')
        assert opcode.count('.') <= 1
        opcode = self.interpret_opcode(opcode.strip(), context)
        if opcode is None:
            return None
        manifest = self.config['contexts'][context]['instructions'][opcode]
        parameters = parameters.replace(' ', '').strip()
        if parameters:
            parameters = parameters.split(',')
        else:
            parameters = []
        if 'parameter_order' in manifest:
            if len(parameters) != len(manifest['parameter_order']):
                return None
        elif parameters:
            return None
        parameters = [self.interpret_parameter(parameter)
                      for parameter in parameters]
        if parameters:
            parameter_order = manifest['parameter_order']
            parameters = dict(zip(parameter_order, parameters))
        else:
            parameters = {}
        try:
            i = self.Instruction(script=script, opcode=opcode,
                                 parameters=parameters)
        except:
            return None
        if line_number is not None:
            i.start_address = line_number
        return i

    def interpret_text(self, text, instruction):
        text = text.strip()
        for parameter_name in instruction.text_parameters:
            if text.startswith(f'{parameter_name}:'):
                text = text.split(':', 1)[1].strip()
                break
        else:
            parameter_name = None
        if not (text.startswith('|') and text.endswith('|')):
            return None
        text = text[1:-1]
        return instruction.update_text(text, parameter_name=parameter_name)

    def import_script(self, script_text):
        current_script = None
        for line in script_text.split('\n'):
            line = line.strip()
            if line.startswith('#'):
                continue
            if not line:
                continue
            result = self.interpret_pointer(line)
            if result:
                if result.pointer in self.scripts:
                    current_script = self.scripts[result.pointer]
                    current_script.instructions = []
                else:
                    current_script = self.Script(pointer=result, parser=self)
                    self.scripts[result.pointer] = current_script
                assert current_script is self.scripts[result.pointer]
                continue
            if current_script:
                result = self.interpret_instruction(line, current_script)
                if result is True:
                    # script is joined to next script
                    assert current_script.joined_after is not None
                    current_script = None
                    continue
                if isinstance(result, self.Instruction):
                    #print(result)
                    assert result.script is current_script
                    continue
            prev_instruction = None
            if current_script and current_script.instructions:
                prev_instruction = current_script.instructions[-1]
            if prev_instruction and prev_instruction.text_parameters:
                result = self.interpret_text(line, prev_instruction)
                if result:
                    continue
            raise Exception(f'Unable to interpret "{line}"')

    def text_to_parameter_bytecode(self, parameter_name, instruction):
        raise NotImplementedError

    def instruction_to_bytecode(self, instruction):
        length = instruction.manifest['length']
        if length == 'variable':
            raise NotImplementedError

        difference = (instruction.manifest['length'] -
                      instruction.manifest['opcode_size'])
        assert difference >= 0
        opcode = instruction.opcode << (difference * 8)
        opcode_mask = instruction.manifest['mask'] << (difference * 8)
        value = opcode
        for verify in [False, True]:
            for parameter_name in instruction.manifest['parameter_order']:
                parameter = instruction.parameters[parameter_name]
                if isinstance(parameter, self.TrackedPointer):
                    parameter = parameter.converted_smart
                field = instruction.manifest['fields'][parameter_name]
                mask = field['mask']
                if 'is_text' in field:
                    raise NotImplementedError
                if 'byteorder' in field and field['byteorder'] != 'big':
                    parameter = reverse_byte_order(parameter, mask=mask)
                parameter = mask_shift_left(parameter, mask)
                if not verify:
                    value |= parameter
                else:
                    assert value & mask == parameter
        assert value & opcode_mask == opcode
        bytecode = value.to_bytes(length=length, byteorder='big')
        return bytecode

    def script_to_bytecode(self, script):
        return b''.join(i.bytecode for i in script.instructions)

    def dump_all_scripts(self, header=None):
        if header is None:
            header = b''
        bytecode = BytesIO(header)

        if OPTIMIZE:
            scripts_by_dependency = defaultdict(set)
            for _, s in self.scripts.items():
                for d in s.joined_referenced_scripts:
                    scripts_by_dependency[d].add(s)

        done_scripts = set()
        assert not any(hasattr(s.pointer, 'repointer')
                       for s in self.scripts.values())
        chosen = None
        while True:
            todo_scripts = set(self.scripts.values()) - done_scripts
            if not todo_scripts:
                break
            if chosen is None:
                candidates = {s for s in todo_scripts
                              if s.joined_before is None}
                if OPTIMIZE:
                    candidates = {
                        s for s in candidates
                        if s.joined_referenced_scripts <= done_scripts | {s}}
                    chosen = max(candidates,
                                 key=lambda s: (s.joined_bytecode_length, s))
                else:
                    chosen = min(candidates, key=lambda s: s.pointer.pointer)
            assert chosen is not None
            assert chosen not in done_scripts
            assert chosen is self.scripts[chosen.pointer.old_pointer]
            bytecode.seek(0, SEEK_END)
            repointer = bytecode.tell() | chosen.pointer.virtual_address
            assert not hasattr(chosen.pointer, 'repointer')
            assert chosen is self.scripts[chosen.pointer.pointer]
            chosen.pointer.repointer = repointer
            if chosen.joined_before:
                before_pointer = chosen.joined_before.pointer.repointer
                before_length = chosen.joined_before.bytecode_length
                assert repointer-before_pointer == before_length
            assert bytecode.tell() == chosen.pointer.converted_repointer
            bytecode.write(chosen.bytecode)
            done_scripts.add(chosen)
            chosen = chosen.joined_after

        def dump_write_all():
            for s in self.scripts.values():
                bytecode.seek(s.pointer.converted_repointer)
                bytecode.write(s.bytecode)

        if OPTIMIZE:
            ordered = sorted(self.scripts.values(), reverse=True,
                             key=lambda s: (s.joined_bytecode_length, s))
            optimize = OPTIMIZE
            while optimize:
                optimize = False
                dump_write_all()
                bytecode.seek(0)
                data = bytecode.read()
                for s in ordered:
                    sdata = s.bytecode
                    assert sdata in data
                    index = data.index(sdata)
                    assert index <= s.pointer.converted_repointer
                    if index < s.pointer.converted_repointer:
                        if index < len(header):
                            raise NotImplementedError
                        raise NotImplementedError

        dump_write_all()
        for s in self.scripts.values():
            bytecode.seek(s.pointer.converted_repointer)
            script_bytecode = bytecode.read(s.bytecode_length)
            assert s.bytecode == script_bytecode

        bytecode.seek(0)
        result = bytecode.read()
        return result

    def to_bytecode(self):
        raise NotImplementedError


if __name__ == '__main__':
    config_filename, data_filename = argv[1:]
    p = Parser(config_filename)
