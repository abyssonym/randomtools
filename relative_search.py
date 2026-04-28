import gzip
import json
from collections import defaultdict
from io import SEEK_END, BytesIO
from math import ceil
from os import environ, path, replace
from string import ascii_uppercase
from sys import argv
from time import sleep

from bitarray import bitarray

BLOCK_SIZE = 2048
assert bin(BLOCK_SIZE).count('1') == 1
BLOCK_SHIFT = bin(BLOCK_SIZE).count('0') - 1
assert BLOCK_SIZE >> BLOCK_SHIFT == 1
assert (BLOCK_SIZE-1) >> BLOCK_SHIFT == 0

MAX_DIFF_RANGE = 25
DIFF_RANGE_WIDTH = (MAX_DIFF_RANGE * 2) + 1
MAX_RANGE_KEY = (MAX_DIFF_RANGE*2) * (DIFF_RANGE_WIDTH + 1)
TEMP_FILE = '_relative.tmp'


def hexify(s, charsize=1, joiner=' '):
    if charsize == 1:
        return ' '.join([f'{c:0>2x}' for c in s])
    assert charsize == 2
    assert len(s) % charsize == 0
    temp = []
    for a, b in zip(s[::2], s[1::2]):
        c = (a << 8) | b
        temp.append(f'{c:0>4x}')
    return joiner.join(temp)


def reprint(msg):
    print(f'\x1b[1A\r{msg:80}')


def get_index_filename(filename):
    head, tail = path.split(filename)
    index_filename = path.join(head, f'.relative.index.{tail}')
    return index_filename


def write_index_file(metadata, index_data, index_filename):
    test = index_data[min(index_data)]
    test = test[min(test)].tobytes()
    data_width = len(test)
    metadata['DATA_WIDTH'] = data_width
    metadata['DATA_ADDRS'] = {}
    metadata_length = len(metadata).to_bytes(4, 'little')
    with open(TEMP_FILE, 'w+') as f:
        pass
    with open(TEMP_FILE, 'r+b') as f:
        f.write(b'\x00\x00\x00\x00')
        for label in sorted(index_data):
            catdata = index_data[label]
            cataddress = f.tell()
            data = b''
            for key in range(max(catdata.keys())+1):
                subdata = catdata[key].tobytes()
                assert len(subdata) == data_width
                data += subdata
            f.write(gzip.compress(data))
            metadata['DATA_ADDRS'][label] = (cataddress, f.tell())
        metadata_address = f.tell()
        metadata = json.dumps(metadata).encode('ascii')
        f.write(metadata)
        f.seek(0)
        f.write(metadata_address.to_bytes(4, 'little'))
    replace(TEMP_FILE, index_filename)


def read_index_file(index_filename):
    with open(index_filename, 'r+b') as f:
        metadata_address = int.from_bytes(f.read(4), 'little')
        f.seek(metadata_address)
        metadata = json.loads(f.read().decode('ascii'))
        index_data = {}
        for label in sorted(metadata['DATA_ADDRS']):
            start, finish = metadata['DATA_ADDRS'][label]
            f.seek(start)
            data = f.read(finish-start)
            index_data[label] = data
    return metadata, index_data


def convert_key(b_c, a_b):
    x = b_c + MAX_DIFF_RANGE
    y = a_b + MAX_DIFF_RANGE
    key = (y * DIFF_RANGE_WIDTH) + x
    return key


def parse_label(label):
    charsize, byteorder, parity = label.split('.')
    charsize = int(charsize)
    offset = None
    if parity == 'even':
        offset = 0
    elif parity == 'odd':
        offset = 1
    return charsize, byteorder, offset


class Indexer:
    def __init__(self, label, max_block):
        print(f'Starting Indexer {label}...')
        charsize, byteorder, offset = parse_label(label)
        assert 1 <= charsize <= 2
        self.label = label
        self.charsize = charsize
        self.byteorder = byteorder
        assert self.byteorder in ('little', 'big')
        self.little = self.byteorder == 'little'
        if offset > 0:
            self.delay_count = offset
        else:
            self.delay_count = None
        self.current, self.previous = None, None
        self.diff, self.prevdiff = None, None
        self.segment_width = self.charsize * 3
        self.set_put()
        self.block_counter = -self.segment_width
        self.data = {}
        for i in range(MAX_RANGE_KEY+1):
            self.data[i] = bitarray(max_block, 'little')
        self.halfword = False
        sleep(1)

    def delay(self, c):
        self.block_counter += 1
        self.delay_count -= 1
        if self.delay_count == 0:
            self.delay_count = None
            self.set_put()

    def put1(self, c):
        self.block_counter += 1
        self.previous, self.current = self.current, c

        # Processing
        self.prevdiff, self.diff = self.diff, self.current - self.previous
        if self.prevdiff is None:
            return
        if not -MAX_DIFF_RANGE <= self.prevdiff <= MAX_DIFF_RANGE:
            return
        if not -MAX_DIFF_RANGE <= self.diff <= MAX_DIFF_RANGE:
            self.diff = None
            return
        self.block = self.block_counter >> BLOCK_SHIFT
        self.data[((self.diff + MAX_DIFF_RANGE) * DIFF_RANGE_WIDTH)
                  + (self.prevdiff + MAX_DIFF_RANGE)][self.block] = 1

    def put2(self, c):
        self.block_counter += 1

        # Special halfword management
        self.halfword = not self.halfword
        if self.halfword:
            self.partial = c
            return
        self.previous = self.current
        if self.little:
            self.current = (c << 8) | self.partial
        else:
            self.current = (self.partial << 8) | c
        self.partial = None

        # Processing
        self.prevdiff, self.diff = self.diff, self.current - self.previous
        if self.prevdiff is None:
            return
        if not -MAX_DIFF_RANGE <= self.prevdiff <= MAX_DIFF_RANGE:
            return
        if not -MAX_DIFF_RANGE <= self.diff <= MAX_DIFF_RANGE:
            self.diff = None
            return
        self.block = self.block_counter >> BLOCK_SHIFT
        self.data[((self.diff + MAX_DIFF_RANGE) * DIFF_RANGE_WIDTH)
                  + (self.prevdiff + MAX_DIFF_RANGE)][self.block] = 1

    def preput1(self, c):
        self.block_counter += 1
        self.previous, self.current = self.current, c

        # Preprocessing
        self.prevdiff = self.diff
        if self.previous is not None:
            self.diff = self.current - self.previous
        if self.block_counter >= -1:
            self.put = self.put1

    def preput2(self, c):
        self.block_counter += 1

        # Special halfword management
        self.halfword = not self.halfword
        if self.halfword:
            self.partial = c
            return
        self.previous = self.current
        if self.little:
            self.current = (c << 8) | self.partial
        else:
            self.current = (self.partial << 8) | c
        self.partial = None

        # Preprocessing
        self.prevdiff = self.diff
        if self.previous is not None:
            self.diff = self.current - self.previous
        if self.block_counter >= -1:
            self.put = self.put2

    def set_put(self):
        if self.delay_count is not None:
            self.put = self.delay
            return
        if self.charsize == 1:
            self.put = self.preput1
            return
        assert self.charsize == 2
        self.put = self.preput2


def indexinate_file(filename, index_filename=None):
    PROGRESS_INTERVAL = BLOCK_SIZE * 0x20
    print(f'INDEXING {filename}...')
    if index_filename is None:
        index_filename = get_index_filename(filename)

    with open(filename, 'r+b') as infile:
        infile.seek(0, SEEK_END)
        last_address = infile.tell()
        max_block = ceil(last_address / BLOCK_SIZE)

        indexers = []
        if 'INDEXER' in environ:
            for label in environ['INDEXER'].split(','):
                indexers.append(Indexer(label, max_block))
        else:
            indexers.append(Indexer('1.little.even', max_block))
            indexers.append(Indexer('2.little.even', max_block))
            indexers.append(Indexer('2.little.odd', max_block))
            indexers.append(Indexer('2.big.even', max_block))
            indexers.append(Indexer('2.big.odd', max_block))

        progress_counter = PROGRESS_INTERVAL
        infile.seek(0)
        print()
        while True:
            try:
                c = ord(infile.read(1))
            except TypeError:
                break
            progress_counter -= 1
            if progress_counter == 0:
                progress_counter = PROGRESS_INTERVAL
                progress = infile.tell()
                percent = int(round(progress * 100 / last_address))
                reprint(f'Progress: {infile.tell():x} / {last_address:x} '
                        f'({percent}%)')

            for i in indexers:
                i.put(c)

    print()
    metadata = {'BLOCK_SIZE': BLOCK_SIZE}
    index_data = {i.label: i.data for i in indexers}
    write_index_file(metadata, index_data, index_filename)


def get_index_data(filename):
    index_filename = get_index_filename(filename)
    if not path.exists(index_filename):
        indexinate_file(filename, index_filename)
    return read_index_file(index_filename)


def relativize_phrase(phrase):
    phrase = [ord(c) for c in phrase]
    phrase = [(b-a) for (a, b) in zip(phrase, phrase[1:])]
    return phrase


def count_candidates(candidates):
    count = 0
    while candidates:
        if candidates & 1:
            count += 1
        candidates >>= 1
    return count


def search_generic(searchstr, filename, metadata, data,
                   charsize, byteorder, offset):
    data = BytesIO(gzip.decompress(data))
    data_width = metadata['DATA_WIDTH']
    key = convert_key(*searchstr[:2])
    data.seek(key * data_width)
    #seed = data.read(data_width)
    seed = bitarray(0, 'little')
    seed.frombytes(data.read(data_width))
    candidates = seed | (seed << 1)
    for key in zip(searchstr[1:], searchstr[2:]):
        key = convert_key(*key)
        data.seek(key * data_width)
        temp = bitarray(0, 'little')
        temp.frombytes(data.read(data_width))
        candidates &= temp
    candidates = (candidates | (candidates >> 1)) & seed
    #candidates = int.from_bytes(candidates.tobytes(), 'little')
    if not candidates.any():
        return []

    block_size = metadata['BLOCK_SIZE']
    length = len(searchstr)
    datalength = (length + 1) * charsize
    addresses = set()
    found = []
    block_index = -1
    with open(filename, 'r+b') as infile:
        while candidates.any():
            block_index += 1
            if not candidates[block_index]:
                continue
            candidates[block_index] = 0
            previous = None
            infile.seek((block_index * block_size)+offset)
            limit = ((block_index+1) * block_size) + len(searchstr)
            log = []
            while True:
                if infile.tell() >= limit:
                    break
                c = infile.read(charsize)
                if (not c) or (charsize >= 2 and len(c) < charsize):
                    break
                c = int.from_bytes(c, byteorder)
                if previous is not None:
                    diff = c - previous
                    log.append(diff)
                    log = log[-length:]
                    if log == searchstr:
                        address = infile.tell() - datalength
                        addresses.add(address)
                previous = c

        for address in sorted(addresses):
            infile.seek(address)
            phrase = infile.read(datalength)
            found.append((address, hexify(phrase,
                                          charsize=charsize, joiner='.')))

    return sorted(set(found))


def search_bytes(searchstr, filename, metadata, data):
    return search_generic(searchstr, filename, metadata, data,
                          charsize=1, byteorder='little', offset=0)


def search_file(searchstr, filename):
    if searchstr not in (searchstr.upper(), searchstr.lower()):
        if searchstr[1:] == searchstr[1:].lower() \
                and searchstr[0] in ascii_uppercase:
            print('WARNING: Mixed case detected. Ignoring first letter.')
            return search_file(searchstr[1:], filename)
        print('WARNING: Mixed case detected. Assuming ascii-like encoding.')
        searchstr = relativize_phrase(searchstr)
    else:
        searchstr = relativize_phrase(searchstr.lower())
    metadata, index_data = get_index_data(filename)
    block_size = metadata['BLOCK_SIZE']
    found = []
    for label, data in index_data.items():
        charsize, byteorder, offset = parse_label(label)
        temp = search_generic(searchstr, filename, metadata, data,
                              charsize=charsize, byteorder=byteorder,
                              offset=offset)
        found += [(filename, label, a, b) for (a, b) in temp]
    return sorted(set(found))


def generate_report(searchstr, filenames):
    all_found = []
    for filename in filenames:
        all_found = search_file(searchstr, filename)
    if not all_found:
        return 'NO RESULTS'
    longest_filename = max(len(filename) for (filename, _, _, _) in all_found)
    longest_address = max(len(f'{addr:x}') for (_, _, addr, _) in all_found)
    lines = []
    for filename, label, address, data in sorted(set(all_found)):
        filename = ('{0:%s}' % longest_filename).format(filename)
        address = ('{0:0>%sx}' % longest_address).format(address)
        line = f'{filename}  {label}  @{address}: {data}'
        lines.append(line)
    return '\n'.join(lines)


if __name__ == '__main__':
    searchstr = argv[1]
    filenames = argv[2:]

    report = generate_report(searchstr, filenames)
    print(f'\n{report}\n')
