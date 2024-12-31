import struct
from typing import List, Tuple


class KTestError(Exception):
  pass


def _read_objects(f) -> List[Tuple[str, int, bytes, list]]:
  """Read objects from a ktest file"""
  version_no = 4
  hdr = f.read(5)
  if len(hdr) != 5 or (hdr != b'KTEST' and hdr != b'BOUT\n'):
    raise KTestError('Unrecognized file format')

  version, = struct.unpack('>i', f.read(4))
  if version > version_no:
    raise KTestError('Unrecognized version')

  # skip arguments
  numArgs, = struct.unpack('>i', f.read(4))
  for _ in range(numArgs):
    size, = struct.unpack('>i', f.read(4))
    f.read(size)  # skip arg data

  # skip symbolic arguments
  if version >= 2:
    f.read(8)  # skip symArgvs and symArgvLen

  objects = []
  num_objects, = struct.unpack('>i', f.read(4))
  for _ in range(num_objects):
    size, = struct.unpack('>i', f.read(4))
    name = f.read(size).decode('utf-8')
    address = struct.unpack('>Q', f.read(8))
    size, = struct.unpack('>i', f.read(4))
    bytes_data = f.read(size)

    pointers = []
    if version >= 4:
      num_pointers, = struct.unpack('>i', f.read(4))
      for _ in range(num_pointers):
        offset, = struct.unpack('>q', f.read(8))
        index, = struct.unpack('>q', f.read(8))
        index_offset, = struct.unpack('>q', f.read(8))
        pointers.append((offset, index, index_offset))

    objects.append((name, address[0], bytes_data, pointers))

  return objects


def ktest_to_bytes(filename: str) -> bytes:
  """
  Parse a ktest file and return a stream of bytes that can be used as an input corpus.
  """
  try:
    with open(filename, 'rb') as f:
      objects = _read_objects(f)

    # Convert objects to a list of Value objects
    bytes = b''
    for name, _, bytes_data, _ in objects:
      if not name.endswith('.kind'):
        bytes += bytes_data
    return bytes

  except IOError as e:
    raise KTestError(f'Failed to open file: {e}')
  except Exception as e:
    raise KTestError(f'Failed to parse ktest file: {e}')
