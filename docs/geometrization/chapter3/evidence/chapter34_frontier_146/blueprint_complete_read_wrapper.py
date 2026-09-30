from pathlib import Path
import hashlib
import io
import _io
import sys
import time

root = Path.cwd().resolve()
audit = root / 'GEOMETRIZATION_BLUEPRINT/audit_blueprint.py'
original_open = Path.open
original_open_code = _io.open_code
cache = {}
retries = []

def complete_bytes(path):
    path = Path(path)
    before = path.stat()
    key = (str(path.absolute()), before.st_size, before.st_mtime_ns)
    if key in cache:
        return cache[key]
    prior_full = None
    for attempt in range(6):
        with original_open(path, 'rb') as stream:
            data = stream.read()
        after = path.stat()
        if len(data) == after.st_size == before.st_size and after.st_mtime_ns == before.st_mtime_ns:
            assert prior_full is None or prior_full == data, "Input bytes changed while stabilizing metadata"
            key = (str(path.absolute()), after.st_size, after.st_mtime_ns)
            cache[key] = data
            return data
        retries.append((str(path), len(data), after.st_size))
        print('Retry incomplete input read:', path, len(data), 'of', after.st_size, flush=True)
        if len(data) == after.st_size:
            assert prior_full is None or prior_full == data, 'Input bytes changed while downloading'
            prior_full = data
        before = after
        time.sleep(1)
    raise RuntimeError('Could not obtain complete unchanged input: ' + str(path))

def complete_open(self, mode='r', buffering=-1, encoding=None, errors=None, newline=None):
    if mode not in ('r', 'rb', 'rt'):
        return original_open(self, mode, buffering, encoding, errors, newline)
    data = complete_bytes(self)
    stream = io.BytesIO(data) if mode == 'rb' else io.StringIO(data.decode(encoding or 'utf-8', errors or 'strict'), newline=newline)
    stream.name = str(self)
    return stream

def complete_open_code(path):
    if str(path).startswith(str(root)):
        stream = io.BytesIO(complete_bytes(path))
        stream.name = str(path)
        return stream
    return original_open_code(path)

Path.open = complete_open
io.open_code = complete_open_code
_io.open_code = complete_open_code
data = complete_bytes(audit)
assert len(data) == 300450
assert hashlib.sha256(data).hexdigest() == 'a71b3b706ed68f757debfad4dbbbf4f80a243ed1db2f56fa5054d23dd54e2018'
print('Executing unchanged audit with complete-file reads; audit SHA256=' + hashlib.sha256(data).hexdigest(), flush=True)
sys.path.insert(0, str(audit.parent))
sys.argv = [str(audit)]
exec(compile(data, str(audit), 'exec'), {'__name__': '__main__', '__file__': str(audit)})
print('Complete-file input validation:', len(cache), 'unchanged size/mtime snapshots;', len(retries), 'incomplete reads retried.', flush=True)
