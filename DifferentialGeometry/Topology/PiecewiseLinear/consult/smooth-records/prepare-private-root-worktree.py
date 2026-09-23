"""Seed a private OutputRoot with already-accepted prerequisite objects for one target module.

Usage:  python prepare-private-root.py <OutputRoot> <Module.Name>
        (set MOISE_CHECKOUT to the worktree path for an isolated checkout)

Computes the target's DifferentialGeometry import closure from the integration
checkout, decides which modules cannot be taken from the shared read-only build
(absent there, or built from a source that no longer matches), finds an object for
each one in a previously accepted batch whose receipt still matches the current
source byte for byte, copies those into <OutputRoot>, and prints whatever still has
to be compiled.

Never writes to the shared build. Never reuses an object whose receipt does not
record exitCode 0, zero diagnostics, a stable source, and the exact current hash.
"""
import os,re,json,sys,glob,hashlib,shutil,io
sys.stdout=io.TextIOWrapper(sys.stdout.buffer,encoding='utf-8',errors='replace')

D=os.environ.get('MOISE_CHECKOUT', r'D:\differential-geometry-moise-int')
EB=r'E:\differential-geometry-dev\.lake\build\lib\lean'
TMP=r'C:\Users\liao9\AppData\Local\Temp'

if len(sys.argv)<3:
    print(__doc__); sys.exit(2)
OUT,TARGET=sys.argv[1],sys.argv[2]

def rel(m): return os.path.join(*m.split('.'))
def src(m):
    p=os.path.join(D,rel(m)+'.lean')
    return open(p,encoding='utf-8').read().replace('\r\n','\n') if os.path.exists(p) else None
def cursha(m):
    p=os.path.join(D,rel(m)+'.lean')
    return hashlib.sha256(open(p,'rb').read()).hexdigest().lower() if os.path.exists(p) else None

seen=set()
def visit(m):
    if m in seen: return
    seen.add(m)
    s=src(m)
    if s is None: return
    for n in re.findall(r'(?m)^(?:public\s+)?import\s+(DifferentialGeometry(?:\.[A-Za-z0-9_]+)*)',s):
        visit(n)
visit(TARGET)
closure=[m for m in seen if m.startswith('DifferentialGeometry')]

need=set()
for m in closure:
    ip=os.path.join(EB,rel(m)+'.ilean'); op=os.path.join(EB,rel(m)+'.olean')
    if not (os.path.exists(ip) and os.path.exists(op)):
        need.add(m); continue
    s=src(m)
    if s is None: continue
    L=[l.encode('utf-16-le') for l in s.split('\n')]
    il=json.load(open(ip,encoding='utf-8'))
    for name,r in il.get('decls',{}).items():
        if len(r)<8: continue
        short=name.split('.')[-1]
        if short.startswith('inst') or '_macroRules_' in name: continue
        got=L[r[4]][r[5]*2:r[7]*2].decode('utf-16-le') if (r[4]==r[6] and 0<=r[4]<len(L)) else None
        if not (got is not None and (got==short or got==name or got.endswith('.'+short))):
            need.add(m); break

roots=[d for d in glob.glob(os.path.join(TMP,'codex-*'))+glob.glob(os.path.join(TMP,'moise-*'))
       + glob.glob(os.path.join(TMP,'claude-moise-*')) if os.path.isdir(d)]
roots=[r for r in roots if os.path.normcase(r)!=os.path.normcase(OUT)]
found={}
for root in roots:
    for m in need:
        h=cursha(m)
        if h is None: continue
        base=os.path.join(root,rel(m)); obj,rc=base+'.olean',base+'.json'
        if not (os.path.exists(obj) and os.path.exists(rc)): continue
        try: r=json.load(open(rc,encoding='utf-8-sig'))
        except Exception: continue
        if r.get('module')!=m: continue
        if r.get('exitCode')!=0 or r.get('diagnosticLines')!=0 or not r.get('sourceStable'): continue
        if str(r.get('sourceSha256','')).lower()!=h: continue
        try:
            if os.path.normcase(os.path.abspath(r['source']))!=os.path.normcase(os.path.join(D,rel(m)+'.lean')):
                continue
        except Exception: continue
        prev=found.get(m)
        if prev is None or os.path.getmtime(obj)>os.path.getmtime(prev[0]):
            found[m]=(obj,rc,root)

def stale(base,m):
    """An object already in OUT is usable only if its own receipt still matches."""
    rc=base+'.json'
    if not os.path.exists(rc): return True
    try: r=json.load(open(rc,encoding='utf-8-sig'))
    except Exception: return True
    if r.get('module')!=m: return True
    if r.get('exitCode')!=0 or r.get('diagnosticLines')!=0 or not r.get('sourceStable'):
        return True
    return str(r.get('sourceSha256','')).lower()!=cursha(m)

copied=0
refreshed=0
for m,(obj,rc,root) in found.items():
    base=os.path.join(OUT,rel(m))
    os.makedirs(os.path.dirname(base),exist_ok=True)
    present=os.path.exists(base+'.olean')
    if present and not stale(base,m): continue
    if present: refreshed+=1
    else: copied+=1
    shutil.copy2(obj,base+'.olean'); shutil.copy2(rc,base+'.json')
    il=obj[:-6]+'.ilean'
    if os.path.exists(il): shutil.copy2(il,base+'.ilean')
rest=sorted(need-set(found))
print(f'target                : {TARGET}')
print(f'import closure        : {len(closure)} DifferentialGeometry modules')
print(f'need private objects  : {len(need)}')
print(f'seeded from accepted  : {len(found)}  ({copied} newly copied, '
      f'{refreshed} stale refreshed, into {OUT})')
print(f'MUST COMPILE YOURSELF : {len(rest)}')
for m in rest: print('   ',m)
