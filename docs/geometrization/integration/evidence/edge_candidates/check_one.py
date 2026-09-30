from pathlib import Path
import subprocess,os,sys
r=Path.cwd();s=Path('/tmp/gc_edge_migration_scratch');env=dict(os.environ);env['LEAN_PATH']=':'.join([str(s/'build'),str(r/'.lake/build/lib/lean')]+[str(p.resolve()/'.lake/build/lib/lean') for p in (r/'.lake/packages').iterdir() if p.is_dir()])
cmd=['/Users/bennettchow/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean','-DautoImplicit=false','-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-Dweak.linter.mathlibStandardSet=true','-Dlinter.style.header=false','-Dlinter.style.longLine=false',*sys.argv[1:]]
sys.exit(subprocess.run(cmd,env=env).returncode)
