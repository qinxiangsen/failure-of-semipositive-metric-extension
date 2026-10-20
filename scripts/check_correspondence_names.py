#!/usr/bin/env python3
"""Check source declaration names and types after the corresponding snapshot build. Not semantic review."""
import pathlib,json,os,subprocess,argparse,datetime,hashlib
p=argparse.ArgumentParser();p.add_argument('--lean',default=os.environ.get('LEAN_BIN','lean'));p.add_argument('--dependencies',default=os.environ.get('LEAN_DEPENDENCY_ROOT'));a=p.parse_args();root=pathlib.Path(__file__).resolve().parents[1]
results=[]
for snap in sorted((root/'snapshots').iterdir()):
 f=snap/'PaperSourceAudit.lean'
 if not f.exists():continue
 deps=pathlib.Path(a.dependencies).resolve() if a.dependencies else snap/'.lake/packages';lock=json.loads((snap/'lake-manifest.json').read_text());env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(snap/'.fresh-build')]+[str(deps/x['name']/'.lake/build/lib/lean') for x in lock['packages']]);log=root/'verification'/snap.name/'CORRESPONDENCE_NAMES.log'
 with log.open('w') as out:r=subprocess.run([a.lean,'-j1',str(f)],cwd=snap,env=env,stdout=out,stderr=subprocess.STDOUT)
 results.append({'snapshot':snap.name,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'command':'lean -j1 PaperSourceAudit.lean','exit_code':r.returncode,'finished_at':datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat()})
(root/'verification/CORRESPONDENCE_NAMES.json').write_text(json.dumps({'scope':'names and types only; see separate semantic review','results':results},indent=2)+'\n')
raise SystemExit(any(x['exit_code'] for x in results))
