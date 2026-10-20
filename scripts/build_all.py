#!/usr/bin/env python3
"""Run independent snapshots; optional cache is fresh for each invocation."""
import subprocess,sys,pathlib,argparse,tempfile,uuid,json,datetime
root=pathlib.Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--round-cache',help='base directory: a new empty run subdirectory is created');a,rest=p.parse_known_args()
cache_args=[]
if a.round_cache:
 base=pathlib.Path(a.round_cache).resolve();base.mkdir(parents=True,exist_ok=True)
 cache=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=base));run_id=str(uuid.uuid4())
 (cache/'SESSION.json').write_text(json.dumps({'run_id':run_id,'created_at':datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat(),'initial_state':'empty newly created directory'},indent=2)+'\n')
 cache_args=['--round-cache',str(cache),'--cache-run-id',run_id]
for snap in sorted((root/'snapshots').iterdir()):
 if snap.is_dir():subprocess.run([sys.executable,str(root/'scripts/build_snapshot.py'),snap.name,*rest,*cache_args],check=True)
