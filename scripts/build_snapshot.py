#!/usr/bin/env python3
"""Recompile every paper-owned module in one isolated snapshot; never reuse its old .olean files."""
import argparse, pathlib, subprocess, os, json, hashlib, datetime, re, shutil, sys
try:
 p=argparse.ArgumentParser();p.add_argument('snapshot');p.add_argument('--lean',default=os.environ.get('LEAN_BIN','lean'));p.add_argument('--dependencies',default=os.environ.get('LEAN_DEPENDENCY_ROOT'));p.add_argument('--round-cache',help=argparse.SUPPRESS);p.add_argument('--cache-run-id',help=argparse.SUPPRESS);p.add_argument('--full-legacy-audit',action='store_true',help='Also run E01 legacy Audit with thousands of repeated print-axioms diagnostics');a=p.parse_args()
 root=pathlib.Path(__file__).resolve().parents[1]; snap=root/'snapshots'/a.snapshot
 if not snap.is_dir():p.error('unknown snapshot')
 deps=pathlib.Path(a.dependencies).resolve() if a.dependencies else snap/'.lake/packages'
 if a.round_cache:
  session=json.loads((pathlib.Path(a.round_cache)/'SESSION.json').read_text())
  if not a.cache_run_id or session.get('run_id')!=a.cache_run_id: raise RuntimeError('round cache requires the current build_all session token')
 manifest=json.loads((snap/'lake-manifest.json').read_text());env=os.environ.copy()
 build=snap/'.fresh-build'
 if build.exists(): shutil.rmtree(build)
 build.mkdir()
 logs=root/'verification'/a.snapshot;logs.mkdir(parents=True,exist_ok=True)
 def now():return datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat()
 report={'snapshot':a.snapshot,'started_at':now(),'status':'running','mode':'fresh own modules; precompiled external dependencies','commands':[],'dependencies':[]}
 def save(): (logs/'BUILD_RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
 version=subprocess.check_output([a.lean,'--version'],text=True).strip();report['lean_version']=version;report['launcher_sha256']=hashlib.sha256(pathlib.Path(shutil.which(a.lean) or a.lean).read_bytes()).hexdigest();actual_lean=pathlib.Path(subprocess.check_output([a.lean,'--print-prefix'],text=True).strip())/'bin/lean';report['lean_binary_sha256']=hashlib.sha256(actual_lean.read_bytes()).hexdigest();report['executable_resolution']='Lean --print-prefix/bin/lean'
 if 'version 4.19.0' not in version:raise RuntimeError('Lean 4.19.0 required: '+version)
 paths=[str(build)]
 for pkg in manifest['packages']:
  d=deps/pkg['name']; rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
  if rev!=pkg['rev']:raise RuntimeError('wrong revision '+pkg['name'])
  dirty=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True)
  if dirty: raise RuntimeError('tracked dependency modifications: '+pkg['name'])
  report['dependencies'].append({'name':pkg['name'],'revision':rev,'tracked_worktree_clean':True})
  paths.append(str(d/'.lake/build/lib/lean'))
 env['LEAN_PATH']=os.pathsep.join(paths)
 # Compile the one standard-library module absent from the cached distribution.
 rees=deps/'mathlib/Mathlib/RingTheory/ReesAlgebra.lean'
 if not (deps/'mathlib/.lake/build/lib/lean/Mathlib/RingTheory/ReesAlgebra.olean').exists():
  shutil.copytree(deps/'mathlib/.lake/build/lib/lean/Mathlib',build/'Mathlib',copy_function=lambda s,d: os.symlink(str(pathlib.Path(s).resolve()),d))
  target=build/'Mathlib/RingTheory/ReesAlgebra.olean';target.parent.mkdir(parents=True,exist_ok=True)
  if target.is_symlink(): target.unlink()
  with (logs/'external-ReesAlgebra.log').open('w') as out:
   cmd=[a.lean,'-j1','-o',str(target),str(rees)];r=subprocess.run(cmd,cwd=deps/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
  report['commands'].append({'module':'Mathlib.RingTheory.ReesAlgebra','command':'lean -j1 -o .fresh-build/Mathlib/RingTheory/ReesAlgebra.olean <dependencies>/mathlib/Mathlib/RingTheory/ReesAlgebra.lean','exit_code':r.returncode})
  if r.returncode:report['status']='failed';save();sys.exit(r.returncode)
 mods={str(f.relative_to(snap).with_suffix('')).replace('/','.'):f for f in snap.rglob('*.lean') if 'historical' not in f.parts and '.lake' not in f.parts and '.fresh-build' not in f.parts}
 if a.snapshot=='E01' and not a.full_legacy_audit:
  mods.pop('Audit',None)
  report['optional_diagnostics']=[{'module':'Audit','status':'not requested','reason':'Legacy repeated print-axioms diagnostic; enable --full-legacy-audit to run.'}]
 imports={m:[n for n in re.findall(r'^import\s+([\w.]+)',f.read_text(),re.M) if n in mods] for m,f in mods.items()}
 order=[];vis=set();active=set()
 def visit(m):
  if m in vis:return
  if m in active:raise RuntimeError('import cycle '+m)
  active.add(m)
  for n in imports[m]:visit(n)
  active.remove(m);vis.add(m);order.append(m)
 for m in sorted(mods):visit(m)
 from round_cache import keys_for, register, retrieve
 keys=keys_for(snap,version);cache=pathlib.Path(a.round_cache) if a.round_cache else None
 for i,m in enumerate(order):
  f=mods[m];target=build/pathlib.Path(*m.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
  log=logs/(m+'.log');cmd=[a.lean,'-j1','-o',str(target),str(f)]
  started=now()
  cached=retrieve(cache,keys[m],target) if cache and m.startswith('FailureOfSemipositiveMetricExtension.') else None
  if cached:
   report['commands'].append({'module':m,'source':str(f.relative_to(snap)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'mode':'reused-this-run','cache_key':keys[m],'producer_snapshot':cached['producer_snapshot'],'producer_receipt':cached.get('producer_receipt','verification/'+cached['producer_snapshot']+'/BUILD_RESULT.json'),'olean_sha256':cached['olean_sha256'],'exit_code':0})
   print(a.snapshot,str(i+1)+'/'+str(len(order)),m,'reused-this-run',flush=True);save();continue
  with log.open('w') as out:r=subprocess.run(cmd,cwd=snap,env=env,stdout=out,stderr=subprocess.STDOUT)
  report['commands'].append({'module':m,'source':str(f.relative_to(snap)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'command':'lean -j1 -o .fresh-build/'+str(target.relative_to(build))+' '+str(f.relative_to(snap)),'started_at':started,'finished_at':now(),'mode':'fresh','cache_key':keys[m],'exit_code':r.returncode})
  if cache and r.returncode==0: register(cache,keys[m],target,a.snapshot,m)
  print(a.snapshot,str(i+1)+'/'+str(len(order)),m,r.returncode,flush=True);save()
  if r.returncode:report['status']='failed';report['finished_at']=now();save();sys.exit(r.returncode)
 report['status']='passed';report['finished_at']=now();report['fresh_own_module_count']=sum(c.get('mode')=='fresh' for c in report['commands']);report['reused_this_run_count']=sum(c.get('mode')=='reused-this-run' for c in report['commands']);save()
except Exception as error:
 if "logs" in globals():
  report["status"]="blocked";report["reason"]=str(error);report["finished_at"]=now();save()
 raise
