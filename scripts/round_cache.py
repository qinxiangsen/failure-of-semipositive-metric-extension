"""Conservative cache for outputs actually compiled during this verification run."""
import hashlib,json,pathlib,re,shutil,os
FLAGS=['-j1']
def keys_for(snap,version):
 files={str(f.relative_to(snap).with_suffix('')).replace('/','.'):f for f in snap.rglob('*.lean') if not {'historical','.lake','.fresh-build'}.intersection(f.parts)}
 lock=json.loads((snap/'lake-manifest.json').read_text());revisions=sorted((p['name'],p['rev']) for p in lock['packages'])
 keys={}
 def key(m):
  if m in keys:return keys[m]
  f=files[m];deps=re.findall(r'^import\s+([\w.]+)',f.read_text(),re.M)
  own=[(d,key(d)) for d in deps if d in files]
  payload={'module':m,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'own_imports':own,'all_imports':deps,'external_revisions':revisions,'lean_version':version,'flags':FLAGS}
  keys[m]=hashlib.sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest();return keys[m]
 for m in files:key(m)
 return keys
def register(cache,key,output,snapshot,module):
 cache.mkdir(parents=True,exist_ok=True);target=cache/key
 if not output.exists():return
 tmp=cache/(key+'.'+str(os.getpid())+'.tmp');shutil.copy2(output,tmp);os.replace(tmp,target)
 session=json.loads((cache/'SESSION.json').read_text())
 meta={'run_id':session['run_id'],'cache_key':key,'compiled_in_this_run':True,'producer_snapshot':snapshot,'producer_module':module,'producer_receipt':'verification/'+snapshot+'/BUILD_RESULT.json','olean_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
 (cache/(key+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
def retrieve(cache,key,target):
 p=cache/key;mp=cache/(key+'.json')
 if not p.exists() or not mp.exists():return None
 meta=json.loads(mp.read_text()); session=json.loads((cache/'SESSION.json').read_text())
 if meta.get('run_id')!=session['run_id'] or meta.get('cache_key')!=key or not meta.get('compiled_in_this_run') or hashlib.sha256(p.read_bytes()).hexdigest()!=meta['olean_sha256']:return None
 shutil.copy2(p,target);return meta
