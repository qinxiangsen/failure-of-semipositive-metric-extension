#!/usr/bin/env python3
"""Freeze distribution hashes and create the source ZIP; does not run Lean."""
from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parents[1];ignored={'.git','.lake','.fresh-build','__pycache__'}
files=sorted(p for p in root.rglob('*') if p.is_file() and not ignored.intersection(p.relative_to(root).parts) and p!=root/'SHA256SUMS')
(root/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))+'\n'for p in files))
files.append(root/'SHA256SUMS');files.sort()
manifest=[]
for p in files:
 data=p.read_bytes()
 try:data.decode('utf-8');kind='text'
 except UnicodeDecodeError:kind='binary'
 manifest.append({'path':str(p.relative_to(root)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'kind':kind})
(root.parent/'CLEAN_FILES.json').write_text(json.dumps({'files':manifest,'file_count':len(manifest)},indent=2)+'\n')
archive=root.parent/'Failure_of_Semipositive_Metric_Extension_Lean.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in files:
  info=zipfile.ZipInfo(root.name+'/'+str(p.relative_to(root)),date_time=(2026,10,20,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,p.read_bytes())
print(json.dumps({'archive':archive.name,'bytes':archive.stat().st_size,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'files':len(files)},indent=2))
