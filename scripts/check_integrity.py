#!/usr/bin/env python3
"""Distribution-byte verification only. Does not invoke Lean or prove semantic coverage."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS'
if not manifest.exists():raise SystemExit('SHA256SUMS is absent: distribution has not been frozen')
fail=[];count=0;expected=set()
for line in manifest.read_text().splitlines():
 digest,rel=line.split('  ',1);expected.add(rel);p=root/rel
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:fail.append(rel)
 count+=1
ignored={'.git','.lake','.fresh-build','__pycache__'}
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and not ignored.intersection(p.relative_to(root).parts) and p!=root/'SHA256SUMS'}
extra=sorted(actual-expected)
print(json.dumps({'checked_files':count,'mismatches':fail,'unexpected_files':extra,'scope':'file integrity only'},indent=2))
raise SystemExit(bool(fail or extra))
