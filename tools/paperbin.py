#!/usr/bin/env python3
"""Restore exact PDF versions from a local paper library; no network access."""
import argparse,hashlib,json,os,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def target(path):
 rel=Path(path)
 if rel.is_absolute() or '..' in rel.parts:raise ValueError('Unsafe PDF path: '+path)
 dest=ROOT/rel
 for parent in dest.parents:
  if parent==ROOT:break
  if parent.is_symlink():raise ValueError('Symlink parent: '+str(parent))
 return dest
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['restore','verify','list']);p.add_argument('--paperbin',type=Path,default=Path(os.environ.get('PAPERBIN',str(Path.home()/'paperbin'))));p.add_argument('--only',default='',help='Original path or directory prefix');p.add_argument('--search',action='store_true',help='Locate matching content anywhere under --paperbin when its indexed location is absent');args=p.parse_args()
 index=json.loads((ROOT/'.papers/index.json').read_text());entries=[e for e in index['papers'] if not args.only or e['path']==args.only or e['path'].startswith(args.only.rstrip('/')+'/')]
 if not entries:raise ValueError('No matching paper paths')
 if args.action=='list':
  for e in entries:print(e['path']+'\t'+e['sha256']+'\t'+e['library_path'])
  return
 found={};counts={'restored':0,'matching':0,'missing':0}
 for e in entries:
  dest=target(e['path'])
  if dest.exists() or dest.is_symlink():
   if dest.is_symlink() or not dest.is_file() or sha(dest)!=e['sha256']:raise ValueError('Refusing to overwrite a different file: '+e['path'])
   counts['matching']+=1;continue
  if args.action=='verify':counts['missing']+=1;continue
  librel=Path(e['library_path'])
  if librel.is_absolute() or '..' in librel.parts:raise ValueError('Unsafe library path')
  source=args.paperbin/librel
  if not source.is_file() or sha(source)!=e['sha256']:
   if args.search and not found:
    for candidate in args.paperbin.rglob('*'):
     if candidate.is_file() and candidate.suffix.lower()=='.pdf':found.setdefault(sha(candidate),candidate)
   source=found.get(e['sha256'])
   if not source:
    print('Missing library PDF: '+e['path']+' (SHA256 '+e['sha256']+')',file=sys.stderr);counts['missing']+=1;continue
  # Verify bytes before exclusive creation; never replace a new report or another session's file.
  raw=source.read_bytes()
  if hashlib.sha256(raw).hexdigest()!=e['sha256']:raise ValueError('Library PDF changed during restore')
  dest.parent.mkdir(parents=True,exist_ok=True)
  with dest.open('xb') as f:f.write(raw)
  dest.chmod(0o755 if e['mode']=='100755' else 0o644);counts['restored']+=1
 print(json.dumps({'paths':len(entries),**counts}))
 if counts['missing']:raise SystemExit(1)
if __name__=='__main__':
 try:main()
 except ValueError as exc:raise SystemExit(str(exc))
