"""Verify publication file hashes; use --write after intentional source changes."""
from pathlib import Path
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/'MANIFEST.json'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    if args.write:
        files={}
        for p in sorted(ROOT.rglob('*')):
            if not p.is_file() or p==MANIFEST:continue
            rel=p.relative_to(ROOT)
            if any(x in ('.git','.lake','__pycache__') for x in rel.parts):continue
            if p.name in ('lake-manifest.json','axiom-audit.log','semantic-audit.log') and p.parent==ROOT/'formal':continue
            raw=p.read_bytes()
            files[rel.as_posix()]=dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        MANIFEST.write_text(json.dumps(dict(version=1,algorithm='SHA256',files=files),indent=2)+'\n')
    data=json.loads(MANIFEST.read_text())
    for name,expected in data['files'].items():
        p=ROOT/name
        assert '..' not in Path(name).parts and not Path(name).is_absolute()
        raw=p.read_bytes()
        assert len(raw)==expected['bytes'],name
        assert hashlib.sha256(raw).hexdigest()==expected['sha256'],name
    print(json.dumps(dict(status='PASS_PUBLICATION_MANIFEST',files_checked=len(data['files']))))

if __name__=='__main__':main()
