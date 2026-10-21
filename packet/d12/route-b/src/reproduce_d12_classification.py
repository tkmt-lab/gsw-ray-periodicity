"""Rebuild the fixed proof certificates in an isolated local scratch directory."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

STUDY=Path(__file__).resolve().parents[1]
ROOT=STUDY.parents[1]
SOURCES=[
    'check_d12_boundary','d12_affine_certificate','verify_d12_blocks_r2','d12_witness',
    'check_d12_short','d12_affine2','affine2','check_d12_loops','d12_affine3',
    'linear_farkas','verify_d12_blocks','d12_atlas_trace','aligned_atlas','d12',
    'aligned_surface','b2','graphs','audit_d12_classification','mac_memory_guard',
]
INPUTS=['d12-boundary/candidates.json','d12-short/candidates-v2.json']
COMMANDS=['check_d12_boundary','verify_d12_blocks_r2','check_d12_short',
          'check_d12_loops','audit_d12_classification']
COMPARE=[
    ('d12-boundary/symbolic-check-v3.json',('cases','constraints','replays')),
    ('d12-positive-r2/affine-certificates.json',None),
    ('d12-positive-r2/joins.json',None),
    ('d12-short/symbolic-check-v5.json',('domains','coverage','constraints')),
    ('d12-loops/symbolic-check.json',('checks','constraints','replays')),
    ('d12-classification-audit/summary-v2.json',('status','counts')),
]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--summary',type=Path,help='Optional new summary path; default is inside the new scratch directory.')
    args=parser.parse_args()
    if args.summary is not None:
        assert not args.summary.exists(),'summary already exists'
    signal.alarm(120)
    tick=time.monotonic()
    scratch=ROOT/'scratch'
    scratch.mkdir(exist_ok=True)
    target=Path(tempfile.mkdtemp(prefix='d12-proof-replay-',dir=scratch))
    (target/'src').mkdir()
    source_hashes={}
    for name in SOURCES:
        original=STUDY/'src'/f'{name}.py'
        source_hashes[name]=hashlib.sha256(original.read_bytes()).hexdigest()
        if name=='mac_memory_guard':
            # Its resolved source location identifies the shared research tree.
            (target/'src'/original.name).symlink_to(original)
        else:
            shutil.copy2(original,target/'src'/original.name)
    for name in INPUTS:
        dst=target/'evidence'/name
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(STUDY/'evidence'/name,dst)
    commands=[]
    for name in COMMANDS:
        started=time.monotonic()
        run=subprocess.run([sys.executable,str(target/'src'/f'{name}.py')],
                           cwd=ROOT,text=True,capture_output=True,timeout=25)
        (target/f'{name}.stdout').write_text(run.stdout)
        (target/f'{name}.stderr').write_text(run.stderr)
        commands.append(dict(script=name,exit=run.returncode,seconds=time.monotonic()-started))
        assert run.returncode==0,(name,run.stderr)
    comparisons=[]
    for name,fields in COMPARE:
        original=json.loads((STUDY/'evidence'/name).read_text())
        rebuilt=json.loads((target/'evidence'/name).read_text())
        if fields is not None:
            original={k:original[k] for k in fields}
            rebuilt={k:rebuilt[k] for k in fields}
        assert original==rebuilt,('semantic certificate differs',name)
        comparisons.append(dict(path=name,fields=fields,status='EXACT_MATCH',
                                semantic_sha256=hashlib.sha256(
                                    json.dumps(original,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
    result=dict(status='PASS',scratch=str(target.relative_to(ROOT)),
                source_sha256=source_hashes,commands=commands,comparisons=comparisons,
                seconds=time.monotonic()-tick)
    summary=args.summary if args.summary is not None else target/'summary.json'
    summary.parent.mkdir(parents=True,exist_ok=True)
    summary.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
