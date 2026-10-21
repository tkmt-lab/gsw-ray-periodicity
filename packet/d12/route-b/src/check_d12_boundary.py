"""Exact verification of the four fixed univariate positive certificates."""
import hashlib
import json
from pathlib import Path
import resource
import signal
import time
import d12_affine_certificate as cert
from mac_memory_guard import Guard


def main():
    signal.alarm(120)
    start = time.monotonic()
    guard = Guard(512*1024**2)
    guard.check(start=True)
    out = Path(__file__).resolve().parents[1]/'evidence/d12-boundary'
    target = out/'symbolic-check-v3.json'
    assert not target.exists()
    raw = (out/'candidates.json').read_bytes()
    data = json.loads(raw)
    result = dict(status='RUNNING', input_sha256=hashlib.sha256(raw).hexdigest(),
                  cases=[], constraints=cert.RECORDS)
    try:
        for case in data['cases']:
            first_constraint = len(cert.RECORDS)
            result['cases'].append(cert.check_case(case))
            for item in cert.RECORDS[first_constraint:]:
                item.update(family=case['name'], lower=case['lower'])
        # Boundary and two explicitly fixed interior replays; these support QA only.
        result['replays'] = [cert.replay(case, t) for case in data['cases']
                             for t in (case['lower'], 7, 11)]
        result['status'] = 'SYMBOLIC_CERTIFICATE_PASS'
    except Exception as error:
        result.update(status='UNPROVED', failure=repr(error))
        raise
    finally:
        guard.check(force=True)
        result['seconds'] = time.monotonic()-start
        result['peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        target.write_text(json.dumps(result, indent=2)+'\n')
        (out/'memory-v3.json').write_text(json.dumps(guard.samples, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('constraints','replays')}))


if __name__ == '__main__':
    main()
