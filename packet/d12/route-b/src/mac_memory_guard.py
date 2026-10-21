"""Read-only Mac pressure/RSS guard for the 2026-10-19 shared research policy."""
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
RESEARCH = ROOT.parents[1].resolve()


def snapshot():
    pressure = subprocess.check_output(['/usr/bin/memory_pressure', '-Q'], text=True, timeout=10)
    match = re.search(r'System-wide memory free percentage:\s*(\d+)%', pressure)
    if match is None:
        raise RuntimeError('unrecognized memory_pressure output')
    process_rows = subprocess.check_output(
        ['/bin/ps', '-axo', 'pid=,ppid=,rss=,comm='], text=True, timeout=10)
    processes = {}
    for line in process_rows.splitlines():
        pid, parent, rss, _ = line.strip().split(None, 3)
        processes[int(pid)] = (int(parent), int(rss)*1024)
    # Inspect only working-directory metadata, never other teams' code/results.
    directories = subprocess.run(['/usr/sbin/lsof', '-n', '-P', '-d', 'cwd', '-F', 'pn'],
                                 capture_output=True, text=True, timeout=15)
    if directories.returncode != 0:
        raise RuntimeError('cannot inventory process working directories')
    selected = {os.getpid()}
    pid = None
    for line in directories.stdout.splitlines():
        if line.startswith('p'):
            pid = int(line[1:])
        elif line.startswith('n/') and pid is not None:
            cwd = Path(line[1:]).resolve()
            if cwd == RESEARCH or RESEARCH in cwd.parents:
                selected.add(pid)
    changed = True
    while changed:
        addition = {pid for pid, (parent, _) in processes.items()
                    if parent in selected and pid not in selected}
        changed = bool(addition)
        selected.update(addition)
    measured = {pid: processes[pid][1] for pid in sorted(selected) if pid in processes}
    return {'utc': datetime.now(timezone.utc).isoformat(), 'free_percent': int(match[1]),
            'research_rss_bytes': sum(measured.values()), 'research_pid_rss_bytes': measured,
            'scope': 'all visible research-directory processes and their descendants; current RSS, not other teams historical peaks',
            'peak_self_rss_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


class Guard:
    def __init__(self, limit_bytes=512*1024**2):
        self.limit = limit_bytes
        self.samples = []
        self.next_check = 0

    def check(self, *, start=False, force=False):
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < self.limit, 'local RSS bound'
        if not (start or force) and time.monotonic() < self.next_check:
            return
        row = snapshot()
        self.samples.append(row)
        self.next_check = time.monotonic()+5
        assert row['research_rss_bytes']*1.3 <= 8_000_000_000, 'shared research RSS plus margin exceeds 8GB'
        if start:
            assert row['free_percent'] >= 30, 'starting memory below 30 percent'
            assert (row['research_rss_bytes']+self.limit)*1.3 <= 8_000_000_000, 'new reservation exceeds 8GB'
        else:
            assert row['free_percent'] >= 10, 'memory below 10 percent; stop and preserve partial output'
        row['may_increase_parallelism'] = row['free_percent'] >= 20
