"""Emit finite data only; completeness is checked inside Lean, not assumed here."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
profiles = json.loads((ROOT/'round2/profiles.json').read_text())['profiles']
lines = ['import ToroidalQueens23.Basic','','set_option maxRecDepth 100000','set_option maxHeartbeats 10000000','','namespace ToroidalQueens23','','def coefficientProfiles : Array (List Nat) := #[']
for b in range(23):
    masks = sorted(profiles[21*b % 23])
    lines.append('  ['+', '.join(map(str,masks))+']'+(',' if b<22 else ''))
lines += [']','','end ToroidalQueens23','']
out = ROOT/'formal/ToroidalQueens23/ProfileData.lean'
out.write_text('\n'.join(lines),encoding='utf-8')
print(out)
