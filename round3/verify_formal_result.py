"""Audit existing successful Lean evidence and identify the exact source.
Does not call Lean or repeat the large finite enumerations.
"""
import hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
FORMAL=ROOT/'formal'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
build=(ROOT/'round3/full-build.log').read_text(encoding='utf-8-sig')
audit=(ROOT/'round3/final-axiom-audit.log').read_text(encoding='utf-8-sig')
assert 'Build completed successfully (1492 jobs).' in build
assert not re.search(r'^error:',build,re.M)
assert 'sorryAx' not in audit
expected={'propext','Classical.choice','Quot.sound',
 'ToroidalQueens23.all_profile_covers_checked._native.native_decide.ax_1_1',
 'ToroidalQueens23.all_profile_masks_checked._native.native_decide.ax_1_1',
 'ToroidalQueens23.powerSum_table._native.native_decide.ax_1_1'}
axioms={}
for theorem in ['minimum_is_twelve','independentDominationNumber_eq_twelve','twelve_suffice']:
 m=re.search(r"'ToroidalQueens23\."+theorem+r"' depends on axioms: \[([^\]]*)\]",audit,re.S)
 assert m,theorem
 names={s.strip() for s in m.group(1).split(',')}
 assert names==(expected if theorem!='twelve_suffice' else {'propext','Classical.choice','Quot.sound'})
 axioms[theorem]=sorted(names)
sources=sorted((FORMAL/'ToroidalQueens23').glob('*.lean'))+[FORMAL/'ToroidalQueens23.lean',FORMAL/'Audit.lean']
native=[]
for p in sources:
 s=p.read_text(encoding='utf-8-sig')
 assert not re.search(r'\b(sorry|admit)\b',s),p
 assert not re.search(r'^\s*(axiom|opaque)\s',s,re.M),p
 for n,line in enumerate(s.splitlines(),1):
  if line.strip()=='native_decide':native.append({'file':str(p.relative_to(ROOT)),'line':n})
assert len(native)==3
dep=json.loads((ROOT/'round3/dependency-audit.json').read_text())
assert dep['status']=='PASS'
profiles=json.loads((ROOT/'round2/profiles.json').read_text())['profiles']
group_counts=[len(profiles[21*b%23]) for b in range(23)]
assert sum(group_counts)==2774
triples=sum(group_counts[b]**2*group_counts[2*b%23] for b in range(23))
assert triples==40620104
M=[[8,0,17,17],[0,2,7,16],[21,0,16,16],[0,15,6,17]]
inverse=[[16,0,6,0],[0,17,0,7],[1,19,4,22],[1,4,4,1]]
assert all(sum(inverse[i][k]*M[k][j] for k in range(4))%23==int(i==j) for i in range(4) for j in range(4))
files=sources+[FORMAL/'lean-toolchain',FORMAL/'lakefile.toml',FORMAL/'lakefile.portable.toml',FORMAL/'lake-manifest.json']
result={'status':'PASS_FORMAL_RESULT_AUDIT','date':'2026-11-08',
 'result':'i(Q_23^t)=12; complete lower bound and upper witness',
 'lean':'4.34.0','mathlib_commit':'5ed2965256430c3649e86755f9576b54eca72435',
 'proof_module_count':len(sources)-2,'source_file_count_including_root_and_audit':len(sources),
 'native_steps':native,'final_axioms':axioms,'candidate_profile_counts_by_root_coefficient':group_counts,
 'all_masks_scanned':8388608,'candidate_entries':2774,'triples_checked':triples,
 'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in files},
 'evidence_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [ROOT/'round3/full-build.log',ROOT/'round3/final-axiom-audit.log',ROOT/'round3/dependency-audit.json',ROOT/'round3/cover-check.log',ROOT/'round3/masks-resume.log']},
 'scope':'Audits completed build and native results, source, dependency comparison, and manuscript arithmetic. Does not rerun exhaustive checks.',
 'portable_export':'Proof source is identical; a separate fresh network build of the portable configuration is not claimed.'}
out=ROOT/'round3/formal-verification.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['source_sha256','evidence_sha256','candidate_profile_counts_by_root_coefficient','final_axioms']}))
