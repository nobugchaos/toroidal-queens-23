"""Check proof-source hygiene, the fixed toolchain, and optional axiom output."""
from pathlib import Path
import argparse,json,re

ROOT=Path(__file__).resolve().parents[1]
FORMAL=ROOT/'formal'

def without_comments(text):
    output=[]
    i=depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:
            if text[i]=='\n':output.append('\n')
            i+=1
        elif text.startswith('--',i):
            end=text.find('\n',i)
            i=len(text) if end<0 else end
        else:output.append(text[i]);i+=1
    if depth:raise RuntimeError('Unterminated block comment')
    return ''.join(output)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--axiom-log',type=Path)
    args=parser.parse_args()
    assert (FORMAL/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.0'
    config=(FORMAL/'lakefile.toml').read_text()
    assert '5ed2965256430c3649e86755f9576b54eca72435' in config
    sources=[FORMAL/'ToroidalQueens23.lean',FORMAL/'Audit.lean',FORMAL/'SemanticAudit.lean']
    sources+=sorted((FORMAL/'ToroidalQueens23').glob('*.lean'))
    assert len(sources)==20
    native=[]
    for f in sources:
        code=without_comments(f.read_text(encoding='utf-8'))
        bad=re.search(r'\b(sorry|admit|sorryAx|unsafe|implemented_by|extern)\b|^\s*(axiom|opaque|macro|elab|elab_rules|syntax)\b|#eval|run_tac',code,re.M)
        assert not bad, (str(f.relative_to(ROOT)),bad.group() if bad else '')
        for i,line in enumerate(code.splitlines(),1):
            if re.search(r'\bnative_decide\b',line):native.append([f.relative_to(ROOT).as_posix(),i])
    assert len(native)==3,native
    assert {p[0] for p in native}=={
        'formal/ToroidalQueens23/Grid.lean',
        'formal/ToroidalQueens23/ProfileEnumeration.lean',
        'formal/ToroidalQueens23/CoverCheck.lean'}
    axioms_checked=[]
    if args.axiom_log:
        log=args.axiom_log.read_text(encoding='utf-8')
        assert 'sorryAx' not in log
        standard={'propext','Classical.choice','Quot.sound'}
        complete=standard|{
            'ToroidalQueens23.powerSum_table._native.native_decide.ax_1_1',
            'ToroidalQueens23.all_profile_masks_checked._native.native_decide.ax_1_1',
            'ToroidalQueens23.all_profile_covers_checked._native.native_decide.ax_1_1'}
        for name,expected in [('minimum_is_twelve',complete),('independentDominationNumber_eq_twelve',complete),('twelve_suffice',standard)]:
            m=re.search(r"'ToroidalQueens23\."+name+r"' depends on axioms: \[(.*?)\]",log,re.S)
            assert m, name
            actual={s.strip() for s in m.group(1).split(',') if s.strip()}
            assert actual==expected,(name,actual)
            axioms_checked.append(name)
    print(json.dumps(dict(status='PASS_SOURCE_AND_AXIOM_CHECK',lean_source_files=len(sources),
                          native_steps=native,axiom_lists_checked=axioms_checked,
                          scope='Static source checks and, if supplied, the exact printed axiom lists; does not run Lean or prove the theorem.')))

if __name__=='__main__':main()
