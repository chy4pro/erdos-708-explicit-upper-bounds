"""Generate exact H97 finite-scale proof certificates.

The source constants supply a selected moment order, not a trusted bound: Lean
checks that order is allowed, its maximizing vertex, and its exact majorant.
Moment bounds are rounded upward to at least fourteen significant decimal digits
using Fraction; scale bounds are rounded upward to multiples of 10^-12. Lean
checks every coefficient row and every N, then proves the eight table bounds.
No floating-point number is used in certificate generation.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys
from math import comb, factorial
if hasattr(sys, "set_int_max_str_digits"): sys.set_int_max_str_digits(0)
ROOT=Path('/Users/roychen/workspace/claudecode/automath')
OUT=ROOT/'lean/proofenv/Erdos708/H97/Proofs'
data=json.loads((ROOT/'engine/out/pro_708_r18/constants.json').read_text())
def frac(v): return F(int(v['numerator']),int(v['denominator']))
def q(v): return f'({v.numerator}/{v.denominator}:ℚ)'
def li(v): return '['+','.join(map(str,v))+']'
def make(j,L,packed=False):
 s=next(s for s in data['finite_scales'] if s['j']==j and s['L']==L)
 lim=s['Nmax']; cap=L+j; name=f'Numeric{j}_{L}'
 es=sorted({a*2**h for h in range(L+1) for a in range(4,8) if j<=a*2**h<=L})
 rows=[]; om=[]; f=[1]+[0]*cap; o=f[:]
 for N in range(lim+1):
  rows.append(f); om.append(o)
  f=[v+sum(f[i-e] for e in es if e<=i) for i,v in enumerate(f)]
  o=[v+sum(o[i-e] for e in es if e<=i and e!=j) for i,v in enumerate(o)]
 eps=[]
 for m in s['moments']:
  ep=frac(m['epsilon']); k=max(14,14+len(str(ep.denominator))-len(str(ep.numerator)))
  den=10**k; eps.append(F((ep.numerator*den+ep.denominator-1)//ep.denominator,den))
 vals=[]
 for N in range(lim+1):
  vals.append(sum((F(rows[N][L+d]-om[N][L+d])*eps[d-1]*max(0,1-max(0,F(N*j-L-d,L))/F(8,3))/max(F(d,L),F(N*j-L,L)) for d in range(1,j+1)),F(0)))
 b=F((max(vals).numerator*10**12+max(vals).denominator-1)//max(vals).denominator,10**12)
 head='import Erdos708.H97.Proofs.NumericDefs\nimport Erdos708.H97.Proofs.ShortExponents\nopen Finset BigOperators\nnamespace Erdos708H97.Proofs.'+name+'\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 1024\n'
 if L>=128: head=head.replace('import Erdos708.H97.Proofs.NumericDefs', 'import Erdos708.H97.Proofs.NumericDefs\nimport Erdos708.H97.Proofs.FastRecurrence')
 if packed: head=head.replace('import Erdos708.H97.Proofs.FastRecurrence','import Erdos708.H97.Proofs.PackedRecurrence')
 text=head+f'def degrees : Finset ℕ := {{{",".join(map(str,es))}}}\nlemma degrees_eq : exponentsExec {j} {L} = degrees := by\n  rw [exponentsExec_eq_short {j} {L} {L.bit_length()-1} (by decide) (by decide)]\n  decide\n'
 if packed:
  digit_bound=1<<max(max(row).bit_length() for row in rows+om)
  radix=64*digit_bound
  text+=f'def radix : ℕ := {radix}\ndef digitBound : ℕ := {digit_bound}\nlemma radix_gt_one : 1<radix := by decide\nlemma digitBound_lt_radix : digitBound<radix := by decide\n'
 for typ,rs in [('f',rows),('o',om)]:
  if L>=128: text+=f'def {typ}degrees : List ℕ := {li(es if typ=="f" else [e for e in es if e!=j])}\n'
  for N,row in enumerate(rs): text+=f'def {typ}{N} : List ℕ := {li(row)}\n'
  E='degrees' if typ=='f' else f'degrees.erase {j}'
  if packed:
   es0=es if typ=='f' else [e for e in es if e!=j]
   code=1+sum(radix**e for e in es0)
   text+=f'def {typ}code : ℕ := {code}\nlemma {typ}code_eq : {typ}code=1+({typ}degrees.map (fun e=>radix^e)).sum := by decide +kernel\n'
   text+=f'lemma {typ}nodup : {typ}degrees.Nodup := by decide\nlemma {typ}set : {typ}degrees.toFinset = {E} := by decide\nlemma {typ}small : ({typ}degrees.length+1)*digitBound<radix := by decide\n'
   for N in range(lim+1): text+=f'lemma {typ}bound{N} : ∀ v∈{typ}{N}, v≤digitBound := by decide +kernel\n'
  for N in range(lim):
   if packed:
    text+=f'lemma {typ}step{N} : {typ}{N+1} = rowStep ({E}) {cap} {typ}{N} := by\n  apply packed_row_certificate {typ}degrees ({E}) {cap} radix digitBound {typ}code {typ}{N} {typ}{N+1} {typ}nodup {typ}set radix_gt_one {typ}small ({typ}bound{N}) (fun v hv => ({typ}bound{N+1} v hv).trans_lt digitBound_lt_radix) (by decide) (by decide) {typ}code_eq\n  decide +kernel\n'
   elif L>=128: text+=f'lemma {typ}step{N} : {typ}{N+1} = rowStepFastList {typ}degrees {typ}{N} := by decide\n'
   else: text+=f'lemma {typ}step{N} : {typ}{N+1} = rowStep ({E}) {cap} {typ}{N} := by decide\n'
  text+=f'def {typ}rows : List (List ℕ) := ['+','.join(f'{typ}{N}' for N in range(lim+1))+']\n'
  text+=f'lemma {typ}base : {typ}rows[0]?.getD [] = rowBase {cap} := by decide\n'
  EE=f'exponentsExec {j} {L}' if typ=='f' else f'(exponentsExec {j} {L}).erase {j}'
  text+=f'lemma {typ}step : ∀ N ∈ range {lim}, {typ}rows[N+1]?.getD [] = rowStep ({EE}) {cap} ({typ}rows[N]?.getD []) := by\n  intro N hN\n  rw [degrees_eq]\n  have hN\' : N < {lim} := mem_range.mp hN\n  interval_cases N\n'
  for N in range(lim):
   text+=f'  · exact {typ}step{N}\n' if L<128 or packed else f'  · exact ({typ}step{N}).trans (rowStepFastList_eq {typ}degrees _ _ _ (by decide) (by decide) (by decide))\n'
 text+='end Erdos708H97.Proofs.'+name+'\n'
 (OUT/(name+'Rows.lean')).write_text(text)
 text=head.replace('import Erdos708.H97.Proofs.NumericDefs',f'import Erdos708.H97.Proofs.{name}Rows')
 text+='def eps : List ℚ := ['+','.join(q(e) for e in eps)+']\n'
 text+=f'lemma eps_bound : ∀ d ∈ (Icc 1 {j} : Finset ℕ), epsilon (({j}:ℝ)/{L}) (1+(d:ℝ)/{L}) ≤ (eps[d-1]?.getD 0:ℚ) := by\n  intro d hd\n  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd\n  interval_cases d\n'
 for m,ep in zip(s['moments'],eps):
  d=m['d'];r=m['r'];v=m['maximizing_vertex']
  aa=(F(541,100)-1-F(d,L))/F(j,L); af=aa.numerator//aa.denominator
  text+=f'  · simp only [Nat.cast_ofNat,Nat.cast_one]\n    have ha : ⌊(T-(1+({d}:ℝ)/{L}))/(({j}:ℝ)/{L})⌋₊ = {af} := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])\n    have hv : maximizingVertex ((T-(1+({d}:ℝ)/{L}))/(({j}:ℝ)/{L})) {r} = {v} := by\n      unfold maximizingVertex\n      apply (Nat.floor_eq_iff (by norm_num [T])).mpr\n      norm_num [T]\n    apply (epsilon_le_moment (({j}:ℝ)/{L}) (1+({d}:ℝ)/{L}) {r} (by rw [momentRange,ha]; norm_num)).trans\n    unfold momentBound hingeMajorant\n    rw [hv,show Nat.choose {v} {r} = {comb(v,r)} by rw [Nat.choose_eq_factorial_div_factorial (by decide)]; decide,show Nat.factorial {r} = {factorial(r)} by decide]\n    norm_num [T,Hstar,eps]\n'
 text+=f'lemma value_bound : ∀ N ∈ range ({lim}+1), rowValueQ {j} {L} N (countsFromRows {j} {L} N frows orows) eps ≤ {q(b)} := by\n  intro N hN\n  have hN\' : N < {lim}+1 := mem_range.mp hN\n  interval_cases N\n'
 for N in range(lim+1):
  counts=[rows[N][L+d]-om[N][L+d] for d in range(1,j+1)]
  text+=f'  · change rowValueQ {j} {L} {N} {li(counts)} eps ≤ {q(b)}\n    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]\n'
 text+=f'lemma scale_bound : AScale {j} {L} ≤ ({b.numerator}/{b.denominator}:ℝ) := by\n  have hh := numeric_scale_bound {j} {L} {q(b)} (fun N => countsFromRows {j} {L} N frows orows) eps\n    (countsFromRows_correct {j} {L} {lim} frows orows fbase fstep obase ostep) eps_bound value_bound\n  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh\n  exact hh\n#print axioms scale_bound\nend Erdos708H97.Proofs.{name}\n'
 (OUT/(name+'.lean')).write_text(text)
 return {'j':j,'L':L,'bound':{'numerator':b.numerator,'denominator':b.denominator},'rows':lim+1}
if __name__=='__main__':
 cases=[(int(sys.argv[1]),int(sys.argv[2]))] if len(sys.argv)>1 else [(s['j'],s['L']) for s in data['finite_scales']]
 result=[make(j,L) for j,L in cases]
 print(json.dumps(result))
