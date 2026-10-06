# VERIFY.md

Verbatim command outputs. Commands were run from the project root, in the order below.

## 1. Clean + full build

Commands run:
```
lake clean; echo CLEAN_EXIT=$?
bash -c 'lake build 2>&1 | tee /tmp/build.log; echo EXIT=$? LAKE_EXIT=${PIPESTATUS[0]}'
```
(`EXIT` is `$?` of the pipeline as requested; `LAKE_EXIT` additionally reports the exit status of `lake build` itself.)

Output of `lake clean; echo CLEAN_EXIT=$?`:
```
CLEAN_EXIT=0
```

`tail -20 /tmp/build.log`:
```
✔ [8343/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B5 (75s)
✔ [8344/8362] Built RequestProject.Zeta7.Hankel2.CertBound (30s)
✔ [8345/8362] Built RequestProject.Zeta35.MainR5 (22s)
✔ [8346/8362] Built RequestProject.Zeta35.DenTable (22s)
✔ [8347/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B4 (76s)
✔ [8348/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B3 (81s)
✔ [8349/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B2 (85s)
✔ [8350/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B1 (87s)
✔ [8351/8362] Built RequestProject.Zeta7.Hankel2.CertData.I0B0 (85s)
✔ [8352/8362] Built RequestProject.Zeta35.MainFinal (17s)
✔ [8353/8362] Built RequestProject.Zeta7.Hankel2.CertData.Interval2 (123s)
✔ [8354/8362] Built RequestProject.Zeta7.Hankel2.CertData.Interval4 (130s)
✔ [8355/8362] Built RequestProject.Zeta7.Hankel2.CertData.Interval3 (131s)
✔ [8356/8362] Built RequestProject.Zeta7.Hankel2.CertData.Interval1 (118s)
✔ [8357/8362] Built RequestProject.Zeta7.Hankel2.CertData.Interval0 (117s)
✔ [8358/8362] Built RequestProject.Zeta7.Hankel2.CertC (11s)
✔ [8359/8362] Built RequestProject.Zeta7.Hankel2.Main2adicR6 (10s)
✔ [8360/8362] Built RequestProject.Zeta7.Hankel2.Main2adicR7 (27s)
✔ [8361/8362] Built RequestProject.Zeta7.Hankel2.Main2adicFinal (9.9s)
Build completed successfully (8362 jobs).
```

EXIT line:
```
EXIT=0 LAKE_EXIT=0
```

`grep -c "error" /tmp/build.log`:
```
0
```

## 2. `lake env lean scripts/print_axioms_Z35_R3.lean; echo EXIT=$?`
```
'Zeta35.zeta3_five_irrational_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.zeta3_five_irrational_R5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Arch.arch_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.thm_5_1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.table_c_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.certL_blk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.lemmaA1_plus3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.prop85_plus3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.TPplus_eq_zero_of_large3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.TP_le_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.sum_psi_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Den.TPplus_le_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.NV.nonvanishing_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta35.Dec.decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

## 3. `lake env lean /tmp/Check.lean; echo EXIT=$?`

Contents of `/tmp/Check.lean` (not kept in the project):
```lean
import RequestProject.Zeta35.MainFinal
#check @Zeta35.zeta3_five_irrational_final
#print Zeta35.zeta3
#print Zeta35.IM
#print Hankel2.volkInt
#print Hankel2.volkSum
#print axioms Zeta35.zeta3_five_irrational_final
```
Output:
```
Zeta35.zeta3_five_irrational_final : ∀ (r : ℚ), Zeta35.zeta3 5 ≠ ↑r
def Zeta35.zeta3 : ℕ → ℚ_[3] :=
fun s => Zeta35.IM (s - 1) / (↑(s - 1) * 3 ^ s)
def Zeta35.IM : ℕ → ℚ_[3] :=
fun M => ∑ a ∈ Finset.Icc 1 2, Hankel2.volkInt 3 fun t => ((t + ↑a / 3) ^ M)⁻¹
def Hankel2.volkInt : (p : ℕ) → [inst : Fact (Nat.Prime p)] → (ℚ_[p] → ℚ_[p]) → ℚ_[p] :=
fun p [Fact (Nat.Prime p)] f => limUnder Filter.atTop (Hankel2.volkSum p f)
def Hankel2.volkSum : (p : ℕ) → [inst : Fact (Nat.Prime p)] → (ℚ_[p] → ℚ_[p]) → ℕ → ℚ_[p] :=
fun p [Fact (Nat.Prime p)] f N => (↑p ^ N)⁻¹ * ∑ t ∈ Finset.range (p ^ N), f ↑t
'Zeta35.zeta3_five_irrational_final' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

## 4. Kernel replay with `leanchecker`

Command: `( time lake env leanchecker RequestProject.Zeta35.MainFinal ) 2>&1; echo EXIT=$?`
(the `real/user/sys` lines come from the shell `time` wrapper; leanchecker itself printed nothing)
```

real	0m29.381s
user	0m16.870s
sys	0m11.970s
EXIT=0
```

Command: `( time lake env leanchecker --fresh RequestProject.Zeta35.MainFinal ) 2>&1; echo EXIT=$?`
(completed; the `real/user/sys` lines come from the shell `time` wrapper; leanchecker itself printed nothing)
```

real	38m27.179s
user	37m9.060s
sys	0m24.730s
EXIT=0
```

## 5. Git state

`git status --short` (before committing `VERIFY.md`):
```
?? VERIFY.md
```

`git diff --stat 1bc2740` (before committing; `1bc2740` is the commit at the start of this task; untracked files are not listed by `git diff`, so the output is empty):
```
```

After `git add VERIFY.md && git commit`, `git diff --stat 1bc2740 HEAD`:
```
 VERIFY.md | 119 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 119 insertions(+)
```

After that commit, `git status --short` (empty):
```
```
