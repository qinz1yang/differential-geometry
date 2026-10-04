import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Second derivatives in the second slot along a second-order curve (S-CVX calculus kernel)

For `Q : E × E → ℝ` of class `C²` on an open set `U`:

* `secondSlotDeriv Q z = D_b Q(z.1, ·)(z.2)` and `secondSlotDeriv2 Q z = D²_b Q(z.1, ·)(z.2)`;
* `continuousAt_secondSlotDeriv`, `continuousAt_secondSlotDeriv2`: both are continuous on `U`
  (joint regularity, `ContDiffAt.fderiv` twice);
* `hasDerivAt_comp_secondSlot`, `hasDerivAt_secondSlotDeriv_comp`: along a curve `Z` with
  `Z' = V(Z)` and `(V w).1 = w.2` (a second-order ODE written as a first-order one),
  `t ↦ Q(a, (Z t).1)` has derivative `D_b Q (Z t).2` and that derivative has derivative
  `D²_b Q((Z t).2, (Z t).2) + D_b Q((V (Z t)).2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `Q` in its second slot. -/
def secondSlotDeriv (Q : E × E → ℝ) (z : E × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun b => Q (z.1, b)) z.2

/-- The second derivative of `Q` in its second slot. -/
def secondSlotDeriv2 (Q : E × E → ℝ) (z : E × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun b => fderiv ℝ (fun b' => Q (z.1, b')) b) z.2

theorem contDiffAt_secondSlotDeriv {Q : E × E → ℝ} {z : E × E} (hQ : ContDiffAt ℝ 2 Q z) :
    ContDiffAt ℝ 1 (secondSlotDeriv Q) z := by
  have hm : ContDiffAt ℝ 2 (fun p : (E × E) × E => (p.1.1, p.2)) (z, z.2) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd |>.contDiffAt
  have hf : ContDiffAt ℝ 2 (Function.uncurry fun (y : E × E) (b : E) => Q (y.1, b)) (z, z.2) := by
    have h : ContDiffAt ℝ 2 Q ((z, z.2).1.1, (z, z.2).2) := hQ
    exact h.comp (z, z.2) hm
  exact ContDiffAt.fderiv (g := Prod.snd) hf contDiffAt_snd (by norm_num)

theorem continuousAt_secondSlotDeriv {Q : E × E → ℝ} {z : E × E} (hQ : ContDiffAt ℝ 2 Q z) :
    ContinuousAt (secondSlotDeriv Q) z :=
  (contDiffAt_secondSlotDeriv hQ).continuousAt

theorem continuousAt_secondSlotDeriv2 {Q : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hQ : ContDiffOn ℝ 2 Q U) {z : E × E} (hz : z ∈ U) :
    ContinuousAt (secondSlotDeriv2 Q) z := by
  have hQz : ContDiffAt ℝ 2 Q z := hQ.contDiffAt (hU.mem_nhds hz)
  have hm : ContDiffAt ℝ 1 (fun p : (E × E) × E => (p.1.1, p.2)) (z, z.2) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd |>.contDiffAt
  have hD1 : ContDiffAt ℝ 1 (secondSlotDeriv Q) ((z, z.2).1.1, (z, z.2).2) :=
    contDiffAt_secondSlotDeriv hQz
  have hf' := hD1.comp (z, z.2) hm
  have hf : ContDiffAt ℝ 1
      (Function.uncurry fun (y : E × E) (b : E) => fderiv ℝ (fun b' => Q (y.1, b')) b)
      (z, z.2) := hf'
  exact (ContDiffAt.fderiv (m := 0) (g := Prod.snd) hf contDiffAt_snd (by norm_num)).continuousAt

/-- First derivative along the curve. -/
theorem hasDerivAt_comp_secondSlot {Q : E × E → ℝ} {a : E} {Z : ℝ → E × E} {Z' : E × E} {t : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (a, (Z t).1)) (hZ : HasDerivAt Z Z' t) (hZ1 : Z'.1 = (Z t).2) :
    HasDerivAt (fun s => Q (a, (Z s).1)) (secondSlotDeriv Q (a, (Z t).1) (Z t).2) t := by
  have hq : ContDiffAt ℝ 2 (fun b => Q (a, b)) (Z t).1 :=
    hQ.comp (Z t).1 ((contDiffAt_const).prodMk contDiffAt_id)
  have hqd : HasFDerivAt (fun b => Q (a, b)) (fderiv ℝ (fun b => Q (a, b)) (Z t).1) (Z t).1 :=
    (hq.differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasDerivAt (fun s => (Z s).1) Z'.1 t :=
    (hasFDerivAt_fst (p := Z t)).comp_hasDerivAt t hZ
  have h := hqd.comp_hasDerivAt t h1
  rw [hZ1] at h
  exact h

/-- Second derivative along the curve. -/
theorem hasDerivAt_secondSlotDeriv_comp {Q : E × E → ℝ} {a : E} {Z : ℝ → E × E} {Z' : E × E}
    {t : ℝ} (hQ : ContDiffAt ℝ 2 Q (a, (Z t).1)) (hZ : HasDerivAt Z Z' t)
    (hZ1 : Z'.1 = (Z t).2) :
    HasDerivAt (fun s => secondSlotDeriv Q (a, (Z s).1) (Z s).2)
      (secondSlotDeriv2 Q (a, (Z t).1) (Z t).2 (Z t).2 +
        secondSlotDeriv Q (a, (Z t).1) Z'.2) t := by
  have hq : ContDiffAt ℝ 2 (fun b => Q (a, b)) (Z t).1 :=
    hQ.comp (Z t).1 ((contDiffAt_const).prodMk contDiffAt_id)
  have hq1 : ContDiffAt ℝ 1 (fderiv ℝ (fun b => Q (a, b))) (Z t).1 :=
    hq.fderiv_right (by norm_num)
  have hqd : HasFDerivAt (fderiv ℝ (fun b => Q (a, b)))
      (fderiv ℝ (fderiv ℝ (fun b => Q (a, b))) (Z t).1) (Z t).1 :=
    (hq1.differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasDerivAt (fun s => (Z s).1) Z'.1 t :=
    (hasFDerivAt_fst (p := Z t)).comp_hasDerivAt t hZ
  have h2 : HasDerivAt (fun s => (Z s).2) Z'.2 t :=
    (hasFDerivAt_snd (p := Z t)).comp_hasDerivAt t hZ
  have hc := hqd.comp_hasDerivAt t h1
  rw [hZ1] at hc
  exact hc.clm_apply h2

end DifferentialGeometry.Geometry.FiniteSoul
