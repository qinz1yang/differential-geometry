import DifferentialGeometry.Analysis.Calculus.Compactness.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def retractionParabolicResidual
    (P : E → E) (A : ℝ × E × E → E) (a : ℝ × E × E → ℝ)
    (q : ℝ × E × E) : E :=
  A q - fderiv ℝ P q.2.1 (A q) +
    a q • fderiv ℝ (fderiv ℝ P) q.2.1 q.2.2 q.2.2

theorem contDiffOn_retractionParabolicResidual
    {P : E → E} {A : ℝ × E × E → E} {a : ℝ × E × E → ℝ}
    {U : Set (ℝ × E × E)} {V : Set E}
    (hV : IsOpen V) (hP : ContDiffOn ℝ 3 P V)
    (hA : ContDiffOn ℝ 1 A U) (ha : ContDiffOn ℝ 1 a U)
    (hUV : ∀ q ∈ U, q.2.1 ∈ V) :
    ContDiffOn ℝ 1 (retractionParabolicResidual P A a) U := by
  have hz : ContDiffOn ℝ 1 (fun q : ℝ × E × E => q.2.1) U :=
    contDiff_fst.comp contDiff_snd |>.contDiffOn
  have hw : ContDiffOn ℝ 1 (fun q : ℝ × E × E => q.2.2) U :=
    contDiff_snd.comp contDiff_snd |>.contDiffOn
  have hDP := hP.fderiv_of_isOpen hV (m := 2) (by norm_num)
  have hDDP := hDP.fderiv_of_isOpen hV (m := 1) (by norm_num)
  exact hA.sub (((hDP.of_le (by norm_num)).comp hz hUV).clm_apply hA) |>.add
    (ha.smul (((hDDP.comp hz hUV).clm_apply hw).clm_apply hw))

theorem exists_retractionParabolicResidual_bound
    {P : E → E} {A : ℝ × E × E → E} {a : ℝ × E × E → ℝ}
    {U K : Set (ℝ × E × E)} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKU : K ⊆ U)
    (hP : ContDiffOn ℝ 3 P V) (hA : ContDiffOn ℝ 1 A U) (ha : ContDiffOn ℝ 1 a U)
    (hUV : ∀ q ∈ U, q.2.1 ∈ V)
    (hPU : ∀ q ∈ K, (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2) ∈ U)
    (hzero : ∀ q ∈ K,
      retractionParabolicResidual P A a (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2) = 0) :
    ∃ L : ℝ≥0, ∀ q ∈ K, ‖retractionParabolicResidual P A a q‖ ≤
      L * (‖q.2.1 - P q.2.1‖ + ‖q.2.2 - fderiv ℝ P q.2.1 q.2.2‖) := by
  obtain ⟨L, hL⟩ := ContDiffOn.exists_norm_le_mul_sum_of_fderiv_comp_eq_zero
    (contDiffOn_retractionParabolicResidual hV hP hA ha hUV) hU hV hK hKU
      (fun q hq => hUV q (hKU hq)) (hP.of_le (by norm_num)) hPU
  exact ⟨L, fun q hq => hL q hq (hzero q hq)⟩

end DifferentialGeometry.Analysis.Parabolic
