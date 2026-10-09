import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateOrthogonalGraph
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Consumer of the orthogonal-sum CGP06 row (G1 of lane C14-BASES-PRE)

Concrete data in the Euclidean plane `ℂ`: the plane `L = ℝ ∙ 1` (the real axis), the retained
coordinate `π = Re` (norm one), the reference derivative `T = ofReal` (`Re ∘ T = id`, `Ω = 1`),
`D = T` (`e = 0`), `Dη = B = id`, normal error `ν = 0`, and an arbitrary constant orthogonal-sum
graph `g ≡ w₀ ∈ Lᗮ` over any ball (slope `a = 0`). The row gives injectivity of `Re` on the whole
graph and the tangent-plane coframe bound `|w|/2 ≤ |Re w|`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Analysis

/-- The real axis of `ℂ` as a plane. -/
abbrev realAxis_BPRE : Submodule ℝ ℂ := ℝ ∙ (1 : ℂ)

theorem finrank_realAxis_BPRE : Module.finrank ℝ realAxis_BPRE = Module.finrank ℝ ℝ := by
  rw [finrank_span_singleton one_ne_zero, Module.finrank_self]

theorem ofRealCLM_mem_realAxis_BPRE (c : ℝ) : Complex.ofRealCLM c ∈ realAxis_BPRE := by
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  simp

/-- **G1 consumer.** For every constant orthogonal-sum graph over the real axis of `ℂ` and every
base point, `Re` is injective on the whole graph over any ball, and on every tangent plane of the
graph `(1/2)|w| ≤ |Re w|`. -/
theorem cgp06_row_orthogonal_graph_realAxis_BPRE (w₀ : realAxis_BPREᗮ) (R : ℝ) (x : ℂ) :
    InjOn (fun t : realAxis_BPRE =>
      Complex.reCLM (x + orthogonalCoordinateSum realAxis_BPRE (t, w₀))) (ball 0 R) ∧
    ∀ t ∈ ball (0 : realAxis_BPRE) R, ∀ w ∈ LinearMap.range
        (fderiv ℝ (fun s : realAxis_BPRE =>
          x + orthogonalCoordinateSum realAxis_BPRE (s, (fun _ => w₀) s)) t :
            realAxis_BPRE →ₗ[ℝ] ℂ),
      (1 / (2 * 1) - 0) * ‖w‖ ≤ (1 + 0) * ‖Complex.reCLM w‖ := by
  have hπT : Complex.reCLM.comp Complex.ofRealCLM = ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp
  have hν : ‖realAxis_BPREᗮ.starProjection.comp Complex.ofRealCLM‖ ≤ 0 := by
    refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun c => ?_
    rw [ContinuousLinearMap.comp_apply,
      Submodule.starProjection_orthogonal_apply_eq_zero (ofRealCLM_mem_realAxis_BPRE c)]
    simp
  have hD : ‖Complex.ofRealCLM - Complex.ofRealCLM.comp (ContinuousLinearMap.id ℝ ℝ)‖ ≤ 0 := by
    simp
  obtain ⟨h1, -, -, -, h5⟩ := cgp06_row_orthogonal_graph_BPRE Complex.reCLM
    Complex.reCLM_norm.le Complex.ofRealCLM hπT Complex.ofRealCLM_norm.le Complex.ofRealCLM
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (by ext; simp)
    (ContinuousLinearMap.norm_id_le.trans (by norm_num)) hD realAxis_BPRE finrank_realAxis_BPRE
    hν le_rfl le_rfl le_rfl (by norm_num) (a := 0) (R := R) (by norm_num) (fun _ => w₀)
    contDiffOn_const (fun t _ => by simp) x
  exact ⟨h1, h5⟩

end DifferentialGeometry.Analysis
