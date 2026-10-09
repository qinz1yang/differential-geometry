import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FactorCurvature
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameExamples

/-!
# Consumers of LFR11 tier T4 (curvature of the zero factor)

* `coefficientSectional_transition_linear`: the cross-space coefficient transition for a linear
  change of model space;
* `inducedMetric_sectionalCurvature_le`, `real_inducedMetric_sectionalCurvature_nonneg`: the
  upper-bound and the rank-one (`F = ℝ`) forms used by LFR15/LFR16;
* `realFrame_inducedMetric_sectionalCurvature_nonneg`: the actual real-line splitting of the
  tier-T3 examples, with no geometric input.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

/-- Coefficient sectional curvature under a linear change of model space. -/
theorem coefficientSectional_transition_linear {V E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : V ≃L[ℝ] E) {W : Set E} (hW : IsOpen W)
    {c : E → E →L[ℝ] E →L[ℝ] ℝ} (hc : ContDiffOn ℝ 2 c W)
    (hcsymm : ∀ z ∈ W, ∀ u v : E, c z u v = c z v u) (hcco : ∀ z ∈ W, IsCoercive (c z))
    {x : V} (hx : L x ∈ W) (v u : V) :
    coefficientSectional (fun y => (c (L y)).bilinearComp (L : V →L[ℝ] E) (L : V →L[ℝ] E)) x v u =
      coefficientSectional c (L x) (L v) (L u) := by
  have hd : ∀ y : V, fderiv ℝ (L : V → E) y = (L : V →L[ℝ] E) := fun y => L.fderiv
  have h := coefficientSectional_transition_cross (U := (L : V → E) ⁻¹' W)
    (b := fun y => (c (L y)).bilinearComp (L : V →L[ℝ] E) (L : V →L[ℝ] E)) (Φ := (L : V → E))
    (hW.preimage L.continuous) hW hc hcsymm hcco L.contDiff.contDiffOn (fun _ hy => hy)
    (fun y _ => by rw [hd y]; exact ⟨L, rfl⟩)
    (fun y _ a a' => by rw [hd y]; rfl) hx v u
  rw [hd x] at h
  exact h

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section General

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)

/-- Upper sectional curvature bounds pass to the zero factor. -/
theorem inducedMetric_sectionalCurvature_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) {K : ℝ}
    (hsec : ∀ (x : M) (v w : TangentSpace I x), g.sectionalCurvature x v w ≤ K) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      (inducedMetric g hr hnorm e).sectionalCurvature z v w ≤ K := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro z v w
  rw [inducedMetric_sectionalCurvature_eq g hr hnorm e z v w]
  exact hsec _ _ _

end General

section RankOne

variable {E H M Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

/-- The rank-one (`F = ℝ`) form of tier T4 used by LFR16: nonnegative curvature of the surface
factor of a nonnegatively curved exact line splitting. -/
theorem real_inducedMetric_sectionalCurvature_nonneg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (ℝ × Y))
    (hsec : ∀ (x : M) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (z : {x : M // (e x).fst = 0})
      (v w : TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) z),
      0 ≤ (inducedMetric g hr hnorm e).sectionalCurvature z v w :=
  inducedMetric_sectionalCurvature_nonneg g hr hnorm e hsec

end RankOne

section RealLine

local instance nezero_finrank_real_F7LFR11b : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

private theorem realFrame_enorm_F7LFR11b : ∀ (x : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x w w)) := by
  intro x w
  change ‖(w : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (w : ℝ) w))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

private theorem realFrameMetric_sectionalCurvature_eq_zero (x : ℝ)
    (v w : TangentSpace 𝓘(ℝ, ℝ) x) : realFrameMetric.sectionalCurvature x v w = 0 := by
  apply ContMDiffRiemannianMetric.sectionalCurvature_eq_zero_of_not_linearIndependent
  intro hli
  have h := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  change 2 ≤ Module.finrank ℝ ℝ at h
  rw [Module.finrank_self] at h
  omega

/-- The actual real-line splitting `ℝ ≃ᵢ ℓ²(ℝ × PUnit)` of tier T3: its zero factor has
nonnegative curvature. -/
theorem realFrame_inducedMetric_sectionalCurvature_nonneg :
    letI := splittingFactorChartedSpace (r := 2) realFrameMetric le_rfl realFrame_enorm_F7LFR11b
      realFrameSplitting.{0}
    letI := splittingFactor_isManifold_one (r := 2) realFrameMetric le_rfl
      realFrame_enorm_F7LFR11b realFrameSplitting.{0}
    ∀ (z : {x : ℝ // (realFrameSplitting.{0} x).fst = 0})
      (v w : TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ ℝ - Module.finrank ℝ ℝ) → ℝ) z),
      0 ≤ (inducedMetric (r := 2) realFrameMetric le_rfl realFrame_enorm_F7LFR11b
        realFrameSplitting.{0}).sectionalCurvature z v w :=
  inducedMetric_sectionalCurvature_nonneg (r := 2) realFrameMetric le_rfl
    realFrame_enorm_F7LFR11b realFrameSplitting.{0}
    (fun x v w => (realFrameMetric_sectionalCurvature_eq_zero x v w).symm.le)

end RealLine

end DifferentialGeometry.Geometry.ExactSplitting
