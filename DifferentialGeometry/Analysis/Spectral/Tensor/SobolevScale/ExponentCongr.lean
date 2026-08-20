import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def tensorHsCongr (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    tensorHs (I := I) (M := M) g r s a ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s b := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

def tensorHsCongrL (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    tensorHs (I := I) (M := M) g r s a →L[ℝ]
      tensorHs (I := I) (M := M) g r s b :=
  (tensorHsCongr (I := I) (M := M) g r s h).toLinearIsometry.toContinuousLinearMap

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsCongr_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongr (I := I) (M := M) g r s (rfl : a = a) =
      LinearIsometryEquiv.refl ℝ _ :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsCongrL_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongrL (I := I) (M := M) g r s (rfl : a = a) =
      ContinuousLinearMap.id ℝ (tensorHs (I := I) (M := M) g r s a) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongrL_apply {a b : ℝ} (h : a = b)
    (u : tensorHs (I := I) (M := M) g r s a) :
    tensorHsCongrL (I := I) (M := M) g r s h u =
      tensorHsCongr (I := I) (M := M) g r s h u :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_tensorHsCongr {a b : ℝ} (h : a = b)
    (u : tensorHs (I := I) (M := M) g r s a) :
    ‖tensorHsCongr (I := I) (M := M) g r s h u‖ = ‖u‖ :=
  (tensorHsCongr (I := I) (M := M) g r s h).norm_map u

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongr_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : tensorHs (I := I) (M := M) g r s b) :
    tensorHsCongr (I := I) (M := M) g r s hac
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab u) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hcd
        (tensorHsCongr (I := I) (M := M) g r s hbd u) := by
  cases hac
  cases hbd
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongrL_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d) :
    (tensorHsCongrL (I := I) (M := M) g r s hac).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hcd).comp
        (tensorHsCongrL (I := I) (M := M) g r s hbd) := by
  cases hac
  cases hbd
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_congr_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (h : a = b)
    (L : X →L[ℝ] tensorHs (I := I) (M := M) g r s a) :
    ‖(tensorHsCongrL (I := I) (M := M) g r s h).comp L‖ = ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.id_comp]

omit [NeZero (Module.finrank ℝ E)] in
theorem opNorm_comp_congr_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a b : ℝ} (h : a = b)
    (L : tensorHs (I := I) (M := M) g r s b →L[ℝ] X) :
    ‖L.comp (tensorHsCongrL (I := I) (M := M) g r s h)‖ ≤ ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.comp_id]

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
