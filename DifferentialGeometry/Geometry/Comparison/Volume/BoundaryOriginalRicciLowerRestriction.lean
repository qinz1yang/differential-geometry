import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalRicciRestriction
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

/-- A corners-native Ricci lower bound restricts to the intrinsic interior's genuine metric.
The Ricci contraction is the original `metricRicciAt`; only after its restriction identity is
applied is it rewritten as the interior `ricciTensor`. -/
theorem boundaryOriginal_metricRicciLower_restrictOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (p : M) (κ L : ℝ)
    (U : TopologicalSpace.Opens M) [T2Space U] [IsManifold I 1 U]
    [BoundarylessManifold I U]
    (hRic : ∀ (x : U) (z : TangentSpace I x),
      DifferentialGeometry.riemannianEDistOf g p (x : M) < ENNReal.ofReal L →
      -2 * κ ^ 2 * g.inner (x : M)
        (mfderiv I I (Subtype.val : U → M) x z)
        (mfderiv I I (Subtype.val : U → M) x z) ≤
        metricRicciAt (I := I) g (x : M)
          (vec2 (mfderiv I I (Subtype.val : U → M) x z)
            (mfderiv I I (Subtype.val : U → M) x z))) :
    ∀ (x : U) (z : TangentSpace I x),
      DifferentialGeometry.riemannianEDistOf g p (x : M) < ENNReal.ofReal L →
      -2 * κ ^ 2 * (g.restrictOpen (I := I) U).inner x z z ≤
        ricciTensor (g.restrictOpen (I := I) U) x z z := by
  intro x z hx
  have h := hRic x z hx
  rw [boundaryOriginal_metricRicciAt_eq_restricted_ricciTensor (I := I) g U x z z] at h
  simp only [mfderiv_subtype_val_apply] at h
  have hinner := SmoothRiemannianMetric.restrictOpen_inner (I := I) g U x z z
  rw [← hinner] at h
  exact h

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
