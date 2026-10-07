import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreBufferRCW_O31
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# CH12-O31, group 6: unscaled centre volume (`[FROZEN] CH12-O31 G6`, first lemma of (a'))

A normalized centre-volume bound `vol_{R(w) g}(B(w, b)) ≥ κ b³` (`b ≤ β`, metric scaled by `R(w)`, as
produced by G3/G4) is the scale-invariant bound `vol_g(B_g(w, r)) ≥ κ r³` for `r √R(w) ≤ β`.
With `R(w) = 2 R(y)` (G4) and `r = δ/√R(y)`, `δ = b_*/√2`, this is `vol ≥ κ δ³` in the
`R(y)`-normalization of D-R4-2.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

/-- **Unscaled centre volume** (`[FROZEN] CH12-O31 G6`). -/
theorem unscaled_centre_volume_O31 {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g' : SmoothRiemannianMetric ThreeModel M) (w : M) (hQ : 0 < metricScalarAt g' w)
    {κ β : ℝ}
    (hvol : ∀ b : ℝ, 0 < b → b ≤ β →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel M (scaleMetric (metricScalarAt g' w) hQ g')
          (riemannianBallOf (scaleMetric (metricScalarAt g' w) hQ g') w b))
    (r : ℝ) (hr : 0 < r) (hrβ : r * Real.sqrt (metricScalarAt g' w) ≤ β) :
    ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume g' w r := by
  set c := metricScalarAt g' w with hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hQ
  have h1 := hvol (Real.sqrt c * r) (mul_pos hsc hr) (by rw [mul_comm]; exact hrβ)
  have h2 : riemannianVolumeMeasure ThreeModel M (scaleMetric c hQ g')
      (riemannianBallOf (scaleMetric c hQ g') w (Real.sqrt c * r)) =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * ballVolume g' w r := by
    have := ballVolume_scaleMetric_finrank (I := ThreeModel) c hQ g' w r
    rw [finrank_euclideanSpace_fin] at this
    exact this
  rw [h2] at h1
  have h3 : ENNReal.ofReal (κ * (Real.sqrt c * r) ^ 3) =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * ENNReal.ofReal (κ * r ^ 3) := by
    rw [← ENNReal.ofReal_pow hsc.le, ← ENNReal.ofReal_mul (pow_nonneg hsc.le 3)]
    congr 1; ring
  rw [h3] at h1
  have hne : ENNReal.ofReal (Real.sqrt c) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (ENNReal.ofReal_pos.mpr hsc))
  have hnt : ENNReal.ofReal (Real.sqrt c) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hne hnt).mp h1

end GC.LongTime.Ch12
