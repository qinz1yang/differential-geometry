import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_endRay_smooth_geodesic
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : EndRay H.endpoint,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ a.point (Ioo 0 (min a.length d)) ∧
      Geodesic.IsGeodesicOn g a.point (Ioo 0 (min a.length d)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro a
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 (min a.length 1)) :
      ContMDiffAt 𝓘(ℝ, ℝ) I3 ∞ a.point t ∧
      Geodesic.HasGeodesicEquationAt g a.point t := by
    have htlength : t < a.length := ht.2.trans_le (min_le_left _ _)
    let R := min t (a.length - t) / 2
    have hmin : 0 < min t (a.length - t) := lt_min ht.1 (sub_pos.mpr htlength)
    have hR : 0 < R := half_pos hmin
    have hRt : R < t := (half_lt_self hmin).trans_le (min_le_left _ _)
    have hRl : R < a.length - t := (half_lt_self hmin).trans_le (min_le_right _ _)
    have hparam (s : ℝ) (hs : s ∈ Icc (-R) R) : t + s ∈ Ioc 0 a.length :=
      ⟨by linarith only [hs.1, hRt], by linarith only [hs.2, hRl]⟩
    have h := contMDiffAt_and_geodesicEquationAt_of_metric_segment g
      (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm)
      a.point t hR (fun s hs v hv => by
        rw [a.minimizing _ (hparam s hs) _ (hparam v hv)]
        congr 1
        ring)
    exact ⟨h.1, h.2.1⟩
  exact ⟨fun t ht => (hpoint t ht).1.contMDiffWithinAt, fun t ht => (hpoint t ht).2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
