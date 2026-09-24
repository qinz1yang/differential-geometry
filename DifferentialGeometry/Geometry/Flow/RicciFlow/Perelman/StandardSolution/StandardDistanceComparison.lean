import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderLimitRicci
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Distance.Ball

noncomputable section
open Set Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.riemannianEDistOf_le_initial
    (S : PartialStandardSolution) {t : ℝ} (ht : t ∈ S.domain) (x y : E3) :
    riemannianEDistOf (S.metric t) x y ≤ riemannianEDistOf StandardCap.metric x y := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hslab : Icc 0 t ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos t htime.1).mpr htime.2
  have hreg : Ioo 0 t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro s hs
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt htime.2⟩
  have hquad : ∀ z : E3, ∀ v : TangentSpace (𝓡 3) z,
      (S.metric t).inner z v v ≤ (1 : ℝ) * StandardCap.metric.inner z v v := by
    intro z v
    have hanti := Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      S.toSolutionOn S.isSolutionOn hslab hreg (fun s hs z v => by
        change 0 ≤ metricRicciAt (S.metric s) z (vec2 v v)
        rw [metricRicciAt_apply_eq_ricciTensor]
        exact S.ricciTensor_nonnegative s (hslab ⟨hs.1.le, hs.2.le⟩) z v) z v
    have hh := hanti ⟨le_rfl, htime.1⟩ ⟨htime.1, le_rfl⟩ htime.1
    simpa only [PartialStandardSolution.toSolutionOn_metric, S.initial, one_mul] using hh
  have h := edistOf_le_of_quad StandardCap.metric (S.metric t) zero_lt_one hquad x y
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

theorem PartialStandardSolution.euclidean_ball_subset_riemannianBallOf
    (S : PartialStandardSolution) {t : ℝ} (ht : t ∈ S.domain) (p x : E3) {R : ℝ}
    (hx : ‖x‖ ≤ R) :
    Metric.ball p 1 ⊆ riemannianBallOf (S.metric t) x (R + ‖p‖ + 1) := by
  intro y hy
  have hdist : dist y p < 1 := hy
  have hxy : dist x y < R + ‖p‖ + 1 := by
    have htri := dist_triangle x p y
    have hxp : dist x p ≤ ‖x‖ + ‖p‖ := dist_le_norm_add_norm x p
    rw [dist_comm p y] at htri
    linarith
  have h := (S.riemannianEDistOf_le_initial ht x y).trans (StandardCap.edist_le_euclidean x y)
  exact h.trans_lt (by rw [edist_dist]; exact (ENNReal.ofReal_lt_ofReal_iff (by have hR : 0 ≤ R := (norm_nonneg x).trans hx; positivity : 0 < R + ‖p‖ + 1)).mpr hxy)

end DifferentialGeometry.PDE.RicciFlow
