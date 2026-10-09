import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderAxialDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Metric.DistancePullback
import Mathlib.Topology.ClusterPt

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)

theorem exists_strict_axial_endpoint_sides_of_cylinder_ray_cluster
    (e : Diffeomorph IC I3 Cylinder P.M ∞) (p : Sphere 2)
    (hmark : e (p, 0) = P.basepoint)
    (hmetric : Diffeomorph.pullbackMetricCross (P.S.base.metric 0) e = cylinderReferenceMetric 0)
    (rays : Fin 2 × ℝ≥0 → P.M)
    (hradial : ∀ j r, metricDistance (P.S.base.metric 0) P.basepoint (rays (j, r)) = r)
    (f : ℕ → Fin 2 × ℝ≥0 → P.M) (hcluster : MapClusterPt rays atTop f)
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ r : ℝ≥0, 0 < r → theta ≤ comparisonAngle r r
      (metricDistance (P.S.base.metric 0) (rays (0, r)) (rays (1, r))))
    (H : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧
      ((∃ᶠ i in atTop, (e.symm (f i (0, r))).2 < -H ∧
          H < (e.symm (f i (1, r))).2) ∨
        (∃ᶠ i in atTop, (e.symm (f i (1, r))).2 < -H ∧
          H < (e.symm (f i (0, r))).2)) := by
  obtain ⟨D, hD, herror⟩ := exists_cylinderReference_axial_distance_error
  obtain ⟨R, hR, hsigns⟩ := exists_opposite_axial_coordinates_threshold hD.le htheta (H + 1)
  let r : ℝ≥0 := ⟨R, hR.le⟩
  have hbaseinv : e.symm P.basepoint = (p, (0 : ℝ)) := by
    rw [← hmark, e.symm_apply_apply]
  have hdist (z w : P.M) : metricDistance (P.S.base.metric 0) z w =
      (riemannianEDistOf (cylinderReference.metric 0) (e.symm z) (e.symm w)).toReal := by
    have hh := edistOf_pullbackMetricCross (P.S.base.metric 0) e (e.symm z) (e.symm w)
    rw [hmetric, e.apply_symm_apply, e.apply_symm_apply] at hh
    exact congrArg ENNReal.toReal hh.symm
  have hraderr (j : Fin 2) : |R - (|(e.symm (rays (j, r))).2|)| ≤ D := by
    have hh := herror cylinderReference (e.symm P.basepoint) (e.symm (rays (j, r)))
    rw [← hdist, hradial j r, hbaseinv] at hh
    change abs (R - abs ((0 : ℝ) - (e.symm (rays (j, r))).2)) ≤ D at hh
    simpa only [zero_sub, abs_neg] using hh
  have hpairerr :
      |metricDistance (P.S.base.metric 0) (rays (0, r)) (rays (1, r)) -
        (|(e.symm (rays (0, r))).2 - (e.symm (rays (1, r))).2|)| ≤ D := by
    rw [hdist]
    exact herror cylinderReference _ _
  have hs := hsigns R le_rfl R R _ _ _ ⟨le_rfl, by linarith⟩ ⟨le_rfl, by linarith⟩
    ENNReal.toReal_nonneg (hraderr 0) (hraderr 1) hpairerr (hangle r hR)
  have hopen (j : Fin 2) : Continuous (fun g : Fin 2 × ℝ≥0 → P.M =>
      (e.symm (g (j, r))).2) :=
    continuous_snd.comp (e.symm.continuous.comp (continuous_apply (j, r)))
  refine ⟨r, hR, ?_⟩
  rcases mul_neg_iff.mp hs.1 with hposneg | hnegpos
  · right
    have ha : (e.symm (rays (1, r))).2 < -H := by
      have hh := hs.2.2
      rw [abs_of_neg hposneg.2] at hh
      linarith
    have hb : H < (e.symm (rays (0, r))).2 := by
      have hh := hs.2.1
      rw [abs_of_pos hposneg.1] at hh
      linarith
    exact hcluster.frequently (p := fun g => (e.symm (g (1, r))).2 < -H ∧
      H < (e.symm (g (0, r))).2)
      (((hopen 1).continuousAt.eventually_lt_const ha).and
        ((hopen 0).continuousAt.eventually_const_lt hb))
  · left
    have ha : (e.symm (rays (0, r))).2 < -H := by
      have hh := hs.2.1
      rw [abs_of_neg hnegpos.1] at hh
      linarith
    have hb : H < (e.symm (rays (1, r))).2 := by
      have hh := hs.2.2
      rw [abs_of_pos hnegpos.2] at hh
      linarith
    exact hcluster.frequently (p := fun g => (e.symm (g (0, r))).2 < -H ∧
      H < (e.symm (g (1, r))).2)
      (((hopen 0).continuousAt.eventually_lt_const ha).and
        ((hopen 1).continuousAt.eventually_const_lt hb))

theorem exists_strict_original_inverse_arm_endpoint_sides
    {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (M i)) (x : ∀ i, M i)
    (Psi : ∀ i, PartialDiffeomorph I3 I3 P.M (M i) ∞)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (arms : ∀ i, Fin 2 → MinimizingArm (g i) (x i))
    (hlength : ∀ j, Tendsto (fun i => Real.sqrt (Q i) * (arms i j).length) atTop atTop)
    (e : Diffeomorph IC I3 Cylinder P.M ∞) (p : Sphere 2)
    (hmark : e (p, 0) = P.basepoint)
    (hmetric : Diffeomorph.pullbackMetricCross (P.S.base.metric 0) e = cylinderReferenceMetric 0)
    (rays : Fin 2 × ℝ≥0 → P.M)
    (hradial : ∀ j r, metricDistance (P.S.base.metric 0) P.basepoint (rays (j, r)) = r)
    (hcluster : MapClusterPt rays atTop
      (fun i z => (Psi i).symm ((arms i z.1).point ((z.2 : ℝ) / Real.sqrt (Q i)))))
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ r : ℝ≥0, 0 < r → theta ≤ comparisonAngle r r
      (metricDistance (P.S.base.metric 0) (rays (0, r)) (rays (1, r)))) (H : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧
      ((∃ᶠ i in atTop,
        (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 0).length ∧
        (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 1).length ∧
        (e.symm ((Psi i).symm ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))))).2 < -H ∧
        H < (e.symm ((Psi i).symm ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))))).2) ∨
      (∃ᶠ i in atTop,
        (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 0).length ∧
        (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 1).length ∧
        (e.symm ((Psi i).symm ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))))).2 < -H ∧
        H < (e.symm ((Psi i).symm ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))))).2)) := by
  obtain ⟨r, hr, hsides⟩ := exists_strict_axial_endpoint_sides_of_cylinder_ray_cluster
    P e p hmark hmetric rays hradial _ hcluster htheta hangle H
  have hmem : ∀ᶠ i in atTop,
      (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 0).length ∧
      (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 1).length := by
    filter_upwards [(hlength 0).eventually_gt_atTop (r : ℝ),
      (hlength 1).eventually_gt_atTop (r : ℝ)] with i h0 h1
    have hpos := Real.sqrt_pos.mpr (hQ i)
    have htpos : 0 < (r : ℝ) / Real.sqrt (Q i) := div_pos (show (0 : ℝ) < r from hr) hpos
    exact ⟨⟨htpos, (div_lt_iff₀ hpos).mpr (by simpa only [mul_comm] using h0)⟩,
      ⟨htpos, (div_lt_iff₀ hpos).mpr (by simpa only [mul_comm] using h1)⟩⟩
  refine ⟨r, hr, ?_⟩
  rcases hsides with h | h
  · left
    exact (h.and_eventually hmem).mono fun i hi => ⟨hi.2.1, hi.2.2, hi.1⟩
  · right
    exact (h.and_eventually hmem).mono fun i hi => ⟨hi.2.1, hi.2.2, hi.1⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
