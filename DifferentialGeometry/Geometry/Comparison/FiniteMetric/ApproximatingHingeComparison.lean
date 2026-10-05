import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.BufferedSmoothHinge
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPointApproximants
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingLensBounds

/-!
Smooth approximant arms and local hyperbolic hinges retain the original ambient ball by
transporting minimizing lenses through the actual bilipschitz induced metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.FiniteComparison

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [groupE : NormedAddCommGroup E] [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E] [rankE : NeZero (Module.finrank ℝ E)]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [sigmaM : SigmaCompactSpace M] [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M] {n : ℕ∞ω}

theorem exists_unit_smooth_approximant_arm
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 3)
    (hbil : ∀ (x : M) (w : TangentSpace I x),
      (1 - δ) ^ 2 * g.inner x w w ≤ h.inner x w w ∧
        h.inner x w w ≤ (1 + δ) ^ 2 * g.inner x w w)
    (o A : M) (hA : A ≠ o) :
    ∃ u : E, h.inner o u u = 1 ∧ h.expMap
      (⟨o, (riemannianEDistOf (I := I) h o A).toReal • u⟩ : TangentBundle I M) = A := by
  have hfin := riemannianEDistOf_ne_top_of_le g hnorm h
    (show 0 < 1 + δ by linarith) (fun x w => (hbil x w).2)
  have hcomplete := completeSpace_inducedEMetricSpace_of_le g hnorm h
    (show 0 < 1 - δ by linarith) (fun x w => (hbil x w).1)
  let mH : MetricSpace M := @EMetricSpace.toMetricSpace M (inducedEMetricSpace h) hfin
  let bundleH : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let riemannianH : IsRiemannianManifold I M := ⟨fun x y => rfl⟩
  let completeH : CompleteSpace M := hcomplete
  let continuousH : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric h
  have hnormH : IsMetricNorm (I := I) h := isMetricNorm_of_smoothRiemannianMetric h
  have hd (x y : M) : (riemannianEDistOf (I := I) h x y).toReal = dist x y := by
    change (edist x y).toReal = dist x y
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  obtain ⟨u, hu, hend⟩ := DifferentialGeometry.Geometry.Topology.soul_unit_minimizing_initial
    h hnormH o A (dist_pos.mpr (Ne.symm hA))
  refine ⟨u, hu, ?_⟩
  rw [hd]
  exact (h.expMap_smul_eq_intrinsicGeodesic hnormH o u (dist o A)).trans hend

theorem hyperbolic_hinge_of_bilipschitz_buffer
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {δ k ρ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 3) (hk : 0 < k)
    (hbil : ∀ (x : M) (w : TangentSpace I x),
      (1 - δ) ^ 2 * g.inner x w w ≤ h.inner x w w ∧
        h.inner x w w ≤ (1 + δ) ^ 2 * g.inner x w w)
    (o A B : M) (u v : E) (hA : A ≠ o) (hB : B ≠ o)
    (hρ : 2 * (dist o A + dist o B) < ρ)
    (hu : h.inner o u u = 1) (hv : h.inner o v v = 1)
    (hreachA : h.expMap
      (⟨o, (riemannianEDistOf (I := I) h o A).toReal • u⟩ : TangentBundle I M) = A)
    (hreachB : h.expMap
      (⟨o, (riemannianEDistOf (I := I) h o B).toReal • v⟩ : TangentBundle I M) = B)
    (hsec : ∀ y ∈ Metric.closedBall o ρ, SectionalBoundedBelowAt h y (-k ^ 2)) :
    hyperbolicComparisonAngle k (riemannianEDistOf (I := I) h o A).toReal
      (riemannianEDistOf (I := I) h o B).toReal (riemannianEDistOf (I := I) h A B).toReal ≤
        Real.arccos (h.inner o u v)
 := by
  have hdist := toReal_riemannianEDistOf_mem_Icc g hnorm h hδ
    (show δ < 1 by linarith) hbil
  have hsum : 0 < dist o A + dist o B :=
    add_pos (dist_pos.mpr (Ne.symm hA)) (dist_pos.mpr (Ne.symm hB))
  have hδone : δ < 1 := by linarith
  have hfin := riemannianEDistOf_ne_top_of_le g hnorm h
    (show 0 < 1 + δ by linarith) (fun x w => (hbil x w).2)
  have hcomplete := completeSpace_inducedEMetricSpace_of_le g hnorm h
    (show 0 < 1 - δ by linarith) (fun x w => (hbil x w).1)
  let mH : MetricSpace M := @EMetricSpace.toMetricSpace M (inducedEMetricSpace h) hfin
  let bundleH : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let riemannianH : IsRiemannianManifold I M := ⟨fun x y => rfl⟩
  let completeH : CompleteSpace M := hcomplete
  let continuousH : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric h
  have hnormH : IsMetricNorm (I := I) h := isMetricNorm_of_smoothRiemannianMetric h
  have hd (x y : M) : (riemannianEDistOf (I := I) h x y).toReal = dist x y := by
    change (edist x y).toReal = dist x y
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hlow (x y : M) :
      (1 - δ) * @dist M metricM.toDist x y ≤ @dist M mH.toDist x y := by
    rw [← hd]
    exact (hdist x y).1
  have hup (x y : M) :
      @dist M mH.toDist x y ≤ (1 + δ) * @dist M metricM.toDist x y := by
    rw [← hd]
    exact (hdist x y).2
  have ha : 0 < (riemannianEDistOf (I := I) h o A).toReal := by
    rw [hd]
    exact dist_pos.mpr (Ne.symm hA)
  have hb : 0 < (riemannianEDistOf (I := I) h o B).toReal := by
    rw [hd]
    exact dist_pos.mpr (Ne.symm hB)
  have he (x y : M) : riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
    rw [← IsRiemannianManifold.out, edist_dist]
  have hdR (x y : M) : (riemannianEDist I x y).toReal = dist x y := by
    rw [he, ENNReal.toReal_ofReal dist_nonneg]
  have hreachA' := (h.expMap_smul_eq_intrinsicGeodesic hnormH o
    (u : TangentSpace I o) (riemannianEDistOf h o A).toReal).symm.trans hreachA
  have hreachB' := (h.expMap_smul_eq_intrinsicGeodesic hnormH o
    (v : TangentSpace I o) (riemannianEDistOf h o B).toReal).symm.trans hreachB
  have hminA : (riemannianEDist I o
      (intrinsicGeodesic h hnormH o u (riemannianEDistOf h o A).toReal)).toReal =
      (riemannianEDistOf h o A).toReal := by
    rw [hreachA', hdR, hd]
  have hminB : (riemannianEDist I o
      (intrinsicGeodesic h hnormH o v (riemannianEDistOf h o B).toReal)).toReal =
      (riemannianEDistOf h o B).toReal := by
    rw [hreachB', hdR, hd]
  have hlens : ∀ s ∈ Icc (0 : ℝ) (riemannianEDistOf h o A).toReal,
      ∀ t ∈ Icc (0 : ℝ) (riemannianEDistOf h o B).toReal, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic h hnormH o u s) y +
        riemannianEDist I y (intrinsicGeodesic h hnormH o v t) =
        riemannianEDist I (intrinsicGeodesic h hnormH o u s)
          (intrinsicGeodesic h hnormH o v t) → SectionalBoundedBelowAt h y (-k ^ 2) := by
    intro s hs t ht y hy
    have hp : dist o (intrinsicGeodesic h hnormH o u s) ≤ dist o A := by
      rw [← hdR, unit_intrinsic_subsegment_dist h hnormH o u hu
        (riemannianEDistOf h o A).toReal s ha hs.1 hs.2 hminA, ← hd]
      exact hs.2
    have hq : dist o (intrinsicGeodesic h hnormH o v t) ≤ dist o B := by
      rw [← hdR, unit_intrinsic_subsegment_dist h hnormH o v hv
        (riemannianEDistOf h o B).toReal t hb ht.1 ht.2 hminB, ← hd]
      exact ht.2
    have hyreal : dist (intrinsicGeodesic h hnormH o u s) y +
        dist y (intrinsicGeodesic h hnormH o v t) =
        dist (intrinsicGeodesic h hnormH o u s) (intrinsicGeodesic h hnormH o v t) := by
      rw [he, he, he, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hy
      simpa only [ENNReal.toReal_ofReal (add_nonneg dist_nonneg dist_nonneg),
        ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal hy
    have hbound := bilipschitz_minimizingLens_dist_le metricM mH hδone hlow hup
      o A B (intrinsicGeodesic h hnormH o u s) (intrinsicGeodesic h hnormH o v t) y
      hp hq hyreal
    have hradius := bilipschitzLens_radius_lt_twice hδsmall hsum
    apply hsec y
    change @dist M metricM.toDist y o ≤ ρ
    rw [@dist_comm M metricM.toPseudoMetricSpace y o]
    exact (hbound.trans_lt (hradius.trans hρ)).le
  have hangle :=
    hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
      h hnormH o u v hk ha hb hu hv hminA hminB hlens
  rw [hreachA', hreachB'] at hangle
  exact hangle

end DifferentialGeometry.Geometry.FiniteComparison
