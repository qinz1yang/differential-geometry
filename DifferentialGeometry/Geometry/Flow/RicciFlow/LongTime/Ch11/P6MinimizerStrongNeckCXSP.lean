import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants

set_option autoImplicit false

/-!
# CX-SPINE: the selected witness is a neck on a two-sided scalar gap

The cap branch of `SpatialCanonicalWitness.nonempty_spatialNeck_of_minimizing_segment`
does not use `SpatialCanonicalAlternative.cap.deep`. Here that field rules out the cap
alternative itself. Its fixed bound is `10000 / sqrt R(center)`; it has no C1/C2 factor.

Exact source steps:
* `Geometry/Neck/SpatialMinimizer.lean:20-81`: a minimizing segment with endpoints outside
  a cap core cannot reach outside the boundary neck's axial [-50,50] band.
* `Perelman/CanonicalNeighborhood/NeckRegionBall.lean:156`: that band is within
  `(50+6)*sqrt(1+eps)/sqrt R(boundary)` of its center.
* `Geometry/Neck/SpatialChart.lean:193`: on the band, R(center) ≤ 2 R(boundary).
* `Perelman/CanonicalNeighborhood/SpatialCanonicalWitness.lean:94-96`: cap depth is
  `10000/sqrt R(center)`, and the boundary neck center belongs to the cap tube.

The numerical contradiction is 10000*sqrt R(boundary) ≤ 112*sqrt R(center), whereas
R(center) ≤ 2 R(boundary). Fixed eps ≤ coneAccuracy pays every smallness requirement.
No adjustment of Gamma.epsilon via pBase.modelAccuracy is being made.
-/

noncomputable section

open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {v : M}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem minimizer_mem_boundary_neck_band_CXSP
    (nk : SpatialNeck g eps v) (heps : eps < 1 / 20000)
    {K : Set M}
    (hfront : frontier K = range (fun z : Sphere 2 => nk.map (z, 0)))
    {gamma : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      riemannianEDistOf g (gamma s) (gamma u) = ENNReal.ofReal |s - u|)
    (ha : gamma a ∉ interior K) (hb : gamma b ∉ interior K)
    (ht : gamma t ∈ interior K) :
    gamma t ∈ nk.map '' (univ ×ˢ Icc (-50 : ℝ) 50) := by
  let _ : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I3
  let _ : RegularSpace M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  by_contra hband
  have hlen : (50 : ℝ) < eps⁻¹ := by
    apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    linarith
  have hroot : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
  have hrootlow : 9 / 10 ≤ Real.sqrt (1 - eps) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [nk.eps_pos])).mpr
    nlinarith
  have hfar : ENNReal.ofReal (45 / Real.sqrt (metricScalarAt g v)) ≤
      riemannianEDistOf g v (gamma t) := by
    have hnot : ¬ riemannianEDistOf g v (gamma t) <
        ENNReal.ofReal (50 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g v)) := by
      intro hnear
      exact hband (nk.ball_subset_image_slab (by norm_num) hlen hnear)
    exact (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hroot.le)).trans (le_of_not_gt hnot)
  have hboundary (z : M) (hz : z ∈ frontier K) :
      edist v z ≤ ENNReal.ofReal (14 / Real.sqrt (metricScalarAt g v)) := by
    rw [hfront] at hz
    obtain ⟨w, rfl⟩ := hz
    have hbound := nk.central_sphere_subset_closedBall
      ⟨(w, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    exact hbound.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by norm_num) hroot.le))
  have hgap : ENNReal.ofReal (2 * (14 / Real.sqrt (metricScalarAt g v))) <
      edist v (gamma t) := by
    have hstrict : 2 * (14 / Real.sqrt (metricScalarAt g v)) <
        45 / Real.sqrt (metricScalarAt g v) := by
      rw [← mul_div_assoc]
      exact div_lt_div_of_pos_right (by norm_num) hroot
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict).trans_le hfar
  exact (EMetric.not_mem_interior_of_minimizing_of_frontier_edist_lt hat htb hmin ha hb
    (fun x hx y hy => EMetric.edist_lt_edist_add_edist_of_close_to_center (by positivity)
      (hboundary x hx) (hboundary y hy) hgap)) ht

private theorem cone_accuracy_lt_twenty_thousandth_CXSP :
    coneAccuracy < 1 / 20000 := by
  have hu : coneAccuracy ≤
      (1 / 4000000 / 26000 / 64) / (13000 * 13000) := by
    unfold coneAccuracy
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  exact hu.trans_lt (by norm_num)

variable [SigmaCompactSpace M] {C1 C2 : ℝ} {x : M}

/-- The same supplied witness must be a neck, so its S16 full-neck implication applies. -/
theorem SpatialCanonicalWitness.alternative_eq_neck_of_minimizing_scalar_gaps_CXSP
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hW : W.capTubeHasNeckChart eps) (heps : eps ≤ coneAccuracy)
    {gamma : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      riemannianEDistOf g (gamma s) (gamma u) = ENNReal.ofReal |s - u|)
    (hx : gamma t = x)
    (hleft : C2 * metricScalarAt g (gamma a) < metricScalarAt g x)
    (hright : C2 * metricScalarAt g x < metricScalarAt g (gamma b)) :
    ∃ neck : SpatialLocalNeck g eps x W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  have hepssmall : eps < 1 / 20000 :=
    heps.trans_lt cone_accuracy_lt_twenty_thousandth_CXSP
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hnotA : gamma a ∉ W.domain.carrier := by
    intro h
    have hlow := mul_le_mul_of_nonneg_left (W.scalar_bounds _ h).1 hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hlow
    linarith
  have hnotB : gamma b ∉ W.domain.carrier := by
    intro h
    linarith [(W.scalar_bounds _ h).2]
  have hcomp : gamma a ∈ connectedComponent x := by
    have hball : gamma a ∈
        {y : M | riemannianEDistOf g x y < ENNReal.ofReal (|t - a| + 1)} := by
      change riemannianEDistOf g x (gamma a) < _
      rw [← hx, hmin t ⟨hat.le, htb.le⟩ a ⟨le_rfl, (hat.trans htb).le⟩]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (lt_add_one _)
    exact Geometry.Metric.edistOf_ball_subset_connCompOpen g x _ hball
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | positive whole _ _ => exact (hnotA (whole.symm ▸ hcomp)).elim
  | round whole _ => exact (hnotA (whole.symm ▸ hcomp)).elim
  | cap data deep =>
    exfalso
    obtain ⟨v, nk, hmap⟩ := hW data deep halt
    have hfront : frontier data.core.carrier =
        range (fun z : Sphere 2 => nk.map (z, 0)) := by
      rw [← data.inner_boundary]
      ext y
      constructor
      · rintro ⟨⟨z, w⟩, ⟨_, hw⟩, rfl⟩
        have hw0 : w = 0 := hw
        subst w
        exact ⟨z, (hmap _).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hmap _⟩
    have hcoreU : data.core.carrier ⊆ W.domain.carrier := fun y hy => by
      rw [data.union_eq]
      exact Or.inl hy
    have hband : x ∈ nk.map '' (univ ×ˢ Icc (-50 : ℝ) 50) := by
      simpa only [hx] using minimizer_mem_boundary_neck_band_CXSP nk hepssmall hfront
        hat htb hmin (fun h => hnotA (hcoreU (interior_subset h)))
        (fun h => hnotB (hcoreU (interior_subset h)))
        (by simpa only [hx] using data.center_inside)
    have hlen : (50 : ℝ) < eps⁻¹ := by
      apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      linarith
    have hwindow : x ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
      apply image_mono _ hband
      intro z hz
      exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hRx : metricScalarAt g x ≤ 2 * metricScalarAt g v := by
      have hcoef : 1 + 4323 * eps ≤ 2 := by linarith
      exact (nk.scalar_bounds_on_image_window hwindow).2.trans
        (mul_le_mul_of_nonneg_right hcoef nk.Q_pos.le)
    have hvTube : v ∈ data.tube := by
      rw [← data.tube_eq]
      exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, (hmap _).trans nk.center_eq⟩
    have hbound := nk.image_slab_subset_closedBall (by norm_num) hlen hband
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · linarith [nk.eps_small]
    have hedist : riemannianEDistOf g v x ≤
        ENNReal.ofReal (112 / Real.sqrt (metricScalarAt g v)) := by
      exact hbound.trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)))
    -- The finite ofReal upper bound justifies conversion to metricDistance.
    have hdist : metricDistance g x v ≤ 112 / Real.sqrt (metricScalarAt g v) := by
      rw [metricDistance, riemannianEDistOf_comm g x v]
      exact ENNReal.toReal_le_of_le_ofReal
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hedist
    have hrootv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
    have hrootx : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
    have hdeep := (deep v hvTube).trans hdist
    have hmul : 10000 * Real.sqrt (metricScalarAt g v) ≤
        112 * Real.sqrt (metricScalarAt g x) :=
      (div_le_div_iff₀ hrootx hrootv).mp hdeep
    have hsq := mul_self_le_mul_self
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hmul
    nlinarith [nk.Q_pos, Real.sq_sqrt nk.Q_pos.le, Real.sq_sqrt W.Q_pos.le]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
