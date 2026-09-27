import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannInward
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardSubsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckPositiveTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize
import DifferentialGeometry.Geometry.Comparison.Toponogov.RayComparisonAngle

section
set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem SpatialNeckSideData.exists_pos_ray_mem_slice
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
    (D : SpatialNeckSideData W) {c : ℝ≥0 → N} (hc : Isometry c)
    (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) (hstart : c 0 ∈ D.lower s) :
    ∃ t : ℝ≥0, 0 < t ∧
      c t ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
  let _ : ConnectedSpace ℝ≥0 :=
    isConnected_iff_connectedSpace.mp (isConnected_Ici : IsConnected (Ici (0 : ℝ)))
  obtain ⟨_, _, hlowOpen, huppOpen, hdisjoint, hcover, _⟩ := D.slice_spec s hs
  have hstartAvoid : c 0 ∉ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
    have hm : c 0 ∈ D.lower s ∪ D.upper s := Or.inl hstart
    rwa [hcover] at hm
  have hex : ∃ t : ℝ≥0,
      c t ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
    by_contra! havoid
    have hsub : range c ⊆ D.lower s ∪ D.upper s := by
      rw [hcover]
      rintro z ⟨t, rfl⟩
      exact havoid t
    have hlower : range c ⊆ D.lower s :=
      (isConnected_range hc.continuous).isPreconnected.subset_left_of_subset_union
        hlowOpen huppOpen hdisjoint hsub ⟨c 0, mem_range_self 0, hstart⟩
    obtain ⟨t, ht⟩ := (D.ray_eventually_upper hc s hs).exists
    exact Set.disjoint_left.mp hdisjoint (hlower (mem_range_self t)) ht
  obtain ⟨t, ht⟩ := hex
  have htne : t ≠ 0 := by
    intro heq
    exact hstartAvoid (heq ▸ ht)
  exact ⟨t, lt_of_le_of_ne (show 0 ≤ t from bot_le) (Ne.symm htne), ht⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end

section
set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

theorem eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop
    {g : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness g (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) g) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (p : N) (hescape : Tendsto (fun i => dist p (centers i)) atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (centers i)) *
      dist p (centers i)) atTop atTop)
    {c d : ℝ≥0 → N} (hc : Isometry c) (hd : Isometry d)
    (hc0 : c 0 = p) (hd0 : d 0 = p) :
    ∀ᶠ i in atTop, ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧
      c s ∈ (W i).core ∧ d t ∈ (W i).core ∧
      dist (centers i) (c s) ≤ spatialNeckCoreRadiusConstant epsilon /
        Real.sqrt (metricScalarAt (I := I) g (centers i)) ∧
      dist (centers i) (d t) ≤ spatialNeckCoreRadiusConstant epsilon /
        Real.sqrt (metricScalarAt (I := I) g (centers i)) := by
  classical
  let _ : NoncompactSpace N := ⟨by
    intro hcompact
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hcompact.isBounded
    obtain ⟨i, hi⟩ := (hescape.eventually_gt_atTop B).exists
    have hh : dist (centers i) p ≤ B := hB (mem_univ _)
    rw [dist_comm] at hh
    linarith⟩
  choose W' hchoice hsphere hcore himage hside using
    fun i : ℕ => (W i).exists_ordered_compact_end_sides hsec
  let D : ∀ i : ℕ, SpatialNeckSideData (W' i) := fun i => Classical.choice (hside i)
  have havoid : ∀ᶠ i in atTop, p ∉ (W' i).core := by
    filter_upwards [hscaled.eventually_gt_atTop (spatialNeckCoreRadiusConstant epsilon)] with i hi
    intro hpin
    have hh := (W' i).core_dist_le hEnorm hsmall hpin
    rw [dist_comm] at hh
    have hroot : 0 < Real.sqrt (metricScalarAt (I := I) g (centers i)) :=
      Real.sqrt_pos.mpr (W i).scalar_pos
    have hprod := (le_div_iff₀ hroot).mp hh
    nlinarith
  have hescape' : Tendsto centers atTop (cocompact N) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop p (by
      simpa only [dist_comm] using hescape)
  have hlower := eventually_mem_spatialNeck_lower W' D hEnorm hsmall hsec.toNonnegative
    hc p havoid hescape'
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    have heps := (W 0).epsilon_pos
    rw [abs_zero]
    positivity
  filter_upwards [hlower] with i hi
  obtain ⟨s, hspos, hs⟩ := (D i).exists_pos_ray_mem_slice hc 0 hzero (hc0.symm ▸ hi)
  obtain ⟨t, htpos, ht⟩ := (D i).exists_pos_ray_mem_slice hd 0 hzero (hd0.symm ▸ hi)
  have hsCore : c s ∈ (W' i).core := by
    obtain ⟨z, hz, hzs⟩ := hs
    exact ⟨z, spatialNeckCentralDomain_subset_core epsilon (W' i).epsilon_pos hz, hzs⟩
  have htCore : d t ∈ (W' i).core := by
    obtain ⟨z, hz, hzt⟩ := ht
    exact ⟨z, spatialNeckCentralDomain_subset_core epsilon (W' i).epsilon_pos hz, hzt⟩
  exact ⟨s, t, hspos, htpos, (hcore i) ▸ hsCore, (hcore i) ▸ htCore,
    (W' i).core_dist_le hEnorm hsmall hsCore,
    (W' i).core_dist_le hEnorm hsmall htCore⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end

section
set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

theorem tendsto_rays_comparisonAngle_zero_of_spatialNecks
    {g : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness g (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) g) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (p : N) (hescape : Tendsto (fun i => dist p (centers i)) atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (centers i)) *
      dist p (centers i)) atTop atTop)
    {c d : ℝ≥0 → N} (hc : Isometry c) (hd : Isometry d)
    (hc0 : c 0 = p) (hd0 : d 0 = p) :
    Tendsto (fun i => Geometry.Comparison.Toponogov.comparisonAngle
      (dist p (centers i)) (dist p (centers i))
      (dist (c (nndist p (centers i))) (d (nndist p (centers i))))) atTop (𝓝 0) := by
  let r : ℕ → ℝ≥0 := fun i => nndist p (centers i)
  let B : ℕ → ℝ := fun i => spatialNeckCoreRadiusConstant epsilon /
    Real.sqrt (metricScalarAt (I := I) g (centers i))
  have hr : ∀ᶠ i in atTop, 0 < r i := by
    filter_upwards [hescape.eventually_gt_atTop 0] with i hi
    exact hi
  have hz : ∀ᶠ i in atTop, dist p (centers i) = (r i : ℝ) :=
    Eventually.of_forall fun _ => rfl
  have hcross : ∀ᶠ i in atTop, ∃ s t : ℝ≥0,
      dist (c s) (centers i) ≤ B i ∧ dist (d t) (centers i) ≤ B i := by
    filter_upwards [eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop
      W hEnorm hsmall hsec p hescape hscaled hc hd hc0 hd0] with i hi
    obtain ⟨s, t, hs, ht, hsc, htc, hsd, htd⟩ := hi
    exact ⟨s, t, by simpa only [dist_comm] using hsd, by simpa only [dist_comm] using htd⟩
  have hthin : Tendsto (fun i => B i / (r i : ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := spatialNeckCoreRadiusConstant epsilon)).mul
      (tendsto_inv_atTop_zero.comp hscaled)
    simpa only [B, r, coe_nndist, div_div, div_eq_mul_inv, Function.comp_apply, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm, mul_zero, zero_mul] using hh
  exact Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points
    hc hd hc0 hd0 r centers B hr hz hcross hthin

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end
