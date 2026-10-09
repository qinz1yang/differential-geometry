import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardAngle
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology NNReal

open private side_data_of_oriented
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides
open private spatialNeckLineHomeomorph spatialNeckLine_center spatialNeckLine_negative_iff
  spatialNeckLine_positive_iff
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckTopology

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
  {X : Type*} [MetricSpace X]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {mark : SpatialNeckSphere}
  {x : N} {epsilon : ℝ} {W : SpatialNeckWitness h mark x epsilon}

theorem exists_separated_dist_gt_of_reference_ray
    (D : SpatialNeckSideData W) (hEnorm : IsMetricNorm h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature h)
    (e : N ≃ₜ X) (A : ℝ)
    (herror : ∀ q r : N, |dist q r - dist (e q) (e r)| ≤ A)
    (c : ℝ≥0 → X) (hc : Isometry c) (p : N)
    (hlevel : busemann c (e p) + 2 * A < busemann c (e x))
    (hp : p ∉ W.core) (R : ℝ) :
    ∃ z : N, R < dist (e p) (e z) ∧
      z ∉ connectedComponentIn W.centralSphereᶜ p := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    rw [abs_zero]
    linarith [Real.pi_pos]
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hrad (t : ℝ≥0) : dist (c t) (c 0) = (t : ℝ) := by
    rw [hc.dist_eq]
    change |(t : ℝ) - 0| = (t : ℝ)
    rw [sub_zero, abs_of_nonneg t.coe_nonneg]
  have hescape : Tendsto c atTop (cocompact X) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (c 0)
    simpa only [hrad, id_eq] using
      (NNReal.tendsto_coe_atTop.mpr (tendsto_id : Tendsto (fun t : ℝ≥0 => t) atTop atTop))
  have hupper (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) :
      ∀ᶠ t in atTop, e.symm (c t) ∈ D.upper s := by
    have hcompact : IsCompact (e '' closure (D.lower s)) :=
      ((D.slice_spec s hs).2.2.2.2.2.2.1).image e.continuous
    filter_upwards [hescape.eventually hcompact.compl_mem_cocompact] with t ht
    have hnot : e.symm (c t) ∉ closure (D.lower s) := by
      intro hh
      exact ht ⟨e.symm (c t), hh, e.apply_symm_apply _⟩
    simpa only [D.closure_lower_eq_compl_upper s hs, mem_compl_iff, not_not] using hnot
  have hnotS : p ∉ W.centralSphere := fun hpS => hp (W.centralSphere_subset_core hpS)
  have hcases : p ∈ D.lower 0 ∪ D.upper 0 := by
    rw [(D.slice_spec 0 hzero).2.2.2.2.2.1]
    exact hnotS
  have hplower : p ∈ D.lower 0 := by
    rcases hcases with hlower | houter
    · exact hlower
    have hnotlower : p ∉ closure (D.lower 0) := by
      rw [D.closure_lower_eq_compl_upper 0 hzero]
      exact fun hn => hn houter
    have hnotband : p ∉ closure (D.lower (5 * Real.pi)) := by
      rw [(D.ordered_band 0 (5 * Real.pi) hzero hs (by positivity)).2.1]
      rintro (hh | ⟨z, hz, heq⟩)
      · exact hnotlower hh
      · apply hp
        refine ⟨z, ?_, heq⟩
        change -epsilon⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ epsilon⁻¹
        constructor <;> linarith [hz.1, hz.2, Real.pi_pos]
    have hpout : p ∈ D.upper (5 * Real.pi) := by
      simpa only [D.closure_lower_eq_compl_upper (5 * Real.pi) hs,
        mem_compl_iff, not_not] using hnotband
    have hevent : ∀ᶠ t in atTop,
        busemannApprox c t (e x) - busemannApprox c t (e p) ≤
          2 * A - dist x p / 4 := by
      filter_upwards [hupper (5 * Real.pi) hs,
        eventually_ge_atTop ((2 * dist x p + A + dist (e x) (c 0)).toNNReal)] with t ht htime
      have htimeReal : 2 * dist x p + A + dist (e x) (c 0) ≤ (t : ℝ) :=
        (Real.le_coe_toNNReal _).trans (by exact_mod_cast htime)
      have htri := dist_triangle (c t) (e x) (c 0)
      rw [hrad, dist_comm (c t) (e x)] at htri
      have hxerr := abs_le.mp (herror x (e.symm (c t)))
      have hperr := abs_le.mp (herror p (e.symm (c t)))
      simp only [e.apply_symm_apply] at hxerr hperr
      have hlarge : 2 * dist x p ≤ dist x (e.symm (c t)) := by
        linarith [hxerr.1]
      have hloss := D.outward_distance_loss hEnorm hsmall hsec ht hpout hlarge
      rw [dist_comm (e.symm (c t)) p] at hloss
      dsimp only [busemannApprox]
      linarith [hxerr.2, hperr.1]
    have hlimit := le_of_tendsto ((tendsto_busemannApprox hc (e x)).sub
      (tendsto_busemannApprox hc (e p))) hevent
    exfalso
    linarith [dist_nonneg (x := x) (y := p)]
  have hfar : ∀ᶠ t in atTop, R < dist (e p) (c t) := by
    filter_upwards [eventually_gt_atTop ((R + dist (e p) (c 0)).toNNReal)] with t ht
    have htimeReal : R + dist (e p) (c 0) < (t : ℝ) :=
      (Real.le_coe_toNNReal _).trans_lt (by exact_mod_cast ht)
    have htri := dist_triangle (c t) (e p) (c 0)
    rw [hrad, dist_comm (c t) (e p)] at htri
    linarith
  obtain ⟨t, ht, hdist⟩ := ((hupper 0 hzero).and hfar).exists
  refine ⟨e.symm (c t), by simpa only [e.apply_symm_apply] using hdist, ?_⟩
  intro hcomp
  obtain ⟨_hL, _hU, hLopen, hUopen, hdisj, hcover, _hLc, _hUc, _hLcl,
    _hLint, _hLfront, _hUfront⟩ := D.slice_spec 0 hzero
  change D.lower 0 ∪ D.upper 0 = W.centralSphereᶜ at hcover
  have hsub : connectedComponentIn W.centralSphereᶜ p ⊆ D.lower 0 :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hLopen hUopen hdisj (by rw [hcover]; exact connectedComponentIn_subset _ _)
      ⟨p, mem_connectedComponentIn hnotS, hplower⟩
  exact Set.disjoint_left.mp hdisj (hsub hcomp) ht

end SpatialNeckSideData

namespace SpatialNeckWitness

theorem exists_separated_dist_gt_of_reference_ray [NoncompactSpace N] [ProperSpace X]
    {h : SmoothRiemannianMetric I N} {mark : SpatialNeckSphere}
    {x : N} {epsilon : ℝ} (W : SpatialNeckWitness h mark x epsilon)
    (hEnorm : IsMetricNorm h) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature h)
    (e : N ≃ₜ X) (A : ℝ)
    (herror : ∀ q r : N, |dist q r - dist (e q) (e r)| ≤ A)
    (c : ℝ≥0 → X) (hc : Isometry c) (p : N)
    (hlevel : busemann c (e p) + 2 * A < busemann c (e x))
    (hfar : spatialNeckCoreRadiusConstant epsilon /
      Real.sqrt (DifferentialGeometry.Geometry.Curvature.metricScalarAt h x) + A < dist (e p) (e x))
    (ρ : C(N, N)) (hρ : ContinuousMap.Homotopic ρ (ContinuousMap.id N))
    (havoid : Disjoint (range ρ) W.centralSphere) (R : ℝ) :
    ∃ z : N, R < dist (e p) (e z) ∧
      z ∉ connectedComponentIn W.centralSphereᶜ p := by
  let _ : LocallyPathConnectedSpace N :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let _ : ConnectedSpace SpatialNeckSphere := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  have hp : p ∉ W.core := by
    intro hp
    have hbound := W.core_dist_le hEnorm hsmall hp
    have herr := (abs_le.mp (herror x p)).1
    rw [dist_comm (e x) (e p)] at herr
    linarith
  let eta := spatialNeckLineHomeomorph epsilon W.epsilon_pos
  let phi : SpatialNeckCylinder → N := W.embedding ∘ eta
  have hphi : _root_.Topology.IsOpenEmbedding phi :=
    W.embedding_isOpenEmbedding.comp eta.isOpenEmbedding
  have hcenter : range (fun y => phi (y, 0)) = W.centralSphere := by
    rw [W.centralSphere_eq_range]
    congr 1
    funext y
    change W.embedding (eta (y, 0)) = W.centralMap y
    rw [spatialNeckLine_center]
    rfl
  have havoidPhi : Disjoint (range ρ) (range (fun y => phi (y, 0))) := by
    rwa [hcenter]
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBfr, hUfr,
    _hBcl, _hUcl, _hcomponents, hn, hpos⟩ :=
    bicollar_complement_components_of_homotopic_disjoint phi hphi ρ hρ havoidPhi
  rw [hcenter] at hcover hBfr hUfr
  have hnegative : ∀ z : spatialNeckBuffer epsilon, z.val.2 < 0 → W.embedding z ∈ B := by
    intro z hz
    have hsz : (eta (eta.symm z)).val.2 < 0 := by rw [eta.apply_symm_apply]; exact hz
    have ht : (eta.symm z).2 < 0 :=
      (spatialNeckLine_negative_iff epsilon W.epsilon_pos (eta.symm z)).mp hsz
    have hmem := hn (eta.symm z).1 (eta.symm z).2 ht
    change W.embedding (eta (eta.symm z)) ∈ B at hmem
    rwa [eta.apply_symm_apply] at hmem
  have hpositive : ∀ z : spatialNeckBuffer epsilon, 0 < z.val.2 → W.embedding z ∈ U := by
    intro z hz
    have hsz : 0 < (eta (eta.symm z)).val.2 := by rw [eta.apply_symm_apply]; exact hz
    have ht : 0 < (eta.symm z).2 :=
      (spatialNeckLine_positive_iff epsilon W.epsilon_pos (eta.symm z)).mp hsz
    have hmem := hpos (eta.symm z).1 (eta.symm z).2 ht
    change W.embedding (eta (eta.symm z)) ∈ U at hmem
    rwa [eta.apply_symm_apply] at hmem
  by_cases hBc : IsCompact (closure B)
  · obtain ⟨D⟩ := side_data_of_oriented W ρ hρ havoid B hB hBop hBc hBfr hnegative
    exact D.exists_separated_dist_gt_of_reference_ray
      hEnorm hsmall hsec e A herror c hc p hlevel hp R
  by_cases hUc : IsCompact (closure U)
  · have havoid' : Disjoint (range ρ) W.reflect.centralSphere := by
      simpa only [W.reflect_centralSphere] using havoid
    have hUfr' : frontier U = W.reflect.centralSphere := by
      simpa only [W.reflect_centralSphere] using hUfr
    have hnegative' : ∀ z : spatialNeckBuffer epsilon,
        z.val.2 < 0 → W.reflect.embedding z ∈ U := by
      intro z hz
      rw [W.reflect_embedding]
      apply hpositive
      rw [spatialNeckReflection_val]
      exact neg_pos.mpr hz
    obtain ⟨D⟩ := side_data_of_oriented W.reflect ρ hρ havoid' U hU hUop hUc hUfr' hnegative'
    have hp' : p ∉ W.reflect.core := by simpa only [W.reflect_core] using hp
    obtain ⟨z, hzfar, hzcomp⟩ := D.exists_separated_dist_gt_of_reference_ray
      hEnorm hsmall hsec e A herror c hc p hlevel hp' R
    exact ⟨z, hzfar, by simpa only [W.reflect_centralSphere] using hzcomp⟩
  have hfarIn (V : Set N) (hV : ¬ IsCompact (closure V)) :
      ∃ z ∈ V, R < dist (e p) (e z) := by
    by_contra! hbounded
    have hsub : V ⊆ e ⁻¹' Metric.closedBall (e p) R := by
      intro z hz
      rw [mem_preimage, Metric.mem_closedBall, dist_comm]
      exact hbounded z hz
    have hcompact : IsCompact (e ⁻¹' Metric.closedBall (e p) R) :=
      e.isCompact_preimage.mpr (isCompact_closedBall _ _)
    exact hV (hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal hsub hcompact.isClosed))
  have hpavoid : p ∉ W.centralSphere := fun hpS => hp (W.centralSphere_subset_core hpS)
  have hpcases : p ∈ B ∪ U := by rw [hcover]; exact hpavoid
  rcases hpcases with hpB | hpU
  · obtain ⟨z, hzU, hzfar⟩ := hfarIn U hUc
    refine ⟨z, hzfar, ?_⟩
    intro hzcomp
    have hsub : connectedComponentIn W.centralSphereᶜ p ⊆ B :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hBop hUop hBU
        (by rw [hcover]; exact connectedComponentIn_subset _ _)
        ⟨p, mem_connectedComponentIn hpavoid, hpB⟩
    exact Set.disjoint_left.mp hBU (hsub hzcomp) hzU
  · obtain ⟨z, hzB, hzfar⟩ := hfarIn B hBc
    refine ⟨z, hzfar, ?_⟩
    intro hzcomp
    have hsub : connectedComponentIn W.centralSphereᶜ p ⊆ U :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hUop hBop hBU.symm
        (by rw [union_comm, hcover]; exact connectedComponentIn_subset _ _)
        ⟨p, mem_connectedComponentIn hpavoid, hpU⟩
    exact Set.disjoint_left.mp hBU hzB (hsub hzcomp)

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
