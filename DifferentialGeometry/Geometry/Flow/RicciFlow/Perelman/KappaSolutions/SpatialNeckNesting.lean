import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.DisjointCompactSides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannOutward

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance nestingSphereConnected : ConnectedSpace SpatialNeckSphere := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {y1 y2 : SpatialNeckSphere}
  {p1 p2 : N} {epsilon : ℝ}
  {W1 : SpatialNeckWitness h y1 p1 epsilon} {W2 : SpatialNeckWitness h y2 p2 epsilon}
  (D1 : SpatialNeckSideData W1) (D2 : SpatialNeckSideData W2)

theorem compact_sides_nested (hcores : Disjoint W1.core W2.core)
    (hcommon : (D1.lower 0 ∩ D2.lower 0).Nonempty) :
    closure (D1.lower 0) ⊆ D2.lower 0 ∨ closure (D2.lower 0) ⊆ D1.lower 0 := by
  have hepsilon := W1.epsilon_pos
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by rw [abs_zero]; positivity
  obtain ⟨hB1, hU1, hB1op, hU1op, hdis1, hcover1, _hcompact1, hnoncompact1,
    _hcl1, _hint1, _hBfr1, hfront1⟩ := D1.slice_spec 0 hzero
  obtain ⟨_hB2, _hU2, hB2op, hU2op, hdis2, hcover2, hcompact2, _hnoncompact2,
    _hcl2, _hint2, _hBfr2, hfront2⟩ := D2.slice_spec 0 hzero
  change D1.lower 0 ∪ D1.upper 0 = W1.centralSphereᶜ at hcover1
  change D2.lower 0 ∪ D2.upper 0 = W2.centralSphereᶜ at hcover2
  change frontier (D1.upper 0) = W1.centralSphere at hfront1
  change frontier (D2.upper 0) = W2.centralSphere at hfront2
  have hcentral : Continuous W2.centralMap := by
    apply W2.embedding.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  have hS2 : IsPreconnected W2.centralSphere := by
    rw [W2.centralSphere_eq_range]
    exact (isConnected_range hcentral).isPreconnected
  exact compact_sides_nested_of_disjoint_slices
    (D1.lower 0) (D1.upper 0) W1.centralSphere (D2.lower 0) (D2.upper 0) W2.centralSphere
    hB1.isPreconnected hU1.isPreconnected hS2 hB1op hU1op hB2op hU2op hdis1 hdis2
    hcover1 hcover2 (D1.closure_lower_eq_compl_upper 0 hzero)
    (D2.closure_lower_eq_compl_upper 0 hzero) hfront1 hfront2 hcompact2 hnoncompact1
    (hcores.mono W1.centralSphere_subset_core W2.centralSphere_subset_core) hcommon

section CompatibleMetric

variable [I.Boundaryless] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance nestingC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem mem_lower_zero_of_busemann_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hlevel : busemann c q ≤ busemann c p1) (hnotcore : q ∉ W1.core) :
    q ∈ D1.lower 0 := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W1.epsilon_pos hsmall
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    rw [abs_zero]
    linarith [Real.pi_pos]
  have hA : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hnotS : q ∉ W1.centralSphere := fun hx => hnotcore (W1.centralSphere_subset_core hx)
  have hcases : q ∈ D1.lower 0 ∪ D1.upper 0 := by
    rw [(D1.slice_spec 0 hzero).2.2.2.2.2.1]
    exact hnotS
  rcases hcases with hqin | hqout
  · exact hqin
  · have hnotzero : q ∉ closure (D1.lower 0) := by
      rw [D1.closure_lower_eq_compl_upper 0 hzero]
      exact fun hn => hn hqout
    have hnotA : q ∉ closure (D1.lower (5 * Real.pi)) := by
      rw [(D1.ordered_band 0 (5 * Real.pi) hzero hA (by positivity)).2.1]
      rintro (hx | ⟨z, hz, heq⟩)
      · exact hnotzero hx
      · apply hnotcore
        refine ⟨z, ?_, heq⟩
        change -epsilon⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ epsilon⁻¹
        constructor <;> linarith [hz.1, hz.2, Real.pi_pos]
    have houtA : q ∈ D1.upper (5 * Real.pi) := by
      simpa only [D1.closure_lower_eq_compl_upper (5 * Real.pi) hA,
        mem_compl_iff, not_not] using hnotA
    exact False.elim ((not_lt_of_ge hlevel)
      (D1.busemann_outward_lt hEnorm hsmall hsec hc houtA))

theorem minimum_mem_lower_zero (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hmin : ∀ x : N, busemann c q ≤ busemann c x) (hnotcore : q ∉ W1.core) :
    q ∈ D1.lower 0 :=
  D1.mem_lower_zero_of_busemann_le hEnorm hsmall hsec hc (hmin p1) hnotcore

end CompatibleMetric

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
