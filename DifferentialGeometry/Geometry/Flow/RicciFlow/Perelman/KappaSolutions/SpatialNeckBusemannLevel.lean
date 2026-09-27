import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannOutward
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

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

private local instance neckLevelC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

include D

omit [ConnectedSpace N] in
private theorem lower_slice_busemann_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {c : ℝ≥0 → N} (hc : Isometry c)
    (z : spatialNeckBuffer epsilon) (hz : z.val.2 = -(5 * Real.pi)) :
    busemann c (W.embedding z) ≤ busemann c p := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |-(5 * Real.pi)| < epsilon⁻¹ + 1 := by
    rw [abs_neg, abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hsub : closure (D.lower (-(5 * Real.pi))) ⊆ {q : N | busemann c q ≤ busemann c p} :=
    closure_minimal (fun q hq => (D.busemann_inward_lt hEnorm hsmall hc hq).le)
      (isClosed_le (lipschitzWith_busemann hc).continuous continuous_const)
  apply hsub
  rw [(D.slice_spec (-(5 * Real.pi)) hs).2.2.2.2.2.2.2.2.1]
  exact Or.inr ⟨z, hz, rfl⟩

private theorem upper_slice_busemann_ge (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c)
    (z : spatialNeckBuffer epsilon) (hz : z.val.2 = 5 * Real.pi) :
    busemann c p ≤ busemann c (W.embedding z) := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hsub : closure (D.upper (5 * Real.pi)) ⊆ {q : N | busemann c p ≤ busemann c q} :=
    closure_minimal (fun q hq => (D.busemann_outward_lt hEnorm hsmall hsec hc hq).le)
      (isClosed_le continuous_const (lipschitzWith_busemann hc).continuous)
  apply hsub
  apply frontier_subset_closure
  rw [(D.slice_spec (5 * Real.pi) hs).2.2.2.2.2.2.2.2.2.2.2]
  exact ⟨z, hz, rfl⟩

theorem busemann_level_subset_band (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    {q : N | busemann c q = busemann c p} ⊆
      W.embedding '' {z : spatialNeckBuffer epsilon | |z.val.2| ≤ 5 * Real.pi} := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hp : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hn : |-(5 * Real.pi)| < epsilon⁻¹ + 1 := by rwa [abs_neg]
  have hcompl := (D.ordered_band (-(5 * Real.pi)) (5 * Real.pi) hn hp
    (by linarith [Real.pi_pos])).2.2
  have hband : {z : spatialNeckBuffer epsilon | -(5 * Real.pi) ≤ z.val.2 ∧ z.val.2 ≤ 5 * Real.pi} =
      {z : spatialNeckBuffer epsilon | |z.val.2| ≤ 5 * Real.pi} := by
    ext z
    exact abs_le.symm
  rw [hband] at hcompl
  intro q hq
  by_contra hnot
  have hout : q ∈ (W.embedding '' {z : spatialNeckBuffer epsilon | |z.val.2| ≤ 5 * Real.pi})ᶜ := hnot
  rw [hcompl] at hout
  rcases hout with hi | ho
  · exact (D.busemann_inward_lt hEnorm hsmall hc hi).ne hq
  · exact (D.busemann_outward_lt hEnorm hsmall hsec hc ho).ne hq.symm

theorem exists_vertical_busemann_level (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) (y : SpatialNeckSphere) :
    ∃ z : spatialNeckBuffer epsilon, z.val.1 = y ∧ |z.val.2| ≤ 5 * Real.pi ∧
      busemann c (W.embedding z) = busemann c p := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hab : -(5 * Real.pi) ≤ 5 * Real.pi := by linarith [Real.pi_pos]
  let lift : Icc (-(5 * Real.pi)) (5 * Real.pi) → spatialNeckBuffer epsilon := fun t =>
    ⟨(y, t.val), by
      have ht := t.property
      change -epsilon⁻¹ - 1 < t.val ∧ t.val < epsilon⁻¹ + 1
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]⟩
  have hlift : Continuous lift := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_subtype_val
  let β : ℝ → spatialNeckBuffer epsilon := lift ∘ projIcc (-(5 * Real.pi)) (5 * Real.pi) hab
  have hβ : Continuous β := hlift.comp continuous_projIcc
  let f : ℝ → ℝ := busemann c ∘ W.embedding ∘ β
  have hf : Continuous f := (lipschitzWith_busemann hc).continuous.comp (W.embedding.continuous.comp hβ)
  have hβlo : (β (-(5 * Real.pi))).val.2 = -(5 * Real.pi) := by
    dsimp only [β, Function.comp_def, lift]
    rw [projIcc_of_mem hab ⟨le_rfl, hab⟩]
  have hβhi : (β (5 * Real.pi)).val.2 = 5 * Real.pi := by
    dsimp only [β, Function.comp_def, lift]
    rw [projIcc_of_mem hab ⟨hab, le_rfl⟩]
  have hbounds : busemann c p ∈ Icc (f (-(5 * Real.pi))) (f (5 * Real.pi)) :=
    ⟨D.lower_slice_busemann_le hEnorm hsmall hc _ hβlo,
      D.upper_slice_busemann_ge hEnorm hsmall hsec hc _ hβhi⟩
  obtain ⟨s, _hs, hfs⟩ := intermediate_value_Icc hab hf.continuousOn hbounds
  refine ⟨β s, rfl, ?_, hfs⟩
  exact abs_le.mpr (projIcc (-(5 * Real.pi)) (5 * Real.pi) hab s).property

theorem busemann_level_ediam_bounds (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
      Metric.ediam {q : N | busemann c q = busemann c p} ∧
    Metric.ediam {q : N | busemann c q = busemann c p} ≤
      ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p) := by
  constructor
  · obtain ⟨z, hz, hzband, hzlevel⟩ := D.exists_vertical_busemann_level hEnorm hsmall hsec hc (-yStar)
    have hlower := W.marked_antipodal_edist_lower hsmall z hzband hz
    rw [riemannianEDistOf_eq_riemannianEDist h hEnorm,
      ← IsRiemannianManifold.out (I := I)] at hlower
    exact hlower.trans (Metric.edist_le_ediam_of_mem (by rfl : p ∈ {q : N | busemann c q = busemann c p})
      hzlevel)
  · exact (Metric.ediam_mono (D.busemann_level_subset_band hEnorm hsmall hsec hc)).trans
      (W.band_ediam_le hEnorm hsmall)

theorem busemann_level_diam_bounds (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    11 / 12 * spatialNeckScale h p * Real.pi ≤
      Metric.diam {q : N | busemann c q = busemann c p} ∧
    Metric.diam {q : N | busemann c q = busemann c p} ≤
      11 * Real.pi * spatialNeckScale h p := by
  obtain ⟨hlower, hupper⟩ := D.busemann_level_ediam_bounds hEnorm hsmall hsec hc
  have hfinite : Metric.ediam {q : N | busemann c q = busemann c p} ≠ ⊤ :=
    ne_of_lt (hupper.trans_lt ENNReal.ofReal_lt_top)
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hfinite).mp hlower,
    ENNReal.toReal_le_of_le_ofReal (by positivity) hupper⟩

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
