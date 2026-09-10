import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

open private geodesicSegment_eqOn_intrinsic
  from DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]

theorem isCompact_busemann_sublevel_of_proper
    (c : ℝ≥0 → X) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) (a : ℝ) :
    IsCompact {x : X | busemann c x ≤ a} := by
  obtain ⟨L, hL⟩ := hbelow
  have hset : {x : X | busemann c x ≤ a} = busemann c ⁻¹' Icc L a := by
    ext x
    exact ⟨fun hx => ⟨hL ⟨x, rfl⟩, hx⟩, fun hx => hx.2⟩
  rw [hset]
  exact hproper.isCompact_preimage isCompact_Icc

theorem isCompact_busemann_level_of_proper
    (c : ℝ≥0 → X) (hproper : IsProperMap (busemann c)) (a : ℝ) :
    IsCompact {x : X | busemann c x = a} := by
  change IsCompact (busemann c ⁻¹' ({a} : Set ℝ))
  exact hproper.isCompact_preimage isCompact_singleton

theorem exists_busemann_minimum_of_proper
    (c : ℝ≥0 → X) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) :
    ∃ p : X, busemann c p = (⨅ x : X, busemann c x) ∧
      ∀ x : X, busemann c p ≤ busemann c x := by
  let _ : Nonempty X := ⟨c 0⟩
  have hK := isCompact_busemann_sublevel_of_proper c hproper hbelow (busemann c (c 0))
  obtain ⟨p, _hp, hmin⟩ :=
    hK.exists_isMinOn ⟨c 0, by simp only [mem_ofPred_eq, le_refl]⟩
      hproper.continuous.continuousOn
  have hglobal (x : X) : busemann c p ≤ busemann c x := by
    by_cases hx : busemann c x ≤ busemann c (c 0)
    · exact (isMinOn_iff.mp hmin) x hx
    · exact ((isMinOn_iff.mp hmin) (c 0)
        (by simp only [mem_ofPred_eq, le_refl])).trans (le_of_not_ge hx)
  refine ⟨p, le_antisymm ?_ (ciInf_le hbelow p), hglobal⟩
  exact (le_ciInf_iff hbelow).mpr hglobal

theorem busemann_sublevel_nonempty_iff
    (c : ℝ≥0 → X) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) (a : ℝ) :
    ({x : X | busemann c x ≤ a}).Nonempty ↔
      (⨅ x : X, busemann c x) ≤ a := by
  constructor
  · rintro ⟨x, hx⟩
    exact (ciInf_le hbelow x).trans hx
  · intro ha
    obtain ⟨p, hp, _hmin⟩ := exists_busemann_minimum_of_proper c hproper hbelow
    exact ⟨p, hp.le.trans ha⟩


theorem busemann_sublevel_mono (c : ℝ≥0 → X) :
    Monotone (fun a : ℝ => {x : X | busemann c x ≤ a}) := by
  intro a b hab x hx
  exact hx.trans hab

theorem iUnion_busemann_sublevel_above_minimum
    (c : ℝ≥0 → X) (hbelow : BddBelow (range (busemann c))) :
    (⋃ a : ℝ, ⋃ (_ : (⨅ x : X, busemann c x) ≤ a),
      {x : X | busemann c x ≤ a}) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨busemann c x,
    mem_iUnion.mpr ⟨ciInf_le hbelow x, by simp only [mem_ofPred_eq, le_refl]⟩⟩

end Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_busemann_level_at_dist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (p : M) (a : ℝ)
    (ha : busemann c p ≤ a) :
    ∃ q : M, busemann c q = a ∧ dist p q = a - busemann c p := by
  obtain ⟨u, _hu, hiso, hcal⟩ := exists_calibrated_intrinsic_ray g hEnorm c hc p
  let s := a - busemann c p
  have hs : 0 ≤ s := sub_nonneg.mpr ha
  refine ⟨intrinsicGeodesic g hEnorm p u s, ?_, ?_⟩
  · rw [hcal s hs]
    dsimp only [s]
    ring
  · have h := hiso.dist_eq 0 ⟨s, hs⟩
    change dist (intrinsicGeodesic g hEnorm p u 0)
      (intrinsicGeodesic g hEnorm p u s) = |(0 : ℝ) - s| at h
    simpa only [intrinsicGeodesic_zero, zero_sub, abs_neg, abs_of_nonneg hs] using h

theorem exists_busemann_gt_in_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (p : M) {r : ℝ} (hr : 0 < r) :
    ∃ q ∈ Metric.ball p r, busemann c p < busemann c q := by
  obtain ⟨q, hq, hd⟩ := exists_busemann_level_at_dist g hEnorm hc p
    (busemann c p + r / 2) (by linarith)
  refine ⟨q, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, hd]
    linarith
  · rw [hq]
    linarith

theorem interior_busemann_sublevel_eq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (a : ℝ) :
    interior {x : M | busemann c x ≤ a} = {x : M | busemann c x < a} := by
  ext p
  constructor
  · intro hp
    have hpa : busemann c p ≤ a :=
      interior_subset (s := {x : M | busemann c x ≤ a}) hp
    rcases lt_or_eq_of_le hpa with hlt | heq
    · exact hlt
    · obtain ⟨r, hr, hball⟩ :=
        Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
      obtain ⟨q, hqball, hqgt⟩ := exists_busemann_gt_in_ball g hEnorm hc p hr
      have hqa : busemann c q ≤ a := hball hqball
      rw [heq] at hqgt
      exact False.elim ((not_lt_of_ge hqa) hqgt)
  · intro hp
    exact mem_interior.mpr ⟨{x : M | busemann c x < a},
      (fun x hx => by change busemann c x ≤ a; exact hx.le),
      isOpen_lt (lipschitzWith_busemann hc).continuous continuous_const, hp⟩

theorem frontier_busemann_sublevel_eq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (a : ℝ) :
    frontier {x : M | busemann c x ≤ a} = {x : M | busemann c x = a} := by
  rw [(isClosed_le (lipschitzWith_busemann hc).continuous continuous_const).frontier_eq,
    interior_busemann_sublevel_eq g hEnorm hc a]
  ext x
  change (busemann c x ≤ a ∧ ¬ busemann c x < a) ↔ busemann c x = a
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt h.2),
    fun h => ⟨h.le, not_lt_of_ge h.ge⟩⟩

theorem busemann_level_nonempty_iff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) (a : ℝ) :
    ({x : M | busemann c x = a}).Nonempty ↔
      (⨅ x : M, busemann c x) ≤ a := by
  constructor
  · rintro ⟨x, hx⟩
    exact (ciInf_le hbelow x).trans hx.le
  · intro ha
    obtain ⟨p, hp, _hmin⟩ := exists_busemann_minimum_of_proper c hproper hbelow
    obtain ⟨q, hq, _hd⟩ := exists_busemann_level_at_dist g hEnorm hc p a (hp.le.trans ha)
    exact ⟨q, hq⟩

theorem interior_busemann_sublevel_nonempty_iff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {c : ℝ≥0 → M} (hc : Isometry c) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) (a : ℝ) :
    (interior {x : M | busemann c x ≤ a}).Nonempty ↔
      (⨅ x : M, busemann c x) < a := by
  rw [interior_busemann_sublevel_eq g hEnorm hc a]
  constructor
  · rintro ⟨x, hx⟩
    exact (ciInf_le hbelow x).trans_lt hx
  · intro ha
    obtain ⟨p, hp, _hmin⟩ := exists_busemann_minimum_of_proper c hproper hbelow
    exact ⟨p, hp.le.trans_lt ha⟩

variable [ConnectedSpace M]

theorem isTotallyConvex_busemann_sublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) (k : ℝ) :
    IsTotallyConvex (I := I) g {x : M | busemann c x ≤ k} := by
  intro γ a b hab hgeo hcont ha hb t ht
  rcases hab.eq_or_lt with rfl | hab
  · have ht' : t = a := le_antisymm ht.2 ht.1
    simpa only [ht'] using ha
  obtain ⟨q, v, r, heq⟩ := geodesicSegment_eqOn_intrinsic g hEnorm hab hgeo hcont
  have hleft : busemann c (intrinsicGeodesic g hEnorm q v (a - r)) ≤ k := by
    simpa only [mem_ofPred_eq, heq (left_mem_Icc.mpr hab.le)] using ha
  have hright : busemann c (intrinsicGeodesic g hEnorm q v (b - r)) ≤ k := by
    simpa only [mem_ofPred_eq, heq (right_mem_Icc.mpr hab.le)] using hb
  change busemann c (γ t) ≤ k
  rw [heq ht]
  have hconv := convexOn_busemann_intrinsicGeodesic g hEnorm hsec hc q v convex_univ
  exact (hconv.le_max_of_mem_Icc (mem_univ (a - r)) (mem_univ (b - r))
      ⟨sub_le_sub_right ht.1 r, sub_le_sub_right ht.2 r⟩).trans
        (max_le hleft hright)

theorem exists_minimizing_intrinsicGeodesic_in_busemann_sublevel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) {a : ℝ} {p q : M}
    (hp : busemann c p ≤ a) (hq : busemann c q ≤ a) :
    ∃ v : TangentSpace I p,
      intrinsicGeodesic g hEnorm p v 1 = q ∧
      MapsTo (intrinsicGeodesic g hEnorm p v) (Icc 0 1)
        {x : M | busemann c x ≤ a} ∧
      Real.sqrt (g.inner p v v) = dist p q := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q)
  have hone : intrinsicGeodesic g hEnorm p v 1 = q := hv
  refine ⟨v, hone, ?_, ?_⟩
  · exact isTotallyConvex_busemann_sublevel g hEnorm hsec hc a
      (by norm_num : (0 : ℝ) ≤ 1)
      ((intrinsicGeodesic_isGeodesic g hEnorm p v).isGeodesicOn _)
      (intrinsicGeodesic_continuous g hEnorm p v).continuousOn
      (by simpa only [mem_ofPred_eq, intrinsicGeodesic_zero] using hp)
      (by simpa only [mem_ofPred_eq, hone] using hq)
  · rwa [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hlen

theorem busemann_sublevel_spec_of_proper
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {c : ℝ≥0 → M} (hc : Isometry c) (hproper : IsProperMap (busemann c))
    (hbelow : BddBelow (range (busemann c))) (a : ℝ)
    (ha : (⨅ x : M, busemann c x) ≤ a) :
    ({x : M | busemann c x ≤ a}).Nonempty ∧
      IsCompact {x : M | busemann c x ≤ a} ∧
      IsPathConnected {x : M | busemann c x ≤ a} ∧
      IsTotallyConvex (I := I) g {x : M | busemann c x ≤ a} := by
  have hne := (busemann_sublevel_nonempty_iff c hproper hbelow a).mpr ha
  have hconv : IsTotallyConvex (I := I) g {x : M | busemann c x ≤ a} :=
    isTotallyConvex_busemann_sublevel g hEnorm hsec hc a
  exact ⟨hne, isCompact_busemann_sublevel_of_proper c hproper hbelow a,
    hconv.isPathConnected g hEnorm hne, hconv⟩

end DifferentialGeometry.Geometry.Topology

end
