import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreNeighborhood
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) (i : Fin T.count)

/-- The positive cusp chart in a real height coordinate. -/
def realCuspChart_CX1 : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) H.Carrier ∞ :=
  ((Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph.prod
    halfSpaceOneInteriorDiffeomorph).trans (cuspChart_CPA2 T i)

theorem realCuspChart_apply_CX1 (p : Torus × ℝ) :
    realCuspChart_CX1 T i p = T.cuspMap i (p.1, halfSpaceOneLift p.2) :=
  cuspChart_apply_CPA2 T i _

theorem realCuspChart_mem_source_CX1 {p : Torus × ℝ} (hp : 0 < p.2) :
    p ∈ (realCuspChart_CX1 T i).source := by
  refine ⟨⟨trivial, hp⟩, ?_⟩
  change (p.1, halfSpaceOneLift p.2) ∈ (cuspChart_CPA2 T i).source
  rw [cuspChart_source_CPA2]
  exact lift_height_pos_CPA2 hp

section Extension

variable (d : SmoothTwoSidedCollar torusModel (𝓡 3)
  (fun x => T.cuspMap i (x, halfZero)))

/-- Glue the smooth extension to the unchanged infinite cusp inside their
positive overlap, retaining the original torus coordinate. -/
def extendedCuspMap_CX1 (p : Torus × ℝ) : H.Carrier :=
  open Classical in
  if p.2 < d.radius / 2 then d.toPartialDiffeomorph p
  else T.cuspMap i (p.1, halfSpaceOneLift p.2)

variable (hd : ∀ p (_hp : 0 ≤ p.2.val),
  d.toFun p = T.cuspMap i (p.1, halfSpaceOneLift p.2.val))

include hd

theorem extendedCuspMap_eq_collar_CX1 {p : Torus × ℝ}
    (hp : p.2 ∈ Ioo (-d.radius) d.radius) :
    extendedCuspMap_CX1 T i d p = d.toPartialDiffeomorph p := by
  classical
  unfold extendedCuspMap_CX1
  split_ifs with h
  · rfl
  · exact (d.toPartialDiffeomorph_apply (p.1, ⟨p.2, hp⟩)).trans
      (hd (p.1, ⟨p.2, hp⟩) (by linarith [d.radius_pos, not_lt.mp h])) |>.symm

theorem extendedCuspMap_eq_cusp_CX1 {p : Torus × ℝ} (hp : 0 ≤ p.2) :
    extendedCuspMap_CX1 T i d p = T.cuspMap i (p.1, halfSpaceOneLift p.2) := by
  classical
  unfold extendedCuspMap_CX1
  split_ifs with h
  · have hsrc : p.2 ∈ Ioo (-d.radius) d.radius :=
      ⟨(neg_lt_zero.mpr d.radius_pos).trans_le hp,
        h.trans (half_lt_self d.radius_pos)⟩
    exact (d.toPartialDiffeomorph_apply (p.1, ⟨p.2, hsrc⟩)).trans
      (hd (p.1, ⟨p.2, hsrc⟩) hp)
  · rfl

theorem extendedCuspMap_local_CX1 :
    IsLocalDiffeomorphOn signedCollarModel (𝓡 3) ∞ (extendedCuspMap_CX1 T i d)
      (univ ×ˢ Ioi (-d.radius)) := by
  intro p
  by_cases h : p.val.2 < d.radius / 2
  · have hp : p.val ∈ d.toPartialDiffeomorph.source := by
      rw [d.toPartialDiffeomorph_source]
      exact ⟨trivial, p.property.2, h.trans (half_lt_self d.radius_pos)⟩
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _
      (d.toPartialDiffeomorph.isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞ hp)
    filter_upwards [d.toPartialDiffeomorph.open_source.mem_nhds hp] with q hq
    rw [d.toPartialDiffeomorph_source] at hq
    exact extendedCuspMap_eq_collar_CX1 T i d hd hq.2
  · have hp : 0 < p.val.2 := by linarith [d.radius_pos, not_lt.mp h]
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _
      ((realCuspChart_CX1 T i).isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞
        (realCuspChart_mem_source_CX1 T i hp))
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact (extendedCuspMap_eq_cusp_CX1 T i d hd hq.le).trans
      (realCuspChart_apply_CX1 T i q).symm

variable (hneg : ∀ p, p.2.val < 0 →
  d.toFun p ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier))

include hneg

theorem extendedCuspMap_negative_CX1 {p : Torus × ℝ}
    (hp : -d.radius < p.2) (hn : p.2 < 0) :
    extendedCuspMap_CX1 T i d p ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) := by
  have hsrc : p.2 ∈ Ioo (-d.radius) d.radius := ⟨hp, hn.trans d.radius_pos⟩
  rw [extendedCuspMap_eq_collar_CX1 T i d hd hsrc,
    d.toPartialDiffeomorph_apply (p.1, ⟨p.2, hsrc⟩)]
  exact hneg _ hn

theorem extendedCuspMap_injective_CX1 :
    InjOn (extendedCuspMap_CX1 T i d) (univ ×ˢ Ioi (-d.radius)) := by
  intro p hp q hq heq
  by_cases hpn : p.2 < 0 <;> by_cases hqn : q.2 < 0
  · have hps : p.2 ∈ Ioo (-d.radius) d.radius := ⟨hp.2, hpn.trans d.radius_pos⟩
    have hqs : q.2 ∈ Ioo (-d.radius) d.radius := ⟨hq.2, hqn.trans d.radius_pos⟩
    rw [extendedCuspMap_eq_collar_CX1 T i d hd hps,
      extendedCuspMap_eq_collar_CX1 T i d hd hqs] at heq
    exact d.toPartialDiffeomorph.toPartialEquiv.injOn
      (by rw [d.toPartialDiffeomorph_source]; exact ⟨trivial, hps⟩)
      (by rw [d.toPartialDiffeomorph_source]; exact ⟨trivial, hqs⟩) heq
  · have hc := (mem_openCoreImage_iff_CX1 T _).mp
      (extendedCuspMap_negative_CX1 T i d hd hneg hp.2 hpn) i
    exact (hc ⟨(q.1, halfSpaceOneLift q.2),
      (extendedCuspMap_eq_cusp_CX1 T i d hd (le_of_not_gt hqn)).symm.trans heq.symm⟩).elim
  · have hc := (mem_openCoreImage_iff_CX1 T _).mp
      (extendedCuspMap_negative_CX1 T i d hd hneg hq.2 hqn) i
    exact (hc ⟨(p.1, halfSpaceOneLift p.2),
      (extendedCuspMap_eq_cusp_CX1 T i d hd (le_of_not_gt hpn)).symm.trans heq⟩).elim
  · rw [extendedCuspMap_eq_cusp_CX1 T i d hd (le_of_not_gt hpn),
      extendedCuspMap_eq_cusp_CX1 T i d hd (le_of_not_gt hqn)] at heq
    have he := (T.cuspEmbedding i).isEmbedding.injective heq
    apply Prod.ext
    · exact congrArg (fun z : CuspHalfSpace => z.1) he
    · have hh := congrArg (fun x : CuspHalfSpace => x.2.val 0) he
      change (halfSpaceOneLift p.2).val 0 = (halfSpaceOneLift q.2).val 0 at hh
      rwa [lift_height_CPA2 (le_of_not_gt hpn), lift_height_CPA2 (le_of_not_gt hqn)] at hh

end Extension

/-- Smooth signed coordinates on an entire end, together with a closed support
set strictly inside its open chart. These are data produced from the truncation. -/
structure CuspEndChart_CX1 where
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) H.Carrier ∞
  source_eq : chart.source = univ ×ˢ Ioi (-radius)
  on_cusp : ∀ q : Torus × ℝ, 0 ≤ q.2 →
    chart q = T.cuspMap i (q.1, halfSpaceOneLift q.2)
  in_core : ∀ q ∈ chart.source,
    chart q ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) ↔ q.2 < 0
  end_subset : chart.target ⊆ endNeighborhood_CX1 T i
  support : Set H.Carrier
  support_closed : IsClosed support
  support_subset : support ⊆ chart.target
  large_heights : chart '' (univ ×ˢ Ici (-(3 * radius / 4))) ⊆ support

/-- Produce signed coordinates on the full actual cusp, including a smooth
inward extension and a closed set supporting the later height change. -/
theorem exists_cuspEndChart_CX1 : Nonempty (CuspEndChart_CX1 T i) := by
  classical
  obtain ⟨d, hd, hneg, hend⟩ := exists_core_cusp_bicollar_CX1 T i
  obtain ⟨E, hEs, hEt, hE⟩ := exists_partialDiffeomorph_of_injOn
    (isOpen_univ.prod isOpen_Ioi) (extendedCuspMap_local_CX1 T i d hd)
    (extendedCuspMap_injective_CX1 T i d hd hneg)
  have heq (q : Torus × ℝ) : E q = extendedCuspMap_CX1 T i d q := congrFun hE q
  have hcusp (q : Torus × ℝ) (hq : 0 ≤ q.2) :
      E q = T.cuspMap i (q.1, halfSpaceOneLift q.2) :=
    (heq q).trans (extendedCuspMap_eq_cusp_CX1 T i d hd hq)
  have hcore (q : Torus × ℝ) (hq : q ∈ E.source) :
      E q ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) ↔ q.2 < 0 := by
    rw [hEs] at hq
    constructor
    · intro hqcore
      by_contra hn
      have hnot := (mem_openCoreImage_iff_CX1 T (E q)).mp hqcore i
      exact hnot ⟨(q.1, halfSpaceOneLift q.2), (hcusp q (le_of_not_gt hn)).symm⟩
    · intro hn
      rw [heq]
      exact extendedCuspMap_negative_CX1 T i d hd hneg hq.2 hn
  have htarget : E.target ⊆ endNeighborhood_CX1 T i := by
    rw [hEt]
    rintro _ ⟨q, hq, rfl⟩
    by_cases hn : q.2 < d.radius / 2
    · have hq' : q.2 ∈ Ioo (-d.radius) d.radius :=
        ⟨hq.2, hn.trans (half_lt_self d.radius_pos)⟩
      rw [extendedCuspMap_eq_collar_CX1 T i d hd hq',
        d.toPartialDiffeomorph_apply (q.1, ⟨q.2, hq'⟩)]
      exact hend (d.toDiffeomorph (q.1, ⟨q.2, hq'⟩)).property
    · rw [extendedCuspMap_eq_cusp_CX1 T i d hd (by linarith [d.radius_pos, not_lt.mp hn])]
      exact cusp_subset_endNeighborhood_CX1 T i ⟨_, rfl⟩
  have hrange : range (T.cuspMap i) ⊆ E.target := by
    rintro _ ⟨q, rfl⟩
    have hqs : (q.1, q.2.val 0) ∈ E.source := by
      rw [hEs]
      exact ⟨trivial, (neg_lt_zero.mpr d.radius_pos).trans_le q.2.property⟩
    have hqeq : E (q.1, q.2.val 0) = T.cuspMap i q := by
      rw [hcusp _ q.2.property]
      congr 1
      refine Prod.ext rfl ?_
      apply Subtype.ext
      ext j
      rw [Subsingleton.elim j 0]
      exact max_eq_left q.2.property
    exact hqeq ▸ E.map_source hqs
  let strip : Set (Torus × ℝ) := univ ×ˢ Icc (-(3 * d.radius / 4)) 0
  have hstrip : strip ⊆ E.source := by
    intro q hq
    rw [hEs]
    refine ⟨trivial, ?_⟩
    have h := hq.2.1
    change -d.radius < q.2
    linarith [d.radius_pos]
  let K := E '' strip ∪ range (T.cuspMap i)
  have hK : IsClosed K :=
    ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (E.contMDiffOn.continuousOn.mono hstrip)).isClosed.union
        (isClosed_range_cuspMap_CPA2 T i)
  refine ⟨{
    radius := d.radius
    radius_pos := d.radius_pos
    chart := E
    source_eq := hEs
    on_cusp := hcusp
    in_core := hcore
    end_subset := htarget
    support := K
    support_closed := hK
    support_subset := union_subset
      (image_subset_iff.mpr (fun q hq => E.map_source (hstrip hq))) hrange
    large_heights := ?_ }⟩
  rintro _ ⟨q, hq, rfl⟩
  by_cases hn : q.2 ≤ 0
  · exact Or.inl ⟨q, ⟨trivial, hq.2, hn⟩, rfl⟩
  · exact Or.inr ⟨(q.1, halfSpaceOneLift q.2), (hcusp q (le_of_not_ge hn)).symm⟩

/-- Chosen signed chart on the entire cusp. -/
def cuspEndChart_CX1 : CuspEndChart_CX1 T i :=
  Classical.choice (exists_cuspEndChart_CX1 T i)

end GC.LongTime.Ch12
