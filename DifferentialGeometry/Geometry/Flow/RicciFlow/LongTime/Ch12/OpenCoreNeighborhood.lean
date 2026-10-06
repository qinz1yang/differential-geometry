import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicClosedRange
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRestriction

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- A topological neighborhood of one entire end, using the given inward collar.
Only its topology is used; no smoothness across its zero torus is asserted. -/
def endNeighborhood_CX1 (i : Fin T.count) : Set H.Carrier :=
  (range fun z : thetaDom_CPA2 => theta_CPA2 T i z.val) ∪ cuspW_CPA2 T i

theorem endNeighborhood_open_CX1 (i : Fin T.count) :
    IsOpen (endNeighborhood_CX1 T i) := by
  apply IsOpen.union _ (isOpen_cuspW_CPA2 T i)
  have h := isOpen_image_interior_CPA2 (N := H.Carrier) signedCollarModel
    (by simp [Module.finrank_prod]) (continuous_theta_CPA2 T i) (injective_theta_CPA2 T i)
  simpa only [ModelWithCorners.interior_eq_univ, image_univ] using h

theorem cusp_subset_endNeighborhood_CX1 (i : Fin T.count) :
    range (T.cuspMap i) ⊆ endNeighborhood_CX1 T i := by
  rintro _ ⟨q, rfl⟩
  rcases q.2.property.eq_or_lt with hzero | hpos
  · have hq := halfZero_of_height_zero'_CPA2 hzero.symm
    left
    refine ⟨⟨(q.1, 0), by constructor <;> norm_num⟩, ?_⟩
    exact (theta_zero_CPA2 T i q.1).trans
      (congrArg (T.cuspMap i) (Prod.ext rfl hq.symm))
  · exact Or.inr ⟨q, hpos, rfl⟩

theorem endNeighborhood_subset_CX1 (i : Fin T.count) :
    endNeighborhood_CX1 T i ⊆
      T.inclusion '' ((T.boundary.collar i).target ∩ T.core.interior) ∪ range (T.cuspMap i) := by
  rintro p (⟨z, rfl⟩ | hp)
  · by_cases hz : 0 ≤ z.val.2
    · right
      change theta_CPA2 T i z.val ∈ range (T.cuspMap i)
      rw [theta_of_nonneg_CPA2 T i hz]
      exact ⟨_, rfl⟩
    · left
      have hneg : z.val.2 < 0 := not_le.mp hz
      have hheight : (halfSpaceOneLift (-z.val.2)).val 0 < 1 := by
        rw [lift_height_CPA2 (by linarith)]
        linarith [z.property.1]
      refine ⟨T.boundary.collar i (z.val.1, halfSpaceOneLift (-z.val.2)), ⟨?_, ?_⟩,
        (theta_of_neg_CPA2 T i hneg).symm⟩
      · apply (T.boundary.collar i).map_source
        rw [T.boundary.source_eq]
        exact hheight
      · exact collar_interior_CPA2 T i hheight (lift_height_pos_CPA2 (by linarith))
  · exact Or.inr (image_subset_range _ _ hp)

theorem endNeighborhood_disjoint_CX1 :
    Pairwise (fun i j => Disjoint (endNeighborhood_CX1 T i) (endNeighborhood_CX1 T j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro p hi hj
  rcases endNeighborhood_subset_CX1 T i hi with ⟨x, hx, rfl⟩ | hi
  · rcases endNeighborhood_subset_CX1 T j hj with ⟨y, hy, heq⟩ | hj
    · have hxy : y = x := T.embedding.isEmbedding.injective heq
      subst y
      exact Set.disjoint_left.mp (T.boundary.disjoint hij) hx.1 hy.1
    · exact inclusion_not_mem_range_of_interior_CPA2 T j hx.2 hj
  · rcases endNeighborhood_subset_CX1 T j hj with ⟨y, hy, rfl⟩ | hj
    · exact inclusion_not_mem_range_of_interior_CPA2 T i hy.2 hi
    · exact Set.disjoint_left.mp (T.cusp_disjoint hij) hi hj

/-- Shrink a smooth bicollar uniformly over its compact zero torus. -/
theorem exists_small_bicollar_CX1 {e : Torus → H.Carrier}
    (d : SmoothTwoSidedCollar torusModel (𝓡 3) e)
    {V : Set H.Carrier} (hV : IsOpen V) (heV : ∀ x, e x ∈ V) :
    ∃ (r : ℝ) (hr : 0 < r) (hrd : r ≤ d.radius),
      ((d.restrictRadius r hr hrd).neighborhood : Set H.Carrier) ⊆ V := by
  let N : Set (Torus × ℝ) := d.toPartialDiffeomorph ⁻¹' V
  have hN : ∀ x : Torus, N ∈ 𝓝 (x, (0 : ℝ)) := by
    intro x
    have hx : (x, (0 : ℝ)) ∈ d.toPartialDiffeomorph.source := by
      rw [d.toPartialDiffeomorph_source]
      exact ⟨trivial, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩
    have hval : d.toPartialDiffeomorph (x, (0 : ℝ)) = e x := by
      exact (d.toPartialDiffeomorph_apply
        (x, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)).trans (d.toFun_zero x)
    exact (d.toPartialDiffeomorph.toOpenPartialHomeomorph.continuousAt hx).preimage_mem_nhds
      (hV.mem_nhds (by
        change d.toPartialDiffeomorph (x, (0 : ℝ)) ∈ V
        rw [hval]
        exact heV x))
  have hprod : N ∈ nhdsSet (univ : Set Torus) ×ˢ 𝓝 (0 : ℝ) :=
    isCompact_univ.mem_nhdsSet_prod_of_forall (fun x _ => by
      simpa [nhds_prod_eq] using hN x)
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hprod
  have hAall : ∀ x : Torus, x ∈ A := by
    have hAu : A = univ := by simpa using hA
    simp [hAu]
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hB
  let r := min δ d.radius
  have hr : 0 < r := lt_min hδ d.radius_pos
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  rw [d.restrictRadius_neighborhood]
  rintro _ ⟨q, rfl⟩
  have hqB : q.2.val ∈ B := by
    apply hδB
    rw [Real.ball_eq_Ioo]
    simp only [zero_sub, zero_add, mem_Ioo]
    constructor
    · linarith [q.2.property.1, min_le_left δ d.radius]
    · exact q.2.property.2.trans_le (min_le_left _ _)
  have hq := hAB (show (q.1, q.2.val) ∈ A ×ˢ B from ⟨hAall q.1, hqB⟩)
  change d.toPartialDiffeomorph (q.1, q.2.val) ∈ V at hq
  rwa [d.toPartialDiffeomorph_apply
    (q.1, ⟨q.2.val, (Ioo_subset_Ioo (neg_le_neg (min_le_right δ d.radius))
      (min_le_right δ d.radius)) q.2.property⟩)] at hq

/-- The actual open core is the complement of all closed cusp ends. -/
theorem mem_openCoreImage_iff_CX1 (p : H.Carrier) :
    p ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) ↔
      ∀ i, p ∉ range (T.cuspMap i) := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact inclusion_not_mem_range_of_interior_CPA2 T i hx
  · intro hp
    have hex : p ∈ range T.inclusion ∪ ⋃ i, range (T.cuspMap i) := by
      rw [T.exhausts]
      trivial
    rcases hex with ⟨x, rfl⟩ | hex
    · refine ⟨x, ?_, rfl⟩
      by_contra hx
      have hb := (T.core.model.isInteriorPoint_or_isBoundaryPoint x).resolve_left hx
      have hb' : x ∈ T.boundary.image := by rwa [← T.boundary_exhausted]
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hb'
      exact hp i ⟨(t, halfZero), (T.cusp_zero i t).trans (congrArg T.inclusion ht)⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hex
      exact (hp i hi).elim

/-- An actual cusp has a smooth bicollar whose negative side lies in the open
core, and whose whole finite collar stays in its own disjoint end neighborhood. -/
theorem exists_core_cusp_bicollar_CX1 (i : Fin T.count) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3)
        (fun x => T.cuspMap i (x, halfZero)),
      (∀ p (_hp : 0 ≤ p.2.val),
        d.toFun p = T.cuspMap i (p.1, halfSpaceOneLift p.2.val)) ∧
      (∀ p, p.2.val < 0 →
        d.toFun p ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier)) ∧
      (d.neighborhood : Set H.Carrier) ⊆ endNeighborhood_CX1 T i := by
  obtain ⟨d, _, hd⟩ := exists_cusp_bicollar_CX1 T i
  let tail : Set H.Carrier := T.cuspMap i '' {q | d.radius / 2 ≤ q.2.val 0}
  have htail : IsClosed tail :=
    isClosed_cuspTail_CPA2 T (isClosed_range_cuspMap_CPA2 T) i (d.radius / 2)
  have hzero : ∀ x, T.cuspMap i (x, halfZero) ∈ endNeighborhood_CX1 T i ∩ tailᶜ := by
    intro x
    refine ⟨cusp_subset_endNeighborhood_CX1 T i ⟨_, rfl⟩, ?_⟩
    rintro ⟨q, hq, heq⟩
    have h := (T.cuspEmbedding i).isEmbedding.injective heq
    rw [h] at hq
    change d.radius / 2 ≤ 0 at hq
    linarith [d.radius_pos]
  obtain ⟨r, hr, hrd, hsmall⟩ := exists_small_bicollar_CX1 d
    ((endNeighborhood_open_CX1 T i).inter htail.isOpen_compl) hzero
  let c := d.restrictRadius r hr hrd
  have hinside (p : Torus × symmetricOpenInterval c.radius) :
      c.toFun p ∈ endNeighborhood_CX1 T i ∩ tailᶜ :=
    hsmall (c.toDiffeomorph p).property
  have hpos (p : Torus × symmetricOpenInterval c.radius) (hp : 0 ≤ p.2.val) :
      c.toFun p = T.cuspMap i (p.1, halfSpaceOneLift p.2.val) :=
    hd (p.1, ⟨p.2.val, (Ioo_subset_Ioo (neg_le_neg hrd) hrd) p.2.property⟩) hp
  refine ⟨c, hpos, ?_, fun _ hx => (hsmall hx).1⟩
  intro p hp
  rw [mem_openCoreImage_iff_CX1]
  intro j hj
  by_cases hji : j = i
  · subst j
    obtain ⟨q, hq⟩ := hj
    have hheight : q.2.val 0 < d.radius / 2 := by
      by_contra h
      exact (hinside p).2 ⟨q, le_of_not_gt h, hq⟩
    let z : Torus × symmetricOpenInterval d.radius :=
      (q.1, ⟨q.2.val 0, (neg_lt_zero.mpr d.radius_pos).trans_le q.2.property,
        hheight.trans (half_lt_self d.radius_pos)⟩)
    have hz : d.toFun z = T.cuspMap i q := by
      rw [hd z q.2.property]
      exact congrArg (T.cuspMap i) (Prod.ext rfl (by
        apply Subtype.ext
        ext j
        rw [Subsingleton.elim j 0]
        exact max_eq_left q.2.property))
    have heq : z = (p.1, ⟨p.2.val, (Ioo_subset_Ioo (neg_le_neg hrd) hrd) p.2.property⟩) :=
      d.isOpenEmbedding_toFun.injective (hz.trans hq)
    have ht := congrArg (fun z : Torus × symmetricOpenInterval d.radius => z.2.val) heq
    change q.2.val 0 = p.2.val at ht
    linarith [q.2.property]
  · exact Set.disjoint_left.mp (endNeighborhood_disjoint_CX1 T (Ne.symm hji))
      (hinside p).1 (cusp_subset_endNeighborhood_CX1 T j hj)

end GC.LongTime.Ch12
