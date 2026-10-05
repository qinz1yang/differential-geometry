import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RelativeCaps
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped

/-!
# Chapter-14 assembly, L2-relative COMPARE A6-a, part 1: the cut collar inside a capped carrier

Lane ASM-L2c. For a relative sphere capping `K : RelativeSphereCapping C Q B` and a cut sphere `i`,
the collar `capCollar K i (z, s) = K.core (B.sphere i (z, s))` of the cut sphere, seen in the capped
carrier `Q`, and its point-set topology near the cap:

* `cap_isInteriorPoint`: the cap lies in the interior of `Q`;
* `capCollar_notMem_range_cap`: positive heights avoid the cap;
* `capCollar_injOn`: the collar is injective on heights `[0, 1)`;
* `capRegion`, `isOpen_capRegion`: the cap together with the collar below a height `s₁ ≤ 1` is open
  (its complement is the compact image of the rest of the cut carrier and the other caps).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section ShellCollar

variable {C Q : CompactCarrier.{u}} {B : MixedBoundaryCertificate C}
  (K : RelativeSphereCapping C Q B) (i : Fin B.sphereCount)

/-- The lift of a real height to the closed half line at `0` is the boundary point. -/
theorem shellLift_zero : halfSpaceOneLift 0 = halfZero :=
  (halfPoint_eq_self (halfSpaceOneLift 0) le_rfl (by
    change (0 : ℝ) = max 0 0
    exact (max_self 0).symm)).symm

theorem shellLift_coord (s : ℝ) : (halfSpaceOneLift s).val 0 = max s 0 := rfl

/-- Every point of the closed half line is the lift of its coordinate. -/
theorem shellLift_val (h : EuclideanHalfSpace 1) : halfSpaceOneLift (h.val 0) = h :=
  (halfPoint_eq_self (halfSpaceOneLift (h.val 0)) h.property (by
    rw [shellLift_coord, max_eq_left h.property])).symm.trans
    (halfPoint_eq_self h h.property rfl)

theorem shellLift_mem_source (z : ClosureSphere.{u}) {s : ℝ} (hs : s < 1) :
    (z, halfSpaceOneLift s) ∈ sphereHalfCollarSource := by
  change (halfSpaceOneLift s).val 0 < 1
  rw [shellLift_coord]
  exact max_lt hs one_pos

/-- The collar of the cut sphere `i`, seen in the capped carrier. -/
def capCollar (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) : Q.Carrier :=
  K.core (B.sphere i (ULift.up p.1, halfSpaceOneLift p.2))

theorem capCollar_zero (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    capCollar K i (z, 0) = K.core (B.sphere i (ULift.up z, halfZero)) := by
  rw [capCollar, shellLift_zero]

theorem core_injective : Injective K.core := K.core_embedding.isEmbedding.injective

theorem sphere_zero_mem_target (j : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphere j (z, halfZero) ∈ (B.sphere j).target := by
  apply (B.sphere j).map_source
  rw [B.sphere_source]
  change (0 : ℝ) < 1
  norm_num

/-- A point of a cap that is also in the core lies on the cut sphere of that cap. -/
theorem exists_sphere_of_core_eq_cap {j : Fin B.sphereCount} {c : C.Carrier}
    {y : ClosedCell 3} (h : K.core c = K.cap j y) : ∃ z, c = B.sphere j (z, halfZero) := by
  have hm : K.core c ∈ range K.core ∩ range (K.cap j) := ⟨⟨c, rfl⟩, ⟨y, h.symm⟩⟩
  rw [K.core_cap_intersection] at hm
  obtain ⟨z, hz⟩ := hm
  exact ⟨z, core_injective K hz.symm⟩

/-- The caps lie in the interior of the capped carrier. -/
theorem cap_isInteriorPoint (x : ClosedCell 3) : Q.model.IsInteriorPoint (K.cap i x) := by
  rw [Q.model.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hm : K.cap i x ∈ Q.model.boundary Q.Carrier := hb
  rw [K.boundary_exhausted] at hm
  obtain ⟨j, t, ht⟩ := mem_iUnion.mp hm
  rw [K.retained_zero] at ht
  obtain ⟨z, hz⟩ := exists_sphere_of_core_eq_cap K ht
  have h1 : B.tori.collar j (t, halfZero) ∈ (B.tori.collar j).target := by
    apply (B.tori.collar j).map_source
    rw [B.tori.source_eq]
    exact zero_mem_halfCollarSource t
  have h2 := sphere_zero_mem_target i z
  change B.tori.collar j (t, halfZero) = _ at hz
  rw [hz] at h1
  exact Set.disjoint_left.mp (B.cross_disjoint j i) h1 h2

/-- Positive heights of the collar avoid the cap. -/
theorem capCollar_notMem_range_cap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : capCollar K i (z, s) ∉ range (K.cap i) := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := exists_sphere_of_core_eq_cap K hy.symm
  have hs : (ULift.up z, halfSpaceOneLift s) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    exact shellLift_mem_source _ hs1
  have hw' : (w, halfZero) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  have he := (B.sphere i).toPartialEquiv.injOn hs hw' hw
  have hc := congrArg (fun q : ClosureSphere.{u} × EuclideanHalfSpace 1 => q.2.val 0) he
  change (halfSpaceOneLift s).val 0 = (halfZero : EuclideanHalfSpace 1).val 0 at hc
  rw [shellLift_coord, max_eq_left hs0.le] at hc
  change s = (0 : ℝ) at hc
  linarith

/-- The collar is injective on heights `[0, 1)`. -/
theorem capCollar_injOn : InjOn (capCollar K i) {p | 0 ≤ p.2 ∧ p.2 < 1} := by
  intro p hp q hq h
  have hps : (ULift.up p.1, halfSpaceOneLift p.2) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    exact shellLift_mem_source _ hp.2
  have hqs : (ULift.up q.1, halfSpaceOneLift q.2) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    exact shellLift_mem_source _ hq.2
  have he := (B.sphere i).toPartialEquiv.injOn hps hqs (core_injective K h)
  have h1 : p.1 = q.1 := ULift.up_injective (congrArg Prod.fst he)
  have h2 := congrArg (fun r : ClosureSphere.{u} × EuclideanHalfSpace 1 => r.2.val 0) he
  change (halfSpaceOneLift p.2).val 0 = (halfSpaceOneLift q.2).val 0 at h2
  rw [shellLift_coord, shellLift_coord, max_eq_left hp.1, max_eq_left hq.1] at h2
  exact Prod.ext h1 h2

/-- The cap together with the collar below height `s₁`. -/
def capRegion (s₁ : ℝ) : Set Q.Carrier :=
  range (K.cap i) ∪ capCollar K i '' {p | 0 ≤ p.2 ∧ p.2 < s₁}

/-- The part of the cut carrier below height `s₁` on the cut sphere `i`. -/
private def lowCut (s₁ : ℝ) : Set C.Carrier :=
  B.sphere i '' {q | q.2.val 0 < s₁}

private theorem isOpen_lowCut {s₁ : ℝ} (h1 : s₁ ≤ 1) : IsOpen (lowCut (B := B) i s₁) := by
  apply (B.sphere i).toOpenPartialHomeomorph.isOpen_image_of_subset_source
  · exact isOpen_lt (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).comp
      continuous_snd) continuous_const
  · intro q hq
    change q ∈ (B.sphere i).source
    rw [B.sphere_source]
    exact lt_of_lt_of_le hq h1

variable {i} in
private theorem mem_lowCut_iff_capCollar {s₁ : ℝ} {c : C.Carrier} :
    c ∈ lowCut (B := B) i s₁ ↔ ∃ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
      (0 ≤ p.2 ∧ p.2 < s₁) ∧ B.sphere i (ULift.up p.1, halfSpaceOneLift p.2) = c := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(q.1.down, q.2.val 0), ⟨q.2.property, hq⟩, ?_⟩
    change B.sphere i (ULift.up q.1.down, halfSpaceOneLift (q.2.val 0)) = B.sphere i q
    rw [shellLift_val]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(ULift.up p.1, halfSpaceOneLift p.2), ?_, rfl⟩
    change (halfSpaceOneLift p.2).val 0 < s₁
    rw [shellLift_coord, max_eq_left hp.1]
    exact hp.2

/-- **The cap region is open.** Its complement is the compact image of the rest of the cut carrier
together with the other caps. -/
theorem isOpen_capRegion {s₁ : ℝ} (h0 : 0 < s₁) (h1 : s₁ ≤ 1) :
    IsOpen (capRegion K i s₁) := by
  let Z : Set Q.Carrier :=
    K.core '' (lowCut (B := B) i s₁)ᶜ ∪ ⋃ j ∈ ({i}ᶜ : Set (Fin B.sphereCount)), range (K.cap j)
  have hZ : IsCompact Z := by
    refine IsCompact.union ?_ ?_
    · exact ((isOpen_lowCut i h1).isClosed_compl.isCompact).image K.core.continuous
    · exact (Set.toFinite _).isCompact_biUnion fun j _ => isCompact_range (K.cap j).continuous
  have heq : capRegion K i s₁ = Zᶜ := by
    ext x
    constructor
    · intro hx hZx
      rcases hx with ⟨y, rfl⟩ | ⟨p, hp, rfl⟩
      · rcases hZx with ⟨c, hc, hce⟩ | hZx
        · obtain ⟨z, rfl⟩ := exists_sphere_of_core_eq_cap K hce
          apply hc
          refine ⟨(z, halfZero), ?_, rfl⟩
          change (0 : ℝ) < s₁
          exact h0
        · obtain ⟨j, hj, y', hy'⟩ := mem_iUnion₂.mp hZx
          exact Set.disjoint_left.mp (K.cap_disjoint hj) ⟨y', hy'⟩ ⟨y, rfl⟩
      · rcases hZx with ⟨c, hc, hce⟩ | hZx
        · apply hc
          rw [core_injective K hce]
          exact mem_lowCut_iff_capCollar.mpr ⟨p, hp, rfl⟩
        · obtain ⟨j, hj, y', hy'⟩ := mem_iUnion₂.mp hZx
          obtain ⟨w, hw⟩ := exists_sphere_of_core_eq_cap K hy'.symm
          have ht1 : B.sphere i (ULift.up p.1, halfSpaceOneLift p.2) ∈ (B.sphere i).target := by
            apply (B.sphere i).map_source
            rw [B.sphere_source]
            exact shellLift_mem_source _ (lt_of_lt_of_le hp.2 h1)
          rw [hw] at ht1
          exact Set.disjoint_left.mp (B.sphere_disjoint hj) (sphere_zero_mem_target j w) ht1
    · intro hx
      rcases K.every_point x with ⟨c, rfl⟩ | ⟨j, y, rfl⟩
      · by_cases hc : c ∈ lowCut (B := B) i s₁
        · obtain ⟨p, hp, rfl⟩ := mem_lowCut_iff_capCollar.mp hc
          exact Or.inr ⟨p, hp, rfl⟩
        · exact absurd (show K.core c ∈ Z from Or.inl ⟨c, hc, rfl⟩) hx
      · by_cases hj : j = i
        · subst hj
          exact Or.inl ⟨y, rfl⟩
        · exact absurd (show K.cap j y ∈ Z from Or.inr (mem_iUnion₂.mpr ⟨j, hj, y, rfl⟩)) hx
  rw [heq]
  exact hZ.isClosed.isOpen_compl

theorem continuous_shellLift : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

/-- The collar is continuous below height `1`. -/
theorem continuousOn_capCollar : ContinuousOn (capCollar K i) {p | p.2 < 1} := by
  have hf : Continuous fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
      ((ULift.up p.1 : ClosureSphere.{u}), halfSpaceOneLift p.2) :=
    (continuous_uliftUp.comp continuous_fst).prodMk (continuous_shellLift.comp continuous_snd)
  refine K.core.continuous.comp_continuousOn
    ((B.sphere i).contMDiffOn.continuousOn.comp hf.continuousOn ?_)
  intro p hp
  rw [B.sphere_source]
  exact shellLift_mem_source _ hp

/-- The boundary sphere of the collar lies on the cap. -/
theorem capCollar_zero_mem_range_cap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    capCollar K i (z, 0) ∈ range (K.cap i) := by
  refine ⟨closureSphereToBall ((K.attaching i).symm (ULift.up z)), ?_⟩
  rw [K.boundary_eq, Diffeomorph.apply_symm_apply, capCollar_zero]

/-- The cap together with the collar up to height `s₁` (included). -/
def capRegionClosed (s₁ : ℝ) : Set Q.Carrier :=
  range (K.cap i) ∪ capCollar K i '' {p | 0 ≤ p.2 ∧ p.2 ≤ s₁}

theorem isCompact_capRegionClosed {s₁ : ℝ} (h1 : s₁ < 1) :
    IsCompact (capRegionClosed K i s₁) := by
  refine (isCompact_range (K.cap i).continuous).union ?_
  have hc : IsCompact (univ ×ˢ Icc (0 : ℝ) s₁ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  have he : {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ | 0 ≤ p.2 ∧ p.2 ≤ s₁} =
      univ ×ˢ Icc (0 : ℝ) s₁ := by
    ext p
    simp [Set.mem_prod]
  rw [he]
  exact hc.image_of_continuousOn ((continuousOn_capCollar K i).mono fun p hp =>
    lt_of_le_of_lt hp.2.2 h1)

theorem capRegion_subset_closed (s₁ : ℝ) : capRegion K i s₁ ⊆ capRegionClosed K i s₁ := by
  rintro x (hx | ⟨p, hp, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨p, ⟨hp.1, hp.2.le⟩, rfl⟩

/-- The closure of the cap region adds exactly the collar sphere at height `s₁`. -/
theorem closure_capRegion {s₁ : ℝ} (h0 : 0 < s₁) (h1 : s₁ < 1) :
    closure (capRegion K i s₁) = capRegionClosed K i s₁ := by
  apply le_antisymm
  · exact closure_minimal (capRegion_subset_closed K i s₁)
      (isCompact_capRegionClosed K i h1).isClosed
  · rintro x (hx | ⟨p, hp, rfl⟩)
    · exact subset_closure (Or.inl hx)
    · let s : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
        univ ×ˢ Ico (0 : ℝ) s₁
      have hcl : closure s = univ ×ˢ Icc (0 : ℝ) s₁ := by
        rw [closure_prod_eq, closure_univ, closure_Ico h0.ne]
      have hps : p ∈ closure s := by
        rw [hcl]
        exact ⟨mem_univ _, hp⟩
      have hcont : ContinuousOn (capCollar K i) (closure s) := by
        rw [hcl]
        exact (continuousOn_capCollar K i).mono fun q hq => lt_of_le_of_lt hq.2.2 h1
      have himg := hcont.image_closure (mem_image_of_mem _ hps)
      refine closure_mono ?_ himg
      rintro y ⟨q, hq, rfl⟩
      exact Or.inr ⟨q, hq.2, rfl⟩

/-- The frontier of the cap region is the collar sphere at height `s₁`. -/
theorem frontier_capRegion {s₁ : ℝ} (h0 : 0 < s₁) (h1 : s₁ < 1) :
    frontier (capRegion K i s₁) = capCollar K i '' {p | p.2 = s₁} := by
  rw [frontier, closure_capRegion K i h0 h1, (isOpen_capRegion K i h0 h1.le).interior_eq]
  ext x
  constructor
  · rintro ⟨hx | ⟨p, hp, rfl⟩, hn⟩
    · exact absurd (Or.inl hx) hn
    · rcases hp.2.lt_or_eq with hlt | heq
      · exact absurd (Or.inr ⟨p, ⟨hp.1, hlt⟩, rfl⟩) hn
      · exact ⟨p, heq, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Or.inr ⟨p, ⟨hp ▸ h0.le, hp.le⟩, rfl⟩, ?_⟩
    rintro (⟨y, hy⟩ | ⟨q, hq, he⟩)
    · exact capCollar_notMem_range_cap K i p.1 (hp ▸ h0) (hp ▸ h1)
        ⟨y, by rw [hy]⟩
    · have hpq := capCollar_injOn K i ⟨hq.1, lt_trans hq.2 h1⟩ ⟨hp ▸ h0.le, hp ▸ h1⟩ he
      rw [hpq] at hq
      have h2 := hq.2
      rw [hp] at h2
      exact lt_irrefl s₁ h2

/-- The cap region is preconnected. -/
theorem isPreconnected_capRegion {s₁ : ℝ} (h0 : 0 < s₁) (h1 : s₁ < 1) :
    IsPreconnected (capRegion K i s₁) := by
  have hcap : IsPreconnected (range (K.cap i)) := by
    have := closedCell_three_connectedSpace
    exact isPreconnected_range (K.cap i).continuous
  have hcol : IsPreconnected (capCollar K i '' {p | 0 ≤ p.2 ∧ p.2 < s₁}) := by
    have he : {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ | 0 ≤ p.2 ∧ p.2 < s₁} =
        univ ×ˢ Ico (0 : ℝ) s₁ := by
      ext p
      simp [Set.mem_prod]
    rw [he]
    have hS : PreconnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
      have hc : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
        isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one
      exact isPreconnected_iff_preconnectedSpace.mp hc.isPreconnected
    exact (isPreconnected_univ.prod isPreconnected_Ico).image _
      ((continuousOn_capCollar K i).mono fun q hq => lt_trans hq.2.2 h1)
  refine hcap.union' ?_ hcol
  obtain ⟨z⟩ : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact ⟨capCollar K i (z, 0), capCollar_zero_mem_range_cap K i z,
    ⟨(z, 0), ⟨le_rfl, h0⟩, rfl⟩⟩

end ShellCollar

end GC.GraphManifold.Assembly
