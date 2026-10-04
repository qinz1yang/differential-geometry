import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RelativeCaps
import DifferentialGeometry.Topology.Attachment.BoundaryGluing

/-!
The actual compact Hausdorff quotient attaching one real closed ball to each spherical boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {C : CompactCarrier.{u}}

abbrev SphereCapCut (B : MixedBoundaryCertificate C) :=
  C.Carrier ⊕ (Fin B.sphereCount × ClosedCell 3)

namespace MixedBoundaryCertificate

variable (B : MixedBoundaryCertificate C)

def sphereCapLeft (i : Fin B.sphereCount) : ClosureSphere.{u} → SphereCapCut B :=
  fun z => Sum.inl (B.sphereMap i z)

def sphereCapRight (i : Fin B.sphereCount) : ClosureSphere.{u} → SphereCapCut B :=
  fun z => Sum.inr (i, closureSphereToBall z)

theorem sphereCapLeft_continuous (i : Fin B.sphereCount) : Continuous (B.sphereCapLeft i) :=
  continuous_inl.comp (B.sphereMap i).continuous

theorem sphereCapRight_continuous (i : Fin B.sphereCount) : Continuous (B.sphereCapRight i) := by
  apply continuous_inr.comp
  apply continuous_const.prodMk
  exact (continuous_subtype_val.comp continuous_uliftDown).subtype_mk _

theorem sphereCapLeft_injective (i : Fin B.sphereCount) : Injective (B.sphereCapLeft i) :=
  Sum.inl_injective.comp (B.sphereMap_injective i)

theorem sphereCapRight_injective (i : Fin B.sphereCount) : Injective (B.sphereCapRight i) := by
  intro z w h
  apply ULift.ext
  apply Subtype.ext
  exact congrArg (fun x : Fin B.sphereCount × ClosedCell 3 => x.2.val)
    (Sum.inr_injective h)

private theorem sphereCapLeft_embedding (i : Fin B.sphereCount) :
    Topology.IsEmbedding (B.sphereCapLeft i) :=
  (B.sphereCapLeft_continuous i).isClosedEmbedding (B.sphereCapLeft_injective i) |>.isEmbedding

private theorem sphereCapRight_embedding (i : Fin B.sphereCount) :
    Topology.IsEmbedding (B.sphereCapRight i) :=
  (B.sphereCapRight_continuous i).isClosedEmbedding (B.sphereCapRight_injective i) |>.isEmbedding

def sphereCapGluing : BoundaryGluing (SphereCapCut B) (Fin B.sphereCount) where
  left i := range (B.sphereCapLeft i)
  right i := range (B.sphereCapRight i)
  attaching i := (B.sphereCapLeft_embedding i).toHomeomorph.symm.trans
    (B.sphereCapRight_embedding i).toHomeomorph
  isClosed_left i := (isCompact_range (B.sphereCapLeft_continuous i)).isClosed
  isClosed_right i := (isCompact_range (B.sphereCapRight_continuous i)).isClosed
  disjoint_left_right i := by
    rw [disjoint_left]
    rintro x ⟨z, rfl⟩ ⟨w, hw⟩
    dsimp [sphereCapLeft, sphereCapRight] at hw
    cases hw
  disjoint_blocks i j hij := by
    rw [disjoint_left]
    rintro x (⟨z, rfl⟩ | ⟨z, rfl⟩) (⟨w, hw⟩ | ⟨w, hw⟩)
    · have hz : (z, halfZero) ∈ (B.sphere i).source := by
        rw [B.sphere_source]
        change (0 : ℝ) < 1
        norm_num
      have hw' : (w, halfZero) ∈ (B.sphere j).source := by
        rw [B.sphere_source]
        change (0 : ℝ) < 1
        norm_num
      have he : B.sphere j (w, halfZero) = B.sphere i (z, halfZero) :=
        Sum.inl_injective hw
      exact (B.sphere_disjoint hij).le_bot
        ⟨(B.sphere i).map_source' hz, he ▸ (B.sphere j).map_source' hw'⟩
    · dsimp [sphereCapLeft, sphereCapRight] at hw
      cases hw
    · dsimp [sphereCapLeft, sphereCapRight] at hw
      cases hw
    · exact hij (congrArg Prod.fst (Sum.inr_injective hw)).symm

abbrev SphereCapQuotient := Quotient B.sphereCapGluing.setoid

def sphereCapQuotientMap : C(SphereCapCut B, B.SphereCapQuotient) :=
  ⟨Quotient.mk'', continuous_quotient_mk'⟩

theorem sphereCapQuotientMap_surjective : Surjective B.sphereCapQuotientMap :=
  Quotient.mk''_surjective

theorem sphereCapQuotientMap_eq_iff (x y : SphereCapCut B) :
    B.sphereCapQuotientMap x = B.sphereCapQuotientMap y ↔ B.sphereCapGluing.rel x y :=
  Quotient.eq'

instance sphereCapQuotientCompact : CompactSpace B.SphereCapQuotient := inferInstance

instance sphereCapQuotientHausdorff : T2Space B.SphereCapQuotient := inferInstance

theorem sphereCapGluing_attaching (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    (B.sphereCapGluing.attaching i
      ⟨B.sphereCapLeft i z, mem_range_self z⟩).val = B.sphereCapRight i z := by
  change ((B.sphereCapRight_embedding i).toHomeomorph
    ((B.sphereCapLeft_embedding i).toHomeomorph.symm
      ((B.sphereCapLeft_embedding i).toHomeomorph z))).val = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem sphereCapGluing_symm_attaching (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    ((B.sphereCapGluing.attaching i).symm
      ⟨B.sphereCapRight i z, mem_range_self z⟩).val = B.sphereCapLeft i z := by
  change ((B.sphereCapLeft_embedding i).toHomeomorph
    ((B.sphereCapRight_embedding i).toHomeomorph.symm
      ((B.sphereCapRight_embedding i).toHomeomorph z))).val = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem sphereCapGluing_rel_iff (x y : SphereCapCut B) :
    B.sphereCapGluing.rel x y ↔ x = y ∨ ∃ i z,
      (x = B.sphereCapLeft i z ∧ y = B.sphereCapRight i z) ∨
      (x = B.sphereCapRight i z ∧ y = B.sphereCapLeft i z) := by
  constructor
  · rintro (h | ⟨i, hx, hy⟩)
    · exact Or.inl h
    · rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rw [B.sphereCapGluing.flip_of_mem_left (mem_range_self z),
          B.sphereCapGluing_attaching] at hy
        exact Or.inr ⟨i, z, Or.inl ⟨rfl, hy⟩⟩
      · rw [B.sphereCapGluing.flip_of_mem_right (mem_range_self z),
          B.sphereCapGluing_symm_attaching] at hy
        exact Or.inr ⟨i, z, Or.inr ⟨rfl, hy⟩⟩
  · rintro (h | ⟨i, z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl h
    · have h := B.sphereCapGluing.rel_of_mem_left (i := i)
        (x := B.sphereCapLeft i z) (mem_range_self z)
      rw [B.sphereCapGluing_attaching] at h
      exact h
    · have h := B.sphereCapGluing.rel_of_mem_right (i := i)
        (x := B.sphereCapRight i z) (mem_range_self z)
      rw [B.sphereCapGluing_symm_attaching] at h
      exact h

def sphereCapCore : C(C.Carrier, B.SphereCapQuotient) :=
  B.sphereCapQuotientMap.comp ⟨Sum.inl, continuous_inl⟩

def sphereCapBall (i : Fin B.sphereCount) : C(ClosedCell 3, B.SphereCapQuotient) :=
  B.sphereCapQuotientMap.comp
    ⟨fun z => Sum.inr (i, z), continuous_inr.comp (continuous_const.prodMk continuous_id)⟩

theorem sphereCap_attachment (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereCapCore (B.sphereMap i z) = B.sphereCapBall i (closureSphereToBall z) := by
  apply Quotient.sound
  have h := B.sphereCapGluing.rel_of_mem_left (i := i)
    (x := B.sphereCapLeft i z) (mem_range_self z)
  rw [B.sphereCapGluing_attaching i z] at h
  exact h

theorem sphereCapCore_injective : Injective B.sphereCapCore := by
  intro x y h
  have hr := (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact h)
  rcases hr with he | ⟨i, z, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · exact Sum.inl_injective he
  · dsimp [sphereCapRight] at hy
    cases hy
  · dsimp [sphereCapRight] at hx
    cases hx

theorem sphereCapBall_injective (i : Fin B.sphereCount) : Injective (B.sphereCapBall i) := by
  intro x y h
  have hr := (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact h)
  rcases hr with he | ⟨j, z, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · exact congrArg Prod.snd (Sum.inr_injective he)
  · dsimp [sphereCapLeft] at hx
    cases hx
  · dsimp [sphereCapLeft] at hy
    cases hy

theorem sphereCapCore_embedding : Topology.IsClosedEmbedding B.sphereCapCore :=
  B.sphereCapCore.continuous.isClosedEmbedding B.sphereCapCore_injective

theorem sphereCapBall_embedding (i : Fin B.sphereCount) :
    Topology.IsClosedEmbedding (B.sphereCapBall i) :=
  (B.sphereCapBall i).continuous.isClosedEmbedding (B.sphereCapBall_injective i)

theorem sphereCapBall_disjoint :
    Pairwise fun i j => Disjoint (range (B.sphereCapBall i)) (range (B.sphereCapBall j)) := by
  intro i j hij
  rw [disjoint_left]
  rintro q ⟨x, hx⟩ ⟨y, hy⟩
  have hr := (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact (hx.trans hy.symm))
  rcases hr with he | ⟨a, z, ⟨hx', hy'⟩ | ⟨hx', hy'⟩⟩
  · exact hij (congrArg Prod.fst (Sum.inr_injective he))
  · dsimp [sphereCapLeft] at hx'
    cases hx'
  · dsimp [sphereCapLeft] at hy'
    cases hy'

theorem sphereCapCore_ball_intersection (i : Fin B.sphereCount) :
    range B.sphereCapCore ∩ range (B.sphereCapBall i) =
      range fun z => B.sphereCapCore (B.sphereMap i z) := by
  ext q
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hr := (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact (hx.trans hy.symm))
    rcases hr with he | ⟨j, z, ⟨hx', hy'⟩ | ⟨hx', hy'⟩⟩
    · cases he
    · have hij : i = j := congrArg Prod.fst (Sum.inr_injective hy')
      subst j
      refine ⟨z, ?_⟩
      change B.sphereCapCore (B.sphereMap i z) = q
      rw [← Sum.inl_injective hx']
      exact hx
    · dsimp [sphereCapRight] at hx'
      cases hx'
  · rintro ⟨z, rfl⟩
    exact ⟨⟨B.sphereMap i z, rfl⟩,
      ⟨closureSphereToBall z, (B.sphereCap_attachment i z).symm⟩⟩

theorem sphereCap_covers : range B.sphereCapCore ∪ (⋃ i, range (B.sphereCapBall i)) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨x, rfl⟩ := B.sphereCapQuotientMap_surjective q
  cases x with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr x => exact Or.inr (mem_iUnion.mpr ⟨x.1, x.2, rfl⟩)

theorem sphereCapQuotientMap_isClosedMap : IsClosedMap B.sphereCapQuotientMap :=
  isClosedMap_quotient_mk_of_isClosed_rel B.sphereCapGluing.isClosed_setOf_rel

instance sphereCapQuotientSecondCountable :
    SecondCountableTopology B.SphereCapQuotient := by
  classical
  let basis := countableBasis (SphereCapCut B)
  let U : Finset basis → Set (SphereCapCut B) := fun b => ⋃ s ∈ b, (s : Set (SphereCapCut B))
  let V : Finset basis → Set B.SphereCapQuotient := fun b => (B.sphereCapQuotientMap '' (U b)ᶜ)ᶜ
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    exact isOpen_biUnion fun s => Function.const (s ∈ b)
      (isOpen_of_mem_countableBasis s.property)
  have hV : ∀ b, IsOpen (V b) := fun b =>
    (B.sphereCapQuotientMap_isClosedMap (U b)ᶜ (hU b).isClosed_compl).isOpen_compl
  have hcount : (range V).Countable := Set.countable_range V
  apply (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hcount
  · rintro A ⟨b, rfl⟩
    exact hV b
  · intro q A hq hA
    let K : Set (SphereCapCut B) := B.sphereCapQuotientMap ⁻¹' {q}
    have hK : IsCompact K :=
      (isClosed_singleton.preimage B.sphereCapQuotientMap.continuous).isCompact
    have hx : ∀ x : K, ∃ b : basis, x.val ∈ b.val ∧ b.val ⊆ B.sphereCapQuotientMap ⁻¹' A := by
      intro x
      have hpx : B.sphereCapQuotientMap x.val = q := x.property
      obtain ⟨b, hb, hxb, hbA⟩ := (isBasis_countableBasis (SphereCapCut B)).isOpen_iff.mp
        (hA.preimage B.sphereCapQuotientMap.continuous) x.val (by
          change B.sphereCapQuotientMap x.val ∈ A
          rw [hpx]
          exact hq)
      exact ⟨⟨b, hb⟩, hxb, hbA⟩
    let b : K → basis := fun x => (hx x).choose
    have hb : ∀ x : K, x.val ∈ (b x).val ∧ (b x).val ⊆ B.sphereCapQuotientMap ⁻¹' A :=
      fun x => (hx x).choose_spec
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (b x).val)
      (fun x => isOpen_of_mem_countableBasis (b x).property) (by
        intro x hxK
        exact mem_iUnion.mpr ⟨⟨x, hxK⟩, (hb ⟨x, hxK⟩).1⟩)
    let t : Finset basis := s.image b
    have hKU : K ⊆ U t := by
      intro x hxK
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hxK)
      exact mem_iUnion₂.mpr ⟨b y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩
    have hUA : U t ⊆ B.sphereCapQuotientMap ⁻¹' A := by
      intro x hxU
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxU
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
      rw [← hyz] at hxz
      exact (hb y).2 hxz
    refine ⟨V t, mem_range_self t, ?_, ?_⟩
    · rintro ⟨x, hx, hxq⟩
      exact hx (hKU hxq)
    · intro y hy
      obtain ⟨x, rfl⟩ := B.sphereCapQuotientMap_surjective y
      apply hUA
      by_contra hx
      exact hy ⟨x, hx, rfl⟩

end MixedBoundaryCertificate

end GC.GraphManifold
