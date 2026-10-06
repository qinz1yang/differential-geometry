import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Covering.Quotient
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X]

/-- All ordered distinct equal-image pairs of the supplied map. No bound on
the number of preimages of a target point is imposed. -/
def orderedCollisionPairs (f : X → Y) : Set (X × X) :=
  {z | z.1 ≠ z.2 ∧ f z.1 = f z.2}

/-- Local injectivity prevents the actual collision relation from accumulating
on the diagonal. Compactness concerns the full relation of the supplied map. -/
theorem isCompact_orderedCollisionPairs [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hloc : IsLocallyInjective f) :
    IsCompact (orderedCollisionPairs f) := by
  have hclosed : IsClosed (orderedCollisionPairs f) := by
    apply isOpen_compl_iff.mp
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, y⟩ hxy
    by_cases hqxy : f x = f y
    · have heq : x = y := by
        by_contra hne
        exact hxy ⟨hne, hqxy⟩
      subst y
      obtain ⟨U, hU, hxU, hinj⟩ := hloc x
      apply Filter.mem_of_superset ((hU.prod hU).mem_nhds ⟨hxU, hxU⟩)
      intro z hz hbad
      exact hbad.1 (hinj hz.1 hz.2 hbad.2)
    · apply Filter.mem_of_superset
        ((isClosed_eq (hf.comp continuous_fst)
          (hf.comp continuous_snd)).isOpen_compl.mem_nhds hqxy)
      intro z hz hbad
      exact hz hbad.2
  exact hclosed.isCompact

/-- The first canonical projection retains the original source point. -/
def collisionFirst (f : X → Y) : C(orderedCollisionPairs f, X) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The second canonical projection retains the other original source point. -/
def collisionSecond (f : X → Y) : C(orderedCollisionPairs f, X) :=
  ⟨fun z => z.1.2, continuous_snd.comp continuous_subtype_val⟩

theorem collision_projections_same_map (f : X → Y) :
    f ∘ collisionFirst f = f ∘ collisionSecond f := by
  ext z
  exact z.property.2

/-- The canonical coordinate swap on actual ordered collisions. -/
def collisionSwap (f : X → Y) :
    orderedCollisionPairs f ≃ₜ orderedCollisionPairs f where
  toFun z := ⟨(z.1.2, z.1.1), fun h => z.property.1 h.symm, z.property.2.symm⟩
  invFun z := ⟨(z.1.2, z.1.1), fun h => z.property.1 h.symm, z.property.2.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _

@[simp] theorem collisionSwap_involutive (f : X → Y)
    (z : orderedCollisionPairs f) : collisionSwap f (collisionSwap f z) = z :=
  Subtype.ext rfl

theorem collisionSwap_fixed_point_free (f : X → Y)
    (z : orderedCollisionPairs f) : collisionSwap f z ≠ z := by
  intro h
  exact z.property.1
    (congrArg (fun w : orderedCollisionPairs f => w.1.1) h).symm

@[simp] theorem collisionFirst_swap (f : X → Y)
    (z : orderedCollisionPairs f) :
    collisionFirst f (collisionSwap f z) = collisionSecond f z := rfl

@[simp] theorem collisionSecond_swap (f : X → Y)
    (z : orderedCollisionPairs f) :
    collisionSecond f (collisionSwap f z) = collisionFirst f z := rfl

private def collisionSwapGroup (f : X → Y) :
    Subgroup (Equiv.Perm (orderedCollisionPairs f)) where
  carrier := {g | g = 1 ∨ g = (collisionSwap f).toEquiv}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · left
      exact Equiv.ext (fun z => collisionSwap_involutive f z)
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · right
      exact Equiv.ext (fun _ => rfl)

private instance collisionSwapGroup_smul (f : X → Y) :
    SMul (collisionSwapGroup f) (orderedCollisionPairs f) where
  smul g z := g.1 z

private instance collisionSwapGroup_mulAction (f : X → Y) :
    MulAction (collisionSwapGroup f) (orderedCollisionPairs f) := inferInstance

private instance collisionSwapGroup_continuous (f : X → Y) :
    ContinuousConstSMul (collisionSwapGroup f) (orderedCollisionPairs f) where
  continuous_const_smul g := by
    change Continuous (g.1 : orderedCollisionPairs f → orderedCollisionPairs f)
    rcases g.property with h | h
    · rw [h]
      exact continuous_id
    · rw [h]
      exact (collisionSwap f).continuous

/-- The standard unordered-pair relation restricted to actual collisions. -/
def collisionPairSetoid (f : X → Y) : Setoid (orderedCollisionPairs f) :=
  Setoid.comap (fun z : orderedCollisionPairs f => (z : X × X)) (Sym2.Rel.setoid X)

/-- Unordered actual collision pairs, with the quotient topology for the
restriction of `Sym2.Rel.setoid`. The public type contains no private action. -/
abbrev UnorderedCollisionPairs (f : X → Y) := Quotient (collisionPairSetoid f)

def collisionPairQuotient (f : X → Y) :
    orderedCollisionPairs f → UnorderedCollisionPairs f := Quotient.mk''

theorem collisionPairQuotient_eq_iff (f : X → Y)
    (x y : orderedCollisionPairs f) :
    collisionPairQuotient f x = collisionPairQuotient f y ↔
      x = y ∨ x = collisionSwap f y := by
  constructor
  · intro h
    have hr : Sym2.Rel X x.val y.val := Quotient.exact h
    rcases Sym2.rel_iff'.mp hr with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · rfl
    · apply Quotient.sound
      change Sym2.Rel X y.val.swap y.val
      exact Sym2.rel_iff'.mpr (Or.inr rfl)

private theorem collisionSwapGroup_orbit_iff (f : X → Y)
    (x y : orderedCollisionPairs f) :
    x ∈ MulAction.orbit (collisionSwapGroup f) y ↔
      x = y ∨ x = collisionSwap f y := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases g.property with h | h
    · left
      change g.1 y = y
      rw [h]
      rfl
    · right
      change g.1 y = collisionSwap f y
      rw [h]
      rfl
  · rintro (rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · exact ⟨⟨(collisionSwap f).toEquiv, Or.inr rfl⟩, rfl⟩

/-- The actual ordering quotient is a covering map. Hausdorff separation of
source points suffices: this does not require continuity or local injectivity
of `f`, and it is not a covering of the image of `f`. -/
theorem collisionPairQuotient_isCoveringMap [T2Space X] (f : X → Y) :
    IsCoveringMap (collisionPairQuotient f) := by
  have hcover : IsQuotientCoveringMap (collisionPairQuotient f)
      (collisionSwapGroup f) :=
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_smul := fun g => continuous_const_smul g
      apply_eq_iff_mem_orbit := fun {x y} =>
        (collisionPairQuotient_eq_iff f x y).trans (collisionSwapGroup_orbit_iff f x y).symm
      disjoint := by
        intro z
        obtain ⟨A, B, hA, hB, hzA, hswapB, hAB⟩ :=
          t2_separation (Ne.symm (collisionSwap_fixed_point_free f z))
        refine ⟨A ∩ (collisionSwap f) ⁻¹' B,
          (hA.inter (hB.preimage (collisionSwap f).continuous)).mem_nhds
            ⟨hzA, hswapB⟩, ?_⟩
        intro g hg
        rcases g.property with h | h
        · exact Subtype.ext h
        · exfalso
          obtain ⟨v, ⟨u, hu, hgu⟩, hv⟩ := hg
          have hswap : collisionSwap f u = v := by
            change g.1 u = v at hgu
            rw [h] at hgu
            exact hgu
          exact Set.disjoint_left.mp hAB hv.1 (hswap ▸ hu.2) }
  exact hcover.isCoveringMap

theorem collisionPairQuotient_fiber_eq (f : X → Y)
    (z : orderedCollisionPairs f) :
    (collisionPairQuotient f) ⁻¹' {collisionPairQuotient f z} = {z, collisionSwap f z} := by
  ext w
  exact collisionPairQuotient_eq_iff f w z

/-- Two sheets refer to the ordering of each pair, and impose no bound on
the number of preimages of any value of the original map. -/
theorem collisionPairQuotient_fiber_encard (f : X → Y)
    (z : UnorderedCollisionPairs f) :
    ((collisionPairQuotient f) ⁻¹' {z}).encard = 2 := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
  change ((collisionPairQuotient f) ⁻¹' {collisionPairQuotient f x}).encard = 2
  rw [collisionPairQuotient_fiber_eq]
  exact Set.encard_pair (Ne.symm (collisionSwap_fixed_point_free f x))

end DifferentialGeometry.Topology
