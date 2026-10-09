import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteCoprodSupport
import DifferentialGeometry.External.GraphCoveringTheory.KuroshTheorem
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace GC.Group
open GraphCoveringTheory.Kurosh

theorem kurosh_equiv_vertex (ι : Type v) (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (a : RawBassSerreOrbitVertex G H)
    (x : treeVertexStabilizer G H a) :
    kuroshBassSerreEquiv G H (treeKuroshVertexInclusion G H a x) = x :=
  treeKuroshProductToH_vertex.{u,v,0} G H a x

theorem finite_subgroup_le_conjugate_factor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) [Finite H] [Nontrivial H] :
    ∃ (i : ι) (g : FreeProduct G),
      H ≤ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g := by
  let e := kuroshBassSerreEquiv G H
  let : Finite (TreeKuroshProduct G H) := Finite.of_equiv H e.symm.toEquiv
  let : Nontrivial (TreeKuroshProduct G H) := e.symm.injective.nontrivial
  obtain ⟨q, hq, hsurj⟩ := finite_coprodI_exists_surjective_factor (TreeKuroshComponent G H)
  have honto : Function.Surjective (treeKuroshComponentHom G H q) := by
    intro x
    obtain ⟨z, hz⟩ := e.surjective x
    obtain ⟨a, ha⟩ := hsurj z
    refine ⟨a, ?_⟩
    have hh : e (Monoid.CoprodI.of a) = treeKuroshComponentHom G H q a :=
      Monoid.CoprodI.lift_of _ _
    rw [← hh, ha, hz]
  cases q with
  | inr q =>
      let inj : KuroshFreePart G H → TreeKuroshProduct G H :=
        fun x => Monoid.CoprodI.of (show TreeKuroshComponent G H (Sum.inr q) from ULift.up x)
      have hinj : Function.Injective inj :=
        (Monoid.CoprodI.of_injective (Sum.inr q)).comp ULift.up_injective
      let : Finite (KuroshFreePart G H) := Finite.of_injective inj hinj
      let := finite_isFreeGroup_subsingleton (KuroshFreePart G H)
      let : Subsingleton (TreeKuroshComponent G H (Sum.inr q)) :=
        inferInstanceAs (Subsingleton (ULift (KuroshFreePart G H)))
      let := hq
      exact (not_subsingleton (TreeKuroshComponent G H (Sum.inr q))).elim inferInstance
  | inl a =>
      have htop : treeVertexStabilizer G H a = ⊤ := by
        apply top_unique
        intro x _
        obtain ⟨z, hz⟩ := honto x
        change z.down.val = x at hz
        exact hz ▸ z.down.property
      rcases kurosh_vertex_stabilizer_classification G H a with h | h
      · obtain ⟨g, _, hbot⟩ := h
        have hbad : (⊥ : Subgroup H) = ⊤ := hbot.symm.trans htop
        exact (bot_ne_top hbad).elim
      · obtain ⟨i, g, _, heq⟩ := h
        refine ⟨i, g, ?_⟩
        intro x hx
        have hi : (⟨x,hx⟩ : H) ∈ intersectionFactorInH H i g := by
          rw [← heq, htop]; trivial
        exact hi.2

theorem finite_subgroup_bot_or_le_conjugate_factor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) [Finite H] :
    H = ⊥ ∨ ∃ (i : ι) (g : FreeProduct G),
      H ≤ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g := by
  classical
  rcases subsingleton_or_nontrivial H with hs | hn
  · let := hs
    left
    apply (Subgroup.eq_bot_iff_forall H).mpr
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : H) 1)
  · let := hn
    exact Or.inr (finite_subgroup_le_conjugate_factor G H)

theorem embedding_of_le_conjugate_factor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G)
    (h : H ≤ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g) :
    ∃ f : H →* G i, Function.Injective f ∧
      ∀ x : H, factorInclusion G i (f x) = g⁻¹ * x.val * g := by
  let c : H →* FreeProduct G := (MulAut.conj g⁻¹).toMonoidHom.comp H.subtype
  have hc (x : H) : c x ∈ MonoidHom.range (factorInclusion G i) := by
    simpa [c, MulAut.conj_apply] using
      (mem_conjugateSubgroup_iff _ g x.val).mp (h x.property)
  let cr := c.codRestrict (MonoidHom.range (factorInclusion G i)) hc
  let e := MonoidHom.ofInjective (factorInclusion_injective G i)
  let f : H →* G i := e.symm.toMonoidHom.comp cr
  have hmap (x : H) : factorInclusion G i (f x) = g⁻¹ * x.val * g := by
    have he := congrArg Subtype.val (e.apply_symm_apply (cr x))
    simpa [f, e, cr, c, MulAut.conj_apply] using he
  refine ⟨f, ?_, hmap⟩
  intro x y hxy
  apply Subtype.ext
  have he := (hmap x).symm.trans ((congrArg (factorInclusion G i) hxy).trans (hmap y))
  exact mul_left_cancel (mul_right_cancel he)

theorem finite_subgroup_order_bound_of_finite_factors {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (N : ℕ) (hN : 1 ≤ N) (hcard : ∀ i, Nat.card (G i) ≤ N)
    (H : Subgroup (FreeProduct G)) [Finite H] : Nat.card H ≤ N := by
  rcases finite_subgroup_bot_or_le_conjugate_factor G H with h | ⟨i, g, h⟩
  · subst H
    simpa using hN
  · obtain ⟨f, hf, _⟩ := embedding_of_le_conjugate_factor G H i g h
    exact (Nat.card_le_card_of_injective f hf).trans (hcard i)

end GC.Group
