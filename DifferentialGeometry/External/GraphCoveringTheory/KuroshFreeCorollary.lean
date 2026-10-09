/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreePart

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

noncomputable def testRawTreePath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (x : RawBassSerreVertex G) :
    @Quiver.Path (RawBassSerreVertex G) (testRawTreeQuiver G)
      (RawBassSerreVertex.central 1) x := by
  letI : @Quiver.Arborescence (RawBassSerreVertex G) (testRawTreeQuiver G) :=
    testRawTreeQuiverArborescence G
  letI : Unique (@Quiver.Path (RawBassSerreVertex G) (testRawTreeQuiver G)
      (RawBassSerreVertex.central 1) x) :=
    @Quiver.Arborescence.uniquePath (RawBassSerreVertex G)
      (testRawTreeQuiver G) (testRawTreeQuiverArborescence G) x
  exact default

theorem kurosh_treeDataGenerated_eq_top_for_free_corollary {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    testTreeDataGenerated G H = ⊤ := by
  apply le_antisymm le_top
  intro h _
  let p := testRawTreePath G
    (h.1 • RawBassSerreVertex.central (G := G) 1)
  let a := testRawPathAlignmentGenerated G H p
  have horbit :
      actionOrbitMk H (RawBassSerreVertex G)
          (h.1 • RawBassSerreVertex.central (G := G) 1) =
        rawBassSerreOrbitRoot G H := by
    change actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1) =
      actionOrbitMk H (RawBassSerreVertex G)
        (RawBassSerreVertex.central (G := G) 1)
    exact actionOrbitMk_smul H (RawBassSerreVertex G) h
      (RawBassSerreVertex.central (G := G) 1)
  have hrep : rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1)) =
      RawBassSerreVertex.central (G := G) 1 := by
    rw [horbit]
    exact test_rawTreeRepresentative_root G H
  have hpath : h.1 • RawBassSerreVertex.central (G := G) 1 =
      a.1 • RawBassSerreVertex.central (G := G) 1 := by
    calc
      h.1 • RawBassSerreVertex.central (G := G) 1 = a.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G)
              (h.1 • RawBassSerreVertex.central (G := G) 1)) := a.2.1
      _ = a.1 • RawBassSerreVertex.central (G := G) 1 :=
        congrArg (fun z => (a.1 : FreeProduct G) • z) hrep
  have hval : h.1 = a.1 := by
    change RawBassSerreVertex.central (G := G) ((h.1 : FreeProduct G) * 1) =
      RawBassSerreVertex.central (G := G) ((a.1 : FreeProduct G) * 1) at hpath
    injection hpath with hmul
    simpa only [mul_one] using hmul
  have heq : h = a.1 := Subtype.ext hval
  exact heq ▸ a.2.2

theorem kurosh_treeKuroshProductToH_surjective_for_free_corollary
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) :
    Function.Surjective (treeKuroshProductToH G H) := by
  have hgen : testTreeDataGenerated G H ≤
      MonoidHom.range (treeKuroshProductToH G H) := by
    change Subgroup.closure (testTreeDataGeneratorSet G H) ≤
      MonoidHom.range (treeKuroshProductToH G H)
    rw [Subgroup.closure_le]
    intro h hh
    rcases hh with ⟨a, ha⟩ | ⟨e, he⟩
    · refine ⟨treeKuroshVertexInclusion G H a ⟨h, ha⟩, ?_⟩
      exact treeKuroshProductToH_vertex G H a ⟨h, ha⟩
    · have hlabel : quotientEdgeLabel G H e.2.2 ∈
          MonoidHom.range (treeKuroshProductToH G H) := by
        refine ⟨treeKuroshFreeInclusion G H
          (quotientEdgeLoop G H e.2.2), ?_⟩
        rw [treeKuroshProductToH_free,
          kuroshFreePartHom_quotientEdgeLoop]
      exact he ▸ hlabel
  have hrange_top : MonoidHom.range (treeKuroshProductToH G H) = ⊤ := by
    apply le_antisymm le_top
    intro h _
    apply hgen
    rw [kurosh_treeDataGenerated_eq_top_for_free_corollary G H]
    trivial
  intro h
  have hrange : h ∈ MonoidHom.range (treeKuroshProductToH G H) := by
    rw [hrange_top]
    trivial
  exact hrange

noncomputable def treeKuroshComponentToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : TreeKuroshComponentIndex G H) :
    TreeKuroshComponent G H q →* KuroshFreePart G H := by
  cases q with
  | inl a =>
      change ULift.{max (u + 1) (v + 1)}
          (treeVertexStabilizer G H a) →* KuroshFreePart G H
      exact
        { toFun := fun _ => 1
          map_one' := by rfl
          map_mul' := by intro x y; simp }
  | inr q =>
      change ULift.{max (u + 1) (v + 1)}
          (KuroshFreePart G H) →* KuroshFreePart G H
      exact
        { toFun := fun x => x.down
          map_one' := by rfl
          map_mul' := by intro x y; rfl }

noncomputable def treeKuroshProductToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshProduct G H →* KuroshFreePart G H := by
  change FreeProduct (TreeKuroshComponent G H) →* KuroshFreePart G H
  exact Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H)

theorem treeKuroshProductToFreePart_vertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (x : treeVertexStabilizer G H a) :
    treeKuroshProductToFreePart G H
      (treeKuroshVertexInclusion G H a x) = 1 := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  rw [Monoid.CoprodI.lift_of]
  rfl

@[simp] theorem treeKuroshProductToFreePart_free {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    treeKuroshProductToFreePart G H
      (treeKuroshFreeInclusion G H x) = x := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  rw [Monoid.CoprodI.lift_of]
  rfl

theorem treeKuroshProductToH_factor_through_freePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    treeKuroshProductToH G H =
      (kuroshFreePartHom G H).comp (treeKuroshProductToFreePart G H) := by
  apply Monoid.CoprodI.ext_hom
  intro q
  cases q with
  | inl a =>
      apply MonoidHom.ext
      intro x
      have hx : x.down = (1 : treeVertexStabilizer G H a) := by
        letI := htriv a
        exact Subsingleton.elim _ _
      change treeKuroshComponentHom G H (Sum.inl a) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      change x.down.1 =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      rw [Monoid.CoprodI.lift_of]
      change x.down.1 = 1
      exact congrArg Subtype.val hx
  | inr q =>
      apply MonoidHom.ext
      intro x
      change treeKuroshComponentHom G H (Sum.inr q) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      change kuroshFreePartHom G H x.down =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      rw [Monoid.CoprodI.lift_of]
      rfl

theorem kuroshFreePartHom_surjective_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    Function.Surjective (kuroshFreePartHom G H) := by
  intro h
  obtain ⟨p, hp⟩ :=
    @kurosh_treeKuroshProductToH_surjective_for_free_corollary.{u, v, 0}
      ι G _ H h
  refine ⟨treeKuroshProductToFreePart G H p, ?_⟩
  have hfactor := congrArg
    (fun f : @TreeKuroshProduct.{u, v, 0} ι G _ H →* H => f p)
    (@treeKuroshProductToH_factor_through_freePart.{u, v, 0}
      ι G _ H htriv)
  simpa using hfactor.symm.trans hp

noncomputable def kuroshFreePartEquivOfTrivialStabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    KuroshFreePart G H ≃* H :=
  MulEquiv.ofBijective (kuroshFreePartHom G H)
    ⟨testKuroshFreePartHom_injective G H,
      kuroshFreePartHom_surjective_of_trivial_stabilizers G H htriv⟩

theorem kurosh_subgroup_is_free_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    IsFreeGroup H := by
  exact IsFreeGroup.ofMulEquiv
    (kuroshFreePartEquivOfTrivialStabilizers G H htriv)

end GraphCoveringTheory.Kurosh
