/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshKernel

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

abbrev KuroshActiveVertexIndex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  {a : RawBassSerreOrbitVertex G H //
    treeVertexStabilizer G H a ≠ ⊥}

abbrev KuroshActiveComponentIndex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  KuroshActiveVertexIndex G H ⊕ PUnit

def KuroshActiveComponent {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshActiveComponentIndex G H → Type (max (u + 1) (v + 1)) :=
  Sum.elim
    (fun a => ULift.{max (u + 1) (v + 1)}
      (treeVertexStabilizer G H a.1))
    (fun _ => ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))

instance kuroshActiveComponentGroup {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : KuroshActiveComponentIndex G H) :
    Group (KuroshActiveComponent G H q) := by
  cases q with
  | inl q =>
      change Group (ULift.{max (u + 1) (v + 1)}
        (treeVertexStabilizer G H q.1))
      infer_instance
  | inr q =>
      change Group (ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))
      infer_instance

abbrev KuroshActiveProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  FreeProduct (KuroshActiveComponent G H)

noncomputable def treeVertexComponentToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    TreeKuroshComponent G H (Sum.inl a) →*
      KuroshActiveProduct G H := by
  by_cases htriv : treeVertexStabilizer G H a = ⊥
  · exact
      { toFun := fun _ => 1
        map_one' := by simp
        map_mul' := by intro x y; simp }
  · let j : KuroshActiveVertexIndex G H := ⟨a, htriv⟩
    exact
      { toFun := fun x => Monoid.CoprodI.of
          (show KuroshActiveComponent G H (Sum.inl j) from
            ULift.up x.down)
        map_one' := by
          change Monoid.CoprodI.of
            (show KuroshActiveComponent G H (Sum.inl j) from
              ULift.up (1 : treeVertexStabilizer G H a)) = 1
          exact (Monoid.CoprodI.of :
            KuroshActiveComponent G H (Sum.inl j) →*
              KuroshActiveProduct G H).map_one
        map_mul' := by
          intro x y
          change Monoid.CoprodI.of
              (show KuroshActiveComponent G H (Sum.inl j) from
                ULift.up (x.down * y.down)) =
            Monoid.CoprodI.of
              (show KuroshActiveComponent G H (Sum.inl j) from
                ULift.up x.down) *
              Monoid.CoprodI.of
                (show KuroshActiveComponent G H (Sum.inl j) from
                  ULift.up y.down)
          rw [← (Monoid.CoprodI.of :
            KuroshActiveComponent G H (Sum.inl j) →*
              KuroshActiveProduct G H).map_mul]
          rfl }

noncomputable def activeVertexComponentToTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (j : KuroshActiveVertexIndex G H) :
    KuroshActiveComponent G H (Sum.inl j) →*
      TreeKuroshProduct G H :=
  { toFun := fun x => Monoid.CoprodI.of
      (show TreeKuroshComponent G H (Sum.inl j.1) from ULift.up x.down)
    map_one' := by
      change Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl j.1) from
          ULift.up (1 : treeVertexStabilizer G H j.1)) = 1
      exact (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inl j.1) →*
          TreeKuroshProduct G H).map_one
    map_mul' := by
      intro x y
      change Monoid.CoprodI.of
          (show TreeKuroshComponent G H (Sum.inl j.1) from
            ULift.up (x.down * y.down)) =
        Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inl j.1) from
              ULift.up x.down) *
          Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inl j.1) from
              ULift.up y.down)
      rw [← (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inl j.1) →*
          TreeKuroshProduct G H).map_mul]
      rfl }

noncomputable def treeFreeComponentToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshComponent G H (Sum.inr PUnit.unit) →*
      KuroshActiveProduct G H :=
  { toFun := fun x => Monoid.CoprodI.of
      (show KuroshActiveComponent G H (Sum.inr PUnit.unit) from
        ULift.up x.down)
    map_one' := by
      change Monoid.CoprodI.of
        (show KuroshActiveComponent G H (Sum.inr PUnit.unit) from
          ULift.up (1 : KuroshFreePart G H)) = 1
      exact (Monoid.CoprodI.of :
        KuroshActiveComponent G H (Sum.inr PUnit.unit) →*
          KuroshActiveProduct G H).map_one
    map_mul' := by
      intro x y
      change Monoid.CoprodI.of
          (show KuroshActiveComponent G H (Sum.inr PUnit.unit) from
            ULift.up (x.down * y.down)) =
        Monoid.CoprodI.of
            (show KuroshActiveComponent G H (Sum.inr PUnit.unit) from
              ULift.up x.down) *
          Monoid.CoprodI.of
            (show KuroshActiveComponent G H (Sum.inr PUnit.unit) from
              ULift.up y.down)
      rw [← (Monoid.CoprodI.of :
        KuroshActiveComponent G H (Sum.inr PUnit.unit) →*
          KuroshActiveProduct G H).map_mul]
      rfl }

noncomputable def activeFreeComponentToTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshActiveComponent G H (Sum.inr PUnit.unit) →*
      TreeKuroshProduct G H :=
  { toFun := fun x => Monoid.CoprodI.of
      (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from
        ULift.up x.down)
    map_one' := by
      change Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from
          ULift.up (1 : KuroshFreePart G H)) = 1
      exact (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inr PUnit.unit) →*
          TreeKuroshProduct G H).map_one
    map_mul' := by
      intro x y
      change Monoid.CoprodI.of
          (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from
            ULift.up (x.down * y.down)) =
        Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from
              ULift.up x.down) *
          Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from
              ULift.up y.down)
      rw [← (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inr PUnit.unit) →*
          TreeKuroshProduct G H).map_mul]
      rfl }

noncomputable def treeComponentToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ q : TreeKuroshComponentIndex G H,
      TreeKuroshComponent G H q →* KuroshActiveProduct G H
  | Sum.inl a => treeVertexComponentToActive G H a
  | Sum.inr _ => treeFreeComponentToActive G H

noncomputable def activeComponentToTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ q : KuroshActiveComponentIndex G H,
      KuroshActiveComponent G H q →* TreeKuroshProduct G H
  | Sum.inl j => activeVertexComponentToTree G H j
  | Sum.inr _ => activeFreeComponentToTree G H

noncomputable def treeProductToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshProduct G H →* KuroshActiveProduct G H :=
  Monoid.CoprodI.lift (treeComponentToActive G H)

noncomputable def activeProductToTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshActiveProduct G H →* TreeKuroshProduct G H :=
  Monoid.CoprodI.lift (activeComponentToTree G H)

theorem test_activeProductToTree_comp_treeProductToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (activeProductToTree G H).comp (treeProductToActive G H) =
      MonoidHom.id (TreeKuroshProduct G H) := by
  apply Monoid.CoprodI.ext_hom
  intro q
  apply MonoidHom.ext
  intro x
  cases q with
  | inl a =>
      by_cases htriv : treeVertexStabilizer G H a = ⊥
      · letI : Subsingleton (treeVertexStabilizer G H a) := by
          rw [show treeVertexStabilizer G H a = ⊥ from htriv]
          infer_instance
        have hx : x.down = (1 : treeVertexStabilizer G H a) :=
          Subsingleton.elim _ _
        have hinner : treeVertexComponentToActive G H a x = 1 := by
          simp [treeVertexComponentToActive, htriv]
        change (Monoid.CoprodI.lift (activeComponentToTree G H))
            ((treeVertexComponentToActive G H a) x) =
          Monoid.CoprodI.of x
        rw [hinner]
        have hx' : x = (1 : TreeKuroshComponent G H (Sum.inl a)) := by
          apply ULift.ext
          exact hx
        rw [hx']
        simp
      · let j : KuroshActiveVertexIndex G H := ⟨a, htriv⟩
        have hinner : treeVertexComponentToActive G H a x =
            Monoid.CoprodI.of
              (show KuroshActiveComponent G H (Sum.inl j) from
                ULift.up x.down) := by
          simp [treeVertexComponentToActive, htriv, j]
        change (Monoid.CoprodI.lift (activeComponentToTree G H))
            ((treeVertexComponentToActive G H a) x) =
          Monoid.CoprodI.of x
        rw [hinner, Monoid.CoprodI.lift_of]
        rfl

  | inr q =>
      change (Monoid.CoprodI.lift (activeComponentToTree G H))
          (Monoid.CoprodI.of
            (show KuroshActiveComponent G H (Sum.inr q) from
              ULift.up x.down)) =
        Monoid.CoprodI.of x
      rw [Monoid.CoprodI.lift_of]
      rfl

theorem test_treeProductToActive_comp_activeProductToTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (treeProductToActive G H).comp (activeProductToTree G H) =
      MonoidHom.id (KuroshActiveProduct G H) := by
  apply Monoid.CoprodI.ext_hom
  intro q
  apply MonoidHom.ext
  intro x
  cases q with
  | inl j =>
      have hinner : activeVertexComponentToTree G H j x =
          Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inl j.1) from
              ULift.up x.down) := by
        rfl
      change (Monoid.CoprodI.lift (treeComponentToActive G H))
          ((activeVertexComponentToTree G H j) x) =
        Monoid.CoprodI.of x
      rw [hinner, Monoid.CoprodI.lift_of]
      change treeVertexComponentToActive G H j.1
          (show TreeKuroshComponent G H (Sum.inl j.1) from
            ULift.up x.down) = Monoid.CoprodI.of x
      unfold treeVertexComponentToActive
      rw [dif_neg j.2]
      dsimp
      have hj : (⟨j.1, j.2⟩ : KuroshActiveVertexIndex G H) = j :=
        Subtype.ext rfl
      cases hj
      rfl
  | inr q =>
      change (Monoid.CoprodI.lift (treeComponentToActive G H))
          (Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inr q) from
              ULift.up x.down)) =
        Monoid.CoprodI.of x
      rw [Monoid.CoprodI.lift_of]
      rfl

noncomputable def treeProductActiveEquiv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @TreeKuroshProduct.{u, v, 0} ι G _ H ≃*
      @KuroshActiveProduct.{u, v, 0} ι G _ H :=
  { toFun := treeProductToActive G H
    invFun := activeProductToTree G H
    left_inv := by
      intro x
      exact congrArg (fun f : TreeKuroshProduct G H →* TreeKuroshProduct G H => f x)
        (test_activeProductToTree_comp_treeProductToActive G H)
    right_inv := by
      intro x
      exact congrArg (fun f : KuroshActiveProduct G H →* KuroshActiveProduct G H => f x)
        (test_treeProductToActive_comp_activeProductToTree G H)
    map_mul' := (treeProductToActive G H).map_mul }

/-- The factor-only Kurosh product is isomorphic to the subgroup. -/
noncomputable def kuroshActiveEquivH {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @KuroshActiveProduct.{u, v, 0} ι G _ H ≃* H :=
  (treeProductActiveEquiv G H).symm.trans
    (test_treeKuroshProductMulEquivH G H)

theorem kurosh_active_vertex_intersection {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (j : KuroshActiveVertexIndex G H) :
    ∃ (i : ι) (g : FreeProduct G),
      treeVertexStabilizer G H j.1 = intersectionFactorInH H i g := by
  rcases test_treeVertexStabilizer_central_or_factor G H j.1 with h | h
  · rcases h with ⟨g, _, hbot⟩
    exact (j.2 (hbot.trans rfl)).elim
  · rcases h with ⟨i, g, _, heq⟩
    exact ⟨i, g, heq⟩

end GraphCoveringTheory.Kurosh
