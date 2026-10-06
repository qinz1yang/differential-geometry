import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MultiSeamInjective

/-!
# CP1-C: π₁-injectivity of inclusions across collared gluing steps (core)

General-loop versions of `InjInto.union_of_amalgam` / `InjInto.union_of_hnn`
(`MultiSeamInjective.lean`): the conclusion is injectivity of the *inclusion* of a piece into the
union on `π₁` at every basepoint (`IncInj_CPC`), not just for torus maps.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.LongTime.CuspP1
open GC.Seifert

section Basic
variable {M : Type u} [TopologicalSpace M]

/-- `π₁`-injectivity of the inclusion `S ⊆ S'` at every basepoint of `S`. -/
def IncInj_CPC {S S' : Set M} (h : S ⊆ S') : Prop :=
  ∀ x : S, Function.Injective (FundamentalGroup.map (inclusionMap h) x)

theorem inclusionMap_comp_CPC {S S' S'' : Set M} (h1 : S ⊆ S') (h2 : S' ⊆ S'') :
    inclusionMap (h1.trans h2) = (inclusionMap h2).comp (inclusionMap h1) := rfl

theorem injective_inclusion_trans_CPC {S S' S'' : Set M} (h1 : S ⊆ S') (h2 : S' ⊆ S'') (x : S)
    (hf : Function.Injective (FundamentalGroup.map (inclusionMap h1) x))
    (hg : Function.Injective (FundamentalGroup.map (inclusionMap h2) (inclusionMap h1 x))) :
    Function.Injective (FundamentalGroup.map (inclusionMap (h1.trans h2)) x) := by
  rw [inclusionMap_comp_CPC h1 h2, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact hg.comp hf

theorem injective_inclusion_self_CPC {S : Set M} (h : S ⊆ S) (x : S) :
    Function.Injective (FundamentalGroup.map (inclusionMap h) x) :=
  injective_fundamentalGroup_map_of_leftInverse (inclusionMap h) (inclusionMap h)
    (fun _ => rfl) x

theorem injective_inner_inclusion_CPC {S S' S'' : Set M} (h1 : S ⊆ S') (h2 : S' ⊆ S'') (x : S)
    (hf : Function.Injective (FundamentalGroup.map (inclusionMap (h1.trans h2)) x)) :
    Function.Injective (FundamentalGroup.map (inclusionMap h1) x) := by
  rw [inclusionMap_comp_CPC h1 h2] at hf
  exact GC.Topology.injective_inner_of_composite _ _ x hf

/-- Transport of `π₁`-injectivity along two homeomorphisms intertwining `f` and `g`. -/
theorem injective_iff_homeo2_CPC {Y Y' Z Z' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    [TopologicalSpace Z] [TopologicalSpace Z'] (e : Y ≃ₜ Y') (e' : Z ≃ₜ Z') (f : C(Y, Z))
    (g : C(Y', Z')) (hfg : ∀ y, e' (f y) = g (e y)) (y : Y) :
    Function.Injective (FundamentalGroup.map f y) ↔
      Function.Injective (FundamentalGroup.map g (e y)) := by
  have h1 : (e' : C(Z, Z')).comp f = g.comp (e : C(Y, Y')) :=
    ContinuousMap.ext fun s => hfg s
  have he' : Function.Injective (FundamentalGroup.map (e' : C(Z, Z')) (f y)) :=
    injective_fundamentalGroup_map_of_leftInverse (e' : C(Z, Z')) (e'.symm : C(Z', Z))
      e'.symm_apply_apply (f y)
  have hbe : Function.Surjective (FundamentalGroup.map (e : C(Y, Y')) y) :=
    (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv
      (e : C(Y, Y')) e.symm_apply_apply y).2
  have hA : Function.Injective (FundamentalGroup.map f y) ↔
      Function.Injective (FundamentalGroup.map ((e' : C(Z, Z')).comp f) y) := by
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact ⟨fun hf => he'.comp hf, fun hc => hc.of_comp⟩
  have hB : Function.Injective (FundamentalGroup.map (g.comp (e : C(Y, Y'))) y) ↔
      Function.Injective (FundamentalGroup.map g (e y)) := by
    constructor
    · intro hc
      exact injective_fundamentalGroup_map_of_comp (e : C(Y, Y')) g y hbe hc
    · intro hg
      rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
      exact hg.comp (injective_fundamentalGroup_map_of_leftInverse (e : C(Y, Y'))
        (e.symm : C(Y', Y)) e.symm_apply_apply y)
  rw [hA, h1]
  exact hB

end Basic

end GC.LongTime.CuspP1
