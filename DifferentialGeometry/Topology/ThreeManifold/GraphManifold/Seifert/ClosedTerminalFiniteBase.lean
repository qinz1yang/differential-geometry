import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFinitePantsRelations

/-!
# Native boundary generators of an actual planar pants base

The original planar embedding gives a genuine homeomorphism onto the compact pants.
Its inverse transports the canonical native boundary paths, fundamental group generators
and their same-sign relation, preserving every original boundary map of the base.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

namespace PlanarBase

def closedPantsHomeomorph (P : PlanarBase.{u} 3) : P.surface.Carrier ≃ₜ ClosedPants :=
  P.isSmoothEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr P.range_embedding)

theorem closedPantsHomeomorph_boundaryCircle (P : PlanarBase.{u} 3) (j : Fin 3) (t : Circle) :
    P.closedPantsHomeomorph (P.boundaryCircle j t) = closedPantsCircle j t := by
  apply Subtype.ext
  exact P.embedding_collar j t

def closedPantsHomeomorphOfKind {k : ℕ} (P : PlanarBase.{u} k) (hk : k = 3) :
    P.surface.Carrier ≃ₜ ClosedPants := by
  subst k
  exact P.closedPantsHomeomorph

theorem closedPantsHomeomorphOfKind_boundaryCircle {k : ℕ} (P : PlanarBase.{u} k)
    (hk : k = 3) (j : Fin k) (t : Circle) :
    P.closedPantsHomeomorphOfKind hk (P.boundaryCircle j t) =
      closedPantsCircle (Fin.cast hk j) t := by
  subst k
  exact P.closedPantsHomeomorph_boundaryCircle j t


theorem closedPantsHomeomorph_symm_boundaryCircle (P : PlanarBase.{u} 3)
    (j : Fin 3) (t : Circle) :
    P.closedPantsHomeomorph.symm (closedPantsCircle j t) = P.boundaryCircle j t := by
  apply P.closedPantsHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, P.closedPantsHomeomorph_boundaryCircle]

theorem closedPantsHomeomorph_symm_boundaryMap (P : PlanarBase.{u} 3) (j : Fin 3) :
    (P.closedPantsHomeomorph.symm : C(ClosedPants, P.surface.Carrier)).comp
      (closedPantsCircle j) = P.boundaryCircle j :=
  ContinuousMap.ext (P.closedPantsHomeomorph_symm_boundaryCircle j)

theorem exists_closedTriangleBoundaryGenerators (P : PlanarBase.{u} 3) :
    ∃ b : P.surface.Carrier, ∃ β : (j : Fin 3) → Path b (P.boundaryCircle j 1),
      let x := fun j => GC.Topology.markedMap (P.boundaryCircle j) 1 (β j)
        (FundamentalGroup.fromPath ⟦circleLoop⟧)
      Subgroup.closure (Set.range x) = ⊤ ∧ x 0 * x 2 * x 1 = 1 := by
  obtain ⟨p, β, hgen, hrel⟩ := exists_closedPants_boundary_generators
  let e := P.closedPantsHomeomorph
  let f : C(ClosedPants, P.surface.Carrier) := e.symm
  let F := FundamentalGroup.map f p
  have hpaths : ∀ j : Fin 3, ∃ γ : Path (e.symm p) (P.boundaryCircle j 1),
      ∀ a : FundamentalGroup Circle 1,
        GC.Topology.markedMap (P.boundaryCircle j) 1 γ a =
          F (GC.Topology.markedMap (closedPantsCircle j) 1 (β j) a) := by
    intro j
    rw [← P.closedPantsHomeomorph_symm_boundaryMap j]
    refine ⟨(β j).map e.symm.continuous, fun a => ?_⟩
    exact (DFunLike.congr_fun (map_comp_markedMap (closedPantsCircle j) f 1 (β j)) a).symm
  choose γ hγ using hpaths
  let x := fun j => GC.Topology.markedMap (closedPantsCircle j) 1 (β j)
    (FundamentalGroup.fromPath ⟦circleLoop⟧)
  let y := fun j => F (x j)
  have hF : Function.Bijective F := bijective_map_homeomorph e.symm p
  have hy : Subgroup.closure (Set.range y) = ⊤ := by
    change Subgroup.closure (Set.range ((F : FundamentalGroup ClosedPants p → _) ∘ x)) = ⊤
    rw [Set.range_comp, ← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective F hF.surjective]
  refine ⟨e.symm p, γ, ?_⟩
  have hx : (fun j => GC.Topology.markedMap (P.boundaryCircle j) 1 (γ j)
      (FundamentalGroup.fromPath ⟦circleLoop⟧)) = y := by
    funext j
    exact hγ j (FundamentalGroup.fromPath ⟦circleLoop⟧)
  change Subgroup.closure (Set.range (fun j => GC.Topology.markedMap
    (P.boundaryCircle j) 1 (γ j) (FundamentalGroup.fromPath ⟦circleLoop⟧))) = ⊤ ∧ _
  rw [hx]
  refine ⟨hy, ?_⟩
  simpa only [map_mul, map_one] using congrArg F hrel

theorem exists_closedTriangleBoundaryGeneratorsOfKind {k : ℕ} (P : PlanarBase.{u} k)
    (hk : k = 3) :
    ∃ b : P.surface.Carrier,
      ∃ β : (j : Fin 3) → Path b (P.boundaryCircle (Fin.cast hk.symm j) 1),
        let x := fun j => GC.Topology.markedMap (P.boundaryCircle (Fin.cast hk.symm j))
          1 (β j) (FundamentalGroup.fromPath ⟦circleLoop⟧)
        Subgroup.closure (Set.range x) = ⊤ ∧ x 0 * x 2 * x 1 = 1 := by
  subst k
  exact P.exists_closedTriangleBoundaryGenerators

end PlanarBase
end GC.Seifert
