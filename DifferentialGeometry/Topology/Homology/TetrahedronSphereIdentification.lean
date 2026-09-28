import DifferentialGeometry.Topology.Homology.TetrahedronSphereConstant
import DifferentialGeometry.Topology.Simplex.BoundarySphereReplacement
import DifferentialGeometry.Topology.Simplex.Extension

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology ContinuousMap
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph coordinateEquiv)
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

private theorem cone_three_faces_compatible (σ : integralSingularSimplex 3 X)
    (i : Fin 5) (j : Fin 4) (p : coordinateSet ℝ (Fin 3)) :
    integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i)
        ((coordinateHomeomorph ℝ (Fin 4)).symm (coordinateMap j.succAbove p)) =
      integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ (i.succAbove j))
        ((coordinateHomeomorph ℝ (Fin 4)).symm
          (coordinateMap (j.predAbove i).succAbove p)) := by
  obtain ⟨p, rfl⟩ := (coordinateEquiv ℝ _).surjective p
  have h := congrArg (fun a => integralSingularSimplexEquiv 2 X a p)
    (integralSingularConeThreeFaces_compatible x σ i j)
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeThreeFaces x σ i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
          (integralSingularConeThreeFaces x σ (i.succAbove j))) p at h
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
  change integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i)
      ((coordinateEquiv ℝ _).symm (coordinateMap j.succAbove (coordinateEquiv ℝ _ p))) =
    integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ (i.succAbove j))
      ((coordinateEquiv ℝ _).symm
        (coordinateMap (j.predAbove i).succAbove (coordinateEquiv ℝ _ p)))
  rw [← Convexity.StdSimplex.coordinateEquiv_map, Equiv.symm_apply_apply,
    ← Convexity.StdSimplex.coordinateEquiv_map, Equiv.symm_apply_apply]
  exact h

theorem integralSingularConeThreeSphereMap_homotopic_tetrahedronSphereMap_of_boundary
    (g : C(coordinateSet ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularConeThreeSphereMap x ((integralSingularSimplexEquiv 3 X).symm
      (g.comp ⟨coordinateHomeomorph ℝ (Fin 4),
        (coordinateHomeomorph ℝ (Fin 4)).continuous⟩))).Homotopic
      (Simplex.tetrahedronSphereMap g x hg) := by
  let σ := (integralSingularSimplexEquiv 3 X).symm
    (g.comp ⟨coordinateHomeomorph ℝ (Fin 4),
      (coordinateHomeomorph ℝ (Fin 4)).continuous⟩)
  let κ := (integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x)
  let f (i : Fin 5) := (integralSingularSimplexEquiv 3 X
    (integralSingularConeThreeFaces x σ i)).comp
      ⟨(coordinateHomeomorph ℝ (Fin 4)).symm,
        (coordinateHomeomorph ℝ (Fin 4)).symm.continuous⟩
  let c (i : Fin 5) := (integralSingularSimplexEquiv 3 X
    (integralSingularConeThreeFaces x κ i)).comp
      ⟨(coordinateHomeomorph ℝ (Fin 4)).symm,
        (coordinateHomeomorph ℝ (Fin 4)).symm.continuous⟩
  have hf := cone_three_faces_compatible x σ
  have hc := cone_three_faces_compatible x κ
  let e := Simplex.stdSimplexNormedBoundarySphereHomeomorph (EuclideanSpace.equiv (Fin 4) ℝ).symm
  obtain ⟨H⟩ := integralSingularConeThreeSphereMap_const_homotopic x
  have hnull : (Simplex.boundaryDesc c hc).Nullhomotopic := by
    refine ⟨x, ⟨?_⟩⟩
    refine ⟨(H.toContinuousMap.comp
          (ContinuousMap.prodMap (ContinuousMap.id _) ⟨e, e.continuous⟩)), ?_, ?_⟩
    · intro p
      change H (0, e p) = _
      rw [H.apply_zero]
      change Simplex.boundaryDesc c hc (e.symm (e p)) = _
      rw [e.symm_apply_apply]
    · intro p
      exact H.apply_one (e p)
  obtain ⟨E, hE⟩ := Simplex.exists_continuous_extension_of_nullhomotopic 4
    (Simplex.boundaryDesc c hc) hnull
  have hEface (i : Fin 5) (p : coordinateSet ℝ (Fin 4)) :
      E (coordinateMap i.succAbove p) = c i p := by
    exact (hE ⟨coordinateMap i.succAbove p,
      ⟨i, Simplex.map_succAbove_apply_pivot i p⟩⟩).trans
        (Simplex.boundaryDesc_face c hc i p)
  have hσface (i : Fin 4) : (TopCat.toSSet.obj (TopCat.of X)).δ i σ =
      (TopCat.toSSet.obj (TopCat.of X)).δ i κ := by
    apply (integralSingularSimplexEquiv 2 X).injective
    ext p
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) p =
      (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i κ) p
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
    change g (coordinateEquiv ℝ (Fin 4) (Convexity.StdSimplex.map i.succAbove p)) = x
    rw [Convexity.StdSimplex.coordinateEquiv_map]
    exact hg _ ⟨i, Simplex.map_succAbove_apply_pivot i (coordinateEquiv ℝ (Fin 3) p)⟩
  have hE0 (p : coordinateSet ℝ (Fin 4)) : E (coordinateMap (0 : Fin 5).succAbove p) = x := by
    rw [hEface]
    rfl
  have hEi (i : Fin 4) (p : coordinateSet ℝ (Fin 4)) :
      E (coordinateMap i.succ.succAbove p) = f i.succ p := by
    rw [hEface]
    change integralSingularSimplexEquiv 3 X
        (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ i κ))
          ((coordinateHomeomorph ℝ (Fin 4)).symm p) =
      integralSingularSimplexEquiv 3 X
        (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
          ((coordinateHomeomorph ℝ (Fin 4)).symm p)
    rw [hσface]
  have hf0 : f 0 = g := by
    ext p
    change g (coordinateHomeomorph ℝ (Fin 4)
      ((coordinateHomeomorph ℝ (Fin 4)).symm p)) = g p
    rw [Homeomorph.apply_symm_apply]
  have h := Simplex.boundarySphereDesc_homotopic_simplexSphereMap_of_extension f hf x
    (by simpa only [hf0] using hg) E hE0 hEi
  change (Simplex.boundarySphereDesc f hf).Homotopic (Simplex.simplexSphereMap g x hg)
  simpa only [hf0] using h

theorem integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop_of_boundary
    (g : C(coordinateSet ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    integralSingularTetrahedronSphereClass x ((integralSingularSimplexEquiv 3 X).symm
      (g.comp ⟨coordinateHomeomorph ℝ (Fin 4),
        (coordinateHomeomorph ℝ (Fin 4)).continuous⟩)) =
      (⟦Simplex.tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) :=
  integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop x _ g hg
    (integralSingularConeThreeSphereMap_homotopic_tetrahedronSphereMap_of_boundary x g hg)

end DifferentialGeometry.Topology
