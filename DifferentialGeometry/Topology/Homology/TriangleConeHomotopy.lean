import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.HomotopyExtension

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateMap_comp_apply
  coordinateHomeomorph coordinateHomeomorphI coordinateEquiv_map)
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_triangle_cone_edge_homotopy
    (x : X) (sigma : integralSingularSimplex 2 X) :
    ∃ g : C(coordinateSet ℝ (Fin 3), X),
      (∀ p ∈ Simplex.boundary (Fin 3), g p = x) ∧
      ∃ F : ((integralSingularSimplexEquiv 2 X sigma).comp
          ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
            (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩).Homotopy g,
        ∀ (t : unitInterval) (i : Fin 3) (p : coordinateSet ℝ (Fin 2)),
          F (t, coordinateMap i.succAbove p) =
            integralSingularConeEdgeHomotopy x
              ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
              (t, coordinateHomeomorphI p) := by
  let f : C(coordinateSet ℝ (Fin 3), X) :=
    (integralSingularSimplexEquiv 2 X sigma).comp
      ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩
  let H (i : Fin 3) : C(unitInterval × coordinateSet ℝ (Fin 2), X) :=
    (integralSingularConeEdgeHomotopy x
      ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)).comp
      ⟨fun z => (z.1, coordinateHomeomorphI z.2),
        continuous_fst.prodMk (coordinateHomeomorphI.continuous.comp continuous_snd)⟩
  have hface (i : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
      integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
          ((coordinateHomeomorph ℝ (Fin 2)).symm p) =
        f (coordinateMap i.succAbove p) := by
    obtain ⟨p, rfl⟩ := (coordinateHomeomorph ℝ (Fin 2)).surjective p
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma) _ = _
    rw [Homeomorph.symm_apply_apply, TopCat.toSSetObjEquiv_δ_apply]
    change integralSingularSimplexEquiv 2 X sigma _ =
      integralSingularSimplexEquiv 2 X sigma
        ((coordinateHomeomorph ℝ (Fin 3)).symm
          (coordinateMap i.succAbove (Convexity.StdSimplex.coordinateEquiv ℝ (Fin 2) p)))
    rw [← coordinateEquiv_map]
    exact congrArg _ ((coordinateHomeomorph ℝ (Fin 3)).symm_apply_apply _).symm
  have hH (i : Fin 3) (j : Fin 2) (t : unitInterval) (p : coordinateSet ℝ (Fin 1)) :
      H i (t, coordinateMap j.succAbove p) =
        H (i.succAbove j) (t, coordinateMap (j.predAbove i).succAbove p) := by
    change integralSingularConeEdgeHomotopy x
        ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
        (t, coordinateHomeomorphI (coordinateMap j.succAbove p)) =
      integralSingularConeEdgeHomotopy x
        ((TopCat.toSSet.obj (TopCat.of X)).δ (i.succAbove j) sigma)
        (t, coordinateHomeomorphI (coordinateMap (j.predAbove i).succAbove p))
    rw [integralSingularConeEdgeHomotopy_boundary x _ _
        ⟨j, Simplex.map_succAbove_apply_pivot j p⟩,
      integralSingularConeEdgeHomotopy_boundary x _ _
        ⟨j.predAbove i, Simplex.map_succAbove_apply_pivot (j.predAbove i) p⟩,
      hface, hface]
    have he : coordinateMap i.succAbove (coordinateMap j.succAbove p) =
        coordinateMap (i.succAbove j).succAbove
          (coordinateMap (j.predAbove i).succAbove p) := by
      rw [coordinateMap_comp_apply, coordinateMap_comp_apply]
      congr 1
      funext k
      exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
    rw [he]
  have h₀ (i : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
      H i (0, p) = f (coordinateMap i.succAbove p) := by
    change integralSingularConeEdgeHomotopy x
      ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
      (0, coordinateHomeomorphI p) = _
    rw [integralSingularConeEdgeHomotopy_zero]
    have h := integralPathSimplex_apply
      (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma))
        ((coordinateHomeomorph ℝ (Fin 2)).symm p)
    rw [integralPathSimplex_simplexPath] at h
    exact h.symm.trans (hface i p)
  obtain ⟨G, hG₀, hGs⟩ := Simplex.exists_continuous_homotopy_extension_of_faces
    0 f H hH h₀
  let g : C(coordinateSet ℝ (Fin 3), X) := G.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩
  have hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x := by
    intro p hp
    obtain ⟨i, hi⟩ := hp
    let q := Simplex.faceDelete i ⟨p, hi⟩
    have hq : coordinateMap i.succAbove q = p :=
      congrArg Subtype.val (Simplex.faceInsert_faceDelete i ⟨p, hi⟩)
    change G (1, p) = x
    rw [← hq, hGs]
    exact integralSingularConeEdgeHomotopy_one x _ _
  let F : f.Homotopy g :=
    { toContinuousMap := G
      map_zero_left := hG₀
      map_one_left := fun _ => rfl }
  exact ⟨g, hg, F, fun t i p => hGs i t p⟩

end DifferentialGeometry.Topology
