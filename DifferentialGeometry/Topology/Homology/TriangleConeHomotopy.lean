import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.HomotopyExtension

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_triangle_cone_edge_homotopy
    (x : X) (sigma : integralSingularSimplex 2 X) :
    ∃ g : C(stdSimplex ℝ (Fin 3), X),
      (∀ p ∈ Simplex.boundary (Fin 3), g p = x) ∧
      ∃ F : (integralSingularSimplexEquiv 2 X sigma).Homotopy g,
        ∀ (t : unitInterval) (i : Fin 3) (p : stdSimplex ℝ (Fin 2)),
          F (t, stdSimplex.map i.succAbove p) =
            integralSingularConeEdgeHomotopy x
              ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
              (t, stdSimplexHomeomorphUnitInterval p) := by
  let H (i : Fin 3) : C(unitInterval × stdSimplex ℝ (Fin 2), X) :=
    (integralSingularConeEdgeHomotopy x
      ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)).comp
      ⟨fun z => (z.1, stdSimplexHomeomorphUnitInterval z.2),
        continuous_fst.prodMk (stdSimplexHomeomorphUnitInterval.continuous.comp continuous_snd)⟩
  have hface (i : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
      integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma) p =
        integralSingularSimplexEquiv 2 X sigma (stdSimplex.map i.succAbove p) := by
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma) p = _
    rw [TopCat.toSSetObjEquiv_δ_apply]
    rfl
  have hH (i : Fin 3) (j : Fin 2) (t : unitInterval) (p : stdSimplex ℝ (Fin 1)) :
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    change integralSingularConeEdgeHomotopy x
        ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
        (t, stdSimplexHomeomorphUnitInterval (stdSimplex.map j.succAbove p)) =
      integralSingularConeEdgeHomotopy x
        ((TopCat.toSSet.obj (TopCat.of X)).δ (i.succAbove j) sigma)
        (t, stdSimplexHomeomorphUnitInterval (stdSimplex.map (j.predAbove i).succAbove p))
    rw [integralSingularConeEdgeHomotopy_boundary x _ _
        ⟨j, Simplex.map_succAbove_apply_pivot j p⟩,
      integralSingularConeEdgeHomotopy_boundary x _ _
        ⟨j.predAbove i, Simplex.map_succAbove_apply_pivot (j.predAbove i) p⟩,
      hface, hface]
    have he : stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p) =
        stdSimplex.map (i.succAbove j).succAbove
          (stdSimplex.map (j.predAbove i).succAbove p) := by
      rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
      congr 1
      funext k
      exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
    rw [he]
  have h₀ (i : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
      H i (0, p) = integralSingularSimplexEquiv 2 X sigma (stdSimplex.map i.succAbove p) := by
    change integralSingularConeEdgeHomotopy x
      ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
      (0, stdSimplexHomeomorphUnitInterval p) = _
    rw [integralSingularConeEdgeHomotopy_zero]
    have h := integralPathSimplex_apply
      (integralSimplexPath ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)) p
    rw [integralPathSimplex_simplexPath] at h
    exact h.symm.trans (hface i p)
  obtain ⟨G, hG₀, hGs⟩ := Simplex.exists_continuous_homotopy_extension_of_faces
    0 (integralSingularSimplexEquiv 2 X sigma) H hH h₀
  let g : C(stdSimplex ℝ (Fin 3), X) := G.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩
  have hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x := by
    intro p hp
    obtain ⟨i, hi⟩ := hp
    let q := Simplex.faceDelete i ⟨p, hi⟩
    have hq : stdSimplex.map i.succAbove q = p :=
      congrArg Subtype.val (Simplex.faceInsert_faceDelete i ⟨p, hi⟩)
    change G (1, p) = x
    rw [← hq, hGs]
    exact integralSingularConeEdgeHomotopy_one x _ _
  let F : (integralSingularSimplexEquiv 2 X sigma).Homotopy g :=
    { toContinuousMap := G
      map_zero_left := hG₀
      map_one_left := fun _ => rfl }
  exact ⟨g, hg, F, fun t i p => hGs i t p⟩

end DifferentialGeometry.Topology
