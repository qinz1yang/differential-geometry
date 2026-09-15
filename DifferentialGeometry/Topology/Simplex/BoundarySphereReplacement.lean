import DifferentialGeometry.Topology.Simplex.Sphere
import DifferentialGeometry.Topology.Simplex.BoundaryHomotopy
import DifferentialGeometry.Topology.Simplex.VertexContraction

noncomputable section

namespace DifferentialGeometry.Simplex

open ContinuousMap

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem boundarySphereDesc_homotopic_simplexSphereMap_of_extension
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (hf : ∀ (i : Fin (n + 3)) (j : Fin (n + 2)) (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (x : X) (hg : ∀ p ∈ boundary (Fin (n + 2)), f 0 p = x)
    (E : C(stdSimplex ℝ (Fin (n + 3)), X))
    (hE0 : ∀ p, E (stdSimplex.map (0 : Fin (n + 3)).succAbove p) = x)
    (hEi : ∀ (i : Fin (n + 2)) p, E (stdSimplex.map i.succ.succAbove p) = f i.succ p) :
    (boundarySphereDesc f hf).Homotopic (simplexSphereMap (f 0) x hg) := by
  let R := E.comp (vertexContraction (1 : Fin (n + 3)))
  have hR0 (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))) :
      R (t, stdSimplex.map (0 : Fin (n + 3)).succAbove p) = x := by
    change E (vertexContraction (1 : Fin (n + 3))
      (t, stdSimplex.map (0 : Fin (n + 3)).succAbove p)) = x
    rw [show (1 : Fin (n + 3)) = (0 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) from rfl,
      vertexContraction_map, hE0]
  have hv : E (stdSimplex.vertex (S := ℝ) (1 : Fin (n + 3))) = x := by
    have h := hR0 1 (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)))
    simpa only [R, ContinuousMap.comp_apply, vertexContraction_one] using h
  let H : ∀ i : Fin (n + 3), (f i).Homotopy (simplexSphereFaces (f 0) x i) :=
    Fin.cases (Homotopy.refl (f 0)) fun i =>
      { toContinuousMap := R.comp
          ⟨fun z => (z.1, stdSimplex.map i.succ.succAbove z.2),
            continuous_fst.prodMk ((stdSimplex.continuous_map i.succ.succAbove).comp continuous_snd)⟩
        map_zero_left := by
          intro p
          change E (vertexContraction (1 : Fin (n + 3)) (0, stdSimplex.map i.succ.succAbove p)) = _
          rw [vertexContraction_zero, hEi]
        map_one_left := by
          intro p
          change E (vertexContraction (1 : Fin (n + 3)) (1, stdSimplex.map i.succ.succAbove p)) = x
          rw [vertexContraction_one, hv] }
  have hHface (i : Fin (n + 3)) (j : Fin (n + 2)) (t : unitInterval)
      (p : stdSimplex ℝ (Fin (n + 1))) :
      H i (t, stdSimplex.map j.succAbove p) =
        R (t, stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) := by
    induction i using Fin.cases with
    | zero =>
      change f 0 (stdSimplex.map j.succAbove p) =
        R (t, stdSimplex.map (0 : Fin (n + 3)).succAbove (stdSimplex.map j.succAbove p))
      rw [hR0]
      exact hg _ ⟨j, map_succAbove_apply_pivot j p⟩
    | succ i => rfl
  have hH (i : Fin (n + 3)) (j : Fin (n + 2)) (t : unitInterval)
      (p : stdSimplex ℝ (Fin (n + 1))) :
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    rw [hHface, hHface]
    congr 2
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    congr 1
    funext k
    exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  let B := boundaryHomotopy hf (simplexSphereFaces_compatible (f 0) x hg) H hH
  exact ⟨B.comp (Homotopy.refl
    ⟨(stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm,
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm.continuous⟩)⟩

end DifferentialGeometry.Simplex
