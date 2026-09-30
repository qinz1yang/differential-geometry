import DifferentialGeometry.Topology.Homology.TetrahedronConeHomotopy
import DifferentialGeometry.Topology.Homology.ConeSphereHomotopy
import DifferentialGeometry.Topology.Simplex.FaceCompatibility

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology ContinuousMap
open Convexity.StdSimplex (coordinateSet coordinateMap continuous_coordinateMap
  coordinateHomeomorph coordinateHomeomorphI coordinateEquiv coordinateEquiv_map)
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_terminal_tetrahedron_faces
    (x : X) (tau : integralSingularSimplex 3 X) :
    ∃ G : C(coordinateSet ℝ (Fin 4), X),
      ∃ hG : ∀ p : Simplex.tetrahedronOneSkeleton, G p.val = x,
      ∀ i : Fin 4,
        (integralSingularConeSphereMap x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)).Homotopic
          (Simplex.triangleSphereMap
            (G.comp ⟨coordinateMap i.succAbove, continuous_coordinateMap i.succAbove⟩)
            x
            (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩))) := by
  obtain ⟨F, hF0, hFtrace, hF1⟩ := exists_tetrahedron_cone_edge_homotopy x tau
  let G : C(coordinateSet ℝ (Fin 4), X) :=
    ⟨fun p => F (1, p), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hG : ∀ p : Simplex.tetrahedronOneSkeleton, G p.val = x := by
    intro p
    exact hF1 p
  refine ⟨G, hG, ?_⟩
  intro i
  let g : C(coordinateSet ℝ (Fin 3), X) :=
    G.comp ⟨coordinateMap i.succAbove, continuous_coordinateMap i.succAbove⟩
  let H : ((integralSingularSimplexEquiv 2 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)).comp
        ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
          (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩).Homotopy g := by
    let K : C(unitInterval × coordinateSet ℝ (Fin 3), X) := F.comp ⟨fun z => (z.1, coordinateMap i.succAbove z.2), continuous_fst.prodMk ((continuous_coordinateMap i.succAbove).comp continuous_snd)⟩
    refine { toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }
    · intro p
      change F (0, coordinateMap i.succAbove p) = _
      rw [hF0]
      obtain ⟨p, rfl⟩ := (coordinateHomeomorph ℝ (Fin 3)).surjective p
      change integralSingularSimplexEquiv 3 X tau
          ((coordinateEquiv ℝ (Fin 4)).symm
            (coordinateMap i.succAbove (coordinateEquiv ℝ (Fin 3) p))) =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)
          ((coordinateHomeomorph ℝ (Fin 3)).symm (coordinateHomeomorph ℝ (Fin 3) p))
      rw [← coordinateEquiv_map, Equiv.symm_apply_apply, Homeomorph.symm_apply_apply,
        TopCat.toSSetObjEquiv_δ_apply]
      rfl
    · intro p
      change F (1, coordinateMap i.succAbove p) = _
      rfl
  have hH : ∀ (t : unitInterval) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)),
      H (t, coordinateMap j.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ j
            ((TopCat.toSSet.obj (TopCat.of X)).δ i tau))
          (t, coordinateHomeomorphI p) := by
    intro t j p
    change F (t, coordinateMap i.succAbove (coordinateMap j.succAbove p)) = _
    exact hFtrace i j t p
  exact integralSingularConeSphereMap_homotopic_triangleSphereMap x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i tau) g
    (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩)) H hH

end DifferentialGeometry.Topology
