import DifferentialGeometry.Topology.Homology.SphereFaceChains
import DifferentialGeometry.Topology.Homology.TriangleConeHomotopy
import DifferentialGeometry.Topology.Homology.ConeSphereHomotopy
import DifferentialGeometry.Topology.Simplex.FaceCompatibility

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X]

private theorem sphereFace_compatible
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X))
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i)
        (stdSimplex.map j.succAbove p) =
      integralSingularSimplexEquiv 2 X (integralSingularSphereFace f (i.succAbove j))
        (stdSimplex.map (j.predAbove i).succAbove p) := by
  rw [integralSingularSphereFace_apply, integralSingularSphereFace_apply,
    Simplex.boundary_face_point_eq]

private theorem sphereFace_face_eq
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X))
    (i : Fin 4) (j : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularSphereFace f i) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
        (integralSingularSphereFace f (i.succAbove j)) := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro p
  change (TopCat.of X).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularSphereFace f i)) p =
    (TopCat.of X).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
        (integralSingularSphereFace f (i.succAbove j))) p
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  exact sphereFace_compatible f i j p

private theorem sphereFace_boundarySphereDesc
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) :
    Simplex.boundarySphereDesc
      (fun i => integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i))
      (sphereFace_compatible f) = f := by
  let e := Simplex.stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  have hb : Simplex.boundaryDesc
      (fun i => integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i))
      (sphereFace_compatible f) = f.comp ⟨e,e.continuous⟩ := by
    symm
    apply Simplex.boundaryDesc_unique
    intro i p
    exact (integralSingularSphereFace_apply f i p).symm
  apply ContinuousMap.ext
  intro p
  rw [Simplex.boundarySphereDesc]
  change Simplex.boundaryDesc
    (fun i => integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i))
    (sphereFace_compatible f) (e.symm p) = f p
  rw [hb]
  exact congrArg f (e.apply_symm_apply p)


private theorem terminalSphereFace_compatible
    (g : Fin 4 → C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ i, ∀ p ∈ Simplex.boundary (Fin 3), g i p = x)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    g i (stdSimplex.map j.succAbove p) =
      g (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) :=
  (hg i _ ⟨j, Simplex.map_succAbove_apply_pivot j p⟩).trans
    (hg (i.succAbove j) _
      ⟨j.predAbove i, Simplex.map_succAbove_apply_pivot (j.predAbove i) p⟩).symm

variable [SimplyConnectedSpace X]

theorem exists_sphere_cone_terminal_faces
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) (x : X) :
    ∃ g : Fin 4 → C(stdSimplex ℝ (Fin 3), X),
      ∃ hg : ∀ i, ∀ p ∈ Simplex.boundary (Fin 3), g i p = x,
        f.Homotopic (Simplex.boundarySphereDesc g (terminalSphereFace_compatible g x hg)) ∧
        ∀ i, (integralSingularConeSphereMap x (integralSingularSphereFace f i)).Homotopic
          (Simplex.triangleSphereMap (g i) x (hg i)) := by
  classical
  have hn (i : Fin 4) := exists_triangle_cone_edge_homotopy x (integralSingularSphereFace f i)
  choose g hg F hF using hn
  refine ⟨g, hg, ?_, ?_⟩
  · have hcomp : ∀ (i : Fin 4) (j : Fin 3) (t : unitInterval)
        (p : stdSimplex ℝ (Fin 2)),
        F i (t, stdSimplex.map j.succAbove p) =
          F (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
      intro i j t p
      rw [hF, hF, sphereFace_face_eq f i j]
    let B := Simplex.boundaryHomotopy (sphereFace_compatible f)
      (terminalSphereFace_compatible g x hg) F hcomp
    have H : (Simplex.boundarySphereDesc
        (fun i => integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i))
        (sphereFace_compatible f)).Homotopic
          (Simplex.boundarySphereDesc g (terminalSphereFace_compatible g x hg)) :=
      ⟨B.comp (ContinuousMap.Homotopy.refl
        ⟨(Simplex.stdSimplexNormedBoundarySphereHomeomorph
          (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm,
          (Simplex.stdSimplexNormedBoundarySphereHomeomorph
            (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm.continuous⟩)⟩
    rw [sphereFace_boundarySphereDesc] at H
    exact H
  · intro i
    exact integralSingularConeSphereMap_homotopic_triangleSphereMap
      x (integralSingularSphereFace f i) (g i) (hg i) (F i) (hF i)

end DifferentialGeometry.Topology
