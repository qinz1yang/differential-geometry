import DifferentialGeometry.Topology.Homology.ThreeCycleRealization
import DifferentialGeometry.Topology.Homology.ConeTriangleHomotopy
import DifferentialGeometry.Topology.Simplex.TetrahedronSphere
import DifferentialGeometry.Topology.Simplex.ConeContraction
import DifferentialGeometry.Topology.Simplex.BoundaryHomotopy
import DifferentialGeometry.Topology.Homotopy.SphereClasses

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

private def coneTetrahedronHomotopy (σ : integralSingularSimplex 2 X) :
    (integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)).Homotopy
      (ContinuousMap.const _ x) where
  toContinuousMap := (integralSingularSimplexEquiv 3 X
    (integralSingularConeTetrahedron x σ)).comp (Simplex.vertexContraction (0 : Fin 4))
  map_zero_left p := by simp
  map_one_left p := by
    change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      (Simplex.vertexContraction (0 : Fin 4) (1, p)) = x
    rw [Simplex.vertexContraction_one]
    have h := integralSingularConeTriangleHomotopy_one x σ (stdSimplex.vertex 0)
    simpa only [integralSingularConeTriangleHomotopy, ContinuousMap.comp_apply,
      Simplex.simplexCone_one] using h

private theorem coneTetrahedronHomotopy_face_zero (σ : integralSingularSimplex 2 X)
    (t : unitInterval) (p : stdSimplex ℝ (Fin 3)) :
    coneTetrahedronHomotopy x σ (t, stdSimplex.map (0 : Fin 4).succAbove p) =
      integralSingularConeTriangleHomotopy x σ (t, p) := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
    (Simplex.vertexContraction (0 : Fin 4) (t, stdSimplex.map (0 : Fin 4).succAbove p)) = _
  rw [Simplex.vertexContraction_zero_face_eq_simplexCone]
  rfl

private theorem coneTetrahedronHomotopy_face_succ (σ : integralSingularSimplex 2 X)
    (i : Fin 3) (t : unitInterval) (p : stdSimplex ℝ (Fin 3)) :
    coneTetrahedronHomotopy x σ (t, stdSimplex.map i.succ.succAbove p) =
      integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
        (stdSimplex.map i.succ.succAbove
          (Simplex.vertexContraction (0 : Fin 3) (t, p))) := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
    (Simplex.vertexContraction (0 : Fin 4) (t, stdSimplex.map i.succ.succAbove p)) = _
  rw [Simplex.vertexContraction_zero_face_succ]

theorem integralSingularConeThreeSphereMap_homotopic_tetrahedronSphereMap
    (σ : integralSingularSimplex 3 X) (g : C(stdSimplex ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x)
    (F : (integralSingularSimplexEquiv 3 X σ).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 4) (p : stdSimplex ℝ (Fin 3)),
      F (t, stdSimplex.map i.succAbove p) =
        integralSingularConeTriangleHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) (t, p)) :
    (integralSingularConeThreeSphereMap x σ).Homotopic
      (Simplex.tetrahedronSphereMap g x hg) := by
  let f : Fin 5 → C(stdSimplex ℝ (Fin 4), X) := fun i =>
    integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i)
  have hf : ∀ (i : Fin 5) (j : Fin 4) (p : stdSimplex ℝ (Fin 3)),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p
    have h := congrArg (fun a => integralSingularSimplexEquiv 2 X a p)
      (integralSingularConeThreeFaces_compatible x σ i j)
    change (TopCat.of X).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeThreeFaces x σ i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
          (integralSingularConeThreeFaces x σ (i.succAbove j))) p at h
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
    exact h
  let H : ∀ i : Fin 5, (f i).Homotopy (Simplex.tetrahedronSphereFaces g x i) :=
    Fin.cases F (fun i => coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
  have hH : ∀ (i : Fin 5) (j : Fin 4) (t : unitInterval)
      (p : stdSimplex ℝ (Fin 3)), H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j t p
    fin_cases i <;> fin_cases j
    · change F (t, stdSimplex.map (0 : Fin 4).succAbove p) =
        coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
          (t, stdSimplex.map (0 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact hF t 0 p
    · change F (t, stdSimplex.map (1 : Fin 4).succAbove p) =
        coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
          (t, stdSimplex.map (0 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact hF t 1 p
    · change F (t, stdSimplex.map (2 : Fin 4).succAbove p) =
        coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
          (t, stdSimplex.map (0 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact hF t 2 p
    · change F (t, stdSimplex.map (3 : Fin 4).succAbove p) =
        coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
          (t, stdSimplex.map (0 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact hF t 3 p
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
        (t, stdSimplex.map (0 : Fin 4).succAbove p) =
          F (t, stdSimplex.map (0 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact (hF t 0 p).symm
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
        (t, stdSimplex.map (0 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
            (t, stdSimplex.map (0 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 1 1 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
        (t, stdSimplex.map (1 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
            (t, stdSimplex.map (0 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 1 2 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
        (t, stdSimplex.map (2 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
            (t, stdSimplex.map (0 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 1 3 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
        (t, stdSimplex.map (0 : Fin 4).succAbove p) =
          F (t, stdSimplex.map (1 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact (hF t 1 p).symm
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
        (t, stdSimplex.map (0 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
            (t, stdSimplex.map (0 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 2 1 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
        (t, stdSimplex.map (1 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
            (t, stdSimplex.map (1 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 2 2 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
        (t, stdSimplex.map (2 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
            (t, stdSimplex.map (1 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 2 3 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
        (t, stdSimplex.map (0 : Fin 4).succAbove p) =
          F (t, stdSimplex.map (2 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact (hF t 2 p).symm
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
        (t, stdSimplex.map (0 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
            (t, stdSimplex.map (1 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 3 1 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
        (t, stdSimplex.map (1 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
            (t, stdSimplex.map (1 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 3 2 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
        (t, stdSimplex.map (2 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
            (t, stdSimplex.map (2 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 3 3 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
        (t, stdSimplex.map (0 : Fin 4).succAbove p) =
          F (t, stdSimplex.map (3 : Fin 4).succAbove p)
      rw [coneTetrahedronHomotopy_face_zero]
      exact (hF t 3 p).symm
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
        (t, stdSimplex.map (0 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)
            (t, stdSimplex.map (2 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 4 1 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
        (t, stdSimplex.map (1 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)
            (t, stdSimplex.map (2 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 4 2 (Simplex.vertexContraction (0 : Fin 3) (t, p))
    · change coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)
        (t, stdSimplex.map (2 : Fin 3).succ.succAbove p) =
          coneTetrahedronHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)
            (t, stdSimplex.map (2 : Fin 3).succ.succAbove p)
      rw [coneTetrahedronHomotopy_face_succ, coneTetrahedronHomotopy_face_succ]
      exact hf 4 3 (Simplex.vertexContraction (0 : Fin 3) (t, p))
  let B := Simplex.boundaryHomotopy hf (Simplex.tetrahedronSphereFaces_compatible g x hg) H hH
  exact ⟨B.comp (ContinuousMap.Homotopy.refl
    ⟨(Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm,
      (Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm.continuous⟩)⟩

theorem integralSingularConeThreeSphereMap_free_class_eq_tetrahedronSphereMap
    (σ : integralSingularSimplex 3 X) (g : C(stdSimplex ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x)
    (F : (integralSingularSimplexEquiv 3 X σ).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 4) (p : stdSimplex ℝ (Fin 3)),
      F (t, stdSimplex.map i.succAbove p) =
        integralSingularConeTriangleHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) (t, p)) :
    (homotopyGroupFreeSphereEquiv 2 x).symm
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)) =
      (homotopyGroupFreeSphereEquiv 2 x).symm
        (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)) := by
  apply congrArg (homotopyGroupFreeSphereEquiv 2 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp
    (integralSingularConeThreeSphereMap_homotopic_tetrahedronSphereMap x σ g hg F hF))

end DifferentialGeometry.Topology
