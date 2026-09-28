import DifferentialGeometry.Topology.Simplex.TriangleSphere
import DifferentialGeometry.Topology.Simplex.TriangleContraction
import DifferentialGeometry.Topology.Homology.TwoCycleRealization
import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.BoundaryHomotopy
import DifferentialGeometry.Topology.Homotopy.SphereClasses

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph
  coordinateHomeomorphI coordinateEquiv coordinateEquiv_map)
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def coneFaceHomotopy (x : X) (sigma : integralSingularSimplex 1 X) :
    ((integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)).comp
      ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩).Homotopy
      (ContinuousMap.const _ x) where
  toContinuousMap := (integralSingularSimplexEquiv 2 X
    (integralSingularConeTriangle x sigma)).comp
      ((⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩ :
        C(coordinateSet ℝ (Fin 3), Convexity.StdSimplex ℝ (Fin 3))).comp
          (Simplex.vertexContraction (0 : Fin 3)))
  map_zero_left p := by simp
  map_one_left p := by
    change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
      ((coordinateHomeomorph ℝ (Fin 3)).symm
        (Simplex.vertexContraction (0 : Fin 3) (1, p))) = x
    rw [Simplex.vertexContraction_one]
    have h := integralSingularConeEdgeHomotopy_one x sigma 0
    simpa only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, unitInterval.symm_one, Simplex.triangleJoin_zero] using h

private theorem coneFaceHomotopy_face_zero (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : coordinateSet ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, coordinateMap (0 : Fin 3).succAbove p) =
      integralSingularConeEdgeHomotopy x sigma (t, coordinateHomeomorphI p) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    ((coordinateHomeomorph ℝ (Fin 3)).symm
      (Simplex.vertexContraction (0 : Fin 3) (t, coordinateMap (0 : Fin 3).succAbove p))) = _
  rw [Simplex.vertexContraction_zero_face_zero]
  rfl

private theorem coneFaceHomotopy_face_one (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : coordinateSet ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, coordinateMap (1 : Fin 3).succAbove p) =
      integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
        ((coordinateHomeomorph ℝ (Fin 3)).symm
          (coordinateMap (1 : Fin 3).succAbove
            (Simplex.vertexContraction (0 : Fin 2) (t, p)))) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    ((coordinateHomeomorph ℝ (Fin 3)).symm
      (Simplex.vertexContraction (0 : Fin 3) (t, coordinateMap (1 : Fin 3).succAbove p))) = _
  rw [Simplex.vertexContraction_zero_face_one]

private theorem coneFaceHomotopy_face_two (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : coordinateSet ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, coordinateMap (2 : Fin 3).succAbove p) =
      integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
        ((coordinateHomeomorph ℝ (Fin 3)).symm
          (coordinateMap (2 : Fin 3).succAbove
            (Simplex.vertexContraction (0 : Fin 2) (t, p)))) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    ((coordinateHomeomorph ℝ (Fin 3)).symm
      (Simplex.vertexContraction (0 : Fin 3) (t, coordinateMap (2 : Fin 3).succAbove p))) = _
  rw [Simplex.vertexContraction_zero_face_two]

theorem integralSingularConeSphereMap_homotopic_triangleSphereMap
    (x : X) (sigma : integralSingularSimplex 2 X)
    (g : C(coordinateSet ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (F : ((integralSingularSimplexEquiv 2 X sigma).comp
      ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 3) (p : coordinateSet ℝ (Fin 2)),
      F (t, coordinateMap i.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
          (t, coordinateHomeomorphI p)) :
    (integralSingularConeSphereMap x sigma).Homotopic
      (Simplex.triangleSphereMap g x hg) := by
  let f : Fin 4 → C(coordinateSet ℝ (Fin 3), X) := fun i =>
    (integralSingularSimplexEquiv 2 X (integralSingularConeFaces x sigma i)).comp
      ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩
  have hf : ∀ (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)),
      f i (coordinateMap j.succAbove p) =
        f (i.succAbove j) (coordinateMap (j.predAbove i).succAbove p) := by
    intro i j p
    obtain ⟨p, rfl⟩ := (coordinateEquiv ℝ (Fin 2)).surjective p
    have h := congrArg (fun a => integralSingularSimplexEquiv 1 X a p)
      (integralSingularConeFaces_compatible x sigma i j)
    change (TopCat.of X).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeFaces x sigma i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
          (integralSingularConeFaces x sigma (i.succAbove j))) p at h
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
    change integralSingularSimplexEquiv 2 X (integralSingularConeFaces x sigma i)
        ((coordinateEquiv ℝ _).symm (coordinateMap j.succAbove (coordinateEquiv ℝ _ p))) =
      integralSingularSimplexEquiv 2 X (integralSingularConeFaces x sigma (i.succAbove j))
        ((coordinateEquiv ℝ _).symm
          (coordinateMap (j.predAbove i).succAbove (coordinateEquiv ℝ _ p)))
    rw [← coordinateEquiv_map, Equiv.symm_apply_apply,
      ← coordinateEquiv_map, Equiv.symm_apply_apply]
    exact h
  let H : ∀ i : Fin 4, (f i).Homotopy (Simplex.triangleSphereFaces g x i) :=
    Fin.cases F (fun i => coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma))
  have hH : ∀ (i : Fin 4) (j : Fin 3) (t : unitInterval)
      (p : coordinateSet ℝ (Fin 2)), H i (t, coordinateMap j.succAbove p) =
        H (i.succAbove j) (t, coordinateMap (j.predAbove i).succAbove p) := by
    intro i j t p
    fin_cases i <;> fin_cases j
    · change F (t, coordinateMap (0 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
          (t, coordinateMap (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 0 p
    · change F (t, coordinateMap (1 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
          (t, coordinateMap (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 1 p
    · change F (t, coordinateMap (2 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
          (t, coordinateMap (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 2 p
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, coordinateMap (0 : Fin 3).succAbove p) =
          F (t, coordinateMap (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 0 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, coordinateMap (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
            (t, coordinateMap (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_one]
      exact hf 1 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, coordinateMap (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
            (t, coordinateMap (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_one]
      exact hf 1 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, coordinateMap (0 : Fin 3).succAbove p) =
          F (t, coordinateMap (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 1 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, coordinateMap (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
            (t, coordinateMap (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_one]
      exact hf 2 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, coordinateMap (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
            (t, coordinateMap (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_two]
      exact hf 2 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, coordinateMap (0 : Fin 3).succAbove p) =
          F (t, coordinateMap (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 2 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, coordinateMap (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
            (t, coordinateMap (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_two]
      exact hf 3 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, coordinateMap (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
            (t, coordinateMap (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_two]
      exact hf 3 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
  let B := Simplex.boundaryHomotopy hf (Simplex.triangleSphereFaces_compatible g x hg) H hH
  exact ⟨B.comp (ContinuousMap.Homotopy.refl
    ⟨(Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm,
      (Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm.continuous⟩)⟩

theorem integralSingularConeSphereMap_free_class_eq_triangleSphereMap
    (x : X) (sigma : integralSingularSimplex 2 X)
    (g : C(coordinateSet ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (F : ((integralSingularSimplexEquiv 2 X sigma).comp
      ⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
        (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 3) (p : coordinateSet ℝ (Fin 2)),
      F (t, coordinateMap i.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
          (t, coordinateHomeomorphI p)) :
    (homotopyGroupFreeSphereEquiv 1 x).symm
      (ZerothHomotopy.mk (integralSingularConeSphereMap x sigma)) =
      (homotopyGroupFreeSphereEquiv 1 x).symm
        (ZerothHomotopy.mk (Simplex.triangleSphereMap g x hg)) := by
  apply congrArg (homotopyGroupFreeSphereEquiv 1 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp
    (integralSingularConeSphereMap_homotopic_triangleSphereMap x sigma g hg F hF))

end DifferentialGeometry.Topology
