import DifferentialGeometry.Topology.Homology.ThreeCycleRealization
import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.Cone

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph
  coordinateHomeomorphI coordinateSingle coordinateEquiv_map)
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularConeTriangleHomotopy (σ : integralSingularSimplex 2 X) :
    C(unitInterval × coordinateSet ℝ (Fin 3), X) :=
  (integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)).comp
    ((⟨(coordinateHomeomorph ℝ (Fin 4)).symm,
      (coordinateHomeomorph ℝ (Fin 4)).symm.continuous⟩ :
      C(coordinateSet ℝ (Fin 4), Convexity.StdSimplex ℝ (Fin 4))).comp
        (Simplex.simplexCone 2))

theorem integralSingularConeTriangleHomotopy_zero (σ : integralSingularSimplex 2 X)
    (p : coordinateSet ℝ (Fin 3)) :
    integralSingularConeTriangleHomotopy x σ (0, p) =
      integralSingularSimplexEquiv 2 X σ ((coordinateHomeomorph ℝ (Fin 3)).symm p) := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      ((coordinateHomeomorph ℝ (Fin 4)).symm (Simplex.simplexCone 2 (0, p))) = _
  rw [Simplex.simplexCone_zero]
  obtain ⟨p, rfl⟩ := (coordinateHomeomorph ℝ (Fin 3)).surjective p
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      ((coordinateHomeomorph ℝ (Fin 4)).symm
        (coordinateMap (0 : Fin 4).succAbove
          (Convexity.StdSimplex.coordinateEquiv ℝ (Fin 3) p))) = _
  rw [← coordinateEquiv_map]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTetrahedron x σ)
      ((coordinateHomeomorph ℝ (Fin 4)).symm
        (coordinateHomeomorph ℝ (Fin 4) (Convexity.StdSimplex.map (0 : Fin 4).succAbove p))) = _
  rw [Homeomorph.symm_apply_apply, ← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X
    ((TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x σ)) p = _
  rw [integralSingularConeTetrahedron_face, Homeomorph.symm_apply_apply]
  rfl

private theorem simplexCone_eq_triangleJoin (t : unitInterval)
    (p : coordinateSet ℝ (Fin 2)) :
    Simplex.simplexCone 1 (t, p) =
      Simplex.triangleJoin (unitInterval.symm t, coordinateHomeomorphI p) := by
  apply Subtype.ext
  funext i
  have hp : p.val 0 + p.val 1 = 1 := by simpa only [Fin.sum_univ_two] using p.property.2
  fin_cases i
  · change t.val = 1 - (1 - t.val)
    ring
  · change (1 - t.val) * p.val 0 = (1 - t.val) * (1 - p.val 1)
    congr 1
    linarith
  · rfl

theorem integralSingularConeTriangleHomotopy_face (σ : integralSingularSimplex 2 X)
    (i : Fin 3) (t : unitInterval) (p : coordinateSet ℝ (Fin 2)) :
    integralSingularConeTriangleHomotopy x σ (t, coordinateMap i.succAbove p) =
      integralSingularConeEdgeHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)
        (t, coordinateHomeomorphI p) := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      ((coordinateHomeomorph ℝ (Fin 4)).symm
        (Simplex.simplexCone 2 (t, coordinateMap i.succAbove p))) = _
  rw [Simplex.simplexCone_map_succAbove]
  have he : (coordinateHomeomorph ℝ (Fin 4)).symm
      (coordinateMap i.succ.succAbove (Simplex.simplexCone 1 (t, p))) =
        Convexity.StdSimplex.map i.succ.succAbove
          ((coordinateHomeomorph ℝ (Fin 3)).symm (Simplex.simplexCone 1 (t, p))) := by
    apply (coordinateHomeomorph ℝ (Fin 4)).injective
    rw [Homeomorph.apply_symm_apply]
    change _ = Convexity.StdSimplex.coordinateEquiv ℝ (Fin 4) _
    rw [coordinateEquiv_map]
    exact congrArg (coordinateMap i.succ.succAbove)
      ((coordinateHomeomorph ℝ (Fin 3)).apply_symm_apply _).symm
  rw [he]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTetrahedron x σ)
      (Convexity.StdSimplex.map i.succ.succAbove _) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X
    ((TopCat.toSSet.obj (TopCat.of X)).δ i.succ (integralSingularConeTetrahedron x σ))
      ((coordinateHomeomorph ℝ (Fin 3)).symm (Simplex.simplexCone 1 (t, p))) = _
  rw [integralSingularConeTetrahedron_face]
  change integralSingularSimplexEquiv 2 X
    (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
      ((coordinateHomeomorph ℝ (Fin 3)).symm (Simplex.simplexCone 1 (t, p))) = _
  rw [simplexCone_eq_triangleJoin]
  rfl

theorem integralSingularConeTriangleHomotopy_one (σ : integralSingularSimplex 2 X)
    (p : coordinateSet ℝ (Fin 3)) : integralSingularConeTriangleHomotopy x σ (1, p) = x := by
  let q : coordinateSet ℝ (Fin 2) := coordinateSingle 0
  have h : integralSingularConeTriangleHomotopy x σ (1, p) =
      integralSingularConeTriangleHomotopy x σ (1, coordinateMap (0 : Fin 3).succAbove q) := by
    change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      ((coordinateHomeomorph ℝ (Fin 4)).symm (Simplex.simplexCone 2 (1, p))) =
        integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
          ((coordinateHomeomorph ℝ (Fin 4)).symm
            (Simplex.simplexCone 2 (1, coordinateMap (0 : Fin 3).succAbove q)))
    rw [Simplex.simplexCone_one, Simplex.simplexCone_one]
  rw [h, integralSingularConeTriangleHomotopy_face, integralSingularConeEdgeHomotopy_one]

end DifferentialGeometry.Topology
