import DifferentialGeometry.Topology.Homology.ThreeCycleRealization
import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.Cone

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularConeTriangleHomotopy (σ : integralSingularSimplex 2 X) :
    C(unitInterval × stdSimplex ℝ (Fin 3), X) :=
  (integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)).comp
    (Simplex.simplexCone 2)

theorem integralSingularConeTriangleHomotopy_zero (σ : integralSingularSimplex 2 X)
    (p : stdSimplex ℝ (Fin 3)) :
    integralSingularConeTriangleHomotopy x σ (0, p) =
      integralSingularSimplexEquiv 2 X σ p := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      (Simplex.simplexCone 2 (0, p)) = _
  rw [Simplex.simplexCone_zero]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTetrahedron x σ)
    (stdSimplex.map (0 : Fin 4).succAbove p) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X
    ((TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x σ)) p = _
  rw [integralSingularConeTetrahedron_face]
  rfl

private theorem simplexCone_eq_triangleJoin (t : unitInterval)
    (p : stdSimplex ℝ (Fin 2)) :
    Simplex.simplexCone 1 (t, p) =
      Simplex.triangleJoin (unitInterval.symm t, stdSimplexHomeomorphUnitInterval p) := by
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
    (i : Fin 3) (t : unitInterval) (p : stdSimplex ℝ (Fin 2)) :
    integralSingularConeTriangleHomotopy x σ (t, stdSimplex.map i.succAbove p) =
      integralSingularConeEdgeHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)
        (t, stdSimplexHomeomorphUnitInterval p) := by
  change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      (Simplex.simplexCone 2 (t, stdSimplex.map i.succAbove p)) = _
  rw [Simplex.simplexCone_map_succAbove]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTetrahedron x σ)
      (stdSimplex.map i.succ.succAbove (Simplex.simplexCone 1 (t, p))) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X
    ((TopCat.toSSet.obj (TopCat.of X)).δ i.succ (integralSingularConeTetrahedron x σ))
      (Simplex.simplexCone 1 (t, p)) = _
  rw [integralSingularConeTetrahedron_face]
  change integralSingularSimplexEquiv 2 X
    (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
      (Simplex.simplexCone 1 (t, p)) = _
  rw [simplexCone_eq_triangleJoin]
  rfl

theorem integralSingularConeTriangleHomotopy_one (σ : integralSingularSimplex 2 X)
    (p : stdSimplex ℝ (Fin 3)) : integralSingularConeTriangleHomotopy x σ (1, p) = x := by
  let q : stdSimplex ℝ (Fin 2) := stdSimplex.vertex 0
  have h : integralSingularConeTriangleHomotopy x σ (1, p) =
      integralSingularConeTriangleHomotopy x σ (1, stdSimplex.map (0 : Fin 3).succAbove q) := by
    change integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
      (Simplex.simplexCone 2 (1, p)) =
        integralSingularSimplexEquiv 3 X (integralSingularConeTetrahedron x σ)
          (Simplex.simplexCone 2 (1, stdSimplex.map (0 : Fin 3).succAbove q))
    rw [Simplex.simplexCone_one, Simplex.simplexCone_one]
  rw [h, integralSingularConeTriangleHomotopy_face, integralSingularConeEdgeHomotopy_one]

end DifferentialGeometry.Topology
