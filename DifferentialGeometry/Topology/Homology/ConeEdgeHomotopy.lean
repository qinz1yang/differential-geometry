import DifferentialGeometry.Topology.Simplex.CubeParametrization
import DifferentialGeometry.Topology.Homology.PathCones
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathEvaluation
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section
open CategoryTheory AlgebraicTopology ContinuousMap
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph coordinateHomeomorphI)
open scoped Simplicial Topology unitInterval
namespace DifferentialGeometry.Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private theorem coordinate_homeomorph_symm_face (i : Fin 3) (v : unitInterval) :
    (coordinateHomeomorph ℝ (Fin 3)).symm
      (coordinateMap i.succAbove (coordinateHomeomorphI.symm v)) =
        Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.homeomorphI.symm v) := by
  apply (coordinateHomeomorph ℝ (Fin 3)).injective
  rw [Homeomorph.apply_symm_apply]
  change _ = Convexity.StdSimplex.coordinateEquiv ℝ (Fin 3) _
  rw [Convexity.StdSimplex.coordinateEquiv_map]
  congr 1
  apply coordinateHomeomorphI.injective
  rw [Homeomorph.apply_symm_apply]
  change v = Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.homeomorphI.symm v)
  exact (Homeomorph.apply_symm_apply _ _).symm

def integralSingularConeEdgeHomotopy (a : X) (sigma : integralSingularSimplex 1 X) :
    C(unitInterval × unitInterval, X) :=
  (integralSingularSimplexEquiv 2 X (integralSingularConeTriangle a sigma)).comp
    ((⟨(coordinateHomeomorph ℝ (Fin 3)).symm,
      (coordinateHomeomorph ℝ (Fin 3)).symm.continuous⟩ :
      C(coordinateSet ℝ (Fin 3), Convexity.StdSimplex ℝ (Fin 3))).comp
        (Simplex.triangleJoin.comp ⟨fun z => (unitInterval.symm z.1, z.2), by fun_prop⟩))

theorem integralSingularConeEdgeHomotopy_zero (a : X) (sigma : integralSingularSimplex 1 X)
    (v : unitInterval) :
    integralSingularConeEdgeHomotopy a sigma (0, v) =
      integralSimplexPath sigma v := by
  simp only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    unitInterval.symm_zero]
  rw [Simplex.triangleJoin_one, coordinate_homeomorph_symm_face]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTriangle a sigma)
      (Convexity.StdSimplex.map (0 : Fin 3).succAbove (Convexity.StdSimplex.homeomorphI.symm v)) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 1 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle a sigma)) _ = _
  rw [integralSingularConeTriangle_face_zero]
  have h := integralPathSimplex_apply (integralSimplexPath sigma)
    (Convexity.StdSimplex.homeomorphI.symm v)
  rw [integralPathSimplex_simplexPath sigma, Homeomorph.apply_symm_apply] at h
  exact h

theorem integralSingularConeEdgeHomotopy_left (a : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) :
    integralSingularConeEdgeHomotopy a sigma (t, 0) =
      PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma))
        (unitInterval.symm t) := by
  simp only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Simplex.triangleJoin_second_zero, coordinate_homeomorph_symm_face]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTriangle a sigma)
      (Convexity.StdSimplex.map (2 : Fin 3).succAbove
        (Convexity.StdSimplex.homeomorphI.symm (unitInterval.symm t))) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 1 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle a sigma)) _ = _
  rw [integralSingularConeTriangle_face_two, integralPathSimplex_apply,
    Homeomorph.apply_symm_apply]

theorem integralSingularConeEdgeHomotopy_right (a : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) :
    integralSingularConeEdgeHomotopy a sigma (t, 1) =
      PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma))
        (unitInterval.symm t) := by
  simp only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Simplex.triangleJoin_second_one, coordinate_homeomorph_symm_face]
  change (TopCat.of X).toSSetObjEquiv _ (integralSingularConeTriangle a sigma)
      (Convexity.StdSimplex.map (1 : Fin 3).succAbove
        (Convexity.StdSimplex.homeomorphI.symm (unitInterval.symm t))) = _
  rw [← TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 1 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle a sigma)) _ = _
  rw [integralSingularConeTriangle_face_one, integralPathSimplex_apply,
    Homeomorph.apply_symm_apply]

theorem integralSingularConeEdgeHomotopy_one (a : X) (sigma : integralSingularSimplex 1 X)
    (v : unitInterval) :
    integralSingularConeEdgeHomotopy a sigma (1, v) = a := by
  have h : integralSingularConeEdgeHomotopy a sigma (1, v) =
      integralSingularConeEdgeHomotopy a sigma (1, 0) := by
    simp only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      unitInterval.symm_one, Simplex.triangleJoin_zero]
  rw [h, integralSingularConeEdgeHomotopy_left, unitInterval.symm_one, Path.source]

end DifferentialGeometry.Topology

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularConeEdgeHomotopy_boundary
    (x : X) (sigma : integralSingularSimplex 1 X)
    (p : coordinateSet ℝ (Fin 2)) (hp : p ∈ Simplex.boundary (Fin 2))
    (t : unitInterval) :
    integralSingularConeEdgeHomotopy x sigma (t, coordinateHomeomorphI p) =
      PathConnectedSpace.somePath x (integralSingularSimplexEquiv 1 X sigma
        ((coordinateHomeomorph ℝ (Fin 2)).symm p))
        (unitInterval.symm t) := by
  have heval (q : coordinateSet ℝ (Fin 2)) :
      integralSimplexPath sigma (coordinateHomeomorphI q) =
        integralSingularSimplexEquiv 1 X sigma
          ((coordinateHomeomorph ℝ (Fin 2)).symm q) := by
    have h := integralPathSimplex_apply (integralSimplexPath sigma)
      ((coordinateHomeomorph ℝ (Fin 2)).symm q)
    rw [integralPathSimplex_simplexPath] at h
    exact h.symm
  obtain ⟨i, hi⟩ := hp
  have hsum : p.val 0 + p.val 1 = 1 := by
    simpa only [Fin.sum_univ_two] using p.property.2
  fin_cases i
  · have he : coordinateHomeomorphI p = 1 := by
      apply Subtype.ext
      change p.val 1 = 1
      have hz : p.val 0 = 0 := by simpa using hi
      linarith
    have heq : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma) =
        integralSingularSimplexEquiv 1 X sigma
        ((coordinateHomeomorph ℝ (Fin 2)).symm p) := by
      have h := integralSingularConeEdgeHomotopy_zero x sigma 1
      rw [integralSingularConeEdgeHomotopy_right, unitInterval.symm_zero, Path.target] at h
      rw [h, ← he, heval]
    rw [he, integralSingularConeEdgeHomotopy_right, heq]
  · have he : coordinateHomeomorphI p = 0 := by
      apply Subtype.ext
      change p.val 1 = 0
      simpa using hi
    have heq : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma) =
        integralSingularSimplexEquiv 1 X sigma
        ((coordinateHomeomorph ℝ (Fin 2)).symm p) := by
      have h := integralSingularConeEdgeHomotopy_zero x sigma 0
      rw [integralSingularConeEdgeHomotopy_left, unitInterval.symm_zero, Path.target] at h
      rw [h, ← he, heval]
    rw [he, integralSingularConeEdgeHomotopy_left, heq]

end DifferentialGeometry.Topology
