import DifferentialGeometry.Topology.Homotopy.TriangleBoundaryQuotient
import Mathlib.Topology.Path



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q] {a b c : Q}


def triangleBoundaryPaths (p : Path a b) (q : Path b c) (r : Path a c) :
    C(Fin 3 × unitInterval, Q) :=
  (⟨![q.toContinuousMap, r.toContinuousMap, p.toContinuousMap], continuous_of_discreteTopology⟩ :
    C(Fin 3, C(unitInterval, Q))).uncurry



theorem triangleBoundaryPaths_fiber (p : Path a b) (q : Path b c) (r : Path a c)
    {z w : Fin 3 × unitInterval} (h : triangleBoundaryProjection z = triangleBoundaryProjection w) :
    triangleBoundaryPaths p q r z = triangleBoundaryPaths p q r w := by
  rcases z with ⟨i, s⟩
  rcases w with ⟨j, t⟩
  have he : planeTriangleEdgeValue i s = planeTriangleEdgeValue j t := congrArg Subtype.val h
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases i <;> fin_cases j <;> norm_num [planeTriangleEdgeValue] at hre him
  · change q s = q t
    exact congrArg q (Subtype.ext him)
  · change q s = r t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; simp only [hs] at hre him; linarith only [hre, him])
    simp [hs, ht]
  · change q s = p t
    have hs : s = 0 := him
    have hsR : (s : ℝ) = 0 := congrArg Subtype.val hs
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith only [hre, hsR])
    simp [hs, ht]
  · change r s = q t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; simp only [hs] at hre him; linarith only [hre, him])
    simp [hs, ht]
  · change r s = r t
    exact congrArg r (Subtype.ext him)
  · change r s = p t
    have hs : s = 0 := by assumption
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = q t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = r t
    have hs : s = 0 := by assumption
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = p t
    exact congrArg p (Subtype.ext hre)


def triangleBoundaryMap (p : Path a b) (q : Path b c) (r : Path a c) :
    C(frontier planeTriangle, Q) := by
  let j := Function.surjInv triangleBoundaryProjection_surjective
  let F : frontier planeTriangle → Q := fun z => triangleBoundaryPaths p q r (j z)
  have he : F ∘ triangleBoundaryProjection = triangleBoundaryPaths p q r := by
    funext z
    exact triangleBoundaryPaths_fiber p q r
      (Function.surjInv_eq triangleBoundaryProjection_surjective (triangleBoundaryProjection z))
  exact ⟨F, triangleBoundaryProjection_isQuotientMap.continuous_iff.mpr
    (he.symm ▸ (triangleBoundaryPaths p q r).continuous)⟩


theorem triangleBoundaryMap_edge (p : Path a b) (q : Path b c) (r : Path a c)
    (i : Fin 3) (s : unitInterval) :
    triangleBoundaryMap p q r (planeTriangleEdge i s) = triangleBoundaryPaths p q r (i, s) :=
  triangleBoundaryPaths_fiber p q r
    (Function.surjInv_eq triangleBoundaryProjection_surjective (triangleBoundaryProjection (i, s)))

end DifferentialGeometry.Topology
