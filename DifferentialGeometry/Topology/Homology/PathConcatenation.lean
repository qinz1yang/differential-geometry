/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathEvaluation
import DifferentialGeometry.Topology.Simplex.Coordinates

open AlgebraicTopology ContinuousMap
open scoped Simplicial

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {a b c : X}

noncomputable def pathConcatenationSimplex (p : Path a b) (q : Path b c) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => (p.trans q).extend (t.weights 1 / 2 + t.weights 2),
      (p.trans q).continuous_extend.comp
        (((Convexity.StdSimplex.continuous_weights_apply ℝ 1).div_const 2).add
          (Convexity.StdSimplex.continuous_weights_apply ℝ 2))⟩

theorem pathConcatenationSimplex_faces (p : Path a b) (q : Path b c) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathConcatenationSimplex p q) =
      ![integralPathSimplex q, integralPathSimplex (p.trans q), integralPathSimplex p] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.weights 0 + t.weights 1 = 1 := t.total_fin_two
  have ht₀ := t.weights_nonneg 0
  have ht₁ := t.weights_nonneg 1
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathConcatenationSimplex p q)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (Convexity.StdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  have hmap := congrArg Subtype.val
    (Convexity.StdSimplex.coordinateEquiv_map i.succAbove t)
  change (Convexity.StdSimplex.map i.succAbove t).weights =
    FunOnFinite.linearMap ℝ ℝ i.succAbove t.weights at hmap
  change (p.trans q).extend
    ((Convexity.StdSimplex.map i.succAbove t).weights 1 / 2 +
      (Convexity.StdSimplex.map i.succAbove t).weights 2) = _
  rw [hmap]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    change (p.trans q).extend (t.weights 0 / 2 + t.weights 1) =
      integralSingularSimplexEquiv 1 X (integralPathSimplex q) t
    rw [integralPathSimplex_apply, Path.extend_trans_of_half_le p q (by linarith)]
    convert q.extend_apply (Convexity.StdSimplex.homeomorphI t).property using 1
    congr 1
    change 2 * (t.weights 0 / 2 + t.weights 1) - 1 = t.weights 1
    linarith
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    rw [integralPathSimplex_apply]
    rfl
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    change (p.trans q).extend (t.weights 1 / 2) =
      integralSingularSimplexEquiv 1 X (integralPathSimplex p) t
    rw [integralPathSimplex_apply, Path.extend_trans_of_le_half p q (by linarith)]
    convert p.extend_apply (Convexity.StdSimplex.homeomorphI t).property using 1
    congr 1
    change 2 * (t.weights 1 / 2) = t.weights 1
    ring

theorem pathConcatenationSimplex_boundary (p : Path a b) (q : Path b c) :
    (integralSingularChains X).d 2 1 (integralSimplexChain 2 (pathConcatenationSimplex p q)) =
      integralPathChain q - integralPathChain (p.trans q) + integralPathChain p := by
  rw [integralSimplexChain_boundary_two, pathConcatenationSimplex_faces p q 0,
    pathConcatenationSimplex_faces p q 1, pathConcatenationSimplex_faces p q 2]
  rfl

end DifferentialGeometry.Topology
