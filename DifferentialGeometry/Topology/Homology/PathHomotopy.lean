/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.PathConcatenation

open AlgebraicTopology ContinuousMap Set
open scoped Simplicial

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {a b : X} {p q : Path a b}

def pathHomotopyDiagonal (F : Path.Homotopy p q) : Path a b where
  toFun t := F (t, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_id)
  source' := F.source 0
  target' := F.target 1

noncomputable def pathHomotopyLowerSimplex (F : Path.Homotopy p q) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => F (projIcc 0 1 zero_le_one (t.weights 2),
        projIcc 0 1 zero_le_one (t.weights 1 + t.weights 2)),
      F.continuous.comp
        ((continuous_projIcc.comp (Convexity.StdSimplex.continuous_weights_apply ℝ 2)).prodMk
          (continuous_projIcc.comp ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).add
            (Convexity.StdSimplex.continuous_weights_apply ℝ 2))))⟩

noncomputable def pathHomotopyUpperSimplex (F : Path.Homotopy p q) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => F (projIcc 0 1 zero_le_one (t.weights 1 + t.weights 2),
        projIcc 0 1 zero_le_one (t.weights 2)),
      F.continuous.comp
        ((continuous_projIcc.comp ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).add
          (Convexity.StdSimplex.continuous_weights_apply ℝ 2))).prodMk
          (continuous_projIcc.comp (Convexity.StdSimplex.continuous_weights_apply ℝ 2)))⟩

theorem pathHomotopyLowerSimplex_faces (F : Path.Homotopy p q) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyLowerSimplex F) =
      ![integralPathSimplex (Path.refl b), integralPathSimplex (pathHomotopyDiagonal F),
        integralPathSimplex p] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.weights 0 + t.weights 1 = 1 := t.total_fin_two
  have hp : projIcc (0 : ℝ) 1 zero_le_one (t.weights 1) = Convexity.StdSimplex.homeomorphI t :=
    projIcc_val _ (Convexity.StdSimplex.homeomorphI t)
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyLowerSimplex F)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (Convexity.StdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  have hmap := congrArg Subtype.val
    (Convexity.StdSimplex.coordinateEquiv_map i.succAbove t)
  change (Convexity.StdSimplex.map i.succAbove t).weights =
    FunOnFinite.linearMap ℝ ℝ i.succAbove t.weights at hmap
  change F (projIcc 0 1 zero_le_one
      ((Convexity.StdSimplex.map i.succAbove t).weights 2),
    projIcc 0 1 zero_le_one ((Convexity.StdSimplex.map i.succAbove t).weights 1 +
      (Convexity.StdSimplex.map i.succAbove t).weights 2)) = _
  rw [hmap]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i <;> norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff,
    ht, hp, integralPathSimplex_apply, pathHomotopyDiagonal]

theorem pathHomotopyUpperSimplex_faces (F : Path.Homotopy p q) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyUpperSimplex F) =
      ![integralPathSimplex q, integralPathSimplex (pathHomotopyDiagonal F),
        integralPathSimplex (Path.refl a)] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.weights 0 + t.weights 1 = 1 := t.total_fin_two
  have hp : projIcc (0 : ℝ) 1 zero_le_one (t.weights 1) = Convexity.StdSimplex.homeomorphI t :=
    projIcc_val _ (Convexity.StdSimplex.homeomorphI t)
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyUpperSimplex F)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (Convexity.StdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  have hmap := congrArg Subtype.val
    (Convexity.StdSimplex.coordinateEquiv_map i.succAbove t)
  change (Convexity.StdSimplex.map i.succAbove t).weights =
    FunOnFinite.linearMap ℝ ℝ i.succAbove t.weights at hmap
  change F (projIcc 0 1 zero_le_one
      ((Convexity.StdSimplex.map i.succAbove t).weights 1 +
        (Convexity.StdSimplex.map i.succAbove t).weights 2),
    projIcc 0 1 zero_le_one ((Convexity.StdSimplex.map i.succAbove t).weights 2)) = _
  rw [hmap]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i <;> norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff,
    ht, hp, integralPathSimplex_apply, pathHomotopyDiagonal]

theorem integralPathChain_sub_mem_range_of_homotopic (h : Path.Homotopic p q) :
    integralPathChain p - integralPathChain q ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  obtain ⟨F⟩ := h
  refine ⟨integralSimplexChain 2 (pathHomotopyLowerSimplex F) -
    integralSimplexChain 2 (pathHomotopyUpperSimplex F) -
    integralSimplexChain 2 (pathConcatenationSimplex (Path.refl b) (Path.refl b)) +
    integralSimplexChain 2 (pathConcatenationSimplex (Path.refl a) (Path.refl a)), ?_⟩
  simp only [map_add, map_sub, integralSimplexChain_boundary_two,
    pathHomotopyLowerSimplex_faces, pathHomotopyUpperSimplex_faces,
    pathConcatenationSimplex_faces, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Path.refl_trans_refl]
  change integralPathChain (Path.refl b) - integralPathChain (pathHomotopyDiagonal F) +
      integralPathChain p -
      (integralPathChain q - integralPathChain (pathHomotopyDiagonal F) +
        integralPathChain (Path.refl a)) -
      (integralPathChain (Path.refl b) - integralPathChain (Path.refl b) +
        integralPathChain (Path.refl b)) +
      (integralPathChain (Path.refl a) - integralPathChain (Path.refl a) +
        integralPathChain (Path.refl a)) = _
  abel

end DifferentialGeometry.Topology
