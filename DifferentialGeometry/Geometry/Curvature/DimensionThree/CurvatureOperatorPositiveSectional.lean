import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBasis
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree
open scoped MatrixOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem diagonal_rank_three_nonzero (d : Fin 3 → Real)
    (h : (Matrix.diagonal d).rank = 3) : ∀ i, d i ≠ 0 := by
  intro i hi
  have hcard : Fintype.card {j : Fin 3 // d j ≠ 0} = 3 := by
    have hh := h
    rw [Matrix.rank_diagonal] at hh
    exact_mod_cast hh
  have hcomp : Fintype.card {j : Fin 3 // ¬ d j ≠ 0} =
      3 - Fintype.card {j : Fin 3 // d j ≠ 0} := by
    simpa using (Fintype.card_subtype_compl (p := fun j : Fin 3 => d j ≠ 0))
  have hnonempty : Fintype.card {j : Fin 3 // ¬ d j ≠ 0} ≥ 1 := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨i, by simp [hi]⟩⟩
  omega

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hrank : metricCurvatureOperatorRankAt (I := I) g x hdim = 3)
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ v w : TangentSpace I x,
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  let Rmat : Matrix (Fin 3) (Fin 3) Real :=
    curvatureOperatorMatrixAt (I := I) x basis
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x)
  have hRmat : Rmat = curvatureOperatorDiagonal3
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) := by
    exact metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
        ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) hdiag
  have hRrank : Rmat.rank = 3 := by
    calc
      Rmat.rank = metricCurvatureOperatorRankAt (I := I) g x hdim := by
        symm
        exact metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
          (I := I) (M := M) g x hdim basis horth
      _ = 3 := hrank
  have hsectionalCone :=
    algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone hcone
  have hsectional :=
    (mem_algebraicSectionalNonnegativeCone.mp hsectionalCone)
  have hdiag_nonneg : ∀ i, 0 ≤ Rmat i i := by
    intro i
    fin_cases i
    · have hh := hsectional (basis 0) (basis 1)
      change 0 ≤ Rmat 0 0
      change 0 ≤ tensor04SectionalEval (I := I) (M := M)
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x)
        (basis 0) (basis 1)
      exact hh
    · have hh := hsectional (basis 0) (basis 2)
      change 0 ≤ Rmat 1 1
      change 0 ≤ tensor04SectionalEval (I := I) (M := M)
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x)
        (basis 0) (basis 2)
      exact hh
    · have hh := hsectional (basis 1) (basis 2)
      change 0 ≤ Rmat 2 2
      change 0 ≤ tensor04SectionalEval (I := I) (M := M)
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x)
        (basis 1) (basis 2)
      exact hh
  have hdiag_eq : Rmat = Matrix.diagonal (fun i => Rmat i i) := by
    rw [hRmat]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [curvatureOperatorDiagonal3]
  have hdiag_ne : ∀ i, Rmat i i ≠ 0 := by
    intro i hi
    have hdiag_rank : (Matrix.diagonal (fun j => Rmat j j)).rank = 3 := by
      rw [← hdiag_eq]
      exact hRrank
    have hdiag_ne' : ∀ j, Rmat j j ≠ 0 :=
      diagonal_rank_three_nonzero (fun j => Rmat j j) hdiag_rank
    exact hdiag_ne' i hi
  have hdiag_pos : ∀ i, 0 < Rmat i i := fun i =>
    lt_of_le_of_ne (hdiag_nonneg i) (Ne.symm (hdiag_ne i))
  have hRmat_posDef : Rmat.PosDef := by
    rw [hdiag_eq]
    apply Matrix.PosDef.diagonal
    intro i
    exact hdiag_pos i
  intro v w hvw
  have hTensor_mem : fiberOperatorTensor (I := I) g basis Rmat ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
    have hsymm : Rmat.IsSymm := by
      rw [hRmat]
      exact Matrix.isSymm_diagonal _
    exact fiberOperatorTensor_mem_algebraic (I := I) g basis hsymm
  have hTensor_map : tensor04CurvatureOperatorMatrixAt (I := I) basis
      (fiberOperatorTensor (I := I) g basis Rmat) = Rmat :=
    tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor (I := I) g basis horth Rmat
  have hTensor_eq : fiberOperatorTensor (I := I) g basis Rmat =
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x) := by
    have hzero : (⟨fiberOperatorTensor (I := I) g basis Rmat, hTensor_mem⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) -
        metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x = 0 := by
      apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal
        (I := I) (M := M) g x basis horth
      change tensor04CurvatureOperatorMatrixAt (I := I) basis
          (fiberOperatorTensor (I := I) g basis Rmat -
            (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x)) = 0
      rw [tensor04CurvatureOperatorMatrixAt_sub, hTensor_map]
      change Rmat - curvatureOperatorMatrixAt (I := I) x basis
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) = 0
      simp only [Rmat]
      exact sub_self _
    exact congrArg (fun Y : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      (Y : Tensor04At (I := I) (M := M) x)) (sub_eq_zero.mp hzero)
  let a : Fin 3 → Real := fun p =>
    fiberBivectorTwoForm (I := I) g basis p v w
  let G : Matrix (Fin 2) (Fin 2) Real := fun i j =>
    g.inner x (vec2 (I := I) v w i) (vec2 (I := I) v w j)
  have hGherm : G.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact g.symm x (vec2 (I := I) v w j) (vec2 (I := I) v w i)
  have hGpos : G.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hGherm
    intro c hc
    let u : TangentSpace I x := ∑ i : Fin 2, c i • vec2 (I := I) v w i
    have hu : u ≠ 0 := by
      intro hu
      have hc0 : ∀ i : Fin 2, c i = 0 := by
        intro i
        apply (Fintype.linearIndependent_iff.mp hvw c ?_) i
        simpa [u] using hu
      exact hc (funext hc0)
    have hposu : 0 < g.inner x u u := g.pos x u hu
    convert hposu using 1 <;> try rfl
    simp only [dotProduct, Matrix.mulVec, G, star_trivial]
    simp [u, vec2]
    ring
  have hsum_sq : 0 < ∑ p : Fin 3, a p * a p := by
    rw [show (∑ p : Fin 3, a p * a p) =
      ∑ p : Fin 3, fiberBivectorTwoForm (I := I) g basis p v w *
        fiberBivectorTwoForm (I := I) g basis p v w by rfl]
    rw [fiberBivectorTwoForm_sum_pair (I := I) g basis horth v w v w]
    have hgram := hGpos.det_pos
    rw [Matrix.det_fin_two] at hgram
    simp [G, vec2] at hgram
    linarith
  have ha : a ≠ 0 := by
    intro hz
    have : (∑ p : Fin 3, a p * a p) = 0 := by simp [hz]
    linarith
  have hquad := hRmat_posDef.dotProduct_mulVec_pos ha
  rw [metricRm04StdAt_apply]
  change 0 < (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x : Tensor04At x)
    (vec4 v w w v)
  rw [← hTensor_eq]
  change 0 < tensor04StdAt (I := I) (M := M)
    (fiberOperatorTensor (I := I) g basis Rmat) v w w v
  rw [fiberOperatorTensor_apply]
  have hsumform :
      dotProduct (star a) (Matrix.mulVec Rmat a) =
        ∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * a p * a q := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [← hsumform]
  exact hquad

end DifferentialGeometry.Geometry
