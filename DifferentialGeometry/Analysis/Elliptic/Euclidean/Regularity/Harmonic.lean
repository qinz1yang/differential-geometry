import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem matMulE_one (v : E) : DeGiorgi.matMulE 1 v = v := by
  ext i
  simp only [DeGiorgi.matMulE_apply, Matrix.one_mulVec]

private def laplaceCoeff (Ω : Set E) : DeGiorgi.EllipticCoeff d Ω where
  a := fun _ => 1
  lam := 1
  Λ := 1
  measurable_comp := fun _ _ => measurable_const
  hlam := zero_lt_one
  hΛ := le_rfl
  coercive := Filter.Eventually.of_forall fun _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]
  coercive_inv := Filter.Eventually.of_forall fun _ v => by
    rw [inv_one, one_mul, inv_one, matMulE_one, real_inner_self_eq_norm_sq]

private def laplaceForm :
    NirenbergEuclidean.SmoothEllipticBilinearForm d (Set.univ : Set E) where
  a := fun _ => 1
  c := fun _ => 0
  symm := by
    intro _ i j
    simp only [Matrix.one_apply, eq_comm]
  smooth_a := fun _ _ => contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  ellipticity_pos := zero_lt_one
  ellipticity_le_upper := le_rfl
  coercive := fun _ _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]

private theorem isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    DeGiorgi.IsSolution (laplaceCoeff Ω) u := by
  apply DeGiorgi.isHomogeneousWeakSolution_isSolution
  refine ⟨hu.memW1p, ?_⟩
  apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ (laplaceCoeff Ω)
    (fun _ => 0) (by intros; simp) (by intros; simp) 0 (by intros; simp) hu
  intro φ hφ
  simpa only [DeGiorgi.bilinFormOfCoeff, DeGiorgi.bilinFormIntegrandOfCoeff,
    laplaceCoeff, matMulE_one, DeGiorgi.smoothTestWitness] using hweak φ hφ

theorem memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero
    (k : ℕ) {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hV_compact : IsCompact (closure V)) (hV_sub : closure V ⊆ Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    MemWkp (d := d) k 2 u V := by
  exact (isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero
    hΩ hu hweak).memWkp k hΩ hV hV_compact hV_sub laplaceForm
      (rho := 1) one_ne_zero (by intros; simp only [laplaceCoeff, laplaceForm, one_mul])

theorem exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hV_compact : IsCompact (closure V)) (hV_sub : closure V ⊆ Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    ∃ v : E → ℝ, ContDiffOn ℝ (∞ : WithTop ℕ∞) v V ∧
      u =ᵐ[volume.restrict V] v := by
  exact EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hV
    (fun k => memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero
      k hΩ hV hV_compact hV_sub hu hweak)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
