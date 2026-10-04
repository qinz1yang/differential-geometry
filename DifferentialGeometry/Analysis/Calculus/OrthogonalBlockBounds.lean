import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Orthogonal square summation over finitely many blocks (SGP04, EGP06, TCP05)

Blueprint 207B, SGP04 (`thm:fibration-actual-slim-graph`, B:4602–4665), and likewise EGP06 and
TCP05: the model graph `Φ_i` is a finite orthogonal sum of blocks (the own block `(a,1)`, the listed
scaled cutoff blocks and the possible zero block), and the actual map is compared block by block.
"Orthogonal square summation proves both bounds … regardless of total target dimension": a bound
`c` on every block of a vector, a linear map, a multilinear map, a first derivative or an iterated
derivative gives `√(card ι) · c` on the assembled object in `PiLp 2`. Only the number of blocks
enters, not their dimensions.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι] {B : ι → Type*} [∀ j, NormedAddCommGroup (B j)]
  [∀ j, NormedSpace ℝ (B j)]

omit [∀ j, NormedSpace ℝ (B j)] in
theorem norm_le_sqrt_card_mul_of_blocks (v : PiLp 2 B) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖v j‖ ≤ c) : ‖v‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  rw [PiLp.norm_eq_of_L2, ← Real.sqrt_sq hc, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ j, ‖v j‖ ^ 2 ≤ ∑ _j : ι, c ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h j) 2
    _ = (Fintype.card ι : ℝ) * c ^ 2 := by simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_continuousLinearMap_le_of_blocks (A : V →L[ℝ] PiLp 2 B) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖(PiLp.proj 2 (𝕜 := ℝ) B j).comp A‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  refine A.opNorm_le_bound (by positivity) (fun v => ?_)
  rw [mul_assoc]
  refine norm_le_sqrt_card_mul_of_blocks (A v) (mul_nonneg hc (norm_nonneg v)) (fun j => ?_)
  have := ((PiLp.proj 2 (𝕜 := ℝ) B j).comp A).le_opNorm v
  exact this.trans (mul_le_mul_of_nonneg_right (h j) (norm_nonneg v))

theorem norm_continuousMultilinearMap_le_of_blocks {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) (PiLp 2 B)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖(PiLp.proj 2 (𝕜 := ℝ) B j).compContinuousMultilinearMap M‖ ≤ c) :
    ‖M‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  refine M.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [mul_assoc]
  refine norm_le_sqrt_card_mul_of_blocks (M m)
    (mul_nonneg hc (Finset.prod_nonneg fun i _ => norm_nonneg (m i))) (fun j => ?_)
  have := ((PiLp.proj 2 (𝕜 := ℝ) B j).compContinuousMultilinearMap M).le_opNorm m
  exact this.trans (mul_le_mul_of_nonneg_right (h j)
    (Finset.prod_nonneg fun i _ => norm_nonneg (m i)))

/-- First derivative of a block map from block derivative bounds. -/
theorem norm_fderiv_le_of_blocks (f : V → PiLp 2 B) {x : V} (hf : DifferentiableAt ℝ f x)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ‖fderiv ℝ (fun y => f y j) x‖ ≤ c) :
    ‖fderiv ℝ f x‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  refine norm_continuousLinearMap_le_of_blocks _ hc (fun j => ?_)
  have hcomp : (fun y => f y j) = (PiLp.proj 2 (𝕜 := ℝ) B j) ∘ f := rfl
  have hj := h j
  rw [hcomp, fderiv_comp x (PiLp.proj 2 (𝕜 := ℝ) B j).differentiableAt hf,
    ContinuousLinearMap.fderiv] at hj
  exact hj

/-- Iterated derivatives of a block map from block bounds (SGP04's first and second derivative
bounds, used as `iteratedFDeriv ℝ 2` by FC25). -/
theorem norm_iteratedFDeriv_le_of_blocks (f : V → PiLp 2 B) {N : WithTop ℕ∞} {x : V}
    (hf : ContDiffAt ℝ N f x) {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖iteratedFDeriv ℝ n (fun y => f y j) x‖ ≤ c) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  refine norm_continuousMultilinearMap_le_of_blocks _ hc (fun j => ?_)
  have hcomp : (fun y => f y j) = (PiLp.proj 2 (𝕜 := ℝ) B j) ∘ f := rfl
  have hj := h j
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf hn] at hj
  exact hj

/-- The `C¹` comparison of an actual block map with a model, block by block. -/
theorem c1_dist_le_of_blocks (F G : V → PiLp 2 B) {x : V} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) {c : ℝ} (hc : 0 ≤ c)
    (hval : ∀ j, ‖F x j - G x j‖ ≤ c)
    (hder : ∀ j, ‖fderiv ℝ (fun y => F y j) x - fderiv ℝ (fun y => G y j) x‖ ≤ c) :
    ‖F x - G x‖ ≤ Real.sqrt (Fintype.card ι) * c ∧
      ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  refine ⟨norm_le_sqrt_card_mul_of_blocks _ hc (fun j => ?_), ?_⟩
  · simpa using hval j
  · rw [← fderiv_sub hF hG]
    refine norm_fderiv_le_of_blocks _ (hF.sub hG) hc (fun j => ?_)
    have hFj : DifferentiableAt ℝ (fun y => F y j) x :=
      (PiLp.proj 2 (𝕜 := ℝ) B j).differentiableAt.comp x hF
    have hGj : DifferentiableAt ℝ (fun y => G y j) x :=
      (PiLp.proj 2 (𝕜 := ℝ) B j).differentiableAt.comp x hG
    have hsub' : (fun y => (F - G) y j) = (fun y => F y j) - (fun y => G y j) := rfl
    rw [hsub', fderiv_sub hFj hGj]
    exact hder j

end DifferentialGeometry.Analysis
