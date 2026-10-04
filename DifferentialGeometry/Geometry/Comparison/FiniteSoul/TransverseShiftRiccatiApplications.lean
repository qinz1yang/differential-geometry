import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftRiccati
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart
import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.GlobalExistence

/-!
# The S3-SHIFT kernel for vector solutions (consumer of `norm_apply_le_of_jacobi_operator`)

`norm_le_of_jacobi_vector`: if `R` is continuous on `ℝ` and, on the uniform interval `[0, ρ]`
(`Λ ρ² ≤ 1/4`), self-adjoint, positive semidefinite and bounded by `Λ`, then every solution of
`z'' = −R z` with `z'(0) = 0` satisfies `‖z t‖ ≤ ‖z 0‖` on `[0, ρ]`. The matrix solution `Y` is produced
by the tree's linear ODE existence (`hasLinearODESolution_of_continuousOn`), `z = Y (z 0)` by uniqueness
(`eqOn_Icc_of_hasDerivWithinAt_linear`), and the kernel bounds `Y`. This is the form used by the
general-dimension transverse shift (frame coordinates of a Jacobi field).

The verbatim frozen statement of the kernel (with the unused `ContinuousOn R`) is an `example` below.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped InnerProductSpace NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The first-order system of `Y'' = −R Y` on pairs of operators: `(P, Q) ↦ (Q, −R P)`. -/
def jacobiSystemOp (S : F →L[ℝ] F) :
    ((F →L[ℝ] F) × (F →L[ℝ] F)) →L[ℝ] ((F →L[ℝ] F) × (F →L[ℝ] F)) :=
  (ContinuousLinearMap.snd ℝ (F →L[ℝ] F) (F →L[ℝ] F)).prod
    (-((ContinuousLinearMap.compL ℝ F F F S).comp
      (ContinuousLinearMap.fst ℝ (F →L[ℝ] F) (F →L[ℝ] F))))

/-- The first-order system of `z'' = −R z` on pairs of vectors: `(x, y) ↦ (y, −R x)`. -/
def jacobiSystemVec (S : F →L[ℝ] F) : (F × F) →L[ℝ] (F × F) :=
  (ContinuousLinearMap.snd ℝ F F).prod (-(S.comp (ContinuousLinearMap.fst ℝ F F)))

theorem jacobiSystemOp_apply (S : F →L[ℝ] F) (P Q : F →L[ℝ] F) :
    jacobiSystemOp S (P, Q) = (Q, -(S.comp P)) :=
  rfl

theorem jacobiSystemVec_apply (S : F →L[ℝ] F) (x y : F) :
    jacobiSystemVec S (x, y) = (y, -(S x)) :=
  rfl

theorem continuous_jacobiSystemOp {R : ℝ → F →L[ℝ] F} (hR : Continuous R) :
    Continuous fun t => jacobiSystemOp (R t) := by
  have h2 : Continuous fun t => -((ContinuousLinearMap.compL ℝ F F F (R t)).comp
      (ContinuousLinearMap.fst ℝ (F →L[ℝ] F) (F →L[ℝ] F))) :=
    (((ContinuousLinearMap.compL ℝ F F F).continuous.comp hR).clm_comp continuous_const).neg
  exact (ContinuousLinearMap.prodL ℝ).continuous.comp (continuous_const.prodMk h2)

theorem norm_jacobiSystemVec_le {S : F →L[ℝ] F} {Λ : ℝ} (hS : ‖S‖ ≤ Λ) :
    ‖jacobiSystemVec S‖ ≤ 1 + Λ := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hS
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  rw [jacobiSystemVec, ContinuousLinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖(ContinuousLinearMap.snd ℝ F F) p‖ = ‖p.2‖ := rfl
      _ ≤ ‖p‖ := norm_snd_le p
      _ ≤ (1 + Λ) * ‖p‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  · calc ‖(-(S.comp (ContinuousLinearMap.fst ℝ F F))) p‖ = ‖S p.1‖ := by
          rw [neg_apply, norm_neg]; rfl
      _ ≤ ‖S‖ * ‖p.1‖ := S.le_opNorm _
      _ ≤ Λ * ‖p‖ := mul_le_mul hS (norm_fst_le p) (norm_nonneg _) hΛ
      _ ≤ (1 + Λ) * ‖p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

variable [FiniteDimensional ℝ F]

/-- **The kernel for vector solutions.** -/
theorem norm_le_of_jacobi_vector {R : ℝ → F →L[ℝ] F} {Λ ρ : ℝ} (hρ : 0 < ρ) (hΛ : 0 ≤ Λ)
    (hΛρ : Λ * ρ ^ 2 ≤ 1 / 4) (hRc : Continuous R) (hRsa : ∀ t ∈ Icc 0 ρ, IsSelfAdjoint (R t))
    (hRpos : ∀ t ∈ Icc 0 ρ, ∀ a : F, 0 ≤ ⟪R t a, a⟫_ℝ) (hRbd : ∀ t ∈ Icc 0 ρ, ‖R t‖ ≤ Λ)
    {z z' : ℝ → F} (hz : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt z (z' t) (Icc 0 ρ) t)
    (hz' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt z' (-(R t (z t))) (Icc 0 ρ) t) (hz'0 : z' 0 = 0) :
    ∀ t ∈ Icc 0 ρ, ‖z t‖ ≤ ‖z 0‖ := by
  -- the matrix solution
  obtain ⟨Z, hZ0, hZ⟩ := DifferentialGeometry.Analysis.ODE.Flow.hasLinearODESolution_of_continuousOn
    (A := fun (_ : ℝ) t => jacobiSystemOp (R t)) (h₀ := 0)
    (Z₀ := fun _ => ((1 : F →L[ℝ] F), (0 : F →L[ℝ] F))) (a := -1) (b := ρ + 1)
    ⟨by norm_num, by linarith⟩ (U := univ)
    ((continuous_jacobiSystemOp hRc).comp continuous_snd).continuousOn (mem_univ (0 : ℝ))
  have hsub : Icc 0 ρ ⊆ Ioo (-1) (ρ + 1) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hZd : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Z (jacobiSystemOp (R t) (Z t)) (Icc 0 ρ) t :=
    fun t ht => (hZ t (hsub ht)).hasDerivWithinAt
  have hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt (fun τ => (Z τ).1) (Z t).2 (Icc 0 ρ) t := fun t ht =>
    (ContinuousLinearMap.fst ℝ (F →L[ℝ] F) (F →L[ℝ] F)).hasFDerivAt.comp_hasDerivWithinAt t (hZd t ht)
  have hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt (fun τ => (Z τ).2) (-((R t).comp (Z t).1))
      (Icc 0 ρ) t := fun t ht =>
    (ContinuousLinearMap.snd ℝ (F →L[ℝ] F) (F →L[ℝ] F)).hasFDerivAt.comp_hasDerivWithinAt t (hZd t ht)
  have hker := norm_apply_le_of_jacobi_operator hρ hΛ hΛρ hY hY' (congrArg Prod.fst hZ0)
    (congrArg Prod.snd hZ0) hRsa hRpos hRbd
  -- uniqueness: `(z, z') = (Y (z 0), Y' (z 0))`
  set a := z 0 with ha
  have hw₁ : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt (fun τ => (z τ, z' τ))
      (jacobiSystemVec (R t) (z t, z' t)) (Icc 0 ρ) t := fun t ht => (hz t ht).prodMk (hz' t ht)
  have hw₂ : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt (fun τ => ((Z τ).1 a, (Z τ).2 a))
      (jacobiSystemVec (R t) ((Z t).1 a, (Z t).2 a)) (Icc 0 ρ) t := fun t ht =>
    (hasDerivWithinAt_clm_apply_const (hY t ht) a).prodMk
      (hasDerivWithinAt_clm_apply_const (hY' t ht) a)
  have hK : ∀ t ∈ Icc 0 ρ, ‖jacobiSystemVec (R t)‖ ≤ ((⟨1 + Λ, by positivity⟩ : ℝ≥0) : ℝ) :=
    fun t ht => norm_jacobiSystemVec_le (hRbd t ht)
  have h0 : (0 : ℝ) ∈ Icc 0 ρ := ⟨le_rfl, hρ.le⟩
  have heq := eqOn_Icc_of_hasDerivWithinAt_linear hK
    (fun t ht => (hw₁ t ht).continuousWithinAt) (fun t ht => (hw₂ t ht).continuousWithinAt)
    hw₁ hw₂ h0 (by
      have h1 : (Z 0).1 = 1 := congrArg Prod.fst hZ0
      have h2 : (Z 0).2 = 0 := congrArg Prod.snd hZ0
      simp only [h1, h2, one_apply_eq_self, zero_apply, hz'0, ← ha])
  intro t ht
  have h := congrArg Prod.fst (heq ht)
  simp only at h
  rw [h]
  exact (hker t ht).2 a

/-- The frozen statement of the S3-SHIFT kernel, verbatim (`hRc` is not needed). -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {Y Y' R : ℝ → F →L[ℝ] F} {Λ ρ : ℝ} (hρ : 0 < ρ) (hΛ : 0 ≤ Λ)
    (hΛρ : Λ * ρ ^ 2 ≤ 1 / 4)
    (hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y (Y' t) (Icc 0 ρ) t)
    (hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y' (-((R t).comp (Y t))) (Icc 0 ρ) t)
    (hY0 : Y 0 = 1) (hY'0 : Y' 0 = 0) (_hRc : ContinuousOn R (Icc 0 ρ))
    (hRsa : ∀ t ∈ Icc 0 ρ, IsSelfAdjoint (R t)) (hRpos : ∀ t ∈ Icc 0 ρ, ∀ a : F, 0 ≤ ⟪R t a, a⟫_ℝ)
    (hRbd : ∀ t ∈ Icc 0 ρ, ‖R t‖ ≤ Λ) :
    ∀ t ∈ Icc 0 ρ, IsUnit (Y t) ∧ ∀ a : F, ‖Y t a‖ ≤ ‖a‖ :=
  norm_apply_le_of_jacobi_operator hρ hΛ hΛρ hY hY' hY0 hY'0 hRsa hRpos hRbd

/-- Example: a constant nonnegative scalar curvature `k` with `k ρ² ≤ 1/4` (the operator `k • 1`). -/
example {k ρ : ℝ} (hρ : 0 < ρ) (hk : 0 ≤ k) (hkρ : k * ρ ^ 2 ≤ 1 / 4) {z z' : ℝ → F}
    (hz : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt z (z' t) (Icc 0 ρ) t)
    (hz' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt z' (-(k • z t)) (Icc 0 ρ) t) (hz'0 : z' 0 = 0) :
    ∀ t ∈ Icc 0 ρ, ‖z t‖ ≤ ‖z 0‖ := by
  have hsa : IsSelfAdjoint (k • (1 : F →L[ℝ] F)) :=
    (IsSelfAdjoint.all k).smul (IsSelfAdjoint.one (F →L[ℝ] F))
  refine norm_le_of_jacobi_vector (R := fun _ => k • (1 : F →L[ℝ] F)) (Λ := k) hρ hk hkρ
    continuous_const (fun _ _ => hsa) (fun _ _ a => ?_) (fun _ _ => ?_) hz (fun t ht => ?_) hz'0
  · simp only [smul_apply, one_apply_eq_self, real_inner_smul_left]
    exact mul_nonneg hk real_inner_self_nonneg
  · exact (norm_smul_le k (1 : F →L[ℝ] F)).trans (by
      rw [Real.norm_of_nonneg hk]
      exact mul_le_of_le_one_right hk ContinuousLinearMap.norm_id_le)
  · simpa only [smul_apply, one_apply_eq_self] using hz' t ht

end DifferentialGeometry.Geometry.FiniteSoul
