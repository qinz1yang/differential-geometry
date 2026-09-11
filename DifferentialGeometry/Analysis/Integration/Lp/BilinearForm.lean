import DifferentialGeometry.Analysis.Integration.Lp.Product
import DifferentialGeometry.Analysis.Integration.Lp.Pairing
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Ring

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {Z X : Type*} [MeasurableSpace Z] {μ : Measure Z}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem norm_double_sum_le {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    (A : ι → ι → E) (C : ι → ι → ℝ) (hA : ∀ i j, ‖A i j‖ ≤ C i j) :
    ‖∑ i, ∑ j, A i j‖ ≤ ∑ i, ∑ j, C i j := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun j _ => hA i j

private def lpMulCLM (c : Lp ℝ ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => c • f
      map_add' := fun f g => Lp.add_smul c f g
      map_smul' := fun r f => (Lp.smul_comm r c f).symm }
    ‖c‖ (fun f => Lp.norm_smul_le c f)

private theorem lpMulCLM_coeFn (c : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ) :
    (lpMulCLM c f : Z → ℝ) =ᵐ[μ] fun x => c x * f x := by
  exact Lp.coeFn_lpSMul c f

theorem exists_bilinear_integral_weight_mul_lp
    {ι : Type*} [Fintype ι]
    (D : ι → X →L[ℝ] Lp ℝ 2 μ) (c : ι → ι → Lp ℝ ∞ μ) :
    ∃ F : X →L[ℝ] X →L[ℝ] ℝ,
      (∀ u v, F u v = ∑ i, ∑ j, ∫ z, D i u z * c i j z * D j v z ∂μ) ∧
      ‖F‖ ≤ ∑ i, ∑ j, ‖c i j‖ * ‖D i‖ * ‖D j‖ := by
  let A : ι → ι → X →L[ℝ] X →L[ℝ] ℝ :=
    fun i j => (innerSL ℝ).bilinearComp ((lpMulCLM (c i j)).comp (D i)) (D j)
  let F : X →L[ℝ] X →L[ℝ] ℝ := ∑ i, ∑ j, A i j
  have hA (i j) (u v : X) : A i j u v = ∫ z, D i u z * c i j z * D j v z ∂μ := by
    change inner ℝ (lpMulCLM (c i j) (D i u)) (D j v) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMulCLM_coeFn (c i j) (D i u)] with z hz
    simp only [Real.inner_apply, hz]
    ring
  have hbound (i j) : ‖A i j‖ ≤ ‖c i j‖ * ‖D i‖ * ‖D j‖ := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
    intro u v
    change ‖inner ℝ (lpMulCLM (c i j) (D i u)) (D j v)‖ ≤ _
    calc
      _ ≤ ‖lpMulCLM (c i j) (D i u)‖ * ‖D j v‖ := norm_inner_le_norm _ _
      _ ≤ (‖c i j‖ * ‖D i u‖) * ‖D j v‖ :=
        mul_le_mul_of_nonneg_right (Lp.norm_smul_le (c i j) (D i u)) (norm_nonneg _)
      _ ≤ (‖c i j‖ * (‖D i‖ * ‖u‖)) * (‖D j‖ * ‖v‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((D i).le_opNorm u) (norm_nonneg _))
          ((D j).le_opNorm v) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨F, ?_, ?_⟩
  · intro u v
    simp only [F, sum_apply, hA]
  · change ‖∑ i, ∑ j, A i j‖ ≤ _
    exact norm_double_sum_le A (fun i j => ‖c i j‖ * ‖D i‖ * ‖D j‖) hbound

theorem exists_bilinear_integral_weight_mul_lp_family
    {ι : Type*} [Fintype ι] {τ : Measure ℝ} [SFinite μ]
    (D : ι → X →L[ℝ] Lp ℝ 2 μ) (c : ℝ → ι → ι → Lp ℝ ∞ μ)
    (hc : ∀ i j, AEStronglyMeasurable (fun p : ℝ × Z => c p.1 i j p.2) (τ.prod μ))
    {C : ℝ} (hC : ∀ᵐ t ∂τ, ∀ i j, ‖c t i j‖ ≤ C) :
    ∃ F : ℝ → X →L[ℝ] X →L[ℝ] ℝ,
      (∀ t u v, F t u v = ∑ i, ∑ j, ∫ z, D i u z * c t i j z * D j v z ∂μ) ∧
      (∀ u v, AEStronglyMeasurable (fun t => F t u v) τ) ∧
      ∀ᵐ t ∂τ, ‖F t‖ ≤ ∑ i, ∑ j, C * ‖D i‖ * ‖D j‖ := by
  classical
  choose F hF hFnorm using fun t => exists_bilinear_integral_weight_mul_lp D (c t)
  refine ⟨F, hF, ?_, ?_⟩
  · intro u v
    have hf (i j) : AEStronglyMeasurable
        (fun t => ∫ z, D i u z * c t i j z * D j v z ∂μ) τ := by
      exact (((Lp.memLp (D i u)).1.comp_snd.mul (hc i j)).mul
        (Lp.memLp (D j v)).1.comp_snd).integral_prod_right'
    simpa only [hF] using Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ => Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j _ => hf i j))
  · filter_upwards [hC] with t ht
    apply (hFnorm t).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ht i j) (norm_nonneg _)) (norm_nonneg _)

theorem exists_bilinear_integral_weight_mul_family
    {ι : Type*} [Fintype ι] {τ : Measure ℝ} [IsFiniteMeasure μ]
    (D : ι → X →L[ℝ] Lp ℝ 2 μ) (c : ℝ → ι → ι → Z → ℝ)
    (hcmem : ∀ t i j, MemLp (c t i j) ∞ μ)
    (hc : ∀ i j, AEStronglyMeasurable (fun p : ℝ × Z => c p.1 i j p.2) (τ.prod μ))
    {C : ℝ} (hC : 0 ≤ C) (hcb : ∀ᵐ t ∂τ, ∀ i j, ∀ᵐ z ∂μ, ‖c t i j z‖ ≤ C) :
    ∃ F : ℝ → X →L[ℝ] X →L[ℝ] ℝ,
      (∀ t u v, F t u v = ∑ i, ∑ j, ∫ z, D i u z * c t i j z * D j v z ∂μ) ∧
      (∀ u v, AEStronglyMeasurable (fun t => F t u v) τ) ∧
      ∀ᵐ t ∂τ, ‖F t‖ ≤ ∑ i, ∑ j, C * ‖D i‖ * ‖D j‖ := by
  classical
  let cLp : ℝ → ι → ι → Lp ℝ ∞ μ := fun t i j => (hcmem t i j).toLp (c t i j)
  choose F hF hFnorm using fun t => exists_bilinear_integral_weight_mul_lp D (cLp t)
  have hFraw (t : ℝ) (u v : X) :
      F t u v = ∑ i, ∑ j, ∫ z, D i u z * c t i j z * D j v z ∂μ := by
    apply (hF t u v).trans
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [(hcmem t i j).coeFn_toLp] with z hz
    exact congrArg (fun r : ℝ => D i u z * r * D j v z) hz
  refine ⟨F, hFraw, ?_, ?_⟩
  · intro u v
    have hf (i j) : AEStronglyMeasurable
        (fun t => ∫ z, D i u z * c t i j z * D j v z ∂μ) τ := by
      exact (((Lp.memLp (D i u)).1.comp_snd.mul (hc i j)).mul
        (Lp.memLp (D j v)).1.comp_snd).integral_prod_right'
    simpa only [hFraw] using Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ => Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j _ => hf i j))
  · filter_upwards [hcb] with t ht
    have hnorm (i j) : ‖cLp t i j‖ ≤ C := by
      have h := Lp.norm_le_of_ae_bound (f := cLp t i j) hC (by
        filter_upwards [ht i j, (hcmem t i j).coeFn_toLp] with z hz hze
        exact hze ▸ hz)
      simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using h
    apply (hFnorm t).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hnorm i j) (norm_nonneg _)) (norm_nonneg _)

theorem exists_lp_flux_of_bilinear_integral
    {A B X ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
    {μ : Measure A} {ν : Measure B} [SFinite ν]
    (D : ι → X →L[ℝ] Lp ℝ 2 ν) (c : ι → ι → A × B → ℝ)
    (hc : ∀ i j, MemLp (c i j) ∞ (μ.prod ν))
    (F : A → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ t u v, F t u v = ∑ i, ∑ j, ∫ x, D i u x * c i j (t, x) * D j v x ∂ν)
    (v : Lp X 2 μ) :
    ∃ M : ι → Lp ℝ 2 (μ.prod ν),
      (∀ j, ∀ᵐ t ∂μ, (fun x => M j (t, x)) =ᵐ[ν]
        fun x => ∑ i, c i j (t, x) * D i (v t) x) ∧
      ∀ z : Lp X 2 μ,
        Integrable (fun t => F t (v t) (z t)) μ ∧
        (∫ t, F t (v t) (z t) ∂μ) =
          ∑ j, ∫ t, ∫ x, M j (t, x) * D j (z t) x ∂ν ∂μ := by
  classical
  let U : ι → Lp ℝ 2 (μ.prod ν) := fun i =>
    Lp.uncurry ℝ (by norm_num) ((D i).compLpL 2 μ v)
  have hUs (i) : ∀ᵐ t ∂μ, (fun x => U i (t, x)) =ᵐ[ν] (D i (v t) : B → ℝ) :=
    Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num) (D i) v
  have hMp (j) : MemLp (fun p => ∑ i, c i j p * U i p) 2 (μ.prod ν) := by
    apply memLp_finsetSum
    intro i _
    exact (Lp.memLp (U i)).mul (r := 2) (hc i j)
  let M : ι → Lp ℝ 2 (μ.prod ν) := fun j => (hMp j).toLp (fun p => ∑ i, c i j p * U i p)
  have hMs (j) : ∀ᵐ t ∂μ, (fun x => M j (t, x)) =ᵐ[ν]
      fun x => ∑ i, c i j (t, x) * D i (v t) x := by
    filter_upwards [Measure.ae_ae_of_ae_prod (hMp j).coeFn_toLp,
      ae_all_iff.mpr hUs] with t ht hUt
    filter_upwards [ht, ae_all_iff.mpr hUt] with x hx hUx
    exact hx.trans (Finset.sum_congr rfl fun i _ => congrArg (fun r : ℝ => c i j (t, x) * r) (hUx i))
  refine ⟨M, hMs, ?_⟩
  intro z
  let Z : ι → Lp ℝ 2 (μ.prod ν) := fun j =>
    Lp.uncurry ℝ (by norm_num) ((D j).compLpL 2 μ z)
  have hZs (j) : ∀ᵐ t ∂μ, (fun x => Z j (t, x)) =ᵐ[ν] (D j (z t) : B → ℝ) :=
    Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num) (D j) z
  have hInt (j) : Integrable (fun p => M j p * Z j p) (μ.prod ν) :=
    (Lp.memLp (M j)).integrable_mul (Lp.memLp (Z j))
  have hinner (j) : Integrable (fun t => ∫ x, M j (t, x) * Z j (t, x) ∂ν) μ :=
    (hInt j).integral_prod_left
  have hcs : ∀ᵐ t ∂μ, ∀ i j, MemLp (fun x => c i j (t, x)) ∞ ν :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hc i j).prodMk_left_top
  have hrep : (fun t => F t (v t) (z t)) =ᵐ[μ]
      fun t => ∑ j, ∫ x, M j (t, x) * Z j (t, x) ∂ν := by
    filter_upwards [hcs, ae_all_iff.mpr hMs, ae_all_iff.mpr hZs] with t hct hMt hZt
    rw [hF, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have heq : (fun x => M j (t, x) * Z j (t, x)) =ᵐ[ν]
        fun x => ∑ i, D i (v t) x * c i j (t, x) * D j (z t) x := by
      filter_upwards [hMt j, hZt j] with x hMx hZx
      rw [hMx, hZx, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [integral_congr_ae heq]
    exact (integral_finsetSum _ (fun i _ => integrable_weight_mul_lp _ (hct i j) _ _)).symm
  refine ⟨(integrable_finsetSum _ (fun j _ => hinner j)).congr hrep.symm, ?_⟩
  rw [integral_congr_ae hrep, integral_finsetSum _ (fun j _ => hinner j)]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hZs j] with t ht
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  exact congrArg (fun r : ℝ => M j (t, x) * r) hx

theorem integral_mul_sum_norm_sq_le_bilinear
    {P X Y ι : Type*} [MeasurableSpace P] {μ : Measure P}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]
    (D : ι → X →L[ℝ] Y) (F : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C)
    {u : P → X} (hu : MemLp u 2 μ) {c : ℝ}
    (hcoerc : ∀ᵐ t ∂μ, c * ∑ i, ‖D i (u t)‖ ^ 2 ≤ F t (u t) (u t))
    {ζ : P → ℝ} (hζ : MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    c * (∫ t, ζ t * ∑ i, ‖D i (u t)‖ ^ 2 ∂μ) ≤
      ∫ t, ζ t * F t (u t) (u t) ∂μ := by
  have hD (i : ι) : Integrable (fun t => ‖D i (u t)‖ ^ 2) μ :=
    ((D i).comp_memLp' hu).integrable_norm_pow (by norm_num)
  have hsum : Integrable (fun t => ∑ i, ‖D i (u t)‖ ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => hD i)
  have hleft : Integrable (fun t => c * (ζ t * ∑ i, ‖D i (u t)‖ ^ 2)) μ :=
    (hsum.mul_of_top_right hζ).const_mul c
  have hright : Integrable (fun t => ζ t * F t (u t) (u t)) μ :=
    (integrable_bilinear_of_apply_aestronglyMeasurable F hF hC hu hu).mul_of_top_right hζ
  rw [← integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [hcoerc, hζpos] with t ht hζt
  exact (mul_left_comm c (ζ t) _).le.trans (mul_le_mul_of_nonneg_left ht hζt)



end MeasureTheory
