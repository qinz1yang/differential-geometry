import DifferentialGeometry.Geometry.Collapse.FiniteBlockMap
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false

/-!
# Derivative bound from active blocks (FC02)

Blueprint 207B, `lem:fibration-active-derivative` (FC02, B:138). For the finite block map of
FC01 on a normed source (the tangent space with the original metric norm), the derivative is
bounded by `(Λ² + N B² + B_E²)^{1/2}`, independently of the total number of blocks: at most `N`
constant-radius supports contain the point, the scale block contributes `Λ`, and the single
variable-radius `E'` block contributes `B_E = a_E + (C_E + 1)(b_E + Λ)`.
-/

open Set Filter Function
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The derivative of one block `y ↦ ((R ζ) η, R ζ)` at a point, from the derivatives of its
three factors. -/
noncomputable def blockDeriv (r z : ℝ) (v : W) (dR dζ : E →L[ℝ] ℝ) (dη : E →L[ℝ] W) :
    E →L[ℝ] WithLp 2 (W × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ W ℝ).symm : (W × ℝ) →L[ℝ] WithLp 2 (W × ℝ)).comp
    (((r * z) • dη + (r • dζ + z • dR).smulRight v).prod (r • dζ + z • dR))

theorem hasFDerivAt_block {R ζ : E → ℝ} {η : E → W} {x : E} {dR dζ : E →L[ℝ] ℝ}
    {dη : E →L[ℝ] W} (hR : HasFDerivAt R dR x) (hζ : HasFDerivAt ζ dζ x)
    (hη : HasFDerivAt η dη x) :
    HasFDerivAt (fun y => WithLp.toLp 2 ((R y * ζ y) • η y, R y * ζ y))
      (blockDeriv (R x) (ζ x) (η x) dR dζ dη) x := by
  have hm : HasFDerivAt (fun y => R y * ζ y) (R x • dζ + ζ x • dR) x := hR.mul hζ
  have hv : HasFDerivAt (fun y => (R y * ζ y) • η y)
      ((R x * ζ x) • dη + (R x • dζ + ζ x • dR).smulRight (η x)) x := hm.smul hη
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ W ℝ).symm :
    (W × ℝ) →L[ℝ] WithLp 2 (W × ℝ)).hasFDerivAt.comp x (hv.prodMk hm)

omit [InnerProductSpace ℝ W] in
private theorem norm_toLp_prod_le (v : W) (t : ℝ) :
    ‖(WithLp.toLp 2 (v, t) : WithLp 2 (W × ℝ))‖ ≤ ‖v‖ + |t| := by
  rw [WithLp.prod_norm_eq_of_L2, Real.sqrt_le_left (by positivity)]
  have h1 : (WithLp.toLp 2 (v, t) : WithLp 2 (W × ℝ)).fst = v := rfl
  have h2 : (WithLp.toLp 2 (v, t) : WithLp 2 (W × ℝ)).snd = t := rfl
  rw [h1, h2, Real.norm_eq_abs]
  nlinarith [norm_nonneg v, abs_nonneg t, sq_abs t]

/-- The single-block product-rule estimate: `‖D(block)‖ ≤ a + (C + 1)(b + λ)`. -/
theorem norm_blockDeriv_apply_le {r z : ℝ} {v : W} {dR dζ : E →L[ℝ] ℝ} {dη : E →L[ℝ] W}
    {a b C l : ℝ} (hr : 0 ≤ r) (hz : z ∈ Icc (0 : ℝ) 1) (hv : ‖v‖ ≤ C)
    (ha : r * ‖dη‖ ≤ a) (hb : r * ‖dζ‖ ≤ b) (hl : ‖dR‖ ≤ l) (h : E) :
    ‖blockDeriv r z v dR dζ dη h‖ ≤ (a + (C + 1) * (b + l)) * ‖h‖ := by
  have hC : 0 ≤ C := (norm_nonneg v).trans hv
  have hm : |(r • dζ + z • dR) h| ≤ (b + l) * ‖h‖ := by
    have h1 : |(r • dζ + z • dR) h| ≤ r * (‖dζ‖ * ‖h‖) + z * (‖dR‖ * ‖h‖) := by
      simp only [add_apply, smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hr]
        exact mul_le_mul_of_nonneg_left (by simpa using dζ.le_opNorm h) hr
      · rw [abs_mul, abs_of_nonneg hz.1]
        exact mul_le_mul_of_nonneg_left (by simpa using dR.le_opNorm h) hz.1
    have h2 : z * (‖dR‖ * ‖h‖) ≤ l * ‖h‖ := by
      calc z * (‖dR‖ * ‖h‖) ≤ 1 * (l * ‖h‖) :=
            mul_le_mul hz.2 (mul_le_mul_of_nonneg_right hl (norm_nonneg h))
              (by positivity) zero_le_one
        _ = l * ‖h‖ := one_mul _
    have h3 : r * (‖dζ‖ * ‖h‖) ≤ b * ‖h‖ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hb (norm_nonneg h)
    nlinarith
  have hvec : ‖((r * z) • dη + (r • dζ + z • dR).smulRight v) h‖ ≤
      a * ‖h‖ + C * ((b + l) * ‖h‖) := by
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hz.1)]
      calc r * z * ‖dη h‖ ≤ r * 1 * (‖dη‖ * ‖h‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hz.2 hr) (dη.le_opNorm h) (norm_nonneg _)
              (by positivity)
        _ ≤ a * ‖h‖ := by
            rw [mul_one, ← mul_assoc]; exact mul_le_mul_of_nonneg_right ha (norm_nonneg h)
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul hv hm (abs_nonneg _) hC
  calc ‖blockDeriv r z v dR dζ dη h‖
      ≤ ‖((r * z) • dη + (r • dζ + z • dR).smulRight v) h‖ + |(r • dζ + z • dR) h| := by
        simpa [blockDeriv] using norm_toLp_prod_le _ _
    _ ≤ a * ‖h‖ + C * ((b + l) * ‖h‖) + (b + l) * ‖h‖ := add_le_add hvec hm
    _ = (a + (C + 1) * (b + l)) * ‖h‖ := by ring

section Assembly

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

omit [Fintype κ] in
/-- Outside the closed support of its cutoff a block is locally zero. -/
theorem hasFDerivAt_blockMap_apply_of_notMem_tsupport {R ζ : κ → E → ℝ} {η : ∀ i, E → V i}
    {i : κ} {y : E} (hy : y ∉ tsupport (ζ i)) :
    HasFDerivAt (fun x => blockMap R ζ η x i) (0 : E →L[ℝ] WithLp 2 (V i × ℝ)) y := by
  have hev : (fun x => blockMap R ζ η x i) =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport (ζ i)).isOpen_compl.mem_nhds hy] with x hx
    rw [blockMap_apply, image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_smul]
    rfl
  exact (hasFDerivAt_const 0 y).congr_of_eventuallyEq hev

/-- **FC02** (derivative bound from active blocks), on a normed source: with at most `N`
constant-radius supports at each point, the derivative of the whole block map is bounded by
`(Λ² + N B² + B_E²)^{1/2}`, `B_E = a_E + (C_E + 1)(b_E + Λ)`, independently of the number of
blocks. The scale tag `iρ` is the block `(0, ρ)`; the `E'` tag `iE` has radius `ρ`. -/
theorem norm_fderiv_blockMap_le {R ζ : κ → E → ℝ} {η : ∀ i, E → V i} {U : κ → Set E}
    {ρ : E → ℝ} (iρ iE : κ) (hρE : iρ ≠ iE) (hU : ∀ i, IsOpen (U i))
    (hsupp : ∀ i, tsupport (ζ i) ⊆ U i) (hη : ∀ i, DifferentiableOn ℝ (η i) (U i))
    (hζd : ∀ i, Differentiable ℝ (ζ i)) (hζv : ∀ i y, ζ i y ∈ Icc (0 : ℝ) 1)
    (hρd : Differentiable ℝ ρ) (hρ0 : ∀ y, 0 ≤ ρ y) {Λ : ℝ} (hΛ : ∀ y, ‖fderiv ℝ ρ y‖ ≤ Λ)
    (hRρ : R iρ = ρ) (hζρ : ζ iρ = fun _ => 1) (hηρ : η iρ = fun _ => 0) (hRE : R iE = ρ)
    (rad : κ → ℝ) (hrad : ∀ i, 0 ≤ rad i)
    (hconst : ∀ i, i ≠ iρ → i ≠ iE → R i = fun _ => rad i) {N : ℕ}
    (hcount : ∀ y, {i | i ≠ iρ ∧ i ≠ iE ∧ y ∈ tsupport (ζ i)}.ncard ≤ N)
    {a b C : κ → ℝ} {B : ℝ}
    (hblock : ∀ i, i ≠ iρ → i ≠ iE → ∀ y ∈ tsupport (ζ i), ‖η i y‖ ≤ C i ∧
      rad i * ‖fderiv ℝ (η i) y‖ ≤ a i ∧ rad i * ‖fderiv ℝ (ζ i) y‖ ≤ b i)
    (hB : ∀ i, i ≠ iρ → i ≠ iE → a i + (C i + 1) * b i ≤ B)
    {aE bE CE : ℝ} (haE : 0 ≤ aE) (hbE : 0 ≤ bE) (hCE : 0 ≤ CE)
    (hE : ∀ y ∈ tsupport (ζ iE), ‖η iE y‖ ≤ CE ∧ ρ y * ‖fderiv ℝ (η iE) y‖ ≤ aE ∧
      ρ y * ‖fderiv ℝ (ζ iE) y‖ ≤ bE) (y : E) :
    ‖fderiv ℝ (blockMap R ζ η) y‖ ≤
      Real.sqrt (Λ ^ 2 + N * B ^ 2 + (aE + (CE + 1) * (bE + Λ)) ^ 2) := by
  classical
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ y)
  set BE : ℝ := aE + (CE + 1) * (bE + Λ) with hBE
  have hBE0 : 0 ≤ BE := by positivity
  let bv : κ → ℝ := fun i => if i = iρ then Λ else if i = iE then BE else
    if y ∈ tsupport (ζ i) then B else 0
  have hD : ∀ i, ∃ D : E →L[ℝ] WithLp 2 (V i × ℝ),
      HasFDerivAt (fun x => blockMap R ζ η x i) D y ∧ ∀ h, ‖D h‖ ≤ bv i * ‖h‖ := by
    intro i
    by_cases hiρ : i = iρ
    · subst hiρ
      refine ⟨blockDeriv (ρ y) 1 0 (fderiv ℝ ρ y) 0 0, ?_, fun h => ?_⟩
      · have := hasFDerivAt_block (W := V i) (hρd y).hasFDerivAt
          (hasFDerivAt_const (1 : ℝ) y) (hasFDerivAt_const (0 : V i) y)
        convert this using 2 with x
        simp only [blockMap_apply, hRρ, hζρ, hηρ]
      · have := norm_blockDeriv_apply_le (W := V i) (v := 0) (dζ := 0) (dη := 0) (a := 0) (b := 0)
          (C := 0) (hρ0 y) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp) (by simp) (by simp)
          (hΛ y) h
        simpa [bv] using this
    by_cases hiE : i = iE
    · subst hiE
      by_cases hy : y ∈ tsupport (ζ i)
      · obtain ⟨hC, ha, hb⟩ := hE y hy
        have hηy : HasFDerivAt (η i) (fderiv ℝ (η i) y) y :=
          ((hη i).differentiableAt ((hU i).mem_nhds (hsupp i hy))).hasFDerivAt
        refine ⟨blockDeriv (ρ y) (ζ i y) (η i y) (fderiv ℝ ρ y) (fderiv ℝ (ζ i) y)
          (fderiv ℝ (η i) y), ?_, fun h => ?_⟩
        · have := hasFDerivAt_block (hρd y).hasFDerivAt (hζd i y).hasFDerivAt hηy
          convert this using 2 with x
          simp only [blockMap_apply, hRE]
        · have := norm_blockDeriv_apply_le (hρ0 y) (hζv i y) hC ha hb (hΛ y) h
          simpa [bv, hρE.symm] using this
      · refine ⟨0, hasFDerivAt_blockMap_apply_of_notMem_tsupport hy, fun h => ?_⟩
        rw [show (0 : E →L[ℝ] WithLp 2 (V i × ℝ)) h = 0 from rfl, norm_zero]
        have : bv i = BE := by simp [bv, hρE.symm]
        rw [this]
        positivity
    by_cases hy : y ∈ tsupport (ζ i)
    · obtain ⟨hC, ha, hb⟩ := hblock i hiρ hiE y hy
      have hηy : HasFDerivAt (η i) (fderiv ℝ (η i) y) y :=
        ((hη i).differentiableAt ((hU i).mem_nhds (hsupp i hy))).hasFDerivAt
      refine ⟨blockDeriv (rad i) (ζ i y) (η i y) 0 (fderiv ℝ (ζ i) y) (fderiv ℝ (η i) y), ?_,
        fun h => ?_⟩
      · have := hasFDerivAt_block (hasFDerivAt_const (rad i) y) (hζd i y).hasFDerivAt hηy
        convert this using 2 with x
        simp only [blockMap_apply, hconst i hiρ hiE]
      · have := norm_blockDeriv_apply_le (hrad i) (hζv i y) hC ha hb (le_refl ‖(0 : E →L[ℝ] ℝ)‖) h
        have hbv : bv i = B := by simp [bv, hiρ, hiE, hy]
        rw [hbv]
        refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg h))
        simpa using hB i hiρ hiE
    · refine ⟨0, hasFDerivAt_blockMap_apply_of_notMem_tsupport hy, fun h => ?_⟩
      simp [bv, hiρ, hiE, hy]
  choose D hDd hDb using hD
  let T : E →L[ℝ] BlockSpace V :=
    ((PiLp.continuousLinearEquiv 2 ℝ fun i => WithLp 2 (V i × ℝ)).symm :
      (∀ i, WithLp 2 (V i × ℝ)) →L[ℝ] BlockSpace V).comp (ContinuousLinearMap.pi D)
  have hT : HasFDerivAt (blockMap R ζ η) T y := by
    have hpi : HasFDerivAt (fun x i => blockMap R ζ η x i) (ContinuousLinearMap.pi D) y :=
      hasFDerivAt_pi.2 hDd
    exact ((PiLp.continuousLinearEquiv 2 ℝ fun i => WithLp 2 (V i × ℝ)).symm :
      (∀ i, WithLp 2 (V i × ℝ)) →L[ℝ] BlockSpace V).hasFDerivAt.comp y hpi
  rw [hT.fderiv]
  have hTapply : ∀ h i, T h i = D i h := fun h i => rfl
  have hTb : ∀ h i, ‖T h i‖ ≤ bv i * ‖h‖ := fun h i => by rw [hTapply]; exact hDb i h
  have hsum0 : 0 ≤ ∑ i, bv i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hTn : ‖T‖ ≤ Real.sqrt (∑ i, bv i ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun h => ?_
    have hsq : ‖T h‖ ^ 2 ≤ (Real.sqrt (∑ i, bv i ^ 2) * ‖h‖) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt hsum0, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hTb h i) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  refine hTn.trans (Real.sqrt_le_sqrt ?_)
  set A : Finset κ := Finset.univ.filter fun i => i ≠ iρ ∧ i ≠ iE ∧ y ∈ tsupport (ζ i) with hAdef
  have hA : (A.card : ℝ) ≤ N := by
    have h := hcount y
    have hset : {i | i ≠ iρ ∧ i ≠ iE ∧ y ∈ tsupport (ζ i)} = (A : Set κ) := by
      ext i; simp [A]
    rw [hset, Set.ncard_coe_finset] at h
    exact_mod_cast h
  have hle : ∀ i, bv i ^ 2 ≤ (if i = iρ then Λ ^ 2 else 0) + (if i = iE then BE ^ 2 else 0) +
      (if i ∈ A then B ^ 2 else 0) := by
    intro i
    by_cases h1 : i = iρ
    · subst h1
      have hA1 : i ∉ A := by simp [A]
      simp [bv, hρE, hA1]
    by_cases h2 : i = iE
    · subst h2
      have hA2 : i ∉ A := by simp [A]
      simp [bv, h1, hA2]
    by_cases h3 : y ∈ tsupport (ζ i)
    · have hA3 : i ∈ A := by simp [A, h1, h2, h3]
      simp [bv, h1, h2, h3, hA3]
    · have hA3 : i ∉ A := by simp [A, h3]
      simp [bv, h1, h2, h3, hA3]
  calc ∑ i, bv i ^ 2 ≤ ∑ i, ((if i = iρ then Λ ^ 2 else 0) + (if i = iE then BE ^ 2 else 0) +
        (if i ∈ A then B ^ 2 else 0)) := Finset.sum_le_sum fun i _ => hle i
    _ = Λ ^ 2 + BE ^ 2 + A.card * B ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ iρ,
          Finset.sum_ite_eq' Finset.univ iE, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
        simp
    _ ≤ Λ ^ 2 + N * B ^ 2 + BE ^ 2 := by nlinarith [sq_nonneg B]

end Assembly

end DifferentialGeometry.Geometry.Collapse
