import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Morse

variable {ι : Type} [Fintype ι]

private noncomputable def separableDeriv (f : ι → ℝ → ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, deriv (f i) (x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

private theorem hasFDerivAt_sum_pi {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ (f i) (x i)) :
    HasFDerivAt (fun y : ι → ℝ => ∑ i, f i (y i)) (separableDeriv f x) x := by
  apply HasFDerivAt.fun_sum
  intro i hi
  convert! ((hf i).hasDerivAt.hasFDerivAt).comp x
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)).hasFDerivAt using 1
  ext v
  simp [mul_comm]

private noncomputable def separableSecondDeriv (f : ι → ℝ → ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ) :=
  ∑ i, ((deriv (deriv (f i)) (x i)) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)).smulRight
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

private theorem hasFDerivAt_separableDeriv {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ (deriv (f i)) (x i)) :
    HasFDerivAt (separableDeriv f) (separableSecondDeriv f x) x := by
  apply HasFDerivAt.fun_sum
  intro i hi
  have h : HasFDerivAt (fun y : ι → ℝ => deriv (f i) (y i))
      (deriv (deriv (f i)) (x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
    convert! ((hf i).hasDerivAt.hasFDerivAt).comp x
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)).hasFDerivAt using 1
    ext v
    simp [mul_comm]
  exact h.smul_const ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

private theorem fderiv_fderiv_sum_pi {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) (x i)) :
    fderiv ℝ (fderiv ℝ (fun y : ι → ℝ => ∑ i, f i (y i))) x =
      separableSecondDeriv f x := by
  have hn (i : ι) : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 (f i) (y i) :=
    (continuousAt_apply i x).tendsto.eventually ((hf i).eventually (by simp))
  have heq : fderiv ℝ (fun y : ι → ℝ => ∑ i, f i (y i)) =ᶠ[𝓝 x] separableDeriv f := by
    filter_upwards [Filter.eventually_all.2 hn] with y hy
    exact (hasFDerivAt_sum_pi (fun i => (hy i).differentiableAt (by norm_num))).fderiv
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_separableDeriv fun i =>
    ((hf i).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).fderiv

private theorem chartHessianBilinAt_sum_pi {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) (x i)) (v w : ι → ℝ) :
    chartHessianBilinAt (fun y : ι → ℝ => ∑ i, f i (y i)) x v w =
      ∑ i, deriv (deriv (f i)) (x i) * v i * w i := by
  change fderiv ℝ (fderiv ℝ (fun y : ι → ℝ => ∑ i, f i (y i))) x v w = _
  rw [fderiv_fderiv_sum_pi hf]
  simp [separableSecondDeriv, mul_assoc]

theorem chartHessianAt_sum_pi {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) (x i)) :
    chartHessianAt (fun y : ι → ℝ => ∑ i, f i (y i)) x =
      QuadraticMap.weightedSumSquares ℝ (fun i => deriv (deriv (f i)) (x i)) := by
  ext v
  change chartHessianBilinAt (fun y : ι → ℝ => ∑ i, f i (y i)) x v v = _
  rw [chartHessianBilinAt_sum_pi hf]
  simp [QuadraticMap.weightedSumSquares_apply, mul_assoc]

theorem sigNeg_chartHessianAt_sum_pi {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) (x i)) :
    _root_.sigNeg (chartHessianAt (fun y : ι → ℝ => ∑ i, f i (y i)) x) =
      {i | deriv (deriv (f i)) (x i) < 0}.ncard := by
  rw [chartHessianAt_sum_pi hf, QuadraticForm.sigNeg_weightedSumSquares]

theorem isCriticalPointAt_sum_pi_iff {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ (f i) (x i)) :
    IsCriticalPointAt 𝓘(ℝ, ι → ℝ) (fun y => ∑ i, f i (y i)) x ↔
      ∀ i, deriv (f i) (x i) = 0 := by
  classical
  rw [IsCriticalPointAt, mfderiv_eq_fderiv, (hasFDerivAt_sum_pi hf).fderiv]
  change separableDeriv f x = (0 : (ι → ℝ) →L[ℝ] ℝ) ↔ _
  constructor
  · intro h i
    have hi := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h
    simpa [separableDeriv, Pi.single_apply] using hi
  · intro h
    simp [separableDeriv, h]

theorem isNondegenerateCriticalPointAt_sum_pi_iff {f : ι → ℝ → ℝ} {x : ι → ℝ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) (x i)) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, ι → ℝ) (fun y => ∑ i, f i (y i)) x ↔
      (∀ i, deriv (f i) (x i) = 0) ∧ ∀ i, deriv (deriv (f i)) (x i) ≠ 0 := by
  classical
  have hsymm : ∀ v w, chartHessianBilinAt (fun y : ι → ℝ => ∑ i, f i (y i)) x v w =
      chartHessianBilinAt (fun y : ι → ℝ => ∑ i, f i (y i)) x w v := by
    intro v w
    rw [chartHessianBilinAt_sum_pi hf, chartHessianBilinAt_sum_pi hf]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB : QuadraticMap.associated (R := ℝ)
      (chartHessianAt (fun y : ι → ℝ => ∑ i, f i (y i)) x) =
        chartHessianBilinAt (fun y : ι → ℝ => ∑ i, f i (y i)) x :=
    QuadraticMap.associated_left_inverse ℝ hsymm
  rw [IsNondegenerateCriticalPointAt]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq,
    PartialEquiv.refl_symm]
  rw [isCriticalPointAt_sum_pi_iff (fun i => (hf i).differentiableAt (by norm_num)), hB]
  apply and_congr Iff.rfl
  constructor
  · intro h i hi
    have hz : (Pi.single i (1 : ℝ) : ι → ℝ) = 0 := by
      apply h
      intro w
      rw [chartHessianBilinAt_sum_pi hf]
      simp [Pi.single_apply, hi]
    have hi0 := congrFun hz i
    simp at hi0
  · intro h v hv
    funext i
    have hi := hv (Pi.single i 1)
    rw [chartHessianBilinAt_sum_pi hf] at hi
    have hm : deriv (deriv (f i)) (x i) * v i = 0 := by simpa [Pi.single_apply] using hi
    exact (mul_eq_zero.mp hm).resolve_left (h i)

private theorem sum_sq_add_smoothAbs_critical_properties {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    let F := fun x : Fin (n + 1) → ℝ =>
      (∑ i : Fin n, c i * x i.succ ^ 2) +
        (a / 2 + Real.smoothAbs (a / 2) (x 0 - a / 2))
    (∀ x, IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) F x ↔ x = Fin.cons (a / 2) (0 : Fin n → ℝ)) ∧
      IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) F (Fin.cons (a / 2) (0 : Fin n → ℝ)) := by
  classical
  let ε := a / 2
  let φ := fun u : ℝ => ε + Real.smoothAbs ε (u - ε)
  let f : Fin (n + 1) → ℝ → ℝ := Fin.cases φ (fun i u => c i * u ^ 2)
  have hε : ε ≠ 0 := div_ne_zero ha two_ne_zero
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.add
    ((Real.smoothAbs.contDiff ε).comp (contDiff_id.sub contDiff_const))
  have hderivφ : deriv φ = fun u => deriv (Real.smoothAbs ε) (u - ε) := by
    funext u
    dsimp [φ]
    rw [deriv_const_add, deriv_comp_sub_const]
  have hφcrit (u : ℝ) : deriv φ u = 0 ↔ u = ε := by
    rw [hderivφ, Real.smoothAbs.deriv_eq_zero_iff hε, sub_eq_zero]
  have hφsecond : deriv (deriv φ) ε = 2 / ε := by
    rw [hderivφ, deriv_comp_sub_const, sub_self, Real.smoothAbs.deriv_deriv_zero hε]
  have hsq (i : Fin n) (u : ℝ) : HasDerivAt (fun u : ℝ => c i * u ^ 2) (2 * c i * u) u := by
    convert! ((hasDerivAt_id u).pow 2).const_mul (c i) using 1
    simp only [id_eq]
    ring
  have hsqderiv (i : Fin n) : deriv (fun u : ℝ => c i * u ^ 2) = fun u => 2 * c i * u :=
    funext (fun u => (hsq i u).deriv)
  have hsqsecond (i : Fin n) (u : ℝ) : deriv (deriv (fun u : ℝ => c i * u ^ 2)) u = 2 * c i := by
    rw [hsqderiv]
    simp
  have hf (i : Fin (n + 1)) : ContDiff ℝ 2 (f i) := by
    refine Fin.cases ?_ ?_ i
    · exact hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    · intro j
      change ContDiff ℝ 2 (fun u : ℝ => c j * u ^ 2)
      fun_prop
  have hcoords (x : Fin (n + 1) → ℝ) :
      (∀ i, deriv (f i) (x i) = 0) ↔ x = Fin.cons ε (0 : Fin n → ℝ) := by
    constructor
    · intro h
      funext i
      refine Fin.cases ?_ ?_ i
      · have hz := h 0
        change deriv φ (x 0) = 0 at hz
        exact (hφcrit (x 0)).mp hz
      · intro j
        have hz := h j.succ
        change deriv (fun u : ℝ => c j * u ^ 2) (x j.succ) = 0 at hz
        rw [(hsq j (x j.succ)).deriv] at hz
        exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero (hc j))
    · rintro rfl i
      refine Fin.cases ?_ ?_ i
      · exact (hφcrit ε).mpr rfl
      · intro j
        change deriv (fun u : ℝ => c j * u ^ 2) 0 = 0
        rw [(hsq j 0).deriv]
        ring
  have hF : (fun x : Fin (n + 1) → ℝ =>
      (∑ i : Fin n, c i * x i.succ ^ 2) + (ε + Real.smoothAbs ε (x 0 - ε))) =
      fun x => ∑ i, f i (x i) := by
    funext x
    rw [Fin.sum_univ_succ]
    simp [f, φ, add_comm]
  change (∀ x, IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
    (fun x : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * x i.succ ^ 2) + (ε + Real.smoothAbs ε (x 0 - ε))) x ↔
      x = Fin.cons ε (0 : Fin n → ℝ)) ∧ _
  rw [hF]
  constructor
  · intro x
    rw [isCriticalPointAt_sum_pi_iff (fun i => (hf i).differentiable (by norm_num) (x i))]
    exact hcoords x
  · apply (isNondegenerateCriticalPointAt_sum_pi_iff (fun i => (hf i).contDiffAt)).mpr
    refine ⟨(hcoords _).mpr rfl, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · change deriv (deriv φ) ε ≠ 0
      rw [hφsecond]
      exact div_ne_zero two_ne_zero hε
    · intro j
      change deriv (deriv (fun u : ℝ => c j * u ^ 2)) 0 ≠ 0
      rw [hsqsecond]
      exact mul_ne_zero two_ne_zero (hc j)

theorem chartHessianAt_sum_sq_add_smoothAbs {n : ℕ} (c : Fin n → ℝ)
    (a : ℝ) :
    chartHessianAt (fun y : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * y i.succ ^ 2) +
      (a / 2 + Real.smoothAbs (a / 2) (y 0 - a / 2))) (Fin.cons (a / 2) (0 : Fin n → ℝ)) =
        QuadraticMap.weightedSumSquares ℝ (Fin.cons (4 / a) (fun i => 2 * c i)) := by
  let ε := a / 2
  let φ := fun u : ℝ => ε + Real.smoothAbs ε (u - ε)
  let f : Fin (n + 1) → ℝ → ℝ := Fin.cases φ (fun i u => c i * u ^ 2)
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.add
    ((Real.smoothAbs.contDiff ε).comp (contDiff_id.sub contDiff_const))
  have hderivφ : deriv φ = fun u => deriv (Real.smoothAbs ε) (u - ε) := by
    funext u
    dsimp [φ]
    rw [deriv_const_add, deriv_comp_sub_const]
  have hφsecond : deriv (deriv φ) ε = 4 / a := by
    by_cases ha : a = 0
    · subst a
      simp [φ, ε, Real.smoothAbs]
    · have hε : ε ≠ 0 := div_ne_zero ha two_ne_zero
      rw [hderivφ, deriv_comp_sub_const, sub_self, Real.smoothAbs.deriv_deriv_zero hε]
      dsimp [ε]
      ring
  have hsqderiv (i : Fin n) : deriv (fun u : ℝ => c i * u ^ 2) = fun u => 2 * c i * u := by
    funext u
    have hd : HasDerivAt (fun u : ℝ => c i * u ^ 2) (2 * c i * u) u := by
      convert! ((hasDerivAt_id u).pow 2).const_mul (c i) using 1
      simp only [id_eq]
      ring
    exact hd.deriv
  have hsqsecond (i : Fin n) : deriv (deriv (fun u : ℝ => c i * u ^ 2)) 0 = 2 * c i := by
    rw [hsqderiv]
    simp
  have hf (i : Fin (n + 1)) : ContDiff ℝ 2 (f i) := by
    refine Fin.cases ?_ ?_ i
    · exact hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    · intro j
      change ContDiff ℝ 2 (fun u : ℝ => c j * u ^ 2)
      fun_prop
  have hF : (fun x : Fin (n + 1) → ℝ =>
      (∑ i : Fin n, c i * x i.succ ^ 2) + (ε + Real.smoothAbs ε (x 0 - ε))) =
      fun x => ∑ i, f i (x i) := by
    funext x
    rw [Fin.sum_univ_succ]
    simp [f, φ, add_comm]
  change chartHessianAt
    (fun x : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * x i.succ ^ 2) + (ε + Real.smoothAbs ε (x 0 - ε)))
    (Fin.cons ε (0 : Fin n → ℝ)) = _
  rw [hF, chartHessianAt_sum_pi (fun i => (hf i).contDiffAt)]
  apply congrArg (fun w : Fin (n + 1) → ℝ => QuadraticMap.weightedSumSquares ℝ w)
  funext i
  refine Fin.cases ?_ ?_ i
  · exact hφsecond
  · intro j
    exact hsqsecond j

theorem sigNeg_chartHessianAt_sum_sq_add_smoothAbs {n : ℕ} (c : Fin n → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    _root_.sigNeg (chartHessianAt
      (fun y : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * y i.succ ^ 2) +
        (a / 2 + Real.smoothAbs (a / 2) (y 0 - a / 2))) (Fin.cons (a / 2) (0 : Fin n → ℝ))) =
      {i | c i < 0}.ncard := by
  classical
  rw [chartHessianAt_sum_sq_add_smoothAbs c a, QuadraticForm.sigNeg_weightedSumSquares]
  have hset : {i : Fin (n + 1) | (Fin.cons (4 / a) (fun j => 2 * c j) : Fin (n + 1) → ℝ) i < 0} =
      Fin.succ '' {j : Fin n | c j < 0} := by
    ext i
    refine Fin.cases ?_ ?_ i
    · have hn : ¬ (4 / a : ℝ) < 0 := not_lt.mpr (div_nonneg (by norm_num) ha)
      simp [hn]
    · intro j
      simp [mul_neg_iff]
  rw [hset, Set.ncard_image_of_injective _ (Fin.succ_injective n)]

theorem isCriticalPointAt_sum_sq_add_smoothAbs_iff {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) {a : ℝ} (ha : a ≠ 0) (x : Fin (n + 1) → ℝ) :
    IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
      (fun y : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * y i.succ ^ 2) +
        (a / 2 + Real.smoothAbs (a / 2) (y 0 - a / 2))) x ↔
      x = Fin.cons (a / 2) (0 : Fin n → ℝ) :=
  (sum_sq_add_smoothAbs_critical_properties c hc ha).1 x

theorem isNondegenerateCriticalPointAt_sum_sq_add_smoothAbs {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
      (fun y : Fin (n + 1) → ℝ => (∑ i : Fin n, c i * y i.succ ^ 2) +
        (a / 2 + Real.smoothAbs (a / 2) (y 0 - a / 2))) (Fin.cons (a / 2) (0 : Fin n → ℝ)) :=
  (sum_sq_add_smoothAbs_critical_properties c hc ha).2

end DifferentialGeometry.Topology.Morse
