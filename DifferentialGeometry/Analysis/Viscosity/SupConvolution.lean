import DifferentialGeometry.Analysis.Convex.SupConvolution
import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.Interpolation

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Viscosity

open DifferentialGeometry.Analysis.Convex

theorem le_zero_of_upper_test_supConvolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {K : ℝ≥0} (hs : IsCompact s) (hu : LipschitzOnWith K u s)
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : Metric.closedBall x (2 * ε * K) ⊆ interior s)
    {H : ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hH : ∀ p B, Monotone (fun r => H r p B))
    (hsub : ∀ y ∈ interior s, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun z => u z - ψ z) y → H (u y) (fderiv ℝ ψ y) (fderiv ℝ (fderiv ℝ ψ) y) ≤ 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) :
    H (supConvolutionOn s u ε x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0 := by
  have hxs : x ∈ s := interior_subset (hx (Metric.mem_closedBall_self (by positivity)))
  obtain ⟨y, hy, hmax⟩ := exists_supConvolutionOn_eq_of_isCompact hs ⟨x, hxs⟩
    hu.continuousOn.upperSemicontinuousOn ε x
  have hyi : y ∈ interior s := by
    apply hx
    rw [Metric.mem_closedBall, dist_comm]
    exact dist_le_of_supConvolutionOn_eq hu hε hxs hy hmax
  have hbound : BddAbove (u '' s) := hs.bddAbove_image hu.continuousOn
  have htest := isLocalMax_sub_translate_of_supConvolutionOn hbound hε hyi hmax hm
  have htranslate (z : E) : x + (z - y) = z + (x - y) := by abel
  simp_rw [htranslate] at htest
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ (z + (x - y))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hle := hsub y hyi _ hsmooth htest
  have hxy : y + (x - y) = x := by abel
  have hD : fderiv ℝ (fun z => φ (z + (x - y))) y = fderiv ℝ φ x := by
    rw [DifferentialGeometry.Analysis.fderiv_translate φ (x - y) y
      (hφ.differentiable (by simp) _), hxy]
  have hDD : fderiv ℝ (fderiv ℝ (fun z => φ (z + (x - y)))) y =
      fderiv ℝ (fderiv ℝ φ) x := by
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    rw [DifferentialGeometry.Analysis.fderiv_fderiv_translate φ hφ2 (x - y) y, hxy]
  rw [hD, hDD] at hle
  apply le_trans (hH _ _ ?_) hle
  rw [hmax]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

private theorem quadratic_penalty_derivatives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ε : ℝ) (q v w : E) :
    fderiv ℝ (fun z : E => (2 * ε)⁻¹ * ‖z‖ ^ 2) q = ε⁻¹ • innerSL ℝ q ∧
    fderiv ℝ (fderiv ℝ (fun z : E => (2 * ε)⁻¹ * ‖z‖ ^ 2)) q v w =
      ε⁻¹ * inner ℝ v w := by
  have hscalar : (2 * ε)⁻¹ * 2 = ε⁻¹ := by simp [mul_inv_rev]
  have hd (p : E) : fderiv ℝ (fun z : E => (2 * ε)⁻¹ * ‖z‖ ^ 2) p = ε⁻¹ • innerSL ℝ p := by
    have h := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul ((2 * ε)⁻¹)
    simpa only [two_nsmul, ← two_smul ℝ, smul_smul, hscalar] using h.fderiv
  refine ⟨hd q, ?_⟩
  rw [funext hd]
  change fderiv ℝ (ε⁻¹ • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) q v w = _
  rw [ContinuousLinearMap.fderiv]
  rfl


theorem exists_affine_upper_test_of_supConvolutionOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u φ : E → ℝ} {s : Set E} (hu : BddAbove (u '' s))
    {ε : ℝ} (hε : 0 < ε) {x y : E} (hy : y ∈ interior s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) (A : E →L[ℝ] E) :
    ∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ IsLocalMax (fun z => u z - ψ z) y ∧
      fderiv ℝ ψ y = fderiv ℝ φ x ∧
      ∀ v w, fderiv ℝ (fderiv ℝ ψ) y v w =
        fderiv ℝ (fderiv ℝ φ) x (A v) (A w) + ε⁻¹ * inner ℝ (A v - v) (A w - w) := by
  let c := x - A y
  let B := A - ContinuousLinearMap.id ℝ E
  let q : E → ℝ := fun z => (2 * ε)⁻¹ * ‖z‖ ^ 2
  let f₁ : E → ℝ := fun z => φ (c + A z)
  let f₂ : E → ℝ := fun z => q (c + B z)
  let ψ : E → ℝ := fun z => f₁ z + f₂ z
  have hcA : c + A y = x := by simp [c]
  have hcB : c + B y = x - y := by simp [c, B]
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hf₁ : ContDiff ℝ (⊤ : ℕ∞) f₁ := hφ.comp (contDiff_const.add A.contDiff)
  have hf₂ : ContDiff ℝ (⊤ : ℕ∞) f₂ := hq.comp (contDiff_const.add B.contDiff)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hq2 : ContDiff ℝ 2 q := hq.of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hf₁2 : ContDiff ℝ 2 f₁ := hφ2.comp (contDiff_const.add A.contDiff)
  have hf₂2 : ContDiff ℝ 2 f₂ := hq2.comp (contDiff_const.add B.contDiff)
  have hD₁ (z : E) : fderiv ℝ f₁ z = (fderiv ℝ φ (c + A z)).comp A :=
    ((hφ.differentiable (by simp) _).hasFDerivAt.comp z (A.hasFDerivAt.const_add c)).fderiv
  have hD₂ (z : E) : fderiv ℝ f₂ z = (ε⁻¹ • innerSL ℝ (c + B z)).comp B := by
    have h := ((hq.differentiable (by simp) _).hasFDerivAt.comp z (B.hasFDerivAt.const_add c)).fderiv
    rw [(quadratic_penalty_derivatives ε (c + B z) 0 0).1] at h
    exact h
  have hDψ : fderiv ℝ ψ = fun z => fderiv ℝ f₁ z + fderiv ℝ f₂ z := by
    funext z
    exact fderiv_add (hf₁.differentiable (by simp) z) (hf₂.differentiable (by simp) z)
  refine ⟨ψ, hf₁.add hf₂, ?_, ?_, ?_⟩
  · have hT : ContinuousAt (fun z : E => c + A z) y := by fun_prop
    have hlocal := isLocalMax_sub_penalized_comp_of_supConvolutionOn hu hε hy hmax hm hT hcA
    have hcost (z : E) : dist (c + A z) z ^ 2 / (2 * ε) = q (c + B z) := by
      have heq : c + A z - z = c + B z := by simp [B]; abel
      rw [dist_eq_norm, heq, div_eq_mul_inv]
      dsimp [q]
      ring
    filter_upwards [hlocal] with z hz
    change u z - (f₁ z + f₂ z) ≤ u y - (f₁ y + f₂ y)
    simp_rw [hcost] at hz
    dsimp only [f₁, f₂]
    linarith
  · rw [hDψ]
    change fderiv ℝ f₁ y + fderiv ℝ f₂ y = fderiv ℝ φ x
    rw [hD₁, hD₂, hcA, hcB]
    have hgrad := fderiv_eq_of_upper_test_supConvolutionOn hu hε (interior_subset hy) hmax
      (hφ.differentiable (by simp) x) hm
    rw [hgrad]
    ext v
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
    change ε⁻¹ * inner ℝ (y - x) (A v) + ε⁻¹ * inner ℝ (x - y) (A v - v) =
      ε⁻¹ * inner ℝ (y - x) v
    simp only [inner_sub_left, inner_sub_right]
    ring
  · intro v w
    rw [hDψ]
    change fderiv ℝ (fderiv ℝ f₁ + fderiv ℝ f₂) y v w = _
    rw [fderiv_add ((hf₁2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y)
      ((hf₂2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y)]
    simp only [add_apply]
    change fderiv ℝ (fderiv ℝ (fun z => φ (c + A z))) y v w +
      fderiv ℝ (fderiv ℝ (fun z => q (c + B z))) y v w = _
    rw [DifferentialGeometry.Analysis.fderiv_fderiv_comp_affine A c y v w hφ2.contDiffAt,
      DifferentialGeometry.Analysis.fderiv_fderiv_comp_affine B c y v w hq2.contDiffAt,
      hcA, (quadratic_penalty_derivatives ε (c + B y) (B v) (B w)).2]
    rfl


theorem nondivergence_le_of_upper_test_supConvolutionOn
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    {u φ : E → ℝ} {s : Set E} (hu : BddAbove (u '' s))
    {ε : ℝ} (hε : 0 < ε) {x y : E} (hy : y ∈ interior s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x)
    {σ : E → ι → E} {b : E → E} {c r : E → ℝ} (hc : 0 ≤ c y)
    (A : E →L[ℝ] E) (hA : ∀ i, A (σ y i) = σ x i)
    (hsub : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun z => u z - ψ z) y →
      -(∑ i, fderiv ℝ (fderiv ℝ ψ) y (σ y i) (σ y i)) +
        fderiv ℝ ψ y (b y) + c y * u y ≤ r y) :
    -(∑ i, fderiv ℝ (fderiv ℝ φ) x (σ x i) (σ x i)) +
      fderiv ℝ φ x (b x) + c x * supConvolutionOn s u ε x ≤
        r y + ε⁻¹ * (∑ i, ‖σ x i - σ y i‖ ^ 2) +
          fderiv ℝ φ x (b x - b y) + (c x - c y) * supConvolutionOn s u ε x := by
  obtain ⟨ψ, hψ, hψmax, hD, hDD⟩ :=
    exists_affine_upper_test_of_supConvolutionOn hu hε hy hmax hφ hm A
  have h := hsub ψ hψ hψmax
  simp_rw [hDD, hD, hA, real_inner_self_eq_norm_sq] at h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hv : supConvolutionOn s u ε x ≤ u y := by
    rw [hmax]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
  have hzeroth := mul_le_mul_of_nonneg_left hv hc
  rw [map_sub]
  nlinarith

theorem nondivergence_le_of_upper_test_supConvolutionOn_of_lipschitzOnWith
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    {u : E → ℝ} {s : Set E} {K : ℝ≥0} (hs : IsCompact s) (hu : LipschitzOnWith K u s)
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : Metric.closedBall x (2 * ε * K) ⊆ interior s)
    {σ : E → ι → E} {b : E → E} {c r : E → ℝ}
    {Kσ : ι → ℝ≥0} {Kb Kc Kr : ℝ≥0} {M : ℝ}
    (hσ : ∀ i, LipschitzOnWith (Kσ i) (fun z => σ z i) s)
    (hb : LipschitzOnWith Kb b s) (hc : LipschitzOnWith Kc c s)
    (hr : LipschitzOnWith Kr r s) (hM : ∀ z ∈ s, |u z| ≤ M)
    (hcpos : ∀ z ∈ interior s, 0 ≤ c z)
    (hind : ∀ z ∈ interior s, LinearIndependent ℝ (σ z))
    (hsub : ∀ y ∈ interior s, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun z => u z - ψ z) y →
      -(∑ i, fderiv ℝ (fderiv ℝ ψ) y (σ y i) (σ y i)) +
        fderiv ℝ ψ y (b y) + c y * u y ≤ r y)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) :
    -(∑ i, fderiv ℝ (fderiv ℝ φ) x (σ x i) (σ x i)) +
      fderiv ℝ φ x (b x) + c x * supConvolutionOn s u ε x ≤
        r x + ε * (4 * (K : ℝ) ^ 2 * (∑ i, (Kσ i : ℝ) ^ 2) +
          4 * Kb * (K : ℝ) ^ 2 + 2 * K * (Kc * M + Kr)) := by
  have hxs : x ∈ s := interior_subset (hx (Metric.mem_closedBall_self (by positivity)))
  obtain ⟨y, hy, hmax⟩ := exists_supConvolutionOn_eq_of_isCompact hs ⟨x, hxs⟩
    hu.continuousOn.upperSemicontinuousOn ε x
  have hdist := dist_le_of_supConvolutionOn_eq hu hε hxs hy hmax
  have hyi : y ∈ interior s := hx (by simpa only [Metric.mem_closedBall, dist_comm] using hdist)
  have hbound : BddAbove (u '' s) := hs.bddAbove_image hu.continuousOn
  obtain ⟨A, hA⟩ := (hind y hyi).exists_continuousLinearMap_apply_eq (σ x)
  have hle := nondivergence_le_of_upper_test_supConvolutionOn hbound hε hyi hmax hφ hm
    (hcpos y hyi) A hA (hsub y hyi)
  have hv : |supConvolutionOn s u ε x| ≤ M := by
    apply abs_le.mpr
    constructor
    · have hlow := (supConvolutionOn_sub_mem_Icc_of_lipschitzOnWith hu hε hxs).1
      have hmlo := (abs_le.mp (hM x hxs)).1
      linarith
    · rw [hmax]
      exact (sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))).trans
        ((le_abs_self _).trans (hM y hy))
  have hgrad : ‖fderiv ℝ φ x‖ ≤ 2 * K := by
    rw [fderiv_eq_of_upper_test_supConvolutionOn hbound hε hy hmax
      (hφ.differentiable (by simp) x) hm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε), innerSL_apply_norm]
    rw [← dist_eq_norm, dist_comm]
    calc
      ε⁻¹ * dist x y ≤ ε⁻¹ * (2 * ε * K) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 2 * K := by field_simp
  have hdiff (i : ι) : ‖σ x i - σ y i‖ ≤ (Kσ i : ℝ) * (2 * ε * K) := by
    have h := (hσ i).dist_le_mul x hxs y hy
    rw [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdist (Kσ i).coe_nonneg)
  have hsum : ε⁻¹ * (∑ i, ‖σ x i - σ y i‖ ^ 2) ≤
      ε * (4 * (K : ℝ) ^ 2 * (∑ i, (Kσ i : ℝ) ^ 2)) := by
    calc
      _ ≤ ε⁻¹ * (∑ i, ((Kσ i : ℝ) * (2 * ε * K)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hdiff i) 2
      _ = _ := by
        simp_rw [mul_pow]
        rw [← Finset.sum_mul]
        field_simp
        ring
  have hbxy : ‖b x - b y‖ ≤ Kb * (2 * ε * K) := by
    have h := hb.dist_le_mul x hxs y hy
    rw [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdist Kb.coe_nonneg)
  have hdrift : fderiv ℝ φ x (b x - b y) ≤ ε * (4 * Kb * (K : ℝ) ^ 2) := by
    calc
      _ ≤ ‖fderiv ℝ φ x (b x - b y)‖ := le_abs_self _
      _ ≤ ‖fderiv ℝ φ x‖ * ‖b x - b y‖ := (fderiv ℝ φ x).le_opNorm _
      _ ≤ (2 * K) * (Kb * (2 * ε * K)) := mul_le_mul hgrad hbxy (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcx : |c x - c y| ≤ Kc * (2 * ε * K) := by
    have h := hc.dist_le_mul x hxs y hy
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdist Kc.coe_nonneg)
  have hzero : (c x - c y) * supConvolutionOn s u ε x ≤ Kc * (2 * ε * K) * M := by
    calc
      _ ≤ |(c x - c y) * supConvolutionOn s u ε x| := le_abs_self _
      _ = |c x - c y| * |supConvolutionOn s u ε x| := abs_mul _ _
      _ ≤ _ := mul_le_mul hcx hv (abs_nonneg _) (by positivity)
  have hrxy : r y ≤ r x + Kr * (2 * ε * K) := by
    have hh := hr.dist_le_mul y hy x hxs
    rw [Real.dist_eq, dist_comm] at hh
    have hh' := (le_abs_self (r y - r x)).trans
      (hh.trans (mul_le_mul_of_nonneg_left hdist Kr.coe_nonneg))
    linarith
  linarith

end DifferentialGeometry.Analysis.Viscosity
