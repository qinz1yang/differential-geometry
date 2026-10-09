import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingConductivityBounds
import DifferentialGeometry.Analysis.Complex.NormalizedGradient
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem quadratic_value_linear_derivative_of_zero_fderiv
    {φ : ℂ → X} (hφ : ContDiffAt ℝ 2 φ 0) (hDφ : fderiv ℝ φ 0 = 0) :
    ∃ K > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖φ w - φ 0‖ ≤ K * ‖w‖ ^ 2 ∧ ‖fderiv ℝ φ w‖ ≤ K * ‖w‖ := by
  let f : ℝ × ℂ → X := fun q => φ q.2
  have hf : ContDiffAt ℝ 2 f (0, 0) := hφ.comp (0, 0) contDiffAt_snd
  have hdf (w : ℂ) (hw : ContDiffAt ℝ 2 φ w) :
      fderiv ℝ f (0, w) = (fderiv ℝ φ w).comp (ContinuousLinearMap.snd ℝ ℝ ℂ) :=
    ((hw.differentiableAt (by norm_num)).hasFDerivAt.comp (0, w) hasFDerivAt_snd).fderiv
  have hz : (fderiv ℝ f (0, 0)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) = 0 := by
    rw [hdf 0 hφ, hDφ]
    simp
  obtain ⟨r, K, hr, _hr1, hK, hb⟩ := exists_local_bounds_of_vanishing_slope_derivative hf hz
  refine ⟨K, hK, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr, hφ.eventually (by norm_num)] with w hw hφw
  have hmem : (0, w) ∈ ball ((0 : ℝ), (0 : ℂ)) r := by
    simpa [mem_ball, dist_eq_norm] using hw
  have h := hb (0, w) hmem
  have hcomp : (fderiv ℝ f (0, w)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) =
      fderiv ℝ φ w := by
    rw [hdf w hφw]
    ext v
    rfl
  exact ⟨by simpa [f] using h.1, by simpa [hcomp] using h.2.2⟩

/-- Private receiving step: the position has vanishing first derivative,
whereas the slope is only Lipschitz through zero and C1 away from zero. -/
private theorem quadratic_root_composition
    {F : X × Y → Z} {a : X} (hF : ContDiffAt ℝ 2 F (a, 0))
    (hbound : ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ q ∈ ball (a, (0 : Y)) r,
      ‖F q - F (a, 0)‖ ≤ C * (‖q.1 - a‖ + ‖q.2‖ ^ 2) ∧
      ‖fderiv ℝ F q‖ ≤ C ∧
      ‖(fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ X Y)‖ ≤ C * ‖q - (a, 0)‖)
    {φ : ℂ → X} (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0 = a)
    (hDφ : fderiv ℝ φ 0 = 0)
    {R : ℂ → Y} (hR : ContinuousAt R 0) (hR0 : R 0 = 0)
    (hR1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 R w)
    (hRb : ∃ K > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖R w‖ ≤ K * ‖w‖ ∧ ‖fderiv ℝ R w‖ ≤ K) :
    ∃ C > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ContDiffAt ℝ 1 (fun z => F (φ z, R z)) w ∧
      ‖F (φ w, R w) - F (a, 0)‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖fderiv ℝ (fun z => F (φ z, R z)) w‖ ≤ C * ‖w‖ := by
  obtain ⟨r, B, hr, hB, hb⟩ := hbound
  obtain ⟨P, hP, hφb⟩ := quadratic_value_linear_derivative_of_zero_fderiv hφ hDφ
  obtain ⟨K, hK, hRb⟩ := hRb
  let J : ℂ → X × Y := fun w => (φ w, R w)
  have hJ : ContinuousAt J 0 := hφ.continuousAt.prodMk hR
  have hJ0 : J 0 = (a, 0) := by simp [J, hφ0, hR0]
  have hJlim : Tendsto J (𝓝 (0 : ℂ)) (𝓝 (a, (0 : Y))) := by simpa only [hJ0] using hJ.tendsto
  have hJball : ∀ᶠ w in 𝓝 (0 : ℂ), J w ∈ ball (a, (0 : Y)) r :=
    hJlim.eventually (ball_mem_nhds _ hr)
  have hFnear : ∀ᶠ w in 𝓝 (0 : ℂ), ContDiffAt ℝ 2 F (J w) :=
    hJlim.eventually (hF.eventually (by norm_num))
  let C : ℝ := B * (P + K ^ 2) + B * P + B * (P + K) * K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hR1, hRb, nhdsWithin_le_nhds hφb,
    nhdsWithin_le_nhds hJball, nhdsWithin_le_nhds hFnear,
    nhdsWithin_le_nhds (hφ.eventually (by norm_num)),
    nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) zero_lt_one)] with w hR1w hRbw hφbw hJw hFw hφw hw1
  have ht : ‖w‖ ≤ 1 := (show ‖w‖ < 1 from by
    simpa only [mem_ball, dist_zero_right] using hw1).le
  have hx : ‖φ w - a‖ ≤ P * ‖w‖ ^ 2 := by simpa only [hφ0] using hφbw.1
  have hj : ‖J w - (a, 0)‖ ≤ (P + K) * ‖w‖ := by
    simp only [J, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    apply max_le
    · have hs : ‖w‖ ^ 2 ≤ ‖w‖ := by nlinarith [norm_nonneg w]
      exact (hx.trans (mul_le_mul_of_nonneg_left hs hP.le)).trans
        (by nlinarith [mul_nonneg hK.le (norm_nonneg w)])
    · exact hRbw.1.trans (by nlinarith [mul_nonneg hP.le (norm_nonneg w)])
  have hbs := hb (J w) hJw
  have hcv : ContDiffAt ℝ 1 (fun z => F (φ z, R z)) w :=
    (hFw.of_le (by norm_num)).comp w ((hφw.of_le (by norm_num)).prodMk hR1w)
  have hv : ‖F (φ w, R w) - F (a, 0)‖ ≤ B * (P + K ^ 2) * ‖w‖ ^ 2 := by
    have hs : ‖R w‖ ^ 2 ≤ (K * ‖w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hRbw.1 2
    calc
      _ ≤ B * (‖φ w - a‖ + ‖R w‖ ^ 2) := hbs.1
      _ ≤ B * (P * ‖w‖ ^ 2 + (K * ‖w‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hx hs) hB.le
      _ = _ := by ring
  have hdφ := (hφw.differentiableAt (by norm_num)).hasFDerivAt
  have hdR := (hR1w.differentiableAt one_ne_zero).hasFDerivAt
  have hdF := (hFw.differentiableAt (by norm_num)).hasFDerivAt
  have hdeq : fderiv ℝ (fun z => F (φ z, R z)) w =
      ((fderiv ℝ F (J w)).comp (ContinuousLinearMap.inl ℝ X Y)).comp (fderiv ℝ φ w) +
      ((fderiv ℝ F (J w)).comp (ContinuousLinearMap.inr ℝ X Y)).comp (fderiv ℝ R w) := by
    change fderiv ℝ (F ∘ J) w = _
    rw [(hdF.comp w (hdφ.prodMk hdR)).fderiv]
    ext v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, add_apply,
      Prod.mk_add_mk, add_zero, zero_add] using
      map_add (fderiv ℝ F (J w)) (fderiv ℝ φ w v, 0) (0, fderiv ℝ R w v)
  have hd : ‖fderiv ℝ (fun z => F (φ z, R z)) w‖ ≤
      (B * P + B * (P + K) * K) * ‖w‖ := by
    rw [hdeq]
    have hfirst : ‖(fderiv ℝ F (J w)).comp (ContinuousLinearMap.inl ℝ X Y)‖ ≤ B :=
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ X Y))).trans hbs.2.1
    have hsecond : ‖(fderiv ℝ F (J w)).comp (ContinuousLinearMap.inr ℝ X Y)‖ ≤
        B * ((P + K) * ‖w‖) := hbs.2.2.trans (mul_le_mul_of_nonneg_left hj hB.le)
    calc
      _ ≤ ‖((fderiv ℝ F (J w)).comp (ContinuousLinearMap.inl ℝ X Y)).comp (fderiv ℝ φ w)‖ +
          ‖((fderiv ℝ F (J w)).comp (ContinuousLinearMap.inr ℝ X Y)).comp (fderiv ℝ R w)‖ := norm_add_le _ _
      _ ≤ B * (P * ‖w‖) + (B * ((P + K) * ‖w‖)) * K := by
        apply add_le_add
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hfirst hφbw.2 (norm_nonneg _) hB.le)
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hsecond hRbw.2 (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hvC : B * (P + K ^ 2) ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ B * P by positivity, show 0 ≤ B * (P + K) * K by positivity]
  have hdC : B * P + B * (P + K) * K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ B * (P + K ^ 2) by positivity]
  exact ⟨hcv, hv.trans (mul_le_mul_of_nonneg_right hvC (sq_nonneg _)),
    hd.trans (mul_le_mul_of_nonneg_right hdC (norm_nonneg _))⟩

end DifferentialGeometry.Analysis

open Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The first-sheet conductivity has quadratic deviation from the identity and
linear derivative decay in the literal root coordinate. The actual height
Hessian bound produces the slope estimates; neither desired coefficient bound
is a hypothesis. -/
theorem chartLeadingPlaneProjection_root_conductivity_bounds
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ)
    {m : ℕ} (hm : 1 ≤ m) {H : ℂ → ℝ}
    (hH : ContDiffAt ℝ 2 H 0) (hH0 : H 0 = 0) (hDH : fderiv ℝ H 0 = 0)
    (hHess : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let R := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let Y : ℂ → E := fun w => extChartAt 𝓘(ℝ, E) p x + L (P w - c) + H w • N
    let G : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y w))
        (L (![1, Complex.I] i) + R w (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + R w (![1, Complex.I] j) • N)
    let A : ℂ → ℂ →L[ℝ] ℂ := fun w => complexPlaneMatrixOperator
      (Analysis.planarConductivity (G w 0 0) (G w 1 1) (G w 0 1))
    (A 0 = ContinuousLinearMap.id ℝ ℂ ∧
      ∃ C > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
        ContDiffAt ℝ 1 A w ∧
        ‖A w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
        ‖fderiv ℝ A w‖ ≤ C * ‖w‖) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ),
        Y w ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
        0 < G w 0 0 * G w 1 1 - G w 0 1 ^ 2 := by
  let Yjet : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
    extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
  let Gjet : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
    chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Yjet q))
      (L (![1, Complex.I] i) + q.2 (![1, Complex.I] i) • N)
      (L (![1, Complex.I] j) + q.2 (![1, Complex.I] j) • N)
  let F := fun q => complexPlaneMatrixOperator
    (Analysis.planarConductivity (Gjet q 0 0) (Gjet q 1 1) (Gjet q 0 1))
  let R := Analysis.complexPowerNormalizedGradient m H
  let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  let φ : ℂ → ℂ × ℝ := fun w => (P w, H w)
  let A : ℂ → ℂ →L[ℝ] ℂ := fun w => F (φ w, R w)
  change (A 0 = ContinuousLinearMap.id ℝ ℂ ∧
    ∃ C > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 A w ∧
      ‖A w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖fderiv ℝ A w‖ ≤ C * ‖w‖) ∧
    ∀ᶠ w in 𝓝 (0 : ℂ),
      Yjet (φ w, R w) ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      0 < Gjet (φ w, R w) 0 0 * Gjet (φ w, R w) 1 1 - Gjet (φ w, R w) 0 1 ^ 2
  have houter := chartLeadingPlaneProjection_conductivity_jet_bounds
    g hsrc hb hnull hN hunit L hL c
  change ContDiffAt ℝ 2 F ((c, 0), 0) ∧
    F ((c, 0), 0) = ContinuousLinearMap.id ℝ ℂ ∧ _ at houter
  obtain ⟨hF, hF0, r, B, hr, _hr1, hB, hbnd, hdomain⟩ := houter
  have hφ : ContDiffAt ℝ 2 φ 0 := by
    exact (contDiffAt_const.add ((contDiffAt_id.pow (m + 1)).div_const
      ((m + 1 : ℕ) : ℂ))).prodMk hH
  have hφ0 : φ 0 = (c, 0) := by simp [φ, P, hH0]
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hdP : HasFDerivAt P (0 : ℂ →L[ℝ] ℂ) 0 := by
    have hd := ((hasDerivAt_pow (m + 1) (0 : ℂ)).div_const
      ((m + 1 : ℕ) : ℂ)).const_add c
    have hz : HasDerivAt P 0 0 := by simpa [P, hm0] using hd
    simpa using! hz.hasFDerivAt.restrictScalars ℝ
  have hDφ : fderiv ℝ φ 0 = 0 := by
    have hh : HasFDerivAt H (0 : ℂ →L[ℝ] ℝ) 0 := by
      simpa only [hDH] using (hH.differentiableAt (by norm_num)).hasFDerivAt
    have hd : HasFDerivAt φ (0 : ℂ →L[ℝ] ℂ × ℝ) 0 := by
      simpa only [φ] using! hdP.prodMk hh
    exact hd.fderiv
  obtain ⟨hR0, ε, hε, K, hK, hsize, hder, hLip⟩ :=
    Analysis.exists_normalized_gradient_bounds_of_hessian_order hm hH hDH hHess
  change R 0 = 0 at hR0
  have hR : ContinuousAt R 0 := hLip.continuousOn.continuousAt (ball_mem_nhds _ hε)
  have hR1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 R w := by
    filter_upwards [nhdsWithin_le_nhds (hH.eventually (by norm_num)), self_mem_nhdsWithin] with w hw hw0
    have hne : w ≠ 0 := hw0
    have hM : ContDiffAt ℝ 1 (fun z : ℂ => ContinuousLinearMap.mul ℝ ℂ ((z ^ m)⁻¹)) w :=
      (ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp w
        ((contDiffAt_id.pow m).inv (pow_ne_zero m hne))
    exact (hw.fderiv_right (m := 1) (by norm_num)).clm_comp hM
  have hRb : ∃ K > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖R w‖ ≤ K * ‖w‖ ∧ ‖fderiv ℝ R w‖ ≤ K := by
    refine ⟨K, hK, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hε), self_mem_nhdsWithin] with w hw hw0
    exact ⟨hsize w hw, (hder w hw hw0).2⟩
  have hA0 : A 0 = ContinuousLinearMap.id ℝ ℂ := by
    simpa only [A, hφ0, hR0] using hF0
  have hbnd' : ∀ q ∈ ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r,
      ‖F q - F ((c, 0), 0)‖ ≤ B * (‖q.1 - (c, 0)‖ + ‖q.2‖ ^ 2) ∧
      ‖fderiv ℝ F q‖ ≤ B ∧
      ‖(fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ))‖ ≤
        B * ‖q - ((c, 0), 0)‖ := by
    simpa only [hF0] using hbnd
  obtain ⟨C, hC, hroot⟩ := Analysis.quadratic_root_composition hF
    ⟨r, B, hr, hB, hbnd'⟩ hφ hφ0 hDφ hR hR0 hR1 hRb
  refine ⟨⟨hA0, C, hC, ?_⟩, ?_⟩
  · simpa only [A, hF0] using hroot
  · have hJ : ContinuousAt (fun w => (φ w, R w)) 0 := hφ.continuousAt.prodMk hR
    have hJlim : Tendsto (fun w => (φ w, R w)) (𝓝 (0 : ℂ))
        (𝓝 ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ))) := by
      simpa only [hφ0, hR0] using hJ.tendsto
    filter_upwards [hJlim.eventually (ball_mem_nhds _ hr)] with w hw
    exact hdomain (φ w, R w) hw

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every full-jet interpolation of two literal root-coordinate sheets remains
in the original chart and positive Gram domain. Its slope derivative has a
linear bound uniform in both the root of unity and the interpolation parameter.
The same constant controls the full jet distance from its central value. -/
theorem chartLeadingPlaneProjection_interpolated_root_slope_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ)
    {m : ℕ} (hm : 1 ≤ m) {H : ℂ → ℝ}
    (hH : ContDiffAt ℝ 2 H 0) (hH0 : H 0 = 0) (hDH : fderiv ℝ H 0 = 0)
    (hHess : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q))
        (L (![1, Complex.I] i) + q.2 (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + q.2 (![1, Complex.I] j) • N)
    let A := fun q => complexPlaneMatrixOperator
      (Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1))
    let R := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let J : ℂ → (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) := fun w => ((P w, H w), R w)
    (∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ∀ w, P (ζ * w) = P w) ∧
      ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
        ∀ t ∈ Icc (0 : ℝ) 1,
        let q := (1 - t) • J (ζ * w) + t • J w
        (Y q ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
          0 < G q 0 0 * G q 1 1 - G q 0 1 ^ 2 ∧
          ‖(fderiv ℝ A q).comp (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ))‖ ≤ C * ‖w‖) ∧
        ‖q - ((c, 0), 0)‖ ≤ C * ‖w‖ := by
  intro Y G A R P J
  have hPζ (ζ : ℂ) (hζ : ζ ^ (m + 1) = 1) (w : ℂ) : P (ζ * w) = P w := by
    simp only [P, mul_pow, hζ, one_mul]
  refine ⟨hPζ, ?_⟩
  have houter := chartLeadingPlaneProjection_conductivity_jet_bounds g hsrc hb hnull hN hunit L hL c
  change ContDiffAt ℝ 2 A ((c, 0), 0) ∧ A ((c, 0), 0) = ContinuousLinearMap.id ℝ ℂ ∧ _ at houter
  obtain ⟨_hA, _hA0, r, B, hr, _hr1, hB, hbound, hdomain⟩ := houter
  obtain ⟨hR0, ε, hε, K, _hK, _hsize, _hder, hRLip⟩ :=
    Analysis.exists_normalized_gradient_bounds_of_hessian_order hm hH hDH hHess
  change R 0 = 0 at hR0
  let φ : ℂ → ℂ × ℝ := fun w => (P w, H w)
  have hφ : ContDiffAt ℝ 1 φ 0 :=
    (contDiffAt_const.add ((contDiffAt_id.pow (m + 1)).div_const
      ((m + 1 : ℕ) : ℂ))).prodMk (hH.of_le (by norm_num))
  obtain ⟨Kφ, S, hS, hφLip⟩ := hφ.exists_lipschitzOnWith
  let S' := S ∩ ball (0 : ℂ) ε
  have hS' : S' ∈ 𝓝 (0 : ℂ) := inter_mem hS (ball_mem_nhds _ hε)
  have h0S : (0 : ℂ) ∈ S' := mem_of_mem_nhds hS'
  let KJ : NNReal := max Kφ (3 * K).toNNReal
  have hJLip : LipschitzOnWith KJ J S' :=
    (hφLip.mono inter_subset_left).prodMk (hRLip.mono inter_subset_right)
  have hJ0 : J 0 = ((c, 0), 0) := by simp [J, P, hH0, hR0]
  have hJlim : Tendsto J (𝓝 (0 : ℂ)) (𝓝 ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ))) := by
    simpa only [hJ0] using (hJLip.continuousOn.continuousAt hS').tendsto
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ S' ∧ J w ∈ ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r := by
    filter_upwards [hS', hJlim.eventually (ball_mem_nhds _ hr)] with w hw hJw
    exact ⟨hw, hJw⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  let C : ℝ := (B + 1) * ((KJ : ℝ) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hBKC : B * (KJ : ℝ) ≤ C := by dsimp [C]; nlinarith [KJ.coe_nonneg]
  have hKC : (KJ : ℝ) ≤ C := by
    dsimp [C]
    nlinarith [KJ.coe_nonneg, mul_nonneg hB.le KJ.coe_nonneg]
  refine ⟨C, hC, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with w hwρ
  intro ζ hζ t ht
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by omega)
  have hw := hρsub hwρ
  have hζw := hρsub (show ζ * w ∈ ball (0 : ℂ) ρ from by
    simpa only [mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul] using hwρ)
  let q := (1 - t) • J (ζ * w) + t • J w
  have hq : q ∈ ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r :=
    (convex_ball _ _) hζw.2 hw.2 (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)
  have hfirst : ‖J w - ((c, 0), 0)‖ ≤ (KJ : ℝ) * ‖w‖ := by
    simpa only [hJ0, dist_eq_norm, sub_zero] using hJLip.dist_le_mul w hw.1 0 h0S
  have hsecond : ‖J (ζ * w) - ((c, 0), 0)‖ ≤ (KJ : ℝ) * ‖w‖ := by
    simpa only [hJ0, dist_eq_norm, sub_zero, norm_mul, hζnorm, one_mul] using
      hJLip.dist_le_mul (ζ * w) hζw.1 0 h0S
  have hqnorm : ‖q - ((c, 0), 0)‖ ≤ (KJ : ℝ) * ‖w‖ := by
    have heq : q - ((c, 0), 0) =
        (1 - t) • (J (ζ * w) - ((c, 0), 0)) + t • (J w - ((c, 0), 0)) := by
      calc
        q - ((c, 0), 0) = (1 - t) • J (ζ * w) + t • J w -
            ((1 - t) • (((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ))) +
              t • (((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)))) := by
          rw [← add_smul, sub_add_cancel, one_smul]
        _ = _ := by rw [smul_sub, smul_sub]; abel
    rw [heq]
    calc
      _ ≤ ‖(1 - t) • (J (ζ * w) - ((c, 0), 0))‖ +
          ‖t • (J w - ((c, 0), 0))‖ := norm_add_le _ _
      _ = (1 - t) * ‖J (ζ * w) - ((c, 0), 0)‖ + t * ‖J w - ((c, 0), 0)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * ((KJ : ℝ) * ‖w‖) + t * ((KJ : ℝ) * ‖w‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hfirst ht.1)
      _ = (KJ : ℝ) * ‖w‖ := by ring
  refine ⟨⟨(hdomain q hq).1, (hdomain q hq).2, ?_⟩, ?_⟩
  · calc
      _ ≤ B * ‖q - ((c, 0), 0)‖ := (hbound q hq).2.2
      _ ≤ B * ((KJ : ℝ) * ‖w‖) := mul_le_mul_of_nonneg_left hqnorm hB.le
      _ = (B * (KJ : ℝ)) * ‖w‖ := by ring
      _ ≤ C * ‖w‖ := mul_le_mul_of_nonneg_right hBKC (norm_nonneg w)
  · exact hqnorm.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg w))

end DifferentialGeometry.Geometry
