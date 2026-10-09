import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamily

/-!
# FC11 on the actual manifold: freezing the variable scale `ρ` at `R = ρ(p)`

Blueprint `master207B.tex`, FC11 (`lem:fibration-freeze-scale`, B:665–699): with `R = ρ(p)`,
`D = B(p, LR)`, `ρ` smooth, positive and `Λ`-Lipschitz, all derivatives in `R⁻² g`, `σ = ρ/R`:
`|σ − 1| ≤ LΛ`, `|dσ| ≤ Λ`, `1/2 ≤ σ ≤ 3/2` (for `LΛ ≤ 1/2`), the product estimate
`‖σF − F‖_{C¹} ≤ Λ((L+1)VΔ + LA)` and the quotient estimate
`‖u/σ − u‖_{C¹} ≤ Λ((2L+4)CΔ + 2LD₁)`. The normed-space kernels are `freeze_scale_product_c1_le`,
`freeze_scale_quotient_c1_le` (`Analysis/Calculus/FreezeScale.lean`) and
`finite_packet_freeze_actual_scale`; this module states FC11 on the actual Riemannian manifold
(convention T0: `riemannianEDistOf g = d`), pointwise in the tangent vector `v`, with the norm
`√(R⁻² g(v, v))` of the normalized metric written out.

* `fc11_actual_scale`: the three scale clauses.
* `fc11_actual_product`: the product estimate (value and differential).
* `fc11_actual_quotient`: the quotient estimate (value and differential).
* `fc11_scale_packets`: consumer — the scale clauses on every comparison ball `B(p, Lρ(p))` of an
  actual LC87 family (`LocalChartFamily`, smooth `Λ`-Lipschitz scale).

Dropped (unused): `L > 0` (implied by `x ∈ B(p, LR)`), `Δ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompleteSpace M]
  [SigmaCompactSpace M]

/-- `√(R⁻² a) = R⁻¹ √a` for `R > 0`. -/
theorem sqrt_inv_sq_mul_FC19 {R : ℝ} (hR : 0 < R) (a : ℝ) :
    Real.sqrt (R⁻¹ ^ 2 * a) = R⁻¹ * Real.sqrt a := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hR).le]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [CompleteSpace M] [SigmaCompactSpace M] in
/-- The differential of `σ = ρ/R` at `x`: `dσ(v) = dρ(v)/R`. -/
theorem mvfderiv_div_const_FC19 {ρ : M → ℝ} {x : M} (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (R : ℝ) (v : TangentSpace I x) :
    mvfderiv I (fun y => ρ y / R) x v = R⁻¹ * mvfderiv I ρ x v := by
  have h := mvfderiv_comp_hasDerivAt hρ ((hasDerivAt_id' (ρ x)).div_const R) v
  exact h.trans (by ring)

/-- **FC11, scale clauses** on the actual manifold: for `x ∈ B(p, Lρ(p))` and `σ = ρ/ρ(p)`,
`|σ(x) − 1| ≤ LΛ`, `|dσ_x(v)| ≤ Λ √(ρ(p)⁻² g(v, v))`, and `σ(x) ∈ [1/2, 3/2]` when `LΛ ≤ 1/2`. -/
theorem fc11_actual_scale (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {ρ : M → ℝ} (hρ : ∀ q, 0 < ρ q) (hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : LipschitzWith (Real.toNNReal Λ) ρ) {p x : M} {L : ℝ} (hx : x ∈ ball p (L * ρ p)) :
    |ρ x / ρ p - 1| ≤ L * Λ ∧
      (∀ v : TangentSpace I x, |mvfderiv I (fun y => ρ y / ρ p) x v| ≤
        Λ * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v)) ∧
      (L * Λ ≤ 1 / 2 → ρ x / ρ p ∈ Icc (1 / 2) (3 / 2)) := by
  have hrp := hρ p
  have hd : dist x p < L * ρ p := mem_ball.mp hx
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hlipd : |ρ x - ρ p| ≤ Λ * dist x p := by
    have h := hlip.dist_le_mul x p
    rw [hc, Real.dist_eq] at h
    exact h
  have hclose : |ρ x / ρ p - 1| ≤ L * Λ := by
    have heq : ρ x / ρ p - 1 = (ρ x - ρ p) / ρ p := by field_simp
    rw [heq, abs_div, abs_of_pos hrp, div_le_iff₀ hrp]
    calc |ρ x - ρ p| ≤ Λ * dist x p := hlipd
      _ ≤ Λ * (L * ρ p) := mul_le_mul_of_nonneg_left hd.le hΛ
      _ = L * Λ * ρ p := by ring
  refine ⟨hclose, fun v => ?_, fun hsmall => ?_⟩
  · have hρx : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x := (hsm x).mdifferentiableAt (by simp)
    rw [mvfderiv_div_const_FC19 hρx (ρ p) v, sqrt_inv_sq_mul_FC19 hrp, abs_mul,
      abs_of_pos (inv_pos.mpr hrp)]
    have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hρx
      (L := Λ) (fun y _ z _ => by
        have h := hlip.dist_le_mul y z
        rw [hc, Real.dist_eq] at h
        exact h) v
    calc (ρ p)⁻¹ * |mvfderiv I ρ x v| ≤ (ρ p)⁻¹ * (Λ * Real.sqrt (g.inner x v v)) :=
          mul_le_mul_of_nonneg_left hb (inv_pos.mpr hrp).le
      _ = Λ * ((ρ p)⁻¹ * Real.sqrt (g.inner x v v)) := by ring
  · have h := abs_le.mp hclose
    constructor <;> linarith [h.1, h.2]

/-- **FC11, product estimate** on the actual manifold: a block `F` with `‖F(x)‖ ≤ VΔ` and
`‖dF_x(v)‖ ≤ A √(ρ(p)⁻² g(v, v))` (`A ≥ 0`) has `‖σF − F‖ ≤ Λ((L+1)VΔ + LA)` at `x` and the same
bound, times `√(ρ(p)⁻² g(v, v))`, for the differential. -/
theorem fc11_actual_product (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {ρ : M → ℝ} (hρ : ∀ q, 0 < ρ q) (hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : LipschitzWith (Real.toNNReal Λ) ρ) {p x : M} {L : ℝ} (hx : x ∈ ball p (L * ρ p))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : M → W}
    (hF : MDifferentiableAt I 𝓘(ℝ, W) F x) {V Δ A : ℝ} (hA : 0 ≤ A) (hFv : ‖F x‖ ≤ V * Δ)
    (hDF : ∀ v : TangentSpace I x,
      ‖mvfderiv I F x v‖ ≤ A * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v)) :
    ‖(ρ x / ρ p) • F x - F x‖ ≤ Λ * ((L + 1) * V * Δ + L * A) ∧
      ∀ v : TangentSpace I x,
        ‖mvfderiv I (fun y => (ρ y / ρ p) • F y) x v - mvfderiv I F x v‖ ≤
          Λ * ((L + 1) * V * Δ + L * A) * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v) := by
  obtain ⟨hclose, hdσ, -⟩ := fc11_actual_scale g hmetric hρ hsm hΛ hlip hx
  have hrp := hρ p
  have hL : 0 ≤ L := by
    have h0 := dist_nonneg (x := x) (y := p)
    have h1 := mem_ball.mp hx
    by_contra hneg
    have hneg' : L < 0 := lt_of_not_ge hneg
    nlinarith [hρ p]
  have hVΔ : 0 ≤ V * Δ := (norm_nonneg _).trans hFv
  have hLΛ : 0 ≤ L * Λ := mul_nonneg hL hΛ
  have hval : ‖(ρ x / ρ p) • F x - F x‖ ≤ L * Λ * (V * Δ) := by
    have heq : (ρ x / ρ p) • F x - F x = (ρ x / ρ p - 1) • F x := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hclose hFv (norm_nonneg _) hLΛ
  refine ⟨hval.trans (by nlinarith [mul_nonneg hΛ hVΔ, mul_nonneg hΛ (mul_nonneg hL hA)]),
    fun v => ?_⟩
  set ν := Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v) with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hσs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => ρ y / ρ p) :=
    (contDiff_id.div_const (ρ p)).contMDiff.comp hsm
  have hσd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ρ y / ρ p) x :=
    (hσs x).mdifferentiableAt (by simp)
  have hprod := mvfderiv_fun_smul hσd hF
  have hexp : mvfderiv I (fun y => (ρ y / ρ p) • F y) x v - mvfderiv I F x v =
      (ρ x / ρ p - 1) • mvfderiv I F x v + mvfderiv I (fun y => ρ y / ρ p) x v • F x := by
    rw [hprod]
    change (ρ x / ρ p) • mvfderiv I F x v + mvfderiv I (fun y => ρ y / ρ p) x v • F x -
      mvfderiv I F x v = _
    rw [sub_smul, one_smul]
    abel
  rw [hexp]
  have h1 : ‖(ρ x / ρ p - 1) • mvfderiv I F x v‖ ≤ L * Λ * (A * ν) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hclose (hDF v) (norm_nonneg _) hLΛ
  have h2 : ‖mvfderiv I (fun y => ρ y / ρ p) x v • F x‖ ≤ Λ * ν * (V * Δ) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hdσ v) hFv (norm_nonneg _) (mul_nonneg hΛ hν0)
  calc _ ≤ ‖(ρ x / ρ p - 1) • mvfderiv I F x v‖ +
        ‖mvfderiv I (fun y => ρ y / ρ p) x v • F x‖ := norm_add_le _ _
    _ ≤ L * Λ * (A * ν) + Λ * ν * (V * Δ) := add_le_add h1 h2
    _ ≤ Λ * ((L + 1) * V * Δ + L * A) * ν := by
        nlinarith [mul_nonneg (mul_nonneg hΛ hν0) (mul_nonneg hL hVΔ)]

/-- **FC11, quotient estimate** on the actual manifold: for `LΛ ≤ 1/2`, a scalar `u` with
`|u(x)| ≤ CΔ` and `|du_x(v)| ≤ D₁ √(ρ(p)⁻² g(v, v))` (`D₁ ≥ 0`) has
`|u/σ − u| ≤ Λ((2L+4)CΔ + 2LD₁)` at `x` and the same bound, times `√(ρ(p)⁻² g(v, v))`, for the
differential. -/
theorem fc11_actual_quotient (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {ρ : M → ℝ} (hρ : ∀ q, 0 < ρ q) (hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : LipschitzWith (Real.toNNReal Λ) ρ) {p x : M} {L : ℝ} (hx : x ∈ ball p (L * ρ p))
    (hsmall : L * Λ ≤ 1 / 2) {u : M → ℝ} (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    {C Δ D₁ : ℝ} (hD₁ : 0 ≤ D₁) (huv : |u x| ≤ C * Δ)
    (hDu : ∀ v : TangentSpace I x,
      |mvfderiv I u x v| ≤ D₁ * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v)) :
    |u x / (ρ x / ρ p) - u x| ≤ Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) ∧
      ∀ v : TangentSpace I x,
        |mvfderiv I (fun y => u y / (ρ y / ρ p)) x v - mvfderiv I u x v| ≤
          Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v) := by
  obtain ⟨hclose, hdσ, hint⟩ := fc11_actual_scale g hmetric hρ hsm hΛ hlip hx
  have hrp := hρ p
  have hL : 0 ≤ L := by
    have h0 := dist_nonneg (x := x) (y := p)
    have h1 := mem_ball.mp hx
    by_contra hneg
    have hneg' : L < 0 := lt_of_not_ge hneg
    nlinarith [hρ p]
  have hCΔ : 0 ≤ C * Δ := (abs_nonneg _).trans huv
  have hLΛ : 0 ≤ L * Λ := mul_nonneg hL hΛ
  set σx := ρ x / ρ p with hσx
  have hσI := hint hsmall
  have hσ0 : 0 < σx := by linarith [hσI.1]
  have hinv2 : σx⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hσ0 (by norm_num)]
    linarith [hσI.1]
  have hiclose : |σx⁻¹ - 1| ≤ 2 * (L * Λ) := by
    have heq : σx⁻¹ - 1 = (1 - σx) * σx⁻¹ := by field_simp
    rw [heq, abs_mul, abs_sub_comm, abs_of_pos (inv_pos.mpr hσ0)]
    calc |σx - 1| * σx⁻¹ ≤ (L * Λ) * 2 :=
          mul_le_mul hclose hinv2 (inv_nonneg.mpr hσ0.le) hLΛ
      _ = 2 * (L * Λ) := by ring
  have hval : |u x / σx - u x| ≤ 2 * (L * Λ) * (C * Δ) := by
    have heq : u x / σx - u x = (σx⁻¹ - 1) * u x := by rw [div_eq_mul_inv]; ring
    rw [heq, abs_mul]
    exact mul_le_mul hiclose huv (abs_nonneg _) (by positivity)
  refine ⟨hval.trans (by nlinarith [mul_nonneg hΛ hCΔ, mul_nonneg hΛ (mul_nonneg hL hD₁)]),
    fun v => ?_⟩
  set ν := Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v) with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hσs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => ρ y / ρ p) :=
    (contDiff_id.div_const (ρ p)).contMDiff.comp hsm
  have hσd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ρ y / ρ p) x :=
    (hσs x).mdifferentiableAt (by simp)
  have hinvd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (ρ y / ρ p)⁻¹) x :=
    hσd.inv hσ0.ne'
  have hdinv : mvfderiv I (fun y => (ρ y / ρ p)⁻¹) x v =
      -(σx ^ 2)⁻¹ * mvfderiv I (fun y => ρ y / ρ p) x v :=
    mvfderiv_comp_hasDerivAt hσd (hasDerivAt_inv hσ0.ne') v
  have hmul : mvfderiv I (fun y => u y * (ρ y / ρ p)⁻¹) x v =
      u x * mvfderiv I (fun y => (ρ y / ρ p)⁻¹) x v + (ρ x / ρ p)⁻¹ * mvfderiv I u x v := by
    rw [mvfderiv_fun_mul hu hinvd]
    rfl
  have hfun : (fun y => u y / (ρ y / ρ p)) = fun y => u y * (ρ y / ρ p)⁻¹ := by
    funext y
    rw [div_eq_mul_inv]
  have hexp : mvfderiv I (fun y => u y / (ρ y / ρ p)) x v - mvfderiv I u x v =
      (σx⁻¹ - 1) * mvfderiv I u x v +
        u x * (-(σx ^ 2)⁻¹ * mvfderiv I (fun y => ρ y / ρ p) x v) := by
    rw [hfun, hmul, hdinv]
    ring
  rw [hexp]
  have hsq : (σx ^ 2)⁻¹ ≤ 4 := by
    rw [← inv_pow]
    have h0 : 0 ≤ σx⁻¹ := inv_nonneg.mpr hσ0.le
    nlinarith
  have h1 : |(σx⁻¹ - 1) * mvfderiv I u x v| ≤ 2 * (L * Λ) * (D₁ * ν) := by
    rw [abs_mul]
    exact mul_le_mul hiclose (hDu v) (abs_nonneg _) (by positivity)
  have h2 : |u x * (-(σx ^ 2)⁻¹ * mvfderiv I (fun y => ρ y / ρ p) x v)| ≤
      (C * Δ) * (4 * (Λ * ν)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr (pow_pos hσ0 2))]
    exact mul_le_mul huv (mul_le_mul hsq (hdσ v) (abs_nonneg _) (by norm_num))
      (by positivity) hCΔ
  calc _ ≤ |(σx⁻¹ - 1) * mvfderiv I u x v| +
        |u x * (-(σx ^ 2)⁻¹ * mvfderiv I (fun y => ρ y / ρ p) x v)| := abs_add_le _ _
    _ ≤ 2 * (L * Λ) * (D₁ * ν) + (C * Δ) * (4 * (Λ * ν)) := add_le_add h1 h2
    _ ≤ Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) * ν := by
        nlinarith [mul_nonneg (mul_nonneg hΛ hν0) (mul_nonneg hL hCΔ)]

end Kernel

section Packets

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- **Consumer: FC11 on the actual LC87 scale.** On every comparison ball `B(p, Lρ(p))` of an
actual family with `LΛ ≤ 1/2`, the frozen scale `σ = ρ/ρ(p)` is within `LΛ` of one, lies in
`[1/2, 3/2]`, and its differential is bounded by `Λ` in the normalized metric `ρ(p)⁻² g`. -/
theorem fc11_scale_packets
    (P : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    {p x : X} {L : ℝ} (hx : x ∈ ball p (L * ρ p)) (hsmall : L * Λ ≤ 1 / 2) :
    |ρ x / ρ p - 1| ≤ L * Λ ∧ ρ x / ρ p ∈ Icc (1 / 2) (3 / 2) ∧
      ∀ v : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) (fun y => ρ y / ρ p) x v| ≤
        Λ * Real.sqrt ((ρ p)⁻¹ ^ 2 * g.inner x v v) := by
  obtain ⟨h1, h2, h3⟩ := fc11_actual_scale g hmetric hρ P.contMDiff_scale hΛ P.lipschitz_scale hx
  exact ⟨h1, h3 hsmall, h2⟩

end Packets

end DifferentialGeometry.Geometry.Collapse
