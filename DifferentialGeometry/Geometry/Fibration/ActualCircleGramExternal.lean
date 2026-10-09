import DifferentialGeometry.Geometry.Fibration.ActualConstantComparison

/-!
# TCP01's circle Gram bound against an EXTERNAL tolerance `γ_T`

Lanes C14-FAM2 / C14-FAM2b (external review 50, verdict 6 and lead decision T50-2): the circle
Gram clause of TCP01 (blueprint `master207B.tex`, TCP01, B:5250: "`‖Dη_i(Dη_i)^* − I‖ < γ/4` in
its own normalized metric on `B(p_i, 200)`") is consumed as a LEMMA with a smaller internal
quality and an INDEPENDENT external tolerance `γ_T`: the packet's own quality `γ` and the
splitting error `β₂` are requested below `γ_T/20` (and `β₂ ≤ 10⁻⁷`), and the bound `< γ_T/4` is
proved for the SAME chart — never "the same `γ` gives `γ/4`".

* `gram_external_kernel_FAM2` (kernel, any real inner product spaces `V`, `F`): from the two
  conclusions of the delivered `tcp01_gram` — `‖A w‖ ≤ 1 + γ` for unit `w`, and for every unit `ξ` a
  unit `w` with `⟨A w, ξ⟩ > 1 − d` — with `0 ≤ γ ≤ d < 1`: every singular value of `A` lies in
  `[1 − d, 1 + γ]` (`(1 − d) ≤ ‖A* ξ‖ ≤ 1 + γ` for unit `ξ`) and `‖AA* − I‖ ≤ 2d + d²`.
* `gram_external_right_inverse_FAM2`: for `d < 1/10` both singular values exceed `9/10` and `A` has
  a right inverse `R = A*(AA*)⁻¹` with `‖R‖ ≤ 1/(1 − d) < 2`.
* `gram_external_budget_FAM2`: `γ, β₂ ≤ γ_T/20`, `0 < γ_T ≤ 1` give `2d + d² < γ_T/4`, `d = γ + β₂`.
* `circle_split_error_nonneg_FAM2b` (`0 ≤ β₂`), `tcp01_gram_unit_FAM2b` (the kernel's two inputs in
  the normalized norm), `tcp01_gram_explicit_FAM2`, `tcp01_gram_external`,
  `tcp01_gram_right_inverse_FAM2`: the binding
  for `A = Dη_j(x)` of the circle chart of packet (i) of `LocalChartPackets` at a circle centre `j`,
  `x ∈ B(j, 200ρ(j))`, the tangent space normed by the chart's normalized metric `ρ(j)⁻² g`
  (`radialScaledBundle g ρ(j)⁻¹`, whose inner product is `ρ(j)⁻² g` by definition).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Kernel

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace V] [CompleteSpace F] in
/-- The upper bound on unit vectors gives the operator bound `‖A w‖ ≤ (1 + γ)‖w‖`. -/
theorem gram_upper_scale_FAM2 (A : V →L[ℝ] F) {γ : ℝ}
    (hup : ∀ w : V, ‖w‖ = 1 → ‖A w‖ ≤ 1 + γ) (w : V) : ‖A w‖ ≤ (1 + γ) * ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have h := hup _ hu
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn] at h
  rwa [inv_mul_le_iff₀ hn, mul_comm] at h

/-- The adjoint obeys the same upper bound: `‖A* ξ‖ ≤ (1 + γ)‖ξ‖`. -/
theorem gram_adjoint_upper_FAM2 (A : V →L[ℝ] F) {γ : ℝ} (hγ : 0 ≤ γ)
    (hup : ∀ w : V, ‖w‖ = 1 → ‖A w‖ ≤ 1 + γ) (ξ : F) :
    ‖ContinuousLinearMap.adjoint A ξ‖ ≤ (1 + γ) * ‖ξ‖ := by
  set y := ContinuousLinearMap.adjoint A ξ with hy
  have h1 : ‖y‖ ^ 2 = inner ℝ (A y) ξ := by
    rw [← real_inner_self_eq_norm_sq, hy, ContinuousLinearMap.adjoint_inner_right]
  have h2 : inner ℝ (A y) ξ ≤ ‖A y‖ * ‖ξ‖ := real_inner_le_norm _ _
  have h3 := gram_upper_scale_FAM2 A hup y
  rcases eq_or_ne ‖y‖ 0 with h0 | h0
  · rw [h0]; positivity
  have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have h4 : ‖y‖ ^ 2 ≤ (1 + γ) * ‖y‖ * ‖ξ‖ :=
    h1 ▸ h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
  have h5 : ‖y‖ * ‖y‖ ≤ ‖y‖ * ((1 + γ) * ‖ξ‖) := by nlinarith
  exact le_of_mul_le_mul_left h5 hpos

/-- The lower bound: `(1 − d)‖ξ‖ ≤ ‖A* ξ‖`. -/
theorem gram_adjoint_lower_FAM2 (A : V →L[ℝ] F) {d : ℝ}
    (hlow : ∀ ξ : F, ‖ξ‖ = 1 → ∃ w : V, ‖w‖ = 1 ∧ 1 - d < inner ℝ (A w) ξ) (ξ : F) :
    (1 - d) * ‖ξ‖ ≤ ‖ContinuousLinearMap.adjoint A ξ‖ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hu : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  obtain ⟨w, hw, hlt⟩ := hlow _ hu
  have h1 : inner ℝ (ContinuousLinearMap.adjoint A ξ) w = ‖ξ‖ * inner ℝ (A w) (‖ξ‖⁻¹ • ξ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, real_inner_smul_right,
      ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  have h2 : inner ℝ (ContinuousLinearMap.adjoint A ξ) w ≤ ‖ContinuousLinearMap.adjoint A ξ‖ := by
    have := real_inner_le_norm (ContinuousLinearMap.adjoint A ξ) w
    rwa [hw, mul_one] at this
  have h3 : (1 - d) * ‖ξ‖ ≤ ‖ξ‖ * inner ℝ (A w) (‖ξ‖⁻¹ • ξ) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hlt.le hn.le
  linarith

/-- `⟨(AA* − I)ξ, ξ⟩ = ‖A*ξ‖² − ‖ξ‖²`. -/
theorem gram_inner_self_FAM2 (A : V →L[ℝ] F) (ξ : F) :
    inner ℝ ((A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F) ξ) ξ =
      ‖ContinuousLinearMap.adjoint A ξ‖ ^ 2 - ‖ξ‖ ^ 2 := by
  rw [sub_apply, inner_sub_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ← ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- `AA* − I` is symmetric. -/
theorem gram_isSymmetric_FAM2 (A : V →L[ℝ] F) :
    (A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F).IsSymmetric := by
  intro x y
  change inner ℝ ((A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F) x) y =
    inner ℝ x ((A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F) y)
  rw [sub_apply, sub_apply, inner_sub_left,
    inner_sub_right, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]

/-- **The Gram kernel** (TCP01, review 50 T50-2): with `0 ≤ γ ≤ d < 1`, the two conclusions of
`tcp01_gram` (`‖A w‖ ≤ 1 + γ` on unit `w`; every unit `ξ` has a unit `w` with `⟨A w, ξ⟩ > 1 − d`)
give: every singular value of `A` lies in `[1 − d, 1 + γ]` (in the form `(1 − d) ≤ ‖A* ξ‖ ≤ 1 + γ`
for unit `ξ`) and `‖AA* − I‖ ≤ 2d + d²`. -/
theorem gram_external_kernel_FAM2 (A : V →L[ℝ] F) {γ d : ℝ} (hγ : 0 ≤ γ) (hγd : γ ≤ d)
    (hd1 : d < 1) (hup : ∀ w : V, ‖w‖ = 1 → ‖A w‖ ≤ 1 + γ)
    (hlow : ∀ ξ : F, ‖ξ‖ = 1 → ∃ w : V, ‖w‖ = 1 ∧ 1 - d < inner ℝ (A w) ξ) :
    (∀ ξ : F, ‖ξ‖ = 1 →
      1 - d ≤ ‖ContinuousLinearMap.adjoint A ξ‖ ∧ ‖ContinuousLinearMap.adjoint A ξ‖ ≤ 1 + γ) ∧
    ‖A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F‖ ≤ 2 * d + d ^ 2 := by
  have hup' := gram_adjoint_upper_FAM2 A hγ hup
  have hlow' := gram_adjoint_lower_FAM2 A hlow
  refine ⟨fun ξ hξ => ⟨?_, ?_⟩, ?_⟩
  · have := hlow' ξ; rwa [hξ, mul_one] at this
  · have := hup' ξ; rwa [hξ, mul_one] at this
  set T := A.comp (ContinuousLinearMap.adjoint A) - ContinuousLinearMap.id ℝ F with hT
  have hd0 : 0 ≤ d := hγ.trans hγd
  have hc0 : 0 ≤ 2 * d + d ^ 2 := by positivity
  have hbound : ∀ ξ : F, |inner ℝ (T ξ) ξ| ≤ (2 * d + d ^ 2) * ‖ξ‖ ^ 2 := by
    intro ξ
    rw [hT, gram_inner_self_FAM2]
    have hu := hup' ξ
    have hl := hlow' ξ
    have hn := norm_nonneg ξ
    have ha := norm_nonneg (ContinuousLinearMap.adjoint A ξ)
    have h1 : ((1 - d) * ‖ξ‖) ^ 2 ≤ ‖ContinuousLinearMap.adjoint A ξ‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hn) hl 2
    have h2 : ‖ContinuousLinearMap.adjoint A ξ‖ ^ 2 ≤ ((1 + γ) * ‖ξ‖) ^ 2 :=
      pow_le_pow_left₀ ha hu 2
    have h3 : ((1 + γ) * ‖ξ‖) ^ 2 ≤ ((1 + d) * ‖ξ‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hn) 2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ‖ξ‖, sq_nonneg d]
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T (hT ▸ gram_isSymmetric_FAM2 A)]
  refine ciSup_le fun ξ => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 2)]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simpa using hc0
  have hn : 0 < ‖ξ‖ ^ 2 := by have := norm_pos_iff.mpr hξ; positivity
  rw [div_le_iff₀ hn]
  exact hbound ξ

/-- **Right inverse of norm `< 2`** (TCP01, review 50 T50-2): for `0 ≤ γ ≤ d < 1/10`, both singular
values of `A` exceed `9/10` (`‖A* ξ‖ > 9/10` for unit `ξ`) and `A` has a right inverse `R` with
`‖R‖ ≤ 1/(1 − d) < 2`. -/
theorem gram_external_right_inverse_FAM2 (A : V →L[ℝ] F) {γ d : ℝ} (hγ : 0 ≤ γ) (hγd : γ ≤ d)
    (hd : d < 1 / 10) (hup : ∀ w : V, ‖w‖ = 1 → ‖A w‖ ≤ 1 + γ)
    (hlow : ∀ ξ : F, ‖ξ‖ = 1 → ∃ w : V, ‖w‖ = 1 ∧ 1 - d < inner ℝ (A w) ξ) :
    (∀ ξ : F, ‖ξ‖ = 1 → 9 / 10 < ‖ContinuousLinearMap.adjoint A ξ‖) ∧
    ∃ R : F →L[ℝ] V, A.comp R = ContinuousLinearMap.id ℝ F ∧ ‖R‖ ≤ 1 / (1 - d) ∧ ‖R‖ < 2 := by
  have hd0 : 0 ≤ d := hγ.trans hγd
  obtain ⟨hsv, hG⟩ := gram_external_kernel_FAM2 A hγ hγd (by linarith) hup hlow
  have hlow' := gram_adjoint_lower_FAM2 A hlow
  refine ⟨fun ξ hξ => ((hsv ξ hξ).1).trans_lt' (by linarith), ?_⟩
  set G := A.comp (ContinuousLinearMap.adjoint A) with hGdef
  have ht : ‖(1 : F →L[ℝ] F) - G‖ < 1 := by
    rw [norm_sub_rev]
    refine hG.trans_lt ?_
    nlinarith
  let u := Units.oneSub ((1 : F →L[ℝ] F) - G) ht
  have hu : (u : F →L[ℝ] F) = G := by
    simp only [u, Units.val_oneSub, sub_sub_cancel]
  refine ⟨(ContinuousLinearMap.adjoint A).comp (↑u⁻¹ : F →L[ℝ] F), ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_assoc, ← hGdef, ← hu, ← ContinuousLinearMap.mul_def,
      Units.mul_inv, ContinuousLinearMap.one_def]
  have h1d : 0 < 1 - d := by linarith
  have hR : ‖(ContinuousLinearMap.adjoint A).comp (↑u⁻¹ : F →L[ℝ] F)‖ ≤ 1 / (1 - d) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
    set y := (↑u⁻¹ : F →L[ℝ] F) ξ with hy
    have hGy : G y = ξ := by
      rw [hy, ← hu, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    rw [ContinuousLinearMap.comp_apply, ← hy]
    set z := ContinuousLinearMap.adjoint A y with hz
    have h1 : ‖z‖ ^ 2 = inner ℝ ξ y := by
      rw [← real_inner_self_eq_norm_sq, hz, ContinuousLinearMap.adjoint_inner_right, ← hGy,
        hGdef, ContinuousLinearMap.comp_apply]
    have h2 : inner ℝ ξ y ≤ ‖ξ‖ * ‖y‖ := real_inner_le_norm _ _
    have h3 : (1 - d) * ‖y‖ ≤ ‖z‖ := hlow' y
    have hz0 := norm_nonneg z
    have hξ0 := norm_nonneg ξ
    have hy0 := norm_nonneg y
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h1d]
    rcases eq_or_ne ‖z‖ 0 with h0 | h0
    · rw [h0, zero_mul]; exact hξ0
    have hzpos : 0 < ‖z‖ := lt_of_le_of_ne hz0 (Ne.symm h0)
    have h4 : (1 - d) * ‖z‖ ^ 2 ≤ ‖ξ‖ * ‖z‖ := by
      have := mul_le_mul_of_nonneg_left h3 hξ0
      nlinarith
    have h5 : ‖z‖ * ((1 - d) * ‖z‖) ≤ ‖z‖ * ‖ξ‖ := by nlinarith
    have := le_of_mul_le_mul_left h5 hzpos
    linarith
  refine ⟨hR, hR.trans_lt ?_⟩
  rw [div_lt_iff₀ h1d]
  linarith

/-- **The external Gram budget**: `0 ≤ γ ≤ γ_T/20`, `0 ≤ β ≤ γ_T/20`, `0 < γ_T ≤ 1` give
`2d + d² < γ_T/4` for `d = γ + β`. -/
theorem gram_external_budget_FAM2 {γ β γT : ℝ} (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hγT : γ ≤ γT / 20)
    (hβT : β ≤ γT / 20) (hT : 0 < γT) (hT1 : γT ≤ 1) :
    2 * (γ + β) + (γ + β) ^ 2 < γT / 4 := by
  have hd : γ + β ≤ γT / 10 := by linarith
  have hd0 : 0 ≤ γ + β := by linarith
  have h2 : (γ + β) ^ 2 ≤ (γT / 10) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  nlinarith

end Kernel

section Binding

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The splitting error `β₂` of packet (i) is nonnegative (at any circle centre). -/
theorem circle_split_error_nonneg_FAM2b
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {j : X} (hj : j ∈ P.circle.centres) : 0 ≤ β 2 := by
  let Aj := P.circleAdapted j hj
  let _ := Aj.instY
  exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
    Aj.split).le

/-- The two hypotheses of the Gram kernel for `A = Dη_j(x)` in the normalized metric `ρ(j)⁻² g`
(the norm of `radialScaledBundle g ρ(j)⁻¹`), from the delivered `tcp01_gram`. -/
theorem tcp01_gram_unit_FAM2b
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hβ : β 2 ≤ 1 / 10000000) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = 1 →
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖ ≤ 1 + γ) ∧
    ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = 1 ∧
      1 - (γ + β 2) <
        inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ := by
  let := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hγ0 := circle_quality_nonneg_KA4 P hj
  obtain ⟨hup, hlow⟩ := tcp01_gram P hγ0 hβ hj hx
  have hiff : ∀ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = 1 ↔ (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 := by
    intro w
    have h : ‖w‖ ^ 2 = (ρ j)⁻¹ ^ 2 * g.inner x w w := by
      rw [← real_inner_self_eq_norm_sq]
      rfl
    rw [← h]
    constructor
    · intro hw; rw [hw]; norm_num
    · intro hw; exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) (by norm_num)).mp hw
  refine ⟨fun w hw => hup w ((hiff w).mp hw), fun ξ hξ => ?_⟩
  obtain ⟨w, hw, -, hlt⟩ := hlow ξ hξ
  exact ⟨w, (hiff w).mpr hw, hlt⟩

/-- **TCP01's Gram bound, explicit** (review 50 T50-2): at a circle centre `j` and
`x ∈ B(j, 200ρ(j))`, with `β₂ ≤ 10⁻⁷` and `d = γ + β₂ < 1`, the differential `A = Dη_j(x)` of the
circle chart, in the normalized metric `ρ(j)⁻² g`, has every singular value in `[1 − d, 1 + γ]`
and `‖AA* − I‖ ≤ 2d + d²`. -/
theorem tcp01_gram_explicit_FAM2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ ξ : ℝ², ‖ξ‖ = 1 →
      1 - (γ + β 2) ≤ ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖ ∧
        ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖ ≤ 1 + γ) ∧
    ‖(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp
        (ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x)) -
      ContinuousLinearMap.id ℝ ℝ²‖ ≤ 2 * (γ + β 2) + (γ + β 2) ^ 2 := by
  let := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hγ0 := circle_quality_nonneg_KA4 P hj
  have hβ0 := circle_split_error_nonneg_FAM2b P hj
  obtain ⟨hup, hlow⟩ := tcp01_gram_unit_FAM2b P hβ hj hx
  exact gram_external_kernel_FAM2 _ hγ0 (by linarith) hd hup hlow

/-- **TCP01's Gram bound against an external tolerance `γ_T`** (review 50, verdict 6, T50-2): with
`0 < γ_T ≤ 1`, the packet's own quality `γ ≤ γ_T/20` and splitting error `β₂ ≤ min(10⁻⁷, γ_T/20)`,
the SAME circle chart satisfies `‖Dη_j(Dη_j)* − I‖ < γ_T/4` in its normalized metric on
`B(j, 200ρ(j))`. -/
theorem tcp01_gram_external
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {γT : ℝ} (hγT : 0 < γT) (hγT1 : γT ≤ 1) (hγ : γ ≤ γT / 20) (hβ : β 2 ≤ 1 / 10000000)
    (hβT : β 2 ≤ γT / 20) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ‖(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp
        (ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x)) -
      ContinuousLinearMap.id ℝ ℝ²‖ < γT / 4 := by
  let := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hγ0 := circle_quality_nonneg_KA4 P hj
  have hβ0 := circle_split_error_nonneg_FAM2b P hj
  have hd : γ + β 2 < 1 := by linarith
  exact (tcp01_gram_explicit_FAM2 P hβ hd hj hx).2.trans_lt
    (gram_external_budget_FAM2 hγ0 hβ0 hγ hβT hγT hγT1)

/-- **Right inverse of the circle differential** (review 50 T50-2): for `β₂ ≤ 10⁻⁷` and
`γ + β₂ < 1/10`, both singular values of `Dη_j(x)` exceed `9/10` and `Dη_j(x)` has a right inverse
`R` with `‖R‖ ≤ 1/(1 − (γ + β₂)) < 2` (normalized metric `ρ(j)⁻² g`). -/
theorem tcp01_gram_right_inverse_FAM2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ ξ : ℝ², ‖ξ‖ = 1 → 9 / 10 < ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖) ∧
    ∃ R : ℝ² →L[ℝ] TangentSpace 𝓘(ℝ, E3) x,
      (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp R =
        ContinuousLinearMap.id ℝ ℝ² ∧ ‖R‖ ≤ 1 / (1 - (γ + β 2)) ∧ ‖R‖ < 2 := by
  let := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hγ0 := circle_quality_nonneg_KA4 P hj
  have hβ0 := circle_split_error_nonneg_FAM2b P hj
  obtain ⟨hup, hlow⟩ := tcp01_gram_unit_FAM2b P hβ hj hx
  exact gram_external_right_inverse_FAM2 _ hγ0 (by linarith) hd hup hlow

end Binding

end DifferentialGeometry.Geometry.Collapse
