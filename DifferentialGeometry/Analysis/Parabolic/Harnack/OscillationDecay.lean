import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.MetricSpace.Holder

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

theorem pointwise_oscillation_decay_of_complementary_harnack
    {X : Type*} {early late : Set X} (hearly : early.Nonempty)
    (u : X → ℝ) (m M F : ℝ) (hF : 1 ≤ F)
    (hupper : ∀ e ∈ early, ∀ y ∈ late,
      M - u e ≤ F * (M - u y))
    (hlower : ∀ e ∈ early, ∀ y ∈ late,
      u e - m ≤ F * (u y - m)) :
    ∀ x ∈ late, ∀ y ∈ late,
      u y - u x ≤ (1 - 1 / F) * (M - m) := by
  obtain ⟨e, he⟩ := hearly
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  intro x hx y hy
  have hsum := add_le_add (hupper e he y hy) (hlower e he x hx)
  have hraw : M - m ≤ F * ((M - m) - (u y - u x)) := by
    convert hsum using 1 <;> ring
  have hdiv : (M - m) / F ≤ (M - m) - (u y - u x) := by
    apply (div_le_iff₀ hFpos).2
    simpa only [mul_comm] using hraw
  calc
    u y - u x ≤ (M - m) - (M - m) / F := by linarith
    _ = (1 - 1 / F) * (M - m) := by ring

theorem one_sub_inv_mem_Ico {F : ℝ} (hF : 1 ≤ F) :
    1 - 1 / F ∈ Set.Ico 0 1 := by
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hinvpos : 0 < 1 / F := div_pos zero_lt_one hFpos
  have hinvle : 1 / F ≤ 1 := (div_le_one hFpos).2 hF
  constructor <;> linarith

theorem dist_le_oscillation_contraction_of_complementary_harnack
    {X : Type*} {early late : Set X} (hearly : early.Nonempty)
    (u : X → ℝ) (m M F : ℝ) (hF : 1 ≤ F)
    (hupper : ∀ e ∈ early, ∀ y ∈ late,
      M - u e ≤ F * (M - u y))
    (hlower : ∀ e ∈ early, ∀ y ∈ late,
      u e - m ≤ F * (u y - m)) :
    ∀ x ∈ late, ∀ y ∈ late,
      dist (u x) (u y) ≤ (1 - 1 / F) * (M - m) := by
  intro x hx y hy
  have hxy := pointwise_oscillation_decay_of_complementary_harnack
    hearly u m M F hF hupper hlower x hx y hy
  have hyx := pointwise_oscillation_decay_of_complementary_harnack
    hearly u m M F hF hupper hlower y hy x hx
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem geometric_oscillation_decay
    (oscillation : ℕ → ℝ) {theta : ℝ}
    (htheta : 0 ≤ theta)
    (hstep : ∀ k, oscillation (k + 1) ≤ theta * oscillation k) :
    ∀ k, oscillation k ≤ theta ^ k * oscillation 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        oscillation (k + 1) ≤ theta * oscillation k := hstep k
        _ ≤ theta * (theta ^ k * oscillation 0) :=
          mul_le_mul_of_nonneg_left ih htheta
        _ = theta ^ (k + 1) * oscillation 0 := by ring

theorem exists_holder_exponent_of_contraction
    {lambda theta : ℝ}
    (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1) :
    ∃ alpha : NNReal, 0 < alpha ∧ alpha ≤ 1 ∧
      theta ≤ lambda ^ (alpha : ℝ) := by
  by_cases htheta_zero : theta = 0
  · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    rw [htheta_zero]
    exact Real.rpow_nonneg hlambda.le _
  have htheta_pos : 0 < theta := lt_of_le_of_ne htheta (Ne.symm htheta_zero)
  have hlog_theta : Real.log theta < 0 := Real.log_neg htheta_pos htheta_one
  have hlog_lambda : Real.log lambda < 0 := Real.log_neg hlambda hlambda_one
  let beta := Real.log theta / Real.log lambda
  have hbeta : 0 < beta := div_pos_of_neg_of_neg hlog_theta hlog_lambda
  let alpha : NNReal := ⟨min 1 beta, (lt_min zero_lt_one hbeta).le⟩
  have halpha : 0 < alpha := by
    exact_mod_cast (lt_min zero_lt_one hbeta)
  have halpha_one : alpha ≤ 1 := by
    exact_mod_cast (min_le_left 1 beta)
  refine ⟨alpha, halpha, halpha_one, ?_⟩
  have heq : theta = lambda ^ beta := by
    rw [Real.rpow_def_of_pos hlambda]
    rw [show Real.log lambda * beta = Real.log theta by
      dsimp only [beta]
      field_simp [ne_of_lt hlog_lambda]
    ]
    exact (Real.exp_log htheta_pos).symm
  rw [heq]
  apply Real.rpow_le_rpow_of_exponent_ge hlambda hlambda_one.le
  change (alpha : ℝ) ≤ beta
  exact min_le_right _ _

theorem exists_holder_exponent_of_harnack_factor
    {lambda F : ℝ}
    (hlambda : 0 < lambda) (hlambda_one : lambda < 1) (hF : 1 ≤ F) :
    ∃ alpha : NNReal, 0 < alpha ∧ alpha ≤ 1 ∧
      1 - 1 / F ≤ lambda ^ (alpha : ℝ) := by
  have htheta := one_sub_inv_mem_Ico hF
  exact exists_holder_exponent_of_contraction
    hlambda hlambda_one htheta.1 htheta.2

theorem dist_le_rpow_of_geometric_oscillation_decay
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (u : X → Y)
    {R lambda theta Omega alpha : ℝ}
    (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (htheta : 0 ≤ theta) (hOmega : 0 ≤ Omega) (halpha : 0 < alpha)
    (htheta_lambda : theta ≤ lambda ^ alpha)
    (hdecay : ∀ c ∈ s, ∀ k : ℕ, ∀ x ∈ s,
      dist c x ≤ lambda ^ k * R →
        dist (u c) (u x) ≤ Omega * theta ^ k)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : dist x y ≤ R) :
    dist (u x) (u y) ≤
      Omega * (lambda * R) ^ (-alpha) * dist x y ^ alpha := by
  by_cases hzero : dist x y = 0
  · have hxeq : x = y := dist_eq_zero.mp hzero
    subst y
    rw [dist_self, dist_self, Real.zero_rpow halpha.ne']
    positivity
  have hdist : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
  have hratio_pos : 0 < dist x y / R := div_pos hdist hR
  have hratio_le : dist x y / R ≤ 1 := (div_le_one hR).2 hxy
  obtain ⟨k, hk_lower, hk_upper⟩ :=
    exists_nat_pow_near_of_lt_one hratio_pos hratio_le hlambda hlambda_one
  have hscale_upper : dist x y ≤ lambda ^ k * R := by
    exact (div_le_iff₀ hR).1 hk_upper
  have hdecay_xy := hdecay x hx k y hy hscale_upper
  have htheta_pow : theta ^ k ≤ (lambda ^ alpha) ^ k :=
    pow_le_pow_left₀ htheta htheta_lambda k
  have hlambda_pow_rpow : (lambda ^ alpha) ^ k = (lambda ^ k) ^ alpha := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlambda.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hlambda.le]
    congr 1
    ring
  have hlambdaR_pos : 0 < lambda * R := mul_pos hlambda hR
  have hscale_lower : lambda ^ k < dist x y / (lambda * R) := by
    apply (lt_div_iff₀ hlambdaR_pos).2
    have hmul : lambda ^ k * (lambda * R) = lambda ^ (k + 1) * R := by
      rw [pow_succ]
      ring
    rw [hmul]
    exact (lt_div_iff₀ hR).1 hk_lower
  have hscale_rpow : (lambda ^ k) ^ alpha ≤
      (dist x y / (lambda * R)) ^ alpha :=
    (Real.rpow_lt_rpow (pow_nonneg hlambda.le k) hscale_lower halpha).le
  calc
    dist (u x) (u y) ≤ Omega * theta ^ k := hdecay_xy
    _ ≤ Omega * (lambda ^ alpha) ^ k :=
      mul_le_mul_of_nonneg_left htheta_pow hOmega
    _ = Omega * (lambda ^ k) ^ alpha := by rw [hlambda_pow_rpow]
    _ ≤ Omega * (dist x y / (lambda * R)) ^ alpha :=
      mul_le_mul_of_nonneg_left hscale_rpow hOmega
    _ = Omega * (lambda * R) ^ (-alpha) * dist x y ^ alpha := by
      rw [Real.div_rpow hdist.le hlambdaR_pos.le]
      rw [Real.rpow_neg hlambdaR_pos.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hlambdaR_pos alpha)]

theorem holderOnWith_of_geometric_oscillation_decay
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (u : X → Y)
    {R lambda theta Omega : ℝ} {alpha : NNReal}
    (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (htheta : 0 ≤ theta) (hOmega : 0 ≤ Omega) (halpha : 0 < alpha)
    (htheta_lambda : theta ≤ lambda ^ (alpha : ℝ))
    (hdiameter : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ R)
    (hdecay : ∀ c ∈ s, ∀ k : ℕ, ∀ x ∈ s,
      dist c x ≤ lambda ^ k * R →
        dist (u c) (u x) ≤ Omega * theta ^ k) :
    HolderOnWith
      ⟨Omega * (lambda * R) ^ (-(alpha : ℝ)),
        mul_nonneg hOmega (Real.rpow_nonneg (mul_pos hlambda hR).le _)⟩
      alpha u s := by
  intro x hx y hy
  have halpha_real : 0 < (alpha : ℝ) := by exact_mod_cast halpha
  have hreal := dist_le_rpow_of_geometric_oscillation_decay u hR hlambda
    hlambda_one htheta hOmega halpha_real htheta_lambda hdecay hx hy
      (hdiameter x hx y hy)
  have hconstant : 0 ≤ Omega * (lambda * R) ^ (-(alpha : ℝ)) :=
    mul_nonneg hOmega (Real.rpow_nonneg (mul_pos hlambda hR).le _)
  let K : NNReal := ⟨Omega * (lambda * R) ^ (-(alpha : ℝ)), hconstant⟩
  have hofReal := ENNReal.ofReal_le_ofReal hreal
  change edist (u x) (u y) ≤ (K : ENNReal) * edist x y ^ (alpha : ℝ)
  calc
    edist (u x) (u y) = ENNReal.ofReal (dist (u x) (u y)) := edist_dist _ _
    _ ≤ ENNReal.ofReal
        ((Omega * (lambda * R) ^ (-(alpha : ℝ))) *
          dist x y ^ (alpha : ℝ)) := hofReal
    _ = ENNReal.ofReal (Omega * (lambda * R) ^ (-(alpha : ℝ))) *
        ENNReal.ofReal (dist x y ^ (alpha : ℝ)) := by
      rw [ENNReal.ofReal_mul hconstant]
    _ = (K : ENNReal) * edist x y ^ (alpha : ℝ) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg halpha_real.le]
      rw [(ENNReal.ofReal_eq_coe_nnreal hconstant).symm]

theorem holderOnWith_of_oscillation_decay
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (u : X → Y) (oscillation : X → ℕ → ℝ)
    {R lambda theta Omega : ℝ} {alpha : NNReal}
    (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (htheta : 0 ≤ theta) (hOmega : 0 ≤ Omega) (halpha : 0 < alpha)
    (htheta_lambda : theta ≤ lambda ^ (alpha : ℝ))
    (hdiameter : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ R)
    (hinitial : ∀ c ∈ s, oscillation c 0 ≤ Omega)
    (hstep : ∀ c ∈ s, ∀ k : ℕ,
      oscillation c (k + 1) ≤ theta * oscillation c k)
    (hbound : ∀ c ∈ s, ∀ k : ℕ, ∀ x ∈ s,
      dist c x ≤ lambda ^ k * R →
        dist (u c) (u x) ≤ oscillation c k) :
    HolderOnWith
      ⟨Omega * (lambda * R) ^ (-(alpha : ℝ)),
        mul_nonneg hOmega (Real.rpow_nonneg (mul_pos hlambda hR).le _)⟩
      alpha u s := by
  apply holderOnWith_of_geometric_oscillation_decay u hR hlambda
    hlambda_one htheta hOmega halpha htheta_lambda hdiameter
  intro c hc k x hx hdist
  calc
    dist (u c) (u x) ≤ oscillation c k := hbound c hc k x hx hdist
    _ ≤ theta ^ k * oscillation c 0 :=
      geometric_oscillation_decay (oscillation c) htheta (hstep c hc) k
    _ ≤ theta ^ k * Omega :=
      mul_le_mul_of_nonneg_left (hinitial c hc) (pow_nonneg htheta k)
    _ = Omega * theta ^ k := mul_comm _ _

theorem exists_holderOnWith_of_oscillation_decay
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (u : X → Y) (oscillation : X → ℕ → ℝ)
    {R lambda theta Omega : ℝ}
    (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1) (hOmega : 0 ≤ Omega)
    (hdiameter : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ R)
    (hinitial : ∀ c ∈ s, oscillation c 0 ≤ Omega)
    (hstep : ∀ c ∈ s, ∀ k : ℕ,
      oscillation c (k + 1) ≤ theta * oscillation c k)
    (hbound : ∀ c ∈ s, ∀ k : ℕ, ∀ x ∈ s,
      dist c x ≤ lambda ^ k * R →
        dist (u c) (u x) ≤ oscillation c k) :
    ∃ alpha : NNReal, 0 < alpha ∧ alpha ≤ 1 ∧
      HolderOnWith
        ⟨Omega * (lambda * R) ^ (-(alpha : ℝ)),
          mul_nonneg hOmega (Real.rpow_nonneg (mul_pos hlambda hR).le _)⟩
        alpha u s := by
  obtain ⟨alpha, halpha, halpha_one, htheta_alpha⟩ :=
    exists_holder_exponent_of_contraction hlambda hlambda_one htheta htheta_one
  refine ⟨alpha, halpha, halpha_one, ?_⟩
  exact holderOnWith_of_oscillation_decay u oscillation hR hlambda hlambda_one
    htheta hOmega halpha htheta_alpha hdiameter hinitial hstep hbound

end DifferentialGeometry.Analysis.Parabolic.Harnack
