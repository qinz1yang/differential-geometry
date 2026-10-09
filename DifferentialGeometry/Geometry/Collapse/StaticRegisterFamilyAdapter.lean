import DifferentialGeometry.Geometry.Collapse.StaticRegister

/-!
# The parameters of the final chapter-13 family read off a closed register (FC39-VAL, A1–A8)

Design `build-logs/resume/design-FC39-VAL.md` §2 (external review 49, T49-4). The final family
`LocalChartPacketsC14 … Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz` has more
parameters than PBR01's register (`StaticRegister.lean:281–359`). Each family parameter is a
DETERMINISTIC function of the register `R` (no choice), so that the validity record and the rows at
`R` speak about the same numbers:

* the register's own values: `Λ, Δ, μ, b, τ, γ, T = T₀, V, e = e₀, vs = ve`;
* A1 collar `γc := γ`, `βc := γ / 2000`; A2 smoothing `ε := min 10⁻⁸ (γ / 16000)`;
* A3 splitting vector `β 1 = β₁`, `β 2 = β₂`, `β 3 = β₃`;
* A4 qualities `σc = σs := qe` (PR14's "original edge/slim qualities", B:10148–10152);
* A5 zero tolerances `cap := min ε₀ (θ_s/(100L), θ_e/(100L), θ₂/100)` and the LC73 quality
  `ζ := min (θ_s²/(2·10⁶), θ_e²/10⁸, θ₂²/1000, 1/(1000 L))` (the rows' requests, design C14-FAM
  table (g) entry 12);
* A6 weak/endpoint qualities `b' := τ b'`, `s' := τ s'`, `s := τ s` (review item R-a (ii): the
  producer needs `b', s' < τΔ/10⁹`, C14P:229, which no slot of the register can force);
* A8 `Lmax := 1 + max 1 (400 V)`.

The producer's own conditions that follow from the register ALONE are proved here; those that need
the slot functions (`σc ≤ σ₀`, `τ ≤ τ₀`, `140√τ < ε²/20`, …) are the binding's job.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse

namespace ClosedRegister

variable {D : ClosedEarlyData} {T : ClosedThresholds D} (R : ClosedRegister D T)

/-- A1: the collar quality `γc := γ`. -/
def famγc : ℝ := R.later.circle.γ

/-- A1: the collar transversality `βc := γ / 2000`. -/
def famβc : ℝ := R.later.circle.γ / 2000

/-- A2: the distance-smoothing error `ε := min 10⁻⁸ (γ / 16000)` (root budget `ε < γc/8000`). -/
def famε : ℝ := min (1 / 10 ^ 8) (R.later.circle.γ / 16000)

/-- A3: the splitting vector `β 1 = β₁`, `β 2 = β₂`, `β 3 = β₃`, `0` elsewhere. -/
def famβ (n : ℕ) : ℝ :=
  if n = 1 then R.later.split.β₁ else if n = 2 then R.later.excl.β₂
    else if n = 3 then R.later.excl.β₃ else 0

/-- A4: the edge quality `σc := qe`. -/
def famσc : ℝ := R.later.err.qe

/-- A4: the slim quality `σs := qe`. -/
def famσs : ℝ := R.later.err.qe

/-- A6: the weak edge quality `b' := τ b'`. -/
def famb' : ℝ := R.later.err.τ * R.later.err.b'

/-- A6: the weak slim quality `s' := τ s'`. -/
def fams' : ℝ := R.later.err.τ * R.later.err.s'

/-- A6: the strong endpoint quality `s := τ s`. -/
def fams : ℝ := R.later.err.τ * R.later.err.s

/-- A8: `Lmax := 1 + max 1 (400 V)` (strictly above `400 V`, PR24 B:10234). -/
def famLmax : ℝ := 1 + max 1 (400 * R.later.split.V)

/-- A5: the requested cap of the zero radial difference-Lipschitz constant. -/
def famCap : ℝ :=
  min R.later.err.ε₀ (min (R.later.circle.θs / (100 * closedLongLength R.later.excl))
    (min (R.later.circle.θe / (100 * closedLongLength R.later.excl)) (R.later.circle.θ₂ / 100)))

/-- A5: the LC73 shell quality `ζ` of the rows. -/
def famζ : ℝ :=
  min (R.later.circle.θs ^ 2 / (2 * 10 ^ 6)) (min (R.later.circle.θe ^ 2 / 10 ^ 8)
    (min (R.later.circle.θ₂ ^ 2 / 1000) (1 / (1000 * closedLongLength R.later.excl))))

/-!
### The producer's conditions that follow from the register alone -/

theorem famγc_pos_VAL : 0 < R.famγc := R.later.γ_pos

theorem famβc_pos_VAL : 0 < R.famβc := by
  have := R.later.γ_pos
  unfold famβc
  positivity

theorem famβc_lt_VAL : R.famβc < R.famγc / 1000 := by
  have := R.later.γ_pos
  unfold famβc famγc
  linarith

theorem famε_pos_VAL : 0 < R.famε := by
  have := R.later.γ_pos
  exact lt_min (by norm_num) (by positivity)

theorem famε_le_VAL : R.famε ≤ 1 / 10 ^ 8 := min_le_left _ _

theorem famε_lt_hundredth_VAL : R.famε < 1 / 100 :=
  R.famε_le_VAL.trans_lt (by norm_num)

/-- The root budget's smoothing part (disp-50 A2): `ε < γc / 8000`. -/
theorem famε_lt_VAL : R.famε < R.famγc / 8000 := by
  have := R.later.γ_pos
  have h : R.famε ≤ R.later.circle.γ / 16000 := min_le_right _ _
  unfold famγc
  linarith

@[simp] theorem famβ_one_VAL : R.famβ 1 = R.later.split.β₁ := by simp [famβ]

@[simp] theorem famβ_two_VAL : R.famβ 2 = R.later.excl.β₂ := by simp [famβ]

@[simp] theorem famβ_three_VAL : R.famβ 3 = R.later.excl.β₃ := by simp [famβ]

theorem famβ_one_pos_VAL : 0 < R.famβ 1 := by
  rw [famβ_one_VAL]
  exact R.later.β₁_pos

theorem famβ_one_lt_one_VAL : R.famβ 1 < 1 := by
  rw [famβ_one_VAL]
  have := R.later.β₁_lt_β₂
  have := R.later.β₂_lt_audit
  linarith

theorem famσc_pos_VAL : 0 < R.famσc := R.later.qe_pos

theorem famσs_pos_VAL : 0 < R.famσs := R.later.qe_pos

/-- `qe < θ_e²/10⁸ < 10⁻¹²`. -/
theorem famσs_le_VAL : R.famσs ≤ 1 / 100 := by
  have h1 : R.later.err.qe < R.later.circle.θe ^ 2 / 10 ^ 8 :=
    R.later.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := R.later.θe_lt_hundredth
  have h3 := R.later.θe_pos
  have h4 : R.later.circle.θe ^ 2 < 1 := by nlinarith
  unfold famσs
  have : R.later.circle.θe ^ 2 / 10 ^ 8 < 1 / 100 := by
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  linarith

theorem famσc_lt_one_VAL : R.famσc < 1 := by
  have := R.famσs_le_VAL
  unfold famσs at this
  unfold famσc
  linarith

theorem famμ_le_VAL : R.later.err.μ ≤ 1 / 10 ^ 8 :=
  (R.later.μ_lt.trans_le (min_le_left _ _)).le

theorem famμ_le_million_VAL : R.later.err.μ ≤ 1 / 1000000 :=
  R.famμ_le_VAL.trans (by norm_num)

theorem famb'_pos_VAL : 0 < R.famb' := mul_pos R.later.τ_pos R.later.b'_pos

theorem fams'_pos_VAL : 0 < R.fams' := mul_pos R.later.τ_pos R.later.s'_pos

theorem fams_pos_VAL : 0 < R.fams := mul_pos R.later.τ_pos R.later.s_pos

/-- `s < 10⁻⁵ min{b', s'}` (SR:331) gives `s_fam < b'_fam / 10⁵`. -/
theorem fams_lt_b'_VAL : R.fams < R.famb' / 100000 := by
  have hs : R.later.err.s < 1 / 10 ^ 5 * min R.later.err.b' R.later.err.s' :=
    R.later.s_lt.trans_le (min_le_left _ _)
  have hm : min R.later.err.b' R.later.err.s' ≤ R.later.err.b' := min_le_left _ _
  have hτ := R.later.τ_pos
  unfold fams famb'
  nlinarith

/-- `s < 10⁻⁵ min{b', s'}` (SR:331) gives `s_fam < s'_fam / 10⁵`. -/
theorem fams_lt_s'_VAL : R.fams < R.fams' / 100000 := by
  have hs : R.later.err.s < 1 / 10 ^ 5 * min R.later.err.b' R.later.err.s' :=
    R.later.s_lt.trans_le (min_le_left _ _)
  have hm : min R.later.err.b' R.later.err.s' ≤ R.later.err.s' := min_le_right _ _
  have hτ := R.later.τ_pos
  unfold fams fams'
  nlinarith

/-- `τ < 10⁻⁸` and `s < 10⁻⁶` give `s_fam < 1/100`. -/
theorem fams_lt_hundredth_VAL : R.fams < 1 / 100 := by
  have hτ : R.later.err.τ < 1 / 10 ^ 8 := R.later.τ_lt.trans_le (min_le_left _ _)
  have hs := R.later.s_lt_audit
  have hτ0 := R.later.τ_pos
  have hs0 := R.later.s_pos
  unfold fams
  nlinarith

/-- A6: `b'_fam < τΔ/10⁹` as soon as `b' < Δ/10⁹` (an `lfr29W` request). -/
theorem famb'_lt_tau_VAL (h : R.later.err.b' < R.later.excl.Δ / 1000000000) :
    R.famb' < R.later.err.τ * R.later.excl.Δ / 1000000000 := by
  have hτ := R.later.τ_pos
  unfold famb'
  calc R.later.err.τ * R.later.err.b' < R.later.err.τ * (R.later.excl.Δ / 1000000000) :=
        mul_lt_mul_of_pos_left h hτ
    _ = R.later.err.τ * R.later.excl.Δ / 1000000000 := by ring

/-- A6: `s'_fam < τΔ/10⁹` as soon as `s' < Δ/10⁹` (an `lfr29W` request). -/
theorem fams'_lt_tau_VAL (h : R.later.err.s' < R.later.excl.Δ / 1000000000) :
    R.fams' < R.later.err.τ * R.later.excl.Δ / 1000000000 := by
  have hτ := R.later.τ_pos
  unfold fams'
  calc R.later.err.τ * R.later.err.s' < R.later.err.τ * (R.later.excl.Δ / 1000000000) :=
        mul_lt_mul_of_pos_left h hτ
    _ = R.later.err.τ * R.later.excl.Δ / 1000000000 := by ring

/-- A6: `b'_fam < 1/(10⁶Δ)` as soon as `b' < 1/(10⁶Δ)` (since `τ < 1`). -/
theorem famb'_lt_inv_VAL (h : R.later.err.b' < 1 / (1000000 * R.later.excl.Δ)) :
    R.famb' < 1 / (1000000 * R.later.excl.Δ) := by
  have hτ := R.later.τ_pos
  have hτ1 : R.later.err.τ < 1 :=
    (R.later.τ_lt.trans_le (min_le_left _ _)).trans (by norm_num)
  have hb := R.later.b'_pos
  unfold famb'
  nlinarith

/-- A6: `s'_fam < 1/(10⁶Δ)` as soon as `s' < 1/(10⁶Δ)`. -/
theorem fams'_lt_inv_VAL (h : R.later.err.s' < 1 / (1000000 * R.later.excl.Δ)) :
    R.fams' < 1 / (1000000 * R.later.excl.Δ) := by
  have hτ := R.later.τ_pos
  have hτ1 : R.later.err.τ < 1 :=
    (R.later.τ_lt.trans_le (min_le_left _ _)).trans (by norm_num)
  have hs := R.later.s'_pos
  unfold fams'
  nlinarith

theorem famLmax_pos_VAL : 0 < R.famLmax := by
  have : (1 : ℝ) ≤ max 1 (400 * R.later.split.V) := le_max_left _ _
  unfold famLmax
  linarith

/-- PR24 (B:10234, "Include H_α > 400V"): `400 V < Lmax`. -/
theorem famLmax_gt_VAL : 400 * R.later.split.V < R.famLmax := by
  have : 400 * R.later.split.V ≤ max 1 (400 * R.later.split.V) := le_max_right _ _
  unfold famLmax
  linarith

theorem famCap_pos_VAL : 0 < R.famCap := by
  have hL : 0 < closedLongLength R.later.excl := by
    have := R.later.Δ_pos
    unfold closedLongLength
    positivity
  have := R.later.ε₀_pos
  have := R.later.θs_pos
  have := R.later.θe_pos
  have := R.later.θ₂_pos
  exact lt_min R.later.ε₀_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

theorem famCap_le_VAL : R.famCap ≤ R.later.err.ε₀ := min_le_left _ _

theorem famζ_pos_VAL : 0 < R.famζ := by
  have hL : 0 < closedLongLength R.later.excl := by
    have := R.later.Δ_pos
    unfold closedLongLength
    positivity
  have := R.later.θs_pos
  have := R.later.θe_pos
  have := R.later.θ₂_pos
  exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

/-- `e = e₀ < 1/1000 < 1/40`. -/
theorem fame_lt_VAL : R.later.err.e₀ < 1 / 40 :=
  (R.later.e₀_lt.trans_le (min_le_left _ _)).trans (by norm_num)

end ClosedRegister

end DifferentialGeometry.Geometry.Collapse
