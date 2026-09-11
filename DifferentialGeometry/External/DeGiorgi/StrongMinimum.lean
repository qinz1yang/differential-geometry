import DifferentialGeometry.External.DeGiorgi.WeakHarnack
import DifferentialGeometry.External.DeGiorgi.BallScaling

/-!
# Strong minimum principle on a ball

This file derives the local strong minimum principle for continuous nonnegative
supersolutions from the weak Harnack inequality.
-/

noncomputable section

open Filter MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
private theorem essInf_le_apply
    {u : E → ℝ} {x : E} {r : ℝ}
    (hx : x ∈ ball (0 : E) r)
    (hu : ContinuousOn u (ball (0 : E) r))
    (hlow : ∃ c : ℝ, ∀ y ∈ ball (0 : E) r, c ≤ u y) :
    essInf u (volume.restrict (ball (0 : E) r)) ≤ u x := by
  let μ : Measure E := volume.restrict (ball (0 : E) r)
  obtain ⟨c, hc⟩ := hlow
  have hlow_ae : ∀ᵐ y ∂μ, c ≤ u y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hc y hy
  have hess_ae : ∀ᵐ y ∂μ, essInf u μ ≤ u y :=
    ae_essInf_le ⟨c, hlow_ae⟩
  have hzero_ae :
      (fun y => max (essInf u μ - u y) 0) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hess_ae] with y hy
    exact max_eq_right (sub_nonpos.mpr hy)
  have hcont : ContinuousOn (fun y => max (essInf u μ - u y) 0) (ball (0 : E) r) :=
    (continuousOn_const.sub hu).sup continuousOn_const
  have hzero := Measure.eqOn_open_of_ae_eq
    (μ := volume) hzero_ae isOpen_ball hcont continuousOn_const
  have hdiff : essInf u μ - u x ≤ 0 := by
    calc
      essInf u μ - u x ≤ max (essInf u μ - u x) 0 := le_max_left _ _
      _ = 0 := hzero hx
  exact sub_nonpos.mp hdiff

/-- A continuous nonnegative supersolution on the unit ball that vanishes in
the quarter ball vanishes throughout the quarter ball. -/
theorem IsSupersolution.eq_zero_on_unit_quarter_ball
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ}
    (hu_cont : ContinuousOn u (ball (0 : E) 1))
    (hu_nonneg : ∀ x ∈ ball (0 : E) 1, 0 ≤ u x)
    (hsuper : IsSupersolution A.1 u)
    {x₀ : E}
    (hx₀ : x₀ ∈ ball (0 : E) (1 / 4 : ℝ))
    (hzero : u x₀ = 0) :
    Set.EqOn u (fun _ => 0) (ball (0 : E) (1 / 4 : ℝ)) := by
  let Bq : Set E := ball (0 : E) (1 / 4 : ℝ)
  let μq : Measure E := volume.restrict Bq
  let q : ℝ := ((d : ℝ) - 2) / (d : ℝ)
  let K : ℝ :=
    (CWeakHarnack d hd / (1 - q) ^ weakHarnackDecayExp d) ^
      (A.1.Λ ^ ((1 : ℝ) / 2))
  have hBq : Bq ⊆ ball (0 : E) 1 :=
    Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hdm2_pos : 0 < (d : ℝ) - 2 := by linarith
  have hq_pos : 0 < q := div_pos hdm2_pos hd_pos
  have hq_lt_one : q < 1 := (div_lt_one hd_pos).2 (by linarith)
  have hqd : q * (d : ℝ) = (d : ℝ) - 2 := by
    dsimp [q]
    field_simp
  have hin_exp : q * (d : ℝ) / ((d : ℝ) - 2) = 1 := by
    rw [hqd]
    exact div_self hdm2_pos.ne'
  have hout_exp : ((d : ℝ) - 2) / (q * (d : ℝ)) = 1 := by
    rw [hqd]
    exact div_self hdm2_pos.ne'
  let _ : IsFiniteMeasure μq := by
    rw [isFiniteMeasure_iff]
    simpa [μq, Bq, Measure.restrict_apply, measurableSet_ball] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 / 4 : ℝ)))
  let huWitness : MemW1pWitness 2 u (ball (0 : E) 1) :=
    MemW1p.someWitness hsuper.1
  let huQuarter : MemW1pWitness 2 u Bq :=
    huWitness.restrict isOpen_ball hBq
  have hu_int : Integrable u μq := by
    have hp : (1 : ENNReal) ≤ 2 := by norm_num
    exact huQuarter.memLp.integrable hp
  have hu_nonneg_ae : 0 ≤ᵐ[μq] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hu_nonneg x (hBq hx)
  have hbound : ∀ ε : ℝ, 0 < ε → (∫ x, u x ∂μq) ≤ K * ε := by
    intro ε hε
    let uε : E → ℝ := fun x => u x + ε
    have huε_pos : ∀ x ∈ ball (0 : E) 1, 0 < uε x := by
      intro x hx
      dsimp [uε]
      linarith [hu_nonneg x hx]
    have hsuperε : IsSupersolution A.1 uε := by
      simpa [uε] using
        (hsuper.sub_const_ball (d := d) (c := (0 : E)) (r := (1 : ℝ))
          (by norm_num) (-ε))
    have hess_ge : ε ≤ essInf uε μq := by
      apply le_essInf_real_of_ae_le (d := d)
        (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 4 : ℝ)) (by norm_num))
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      dsimp [uε]
      linarith [hu_nonneg x (hBq hx)]
    have huε_cont : ContinuousOn uε Bq := by
      exact (hu_cont.mono hBq).add continuousOn_const
    have hess_le : essInf uε μq ≤ ε := by
      have hlow : ∃ c : ℝ, ∀ x ∈ Bq, c ≤ uε x := by
        refine ⟨ε, ?_⟩
        intro x hx
        dsimp [uε]
        linarith [hu_nonneg x (hBq hx)]
      have hle := essInf_le_apply (d := d) (u := uε) (x := x₀)
        (r := (1 / 4 : ℝ)) hx₀ huε_cont hlow
      simpa [μq, Bq, uε, hzero] using hle
    have hess : essInf uε μq = ε := le_antisymm hess_le hess_ge
    have hwh := weak_harnack (d := d) hd A hq_pos hq_lt_one huε_pos hsuperε
    rw [hin_exp, hout_exp] at hwh
    simp only [Real.rpow_one] at hwh
    have huε_nonneg_ae : 0 ≤ᵐ[μq] uε := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      dsimp [uε]
      linarith [hu_nonneg x (hBq hx)]
    have habs_ae : (fun x => |uε x|) =ᵐ[μq] uε := by
      filter_upwards [huε_nonneg_ae] with x hx
      exact abs_of_nonneg hx
    change (∫ x, |uε x| ∂μq) ≤ K * essInf uε μq at hwh
    rw [integral_congr_ae habs_ae, hess] at hwh
    have huε_int : Integrable uε μq := by
      exact hu_int.add (integrable_const ε)
    have hmono : (∫ x, u x ∂μq) ≤ ∫ x, uε x ∂μq := by
      apply integral_mono_ae hu_int huε_int
      filter_upwards with x
      dsimp [uε]
      linarith
    exact hmono.trans hwh
  have hint_nonpos : (∫ x, u x ∂μq) ≤ 0 := by
    have hlim :
        Tendsto (fun n : ℕ => K * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply ge_of_tendsto hlim
    filter_upwards with n
    simpa using hbound (1 / ((n : ℝ) + 1)) (by positivity)
  have hint_nonneg : 0 ≤ ∫ x, u x ∂μq := integral_nonneg_of_ae hu_nonneg_ae
  have hint_zero : (∫ x, u x ∂μq) = 0 := le_antisymm hint_nonpos hint_nonneg
  have hu_zero_ae : u =ᵐ[μq] (fun _ => 0) :=
    (integral_eq_zero_iff_of_nonneg_ae hu_nonneg_ae hu_int).mp hint_zero
  exact Measure.eqOn_open_of_ae_eq
    (μ := volume) hu_zero_ae isOpen_ball (hu_cont.mono hBq) continuousOn_const

/-- A continuous nonnegative supersolution on a positive-radius ball that
vanishes in its concentric quarter ball vanishes throughout that quarter ball. -/
theorem IsSupersolution.eq_zero_on_quarter_ball
    (hd : 2 < (d : ℝ))
    {c : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (ball c R))
    {u : E → ℝ}
    (hu_cont : ContinuousOn u (ball c R))
    (hu_nonneg : ∀ x ∈ ball c R, 0 ≤ u x)
    (hsuper : IsSupersolution A.1 u)
    {x₀ : E}
    (hx₀ : x₀ ∈ ball c (R / 4))
    (hzero : u x₀ = 0) :
    Set.EqOn u (fun _ => 0) (ball c (R / 4)) := by
  let T : E → E := fun z => c + R • z
  let S : E → E := fun x => R⁻¹ • (x - c)
  let v : E → ℝ := rescaleToUnitBall (d := d) (x₀ := c) (R := R) u
  let Aunit : NormalizedEllipticCoeff d (ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := c) (R := R) hR A
  have hT_cont : Continuous T := by
    exact continuous_const.add (continuous_const_smul R)
  have hT_map : Set.MapsTo T (ball (0 : E) 1) (ball c R) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : T z - c = R • z := by
      dsimp only [T]
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le]
    calc
      R * ‖z‖ < R * 1 := mul_lt_mul_of_pos_left hz' hR
      _ = R := mul_one R
  have hS_quarter : Set.MapsTo S (ball c (R / 4))
      (ball (0 : E) (1 / 4 : ℝ)) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [S]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    rw [inv_mul_lt_iff₀ hR]
    rw [Metric.mem_ball, dist_eq_norm] at hx
    simpa [div_eq_mul_inv] using hx
  have hTS : ∀ x : E, T (S x) = x := by
    intro x
    dsimp only [T, S]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    abel
  have hv_cont : ContinuousOn v (ball (0 : E) 1) := by
    change ContinuousOn (fun z => u (T z)) (ball (0 : E) 1)
    exact hu_cont.comp hT_cont.continuousOn hT_map
  have hv_nonneg : ∀ z ∈ ball (0 : E) 1, 0 ≤ v z := by
    intro z hz
    change 0 ≤ u (T z)
    exact hu_nonneg (T z) (hT_map hz)
  have hv_super : IsSupersolution Aunit.1 v := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := c) (R := R) hR A.1)
      (rescaleToUnitBall (d := d) (x₀ := c) (R := R) u)
    exact rescaleToUnitBall_isSupersolution
      (d := d) (x₀ := c) (R := R) hR A.1 hsuper
  let z₀ : E := S x₀
  have hz₀ : z₀ ∈ ball (0 : E) (1 / 4 : ℝ) := hS_quarter hx₀
  have hv_zero : v z₀ = 0 := by
    change u (T (S x₀)) = 0
    rw [hTS x₀]
    exact hzero
  have hv_eq : Set.EqOn v (fun _ => 0) (ball (0 : E) (1 / 4 : ℝ)) :=
    IsSupersolution.eq_zero_on_unit_quarter_ball
      (d := d) hd Aunit hv_cont hv_nonneg hv_super hz₀ hv_zero
  intro x hx
  have hz : S x ∈ ball (0 : E) (1 / 4 : ℝ) := hS_quarter hx
  have h := hv_eq hz
  change u (T (S x)) = 0 at h
  rwa [hTS x] at h

end DeGiorgi
