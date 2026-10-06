import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighBasics_EG

/-!
# Existence of a Rayleigh-quotient minimizer for `-Δ + W` on `H¹₀(Ω)` (S-W-EIG, G1)

`exists_rayleigh_minimizer_EG`: for `Ω ⊂ ℝᵈ` open, bounded, nonempty, a measurable weight
`ρ ≥ c₀ > 0` and a measurable potential `W` (both bounded on `Ω`), the quotient
`(∫|∇v|² + W v²) / ∫ ρ v²` has a minimizer `u ∈ H¹₀(Ω)` with `∫ ρ u² = 1`.  The direct method
uses
`rellich_kondrachov_W01p_seq_coordinates`, `exists_weakly_convergent_gradients_of_tendsto_L2`
and the weak lower semicontinuity of the `L²` norm of the gradient.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_le_of_integral_sq_le_EG {v : E → ℝ} (hv : MemLp v 2 (volume.restrict Ω))
    {R : ℝ} (hR : 0 ≤ R) (h : (∫ x in Ω, v x ^ 2) ≤ R ^ 2) :
    eLpNorm v 2 (volume.restrict Ω) ≤ ENNReal.ofReal R := by
  rw [integral_sq_eq_norm_sq_EG hv] at h
  rw [← ENNReal.ofReal_toReal hv.eLpNorm_lt_top.ne]
  apply ENNReal.ofReal_le_ofReal
  rw [← Lp.norm_toLp (f := v) hv]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR (by norm_num)).mp h

theorem mass_ge_EG (hΩ : MeasurableSet Ω) {ρ : E → ℝ} (hρm : Measurable ρ) {c₀ B : ℝ}
    (hc₀ : 0 ≤ c₀) (hρ0 : ∀ x ∈ Ω, c₀ ≤ ρ x) (hρB : ∀ x ∈ Ω, ρ x ≤ B)
    {v : E → ℝ}
    (hv : MemLp v 2 (volume.restrict Ω)) :
    c₀ * (∫ x in Ω, v x ^ 2) ≤ ∫ x in Ω, ρ x * v x ^ 2 := by
  have hρae : ∀ᵐ x ∂(volume.restrict Ω), |ρ x| ≤ B :=
    ae_restrict_of_forall_mem hΩ fun x hx => by
      rw [abs_of_nonneg (hc₀.trans (hρ0 x hx))]
      exact hρB x hx
  rw [← integral_const_mul]
  apply setIntegral_mono_on (hv.integrable_sq.const_mul c₀)
    (integrable_weight_sq_EG hρm hρae hv) hΩ
  intro x hx
  exact mul_le_mul_of_nonneg_right (hρ0 x hx) (sq_nonneg _)

theorem abs_pot_le_EG (hΩ : MeasurableSet Ω) {W : E → ℝ} {B : ℝ}
    (hWB : ∀ x ∈ Ω, |W x| ≤ B) {v : E → ℝ} (hv : MemLp v 2 (volume.restrict Ω)) :
    |∫ x in Ω, W x * v x ^ 2| ≤ B * ∫ x in Ω, v x ^ 2 := by
  have hWae : ∀ᵐ x ∂(volume.restrict Ω), |W x| ≤ B := ae_restrict_of_forall_mem hΩ hWB
  rw [← integral_const_mul]
  have h := norm_integral_le_of_norm_le (hv.integrable_sq.const_mul B)
    (f := fun x => W x * v x ^ 2) (Eventually.mono hWae fun x hx => by
      have hsq : |v x ^ 2| = v x ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, hsq]
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg _))
  simpa only [Real.norm_eq_abs] using h

theorem tendsto_weight_sq_EG (hΩ : MeasurableSet Ω) {c : E → ℝ} (hcm : Measurable c) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x ∈ Ω, |c x| ≤ B) {a : ℕ → E → ℝ} {w : E → ℝ}
    (ha : ∀ n, MemLp (a n) 2 (volume.restrict Ω)) (hw : MemLp w 2 (volume.restrict Ω)) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ n, eLpNorm (a n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R)
    (hlim : Tendsto (fun n => eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)) atTop
      (𝓝 0)) :
    Tendsto (fun n => ∫ x in Ω, c x * a n x ^ 2) atTop (𝓝 (∫ x in Ω, c x * w x ^ 2)) := by
  have hBae : ∀ᵐ x ∂(volume.restrict Ω), |c x| ≤ B := ae_restrict_of_forall_mem hΩ hB
  have ht : Tendsto (fun n => (eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa [Function.comp_def] using h
  have hbound : Tendsto (fun n => B * ((eLpNorm (fun x => a n x - w x) 2
      (volume.restrict Ω)).toReal * (R + (eLpNorm w 2 (volume.restrict Ω)).toReal))) atTop
      (𝓝 0) := by
    simpa using (ht.mul_const (R + (eLpNorm w 2 (volume.restrict Ω)).toReal)).const_mul B
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hbound
  rw [Real.dist_eq]
  refine (abs_integral_weight_sq_sub_le_EG hcm hB0 hBae (ha n) hw).trans ?_
  apply mul_le_mul_of_nonneg_left _ hB0
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have h1 : (eLpNorm (a n) 2 (volume.restrict Ω)).toReal ≤ R := by
    exact ENNReal.toReal_le_of_le_ofReal hR0 (hR n)
  linarith

variable [NeZero d]

theorem exists_h01_pos_mass_EG (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {ρ : E → ℝ}
    (hρm : Measurable ρ) {c₀ B : ℝ} (hc₀ : 0 < c₀)
    (hρ0 : ∀ x ∈ Ω, c₀ ≤ ρ x) (hρB : ∀ x ∈ Ω, ρ x ≤ B) :
    ∃ v : E → ℝ, DeGiorgi.MemW01p 2 v Ω ∧ 0 < ∫ x in Ω, ρ x * v x ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  let f : ContDiffBump x₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hsub : tsupport f ⊆ Ω := by
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change δ / 2 < δ; linarith)).trans hball
  have hf0 : DeGiorgi.MemW01p 2 f Ω := DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset hΩ
    f.contDiff f.hasCompactSupport hsub
  refine ⟨f, hf0, ?_⟩
  have hmass := mass_ge_EG hΩ.measurableSet hρm hc₀.le hρ0 hρB hf0.1.1
  have hout : ∀ x ∉ Ω, f x ^ 2 = 0 := by
    intro x hx
    have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))
    rw [this]
    norm_num
  have hpos : 0 < ∫ x in Ω, f x ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (f.continuous.pow 2) ?_ (fun x => sq_nonneg _) ?_
    · exact f.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    · rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)]
      norm_num
  nlinarith

theorem exists_rayleigh_minimizer_EG (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {ρ W : E → ℝ} (hρm : Measurable ρ) (hWm : Measurable W)
    {c₀ B : ℝ}
    (hc₀ : 0 < c₀) (hρ0 : ∀ x ∈ Ω, c₀ ≤ ρ x) (hρB : ∀ x ∈ Ω, ρ x ≤ B)
    (hWB : ∀ x ∈ Ω, |W x| ≤ B) :
    ∃ u : E → ℝ, DeGiorgi.MemW01p 2 u Ω ∧ ∃ hu : DeGiorgi.MemW1pWitness 2 u Ω,
      (∫ x in Ω, ρ x * u x ^ 2) = 1 ∧
      ∀ v : E → ℝ, DeGiorgi.MemW01p 2 v Ω → ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
        ((∫ x in Ω, ‖hu.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * u x ^ 2) *
            (∫ x in Ω, ρ x * v x ^ 2) ≤
          (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * v x ^ 2 := by
  classical
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  obtain ⟨x₀, hx₀⟩ := hne
  have hB0 : 0 < B := lt_of_lt_of_le hc₀ ((hρ0 x₀ hx₀).trans (hρB x₀ hx₀))
  let D : ∀ v : E → ℝ, DeGiorgi.MemW01p 2 v Ω → ℝ :=
    fun v hv => ∫ x in Ω, ‖(h01Wit_EG hv).weakGrad x‖ ^ 2
  have hL2 : ∀ v : E → ℝ, DeGiorgi.MemW01p 2 v Ω → MemLp v 2 (volume.restrict Ω) :=
    fun v hv => hv.1.1
  have hD0 : ∀ v (hv : DeGiorgi.MemW01p 2 v Ω), 0 ≤ D v hv :=
    fun v hv => integral_nonneg fun x => sq_nonneg _
  have hI0 : ∀ v : E → ℝ, 0 ≤ ∫ x in Ω, v x ^ 2 :=
    fun v => integral_nonneg fun x => sq_nonneg _
  have hN : ∀ v (hv : DeGiorgi.MemW01p 2 v Ω),
      c₀ * (∫ x in Ω, v x ^ 2) ≤ ∫ x in Ω, ρ x * v x ^ 2 :=
    fun v hv => mass_ge_EG hΩm hρm hc₀.le hρ0 hρB (hL2 v hv)
  have hP : ∀ v (hv : DeGiorgi.MemW01p 2 v Ω),
      |∫ x in Ω, W x * v x ^ 2| ≤ B * ∫ x in Ω, v x ^ 2 :=
    fun v hv => abs_pot_le_EG hΩm hWB (hL2 v hv)
  have hBI : ∀ v (hv : DeGiorgi.MemW01p 2 v Ω),
      B * (∫ x in Ω, v x ^ 2) ≤ (B / c₀) * ∫ x in Ω, ρ x * v x ^ 2 := by
    intro v hv
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [hN v hv]
  have hQlow : ∀ v (hv : DeGiorgi.MemW01p 2 v Ω),
      -(B / c₀) * (∫ x in Ω, ρ x * v x ^ 2) ≤ D v hv + ∫ x in Ω, W x * v x ^ 2 := by
    intro v hv
    have h4 := (abs_le.mp (hP v hv)).1
    have h5 := hBI v hv
    have h3 := hD0 v hv
    nlinarith
  let Adm : Set ℝ := {q | ∃ v, ∃ hv : DeGiorgi.MemW01p 2 v Ω,
    (∫ x in Ω, ρ x * v x ^ 2) = 1 ∧ q = D v hv + ∫ x in Ω, W x * v x ^ 2}
  have hAne : Adm.Nonempty := by
    obtain ⟨f, hf, hfpos⟩ := exists_h01_pos_mass_EG hΩ ⟨x₀, hx₀⟩ hρm hc₀ hρ0 hρB
    set s := ∫ x in Ω, ρ x * f x ^ 2 with hs
    have hcf : DeGiorgi.MemW01p 2 (fun x => (1 / Real.sqrt s) * f x) Ω := hf.smul _
    refine ⟨_, fun x => (1 / Real.sqrt s) * f x, hcf, ?_, rfl⟩
    have h1 : ∫ x in Ω, ρ x * ((1 / Real.sqrt s) * f x) ^ 2 = (1 / Real.sqrt s) ^ 2 * s := by
      rw [hs, ← integral_const_mul]
      congr 1
      ext x
      ring
    rw [h1, div_pow, Real.sq_sqrt hfpos.le]
    field_simp
  have hAbdd : BddBelow Adm := by
    refine ⟨-(B / c₀), ?_⟩
    rintro q ⟨v, hv, hNv, rfl⟩
    have := hQlow v hv
    rw [hNv] at this
    linarith
  obtain ⟨e, he_anti, he_lim, he_mem⟩ := exists_seq_tendsto_sInf hAne hAbdd
  choose v hv hNv hev using he_mem
  set m := sInf Adm with hm
  have hmle : ∀ q ∈ Adm, m ≤ q := fun q hq => csInf_le hAbdd hq
  -- bounds along the minimizing sequence
  have hI : ∀ n, (∫ x in Ω, v n x ^ 2) ≤ 1 / c₀ := by
    intro n
    have := hN (v n) (hv n)
    rw [hNv n] at this
    rw [le_div_iff₀ hc₀]
    linarith
  have hDle : ∀ n, D (v n) (hv n) ≤ e 0 + B / c₀ := by
    intro n
    have h1 := (abs_le.mp (hP (v n) (hv n))).1
    have h2 := he_anti (Nat.zero_le n)
    have h3 := hBI (v n) (hv n)
    rw [hNv n] at h3
    have h4 := hev n
    nlinarith
  set C₁ := e 0 + B / c₀ with hC₁
  have hC₁0 : 0 ≤ C₁ := (hD0 (v 0) (hv 0)).trans (hDle 0)
  have hgrad : ∀ n, ‖DeGiorgi.gradLpOfWitness (h01Wit_EG (hv n))‖ ^ 2 = D (v n) (hv n) :=
    fun n => norm_gradLpOfWitness_sq_eq_integral (h01Wit_EG (hv n))
  have hC : ∀ n, ‖DeGiorgi.gradLpOfWitness (h01Wit_EG (hv n))‖ ≤ C₁ + 1 := by
    intro n
    have h1 := hgrad n
    have h2 := hDle n
    nlinarith [sq_nonneg (‖DeGiorgi.gradLpOfWitness (h01Wit_EG (hv n))‖ - 1),
      norm_nonneg (DeGiorgi.gradLpOfWitness (h01Wit_EG (hv n)))]
  have hR0 : 0 ≤ 1 / c₀ + 1 := by positivity
  have hR : ∀ n, eLpNorm (v n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal (1 / c₀ + 1) := by
    intro n
    apply eLpNorm_le_of_integral_sq_le_EG (hL2 _ (hv n)) hR0
    have h1 : 0 ≤ 1 / c₀ := by positivity
    nlinarith [hI n]
  obtain ⟨φ, w, hw, hφ, hlim, hweak⟩ := exists_limit_EG hΩ hΩb hv hR hC
  have hρabs : ∀ x ∈ Ω, |ρ x| ≤ B := fun x hx => by
    rw [abs_of_nonneg (hc₀.le.trans (hρ0 x hx))]
    exact hρB x hx
  have hwL2 : MemLp w 2 (volume.restrict Ω) := hL2 w hw
  have hNlim := tendsto_weight_sq_EG hΩm hρm hB0.le hρabs (a := fun n => v (φ n))
    (fun n => hL2 _ (hv (φ n))) hwL2 hR0 (fun n => hR (φ n)) hlim
  have hPlim := tendsto_weight_sq_EG hΩm hWm hB0.le hWB (a := fun n => v (φ n))
    (fun n => hL2 _ (hv (φ n))) hwL2 hR0 (fun n => hR (φ n)) hlim
  have hNw : (∫ x in Ω, ρ x * w x ^ 2) = 1 := by
    have : (fun n => ∫ x in Ω, ρ x * v (φ n) x ^ 2) = fun _ => 1 := funext fun n => hNv (φ n)
    rw [this] at hNlim
    exact tendsto_nhds_unique hNlim tendsto_const_nhds
  have hPw : Tendsto (fun n => ∫ x in Ω, W x * v (φ n) x ^ 2) atTop
      (𝓝 (∫ x in Ω, W x * w x ^ 2)) := hPlim
  have hDlim : Tendsto (fun n => ‖DeGiorgi.gradLpOfWitness (h01Wit_EG (hv (φ n)))‖ ^ 2) atTop
      (𝓝 (m - ∫ x in Ω, W x * w x ^ 2)) := by
    have h := (he_lim.comp hφ.tendsto_atTop).sub hPw
    refine h.congr fun n => ?_
    rw [hgrad (φ n)]
    change e (φ n) - _ = _
    rw [hev (φ n)]
    ring
  have hle := norm_sq_le_of_weak_EG hweak hDlim
  rw [norm_gradLpOfWitness_sq_eq_integral (h01Wit_EG hw)] at hle
  have hQw : D w hw + ∫ x in Ω, W x * w x ^ 2 ≤ m := by
    change (∫ x in Ω, ‖(h01Wit_EG hw).weakGrad x‖ ^ 2) + _ ≤ m
    linarith
  refine ⟨w, hw, h01Wit_EG hw, hNw, ?_⟩
  intro v' hv0 hv'
  have hD' : (∫ x in Ω, ‖hv'.weakGrad x‖ ^ 2) = D v' hv0 :=
    dir_congr_EG hΩ hv' (h01Wit_EG hv0)
  rw [hD']
  change (D w hw + ∫ x in Ω, W x * w x ^ 2) * _ ≤ _
  have hNv0 : 0 ≤ ∫ x in Ω, ρ x * v' x ^ 2 :=
    (mul_nonneg hc₀.le (hI0 v')).trans (hN v' hv0)
  rcases hNv0.eq_or_lt with hzero | hpos
  · rw [← hzero, mul_zero]
    have := hQlow v' hv0
    rw [← hzero, mul_zero] at this
    exact this
  · set Nv := ∫ x in Ω, ρ x * v' x ^ 2 with hNvdef
    have hcpos : 0 < 1 / Real.sqrt Nv := by positivity
    set c := 1 / Real.sqrt Nv with hc
    have hc2 : c ^ 2 * Nv = 1 := by
      rw [hc, div_pow, Real.sq_sqrt hpos.le]
      field_simp
    have hcv : DeGiorgi.MemW01p 2 (fun x => c * v' x) Ω := hv0.smul c
    have hNcv : (∫ x in Ω, ρ x * (c * v' x) ^ 2) = 1 := by
      have : (∫ x in Ω, ρ x * (c * v' x) ^ 2) = c ^ 2 * Nv := by
        rw [hNvdef, ← integral_const_mul]
        congr 1
        ext x
        ring
      rw [this, hc2]
    have hDcv : D (fun x => c * v' x) hcv = c ^ 2 * D v' hv0 := by
      change (∫ x in Ω, ‖(h01Wit_EG hcv).weakGrad x‖ ^ 2) = _
      rw [dir_congr_EG hΩ (h01Wit_EG hcv) ((h01Wit_EG hv0).smul c), dir_smul_EG]
    have hPcv : (∫ x in Ω, W x * (c * v' x) ^ 2) = c ^ 2 * ∫ x in Ω, W x * v' x ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    have hmem : D (fun x => c * v' x) hcv + ∫ x in Ω, W x * (c * v' x) ^ 2 ∈ Adm :=
      ⟨_, hcv, hNcv, rfl⟩
    have h1 := hmle _ hmem
    rw [hDcv, hPcv, ← mul_add] at h1
    calc (D w hw + ∫ x in Ω, W x * w x ^ 2) * Nv ≤ m * Nv :=
          mul_le_mul_of_nonneg_right hQw hpos.le
      _ ≤ (c ^ 2 * (D v' hv0 + ∫ x in Ω, W x * v' x ^ 2)) * Nv :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = D v' hv0 + ∫ x in Ω, W x * v' x ^ 2 := by
          calc _ = (c ^ 2 * Nv) * (D v' hv0 + ∫ x in Ω, W x * v' x ^ 2) := by ring
            _ = _ := by rw [hc2, one_mul]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
