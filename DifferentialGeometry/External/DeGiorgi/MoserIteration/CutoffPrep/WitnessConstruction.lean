-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import DifferentialGeometry.External.DeGiorgi.MoserIteration.CutoffPrep.RegularizedEnergy

/-!
# Moser Witness Construction

This module constructs the limiting power-cutoff witness from the exact-on-support regularized
witnesses.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

private theorem moserPowerCutoff_functionApprox
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩ_sub : Ω ⊆ Metric.ball (0 : E) 1)
    {u η : E → ℝ} {p N Cη : ℝ}
    (hp : 1 < p) (hN_pos : 0 < N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hqual : ∀ᵐ x ∂(volume.restrict Ω),
      x ∈ tsupport η → max (u x) 0 < N)
    [IsFiniteMeasure (volume.restrict Ω)] :
    let f : E → ℝ := moserPowerCutoff (d := d) η u p
    let fn : ℕ → E → ℝ := fun n =>
      moserExactRegPowerCutoff η u (moserEpsSeq n) N p
    MemLp f 2 (volume.restrict Ω) ∧
      (∀ n, MemLp (fun x => fn n x - f x) 2 (volume.restrict Ω)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => fn n x - f x) 2 (volume.restrict Ω))
        atTop (nhds 0) := by
  classical
  dsimp only
  let μ : Measure E := volume.restrict Ω
  let f : E → ℝ := moserPowerCutoff (d := d) η u p
  let fn : ℕ → E → ℝ := fun n =>
    moserExactRegPowerCutoff η u (moserEpsSeq n) N p
  let wfnBig : ∀ n : ℕ,
      MemW1pWitness 2 (fun x => fn n x) (Metric.ball (0 : E) 1) := fun n => by
    dsimp [fn]
    exact
      moserExactRegPowerCutoffWitness
        (d := d) (u := u) (η := η) (ε := moserEpsSeq n)
        (N := N) (p := p) (Cη := Cη)
        (moserEpsSeq_pos n) hN_pos.le hu1 hη hη_bound hη_grad_bound
  let wfn : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) Ω := fun n =>
    (wfnBig n).restrict hΩ hΩ_sub
  let huΩ : MemW1pWitness 2 u Ω := hu1.restrict hΩ hΩ_sub
  have hfn_tendsto_ae :
      ∀ᵐ x ∂μ, Tendsto (fun n => fn n x) atTop (nhds (f x)) := by
    filter_upwards [hqual] with x hx
    exact
      moserExactRegPowerCutoff_tendsto_powerCutoff_of_support_bound
        (d := d) (u := u) (η := η) (N := N) (p := p) (x := x) hp
        (fun hxη => hx hxη)
  let Cfun : ℝ := 2 * (1 + N) ^ (p / 2)
  have hCfun_nonneg : 0 ≤ Cfun := by
    dsimp [Cfun]
    positivity
  have hCfun_norm : ‖Cfun‖ = Cfun := Real.norm_of_nonneg hCfun_nonneg
  have hCfun_memLp : MemLp (fun _ : E => Cfun) 2 μ := by
    simpa [Cfun] using (memLp_const Cfun : MemLp (fun _ : E => Cfun) 2 μ)
  have hf_memLp : MemLp f 2 μ := by
    refine hCfun_memLp.of_le ?_ ?_
    · have hpow_cont : Continuous fun t : ℝ => t ^ (p / 2) :=
        Real.continuous_rpow_const (by linarith)
      have hpow_meas :
          AEStronglyMeasurable (fun x => |max (u x) 0| ^ (p / 2)) μ :=
        (hpow_cont.measurable.comp_aemeasurable
          (measurable_abs.comp_aemeasurable
            (huΩ.memLp.aestronglyMeasurable.aemeasurable.max
              measurable_const.aemeasurable))).aestronglyMeasurable
      have hmul := hη.continuous.aestronglyMeasurable.mul hpow_meas
      change AEStronglyMeasurable
        (fun x => η x * |max (u x) 0| ^ (p / 2)) μ
      convert hmul using 1
      funext x
      rfl
    · filter_upwards [hqual] with x hx
      by_cases hxη : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hx hxη
        have hmax_abs : |max (u x) 0| = max (u x) 0 :=
          abs_of_nonneg (le_max_right _ _)
        have hpow_le :
            |max (u x) 0| ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          simpa [hmax_abs] using
            Real.rpow_le_rpow (le_max_right _ _) (by linarith) (by linarith)
        have hpow_norm_le :
            ‖|max (u x) 0| ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact hpow_le
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) :=
          Real.rpow_nonneg (by linarith) _
        calc
          ‖f x‖ = ‖η x * (|max (u x) 0| ^ (p / 2))‖ := by
            simp [f, moserPowerCutoff]
          _ = ‖η x‖ * ‖|max (u x) 0| ^ (p / 2)‖ := norm_mul _ _
          _ = |η x| * ‖|max (u x) 0| ^ (p / 2)‖ := by
            rw [Real.norm_eq_abs]
          _ ≤ |η x| * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_left hpow_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ ≤ ‖Cfun‖ := by
            rw [hCfun_norm]
            dsimp [Cfun]
            nlinarith
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
        calc
          ‖f x‖ = 0 := by simp [f, moserPowerCutoff, hηx]
          _ ≤ ‖Cfun‖ := by simpa [hCfun_norm] using hCfun_nonneg
  have hfn_fun_memLp :
      ∀ n, MemLp (fun x => fn n x - f x) 2 μ := fun n =>
    (wfn n).memLp.sub hf_memLp
  have hfn_meas :
      ∀ n, AEStronglyMeasurable (fun x => fn n x - f x) μ := fun n =>
    (hfn_fun_memLp n).aestronglyMeasurable
  have hfn_dom :
      ∀ n, ∀ᵐ x ∂μ, |fn n x - f x| ≤ Cfun := by
    intro n
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hp_nonneg : 0 ≤ p := by linarith
      have hmax_abs : |max (u x) 0| = max (u x) 0 :=
        abs_of_nonneg (le_max_right _ _)
      have hreg_le :
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤
            (1 + N) ^ (p / 2) := by
        have hbase :=
          moserExactRegPow_le_rpow_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p)
            (t := max (u x) 0) (moserEpsSeq_pos n)
            (le_max_right _ _) hboundx.le (by linarith)
        calc
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
              ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
          _ ≤ (1 + N) ^ (p / 2) := by
            exact Real.rpow_le_rpow
              (add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _))
              (by linarith [moserEpsSeq_le_one n]) (by linarith)
      have hreg_nonneg :
          0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) :=
        moserExactRegPow_nonneg_of_nonneg_le_N
          (ε := moserEpsSeq n) (N := N) (p := p)
          (t := max (u x) 0) (moserEpsSeq_pos n)
          (le_max_right _ _) hboundx.le hp_nonneg
      have hreg_norm_le :
          ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤
            (1 + N) ^ (p / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
        exact hreg_le
      have hpow_le :
          |max (u x) 0| ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
        simpa [hmax_abs] using
          Real.rpow_le_rpow (le_max_right _ _) (by linarith) (by linarith)
      have hpow_norm_le :
          ‖|max (u x) 0| ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpow_le
      have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) :=
        Real.rpow_nonneg (by linarith) _
      have hfn_bound : ‖fn n x‖ ≤ (1 + N) ^ (p / 2) := by
        calc
          ‖fn n x‖ =
              |η x| *
                ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
            simp [fn, moserExactRegPowerCutoff, norm_mul]
          _ ≤ |η x| * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_left hreg_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ = (1 + N) ^ (p / 2) := one_mul _
      have hf_bound : ‖f x‖ ≤ (1 + N) ^ (p / 2) := by
        calc
          ‖f x‖ = |η x| * ‖|max (u x) 0| ^ (p / 2)‖ := by
            simp [f, moserPowerCutoff, norm_mul]
          _ ≤ |η x| * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_left hpow_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) :=
            mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ = (1 + N) ^ (p / 2) := one_mul _
      have hfn_abs_bound : |fn n x| ≤ (1 + N) ^ (p / 2) := by
        simpa [Real.norm_eq_abs] using hfn_bound
      have hf_abs_bound : |f x| ≤ (1 + N) ^ (p / 2) := by
        simpa [Real.norm_eq_abs] using hf_bound
      calc
        |fn n x - f x| ≤ ‖fn n x‖ + ‖f x‖ := by
          simpa [Real.norm_eq_abs] using norm_sub_le (fn n x) (f x)
        _ ≤ Cfun := by
          dsimp [Cfun]
          linarith [hfn_abs_bound, hf_abs_bound]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
      calc
        |fn n x - f x| = 0 := by
          simp [fn, f, moserExactRegPowerCutoff, moserPowerCutoff, hηx]
        _ ≤ Cfun := hCfun_nonneg
  have hfn_tendsto :
      Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ)
        atTop (nhds 0) := by
    exact moser_tendsto_eLpNorm_zero_of_dominated
      hCfun_memLp hfn_meas hfn_dom <| by
        filter_upwards [hfn_tendsto_ae] with x hx
        simpa using hx.sub (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => f x) atTop (nhds (f x)))
  exact ⟨hf_memLp, hfn_fun_memLp, hfn_tendsto⟩

private theorem integral_sq_le_two_integrals_of_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g h : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hpointwise :
      ∀ᵐ x ∂μ, (f x) ^ 2 ≤ 2 * (g x) ^ 2 + 2 * (h x) ^ 2) :
    ∫ x, (f x) ^ 2 ∂μ ≤
      2 * ∫ x, (g x) ^ 2 ∂μ + 2 * ∫ x, (h x) ^ 2 ∂μ := by
  have hf_int : Integrable (fun x => (f x) ^ 2) μ := by
    simpa [pow_two] using hf.integrable_sq
  have hg_int : Integrable (fun x => (g x) ^ 2) μ := by
    simpa [pow_two] using hg.integrable_sq
  have hh_int : Integrable (fun x => (h x) ^ 2) μ := by
    simpa [pow_two] using hh.integrable_sq
  have htwo_g_int : Integrable (fun x => 2 * (g x) ^ 2) μ := by
    simpa using hg_int.const_mul (2 : ℝ)
  have htwo_h_int : Integrable (fun x => 2 * (h x) ^ 2) μ := by
    simpa using hh_int.const_mul (2 : ℝ)
  calc
    ∫ x, (f x) ^ 2 ∂μ
        ≤ ∫ x, (2 * (g x) ^ 2 + 2 * (h x) ^ 2) ∂μ := by
          exact integral_mono_ae hf_int (htwo_g_int.add htwo_h_int) hpointwise
    _ = 2 * ∫ x, (g x) ^ 2 ∂μ + 2 * ∫ x, (h x) ^ 2 ∂μ := by
          rw [integral_add htwo_g_int htwo_h_int, integral_const_mul, integral_const_mul]

private theorem integral_mono_set_of_ae_nonneg
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} {f : α → ℝ}
    (hst : s ⊆ t)
    (h_nonneg : 0 ≤ᵐ[μ.restrict t] f)
    (h_int : Integrable f (μ.restrict t)) :
    ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ := by
  exact integral_mono_measure
    (Measure.restrict_mono_set μ hst) h_nonneg h_int

private theorem tendsto_eLpNorm_sub_of_component_decomposition
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    {f₁ f₂ : ℕ → α → ℝ} {g₁ g₂ : α → ℝ}
    (hdecomp :
      ∀ n x, f n x - g x = (f₁ n x - g₁ x) + (f₂ n x - g₂ x))
    (h₁mem : ∀ n, MemLp (fun x => f₁ n x - g₁ x) 2 μ)
    (h₂mem : ∀ n, MemLp (fun x => f₂ n x - g₂ x) 2 μ)
    (h₁tendsto :
      Tendsto (fun n => eLpNorm (fun x => f₁ n x - g₁ x) 2 μ) atTop (nhds 0))
    (h₂tendsto :
      Tendsto (fun n => eLpNorm (fun x => f₂ n x - g₂ x) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (nhds 0) := by
  let rhs : ℕ → ENNReal := fun n =>
    eLpNorm (fun x => f₁ n x - g₁ x) 2 μ +
      eLpNorm (fun x => f₂ n x - g₂ x) 2 μ
  have hbound :
      ∀ n, eLpNorm (fun x => f n x - g x) 2 μ ≤ rhs n := by
    intro n
    have hEq :
        (fun x => f n x - g x) =
          (fun x => (f₁ n x - g₁ x) + (f₂ n x - g₂ x)) := by
      ext x
      exact hdecomp n x
    rw [hEq]
    change eLpNorm
        ((fun x => f₁ n x - g₁ x) + (fun x => f₂ n x - g₂ x)) 2 μ ≤ rhs n
    exact eLpNorm_add_le
      (h₁mem n).aestronglyMeasurable (h₂mem n).aestronglyMeasurable (by norm_num)
  have hsum_tendsto : Tendsto rhs atTop (nhds 0) := by
    simpa [rhs] using h₁tendsto.add h₂tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto
    (fun _ => zero_le) hbound

private theorem moserRegularCutoffTerm_integral_sq_bound
    {u η : E → ℝ} {p N Cη s : ℝ}
    (hp : 1 < p) (hN : 0 ≤ N)
    (hCη_nonneg : 0 ≤ Cη)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hu_meas :
      AEStronglyMeasurable u
        (volume.restrict (Metric.ball (0 : E) s)))
    (hqual :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
        x ∈ tsupport η → max (u x) 0 < N)
    [IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) s))]
    (n : ℕ) (i : Fin d) :
    ∫ x in Metric.ball (0 : E) s,
        ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) ^ 2 ∂volume ≤
      (Cη * (1 + N) ^ (p / 2)) ^ 2 *
        (volume (Metric.ball (0 : E) s)).toReal := by
  let μ : Measure E := volume.restrict (Metric.ball (0 : E) s)
  let C : ℝ := Cη * (1 + N) ^ (p / 2)
  let b : E → ℝ := fun x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) *
      moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
  have hb_pt : ∀ᵐ x ∂μ, (b x) ^ 2 ≤ C ^ 2 := by
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hreg_le :
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤
            (1 + N) ^ (p / 2) := by
        have hbase :=
          moserExactRegPow_le_rpow_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p)
            (t := max (u x) 0) (moserEpsSeq_pos n)
            (le_max_right _ _) hboundx.le (by linarith)
        have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 :=
          add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
        calc
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤
              (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
          _ ≤ (1 + N) ^ (p / 2) := by
            exact Real.rpow_le_rpow hsum_nonneg
              (by linarith [moserEpsSeq_le_one n]) (by linarith)
      have hreg_nonneg :
          0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) :=
        moserExactRegPow_nonneg_of_nonneg_le_N
          (ε := moserEpsSeq n) (N := N) (p := p)
          (t := max (u x) 0) (moserEpsSeq_pos n)
          (le_max_right _ _) hboundx.le (by linarith)
      have hreg_norm_le :
          ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤
            (1 + N) ^ (p / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
        exact hreg_le
      have hfd_le :
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
        calc
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
            simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
              (EuclideanSpace.single i (1 : ℝ))
          _ ≤ Cη := hη_grad_bound x
      have hC_nonneg : 0 ≤ C := by
        exact mul_nonneg hCη_nonneg (Real.rpow_nonneg (by linarith) _)
      have hb_bound : ‖b x‖ ≤ C := by
        calc
          ‖b x‖ =
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                  simp [b, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) :=
            mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
          _ = C := rfl
      exact sq_le_sq.mpr (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hC_nonneg] using hb_bound)
    · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 :=
        fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
      have hC_sq_nonneg : 0 ≤ C ^ 2 := sq_nonneg C
      simpa [b, hfderiv_zero] using hC_sq_nonneg
  have hb_memLp : MemLp b 2 μ := by
    have hmeas :
        AEStronglyMeasurable b μ := by
      have hpow_meas :
          AEMeasurable
            (fun x => moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) μ :=
        (moserExactRegPow_contDiff (moserEpsSeq_pos n) hN).continuous.measurable
          |>.comp_aemeasurable
            (hu_meas.aemeasurable.max measurable_const.aemeasurable)
      exact
        (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
          hpow_meas.aestronglyMeasurable)
    have hC_memLp : MemLp (fun _ : E => C) 2 μ :=
      memLp_const C
    refine hC_memLp.of_le hmeas ?_
    filter_upwards [hb_pt] with x hx
    have hC_nonneg : 0 ≤ C := by
      exact mul_nonneg hCη_nonneg (Real.rpow_nonneg (by linarith) _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hC_nonneg] using sq_le_sq.mp hx
  have hb_int : Integrable (fun x => (b x) ^ 2) μ := by
    simpa [pow_two] using hb_memLp.integrable_sq
  calc
    ∫ x in Metric.ball (0 : E) s,
          ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) ^ 2 ∂volume =
        ∫ x, (b x) ^ 2 ∂μ := by simp [μ, b]
    _ ≤ ∫ x, (C ^ 2 : ℝ) ∂μ := by
      exact integral_mono_ae hb_int (integrable_const (C ^ 2)) hb_pt
    _ = μ.real Set.univ * C ^ 2 := by
      rw [integral_const]
      simp [smul_eq_mul]
    _ = volume.real (Metric.ball (0 : E) s) * C ^ 2 := by
      rw [show μ = volume.restrict (Metric.ball (0 : E) s) by rfl]
      rw [MeasureTheory.measureReal_restrict_apply_univ]
    _ = (volume (Metric.ball (0 : E) s)).toReal * C ^ 2 := rfl
    _ = C ^ 2 * (volume (Metric.ball (0 : E) s)).toReal := by ring

omit [NeZero d] in
private theorem sq_sub_coordinate_le_two_norm_sq (v : E) (i : Fin d) (b : ℝ) :
    (v i - b) ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * b ^ 2 := by
  have haux :
      (v i - b) ^ 2 ≤ 2 * (v i) ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (v i + b)]
  have hcoord_le : |v i| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hcoord_sq_le : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)] using hcoord_le)
  have htwice :
      (2 : ℝ) * (v i) ^ 2 ≤ 2 * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hcoord_sq_le (by norm_num)
  exact haux.trans (add_le_add htwice (le_refl (2 * b ^ 2)))

omit [NeZero d] in
private theorem integral_sq_sub_coordinate_le_of_bounds
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {v : α → E} {b c : α → ℝ}
    (i : Fin d) {A B : ℝ}
    (hc_def : ∀ x, c x = v x i - b x)
    (hc_memLp : MemLp c 2 μ)
    (hv_norm_memLp : MemLp (fun x => ‖v x‖) 2 μ)
    (hb_memLp : MemLp b 2 μ)
    (hv_bound : ∫ x, ‖v x‖ ^ 2 ∂μ ≤ A)
    (hb_bound : ∫ x, (b x) ^ 2 ∂μ ≤ B) :
    ∫ x, (c x) ^ 2 ∂μ ≤ 2 * A + 2 * B := by
  have hpointwise :
      ∀ᵐ x ∂μ, (c x) ^ 2 ≤ 2 * ‖v x‖ ^ 2 + 2 * (b x) ^ 2 := by
    filter_upwards with x
    rw [hc_def x]
    exact sq_sub_coordinate_le_two_norm_sq (d := d) (v x) i (b x)
  exact (integral_sq_le_two_integrals_of_ae
    hc_memLp hv_norm_memLp hb_memLp hpointwise).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left hv_bound (by norm_num))
        (mul_le_mul_of_nonneg_left hb_bound (by norm_num)))

omit [NeZero d] in
private theorem integral_sq_sub_coordinate_le_on_set_of_bounds
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {v : α → E} {b c : α → ℝ}
    (i : Fin d) {A B : ℝ}
    (hc_def : ∀ x, c x = v x i - b x)
    (hc_memLp : MemLp c 2 (μ.restrict s))
    (hv_norm_memLp : MemLp (fun x => ‖v x‖) 2 (μ.restrict s))
    (hb_memLp : MemLp b 2 (μ.restrict s))
    (hv_bound : ∫ x in s, ‖v x‖ ^ 2 ∂μ ≤ A)
    (hb_bound : ∫ x in s, (b x) ^ 2 ∂μ ≤ B) :
    ∫ x in s, (c x) ^ 2 ∂μ ≤ 2 * A + 2 * B :=
  integral_sq_sub_coordinate_le_of_bounds
    i hc_def hc_memLp hv_norm_memLp hb_memLp hv_bound hb_bound

omit [NeZero d] in
private theorem memLp_moserSingularFactor_of_two_le
    {μ : Measure E} {u η : E → ℝ} {p N : ℝ}
    (v : E → E) (i : Fin d)
    (hp : 1 < p) (hp_ge2 : 2 ≤ p) (hN_pos : 0 < N)
    (hη_nonneg : ∀ x, 0 ≤ η x) (hη_bound : ∀ x, |η x| ≤ 1)
    (hv_memLp : MemLp (fun x => v x i) 2 μ)
    (hfactor_aestrong :
      AEStronglyMeasurable
        (fun x =>
          if 0 < u x then
            η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * v x i
          else 0) μ)
    (hqual : ∀ᵐ x ∂μ, x ∈ tsupport η → max (u x) 0 < N)
    (hsublevel : ∀ᵐ x ∂μ, u x ≤ 0 → v x = 0) :
    MemLp
      (fun x =>
        if 0 < u x then
          η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * v x i
        else 0) 2 μ := by
  let K : ℝ := 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1))
  have hK_memLp : MemLp (fun x => K * |v x i|) 2 μ := by
    simpa [K, mul_assoc] using hv_memLp.norm.const_mul K
  refine hK_memLp.of_le hfactor_aestrong ?_
  filter_upwards [hqual, hsublevel] with x hxqual hsublevelx
  by_cases hxη : x ∈ tsupport η
  · by_cases hux : 0 < u x
    · have hboundx : max (u x) 0 < N := hxqual hxη
      have hpow_le :
          (max (u x) 0) ^ (p / 2 - 1) ≤ (1 + N) ^ (p / 2 - 1) := by
        exact Real.rpow_le_rpow (le_max_right _ _) (by linarith) (by linarith)
      have hcoeff_nonneg :
          0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
      have hcoeff_le :
          ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
            (p / 2) * (1 + N) ^ (p / 2 - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
        exact mul_le_mul_of_nonneg_left hpow_le (by linarith)
      have hη_abs_le : |η x| ≤ 1 := by
        simpa [abs_of_nonneg (hη_nonneg x)] using hη_bound x
      calc
        ‖(if 0 < u x then
              η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * v x i
            else 0)‖
            = |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ *
                |v x i| := by
                  simp [hux, norm_mul, Real.norm_eq_abs, mul_assoc]
        _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
            have hmul :
                |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                  1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
              exact mul_le_mul hη_abs_le hcoeff_le (by positivity)
                (by positivity : (0 : ℝ) ≤ 1)
            exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
        _ ≤ K * |v x i| := by
            have hc_nonneg : 0 ≤ (p / 2) * (1 + N) ^ (p / 2 - 1) := by
              exact mul_nonneg (by linarith)
                (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) _)
            have hgrad_nonneg : 0 ≤ |v x i| := abs_nonneg _
            calc
              1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| ≤
                  2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
                    nlinarith
              _ = K * |v x i| := by
                    dsimp [K]
        _ = ‖K * |v x i|‖ := by
            have hK_nonneg : 0 ≤ K := by
              dsimp [K]
              positivity
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK_nonneg (abs_nonneg _))]
    · have hgrad_zero : v x = 0 := hsublevelx (le_of_not_gt hux)
      simp [hux, hgrad_zero, K]
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    calc
      ‖(if 0 < u x then
            η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * v x i
          else 0)‖ = 0 := by simp [hηx]
      _ ≤ K * |v x i| := mul_nonneg hK_nonneg (abs_nonneg _)
      _ = ‖K * |v x i|‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK_nonneg (abs_nonneg _))]

private theorem memLp_two_of_ae_tendsto_of_uniform_integral_sq_bound
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {fn : ℕ → α → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hfn : ∀ n, MemLp (fn n) 2 μ)
    (htendsto : ∀ᵐ x ∂μ, Tendsto (fun n => fn n x) atTop (nhds (f x)))
    (hbound : ∀ n, ∫ x, (fn n x) ^ 2 ∂μ ≤ C) :
    MemLp f 2 μ := by
  have hFatou :
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ ≤
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fn n x) ^ 2) ∂μ) := by
    have hmeas :
        ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((fn n x) ^ 2)) μ := by
      intro n
      exact (((hfn n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    have hleft := MeasureTheory.lintegral_liminf_le'
      (μ := μ) (u := atTop)
      (f := fun n x => ENNReal.ofReal ((fn n x) ^ 2)) hmeas
    have hlim :
        (fun x => Filter.liminf (fun n => ENNReal.ofReal ((fn n x) ^ 2)) atTop) =ᵐ[μ]
          (fun x => ENNReal.ofReal ((f x) ^ 2)) := by
      filter_upwards [htendsto] with x hx
      have hsq :
          Tendsto (fun n => ENNReal.ofReal ((fn n x) ^ 2)) atTop
            (nhds (ENNReal.ofReal ((f x) ^ 2))) := by
        exact (ENNReal.continuous_ofReal.tendsto _
          |>.comp (((continuous_pow 2).tendsto (f x)).comp hx))
      simp [hsq.liminf_eq]
    calc
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ =
          ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal ((fn n x) ^ 2)) atTop ∂μ := by
            exact lintegral_congr_ae hlim.symm
      _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fn n x) ^ 2) ∂μ) := hleft
  have hBound_ne_top :
      atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fn n x) ^ 2) ∂μ) ≠ ⊤ := by
    apply ne_of_lt
    have hle :
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fn n x) ^ 2) ∂μ) ≤
          ENNReal.ofReal C := by
      refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
      have hEq :
          ∫⁻ x, ENNReal.ofReal ((fn n x) ^ 2) ∂μ =
            ENNReal.ofReal (∫ x, (fn n x) ^ 2 ∂μ) := by
        exact
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := μ) (f := fun x => (fn n x) ^ 2)
            (hfn n).integrable_sq (ae_of_all _ fun _ => sq_nonneg _)).symm
      rw [hEq]
      exact ENNReal.ofReal_le_ofReal (hbound n)
    exact lt_of_le_of_lt hle (by simp)
  have hf_sq_int : Integrable (fun x => (f x) ^ 2) μ := by
    have hlin_top : ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hFatou (lt_top_iff_ne_top.mpr hBound_ne_top))
    have hInt :=
      integrable_toReal_of_lintegral_ne_top
        ((hf.aemeasurable.pow_const 2).ennreal_ofReal) hlin_top
    simpa [ENNReal.toReal_ofReal, sq_nonneg] using hInt
  exact (memLp_two_iff_integrable_sq hf).2 hf_sq_int

private def moserSingularFactor
    (η u : E → ℝ) (p : ℝ) (v : E → E) (i : Fin d) (x : E) : ℝ :=
  if 0 < u x then
    η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * v x i
  else 0

private def moserExactSingularFactor
    (η u : E → ℝ) (N p : ℝ) (v : E → E) (n : ℕ) (i : Fin d) (x : E) : ℝ :=
  η x * deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) * v x i

omit [NeZero d] in
private theorem moserExactSingularFactor_sub_le_of_two_le
    {u η : E → ℝ} {p N : ℝ} (v : E → E) (n : ℕ) (i : Fin d) (x : E)
    (hp : 1 < p) (hp_ge2 : 2 ≤ p) (hN_pos : 0 < N)
    (hη_nonneg : ∀ y, 0 ≤ η y) (hη_bound : ∀ y, |η y| ≤ 1)
    (hqual : x ∈ tsupport η → max (u x) 0 < N)
    (hsublevel : u x ≤ 0 → v x = 0) :
    |moserExactSingularFactor η u N p v n i x -
        moserSingularFactor η u p v i x| ≤
      2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
  by_cases hxη : x ∈ tsupport η
  · by_cases hux : 0 < u x
    · have hboundx : max (u x) 0 < N := hqual hxη
      have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 :=
        add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
      have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
        linarith [moserEpsSeq_le_one n]
      have hderiv_nonneg :
          0 ≤ deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) := by
        rw [moserExactRegPow_deriv_eq_shifted
          (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg hsum_nonneg _)
      have hderiv_le :
          ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ ≤
            (p / 2) * (1 + N) ^ (p / 2 - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hderiv_nonneg,
          moserExactRegPow_deriv_eq_shifted
            (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)) (by linarith)
      have hlimit_nonneg :
          0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
      have hlimit_le :
          ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
            (p / 2) * (1 + N) ^ (p / 2 - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hlimit_nonneg]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (le_max_right _ _) (by linarith) (by linarith)) (by linarith)
      have hη_abs_le : |η x| ≤ 1 := by
        simpa [abs_of_nonneg (hη_nonneg x)] using hη_bound x
      have hseq_bound :
          ‖moserExactSingularFactor η u N p v n i x‖ ≤
            ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
        calc
          ‖moserExactSingularFactor η u N p v n i x‖ =
              |η x| *
                ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ *
                |v x i| := by
                  simp [moserExactSingularFactor, norm_mul, mul_assoc]
          _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
              have hmul :
                  |η x| *
                      ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ ≤
                    1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
                exact mul_le_mul hη_abs_le hderiv_le (by positivity)
                  (by positivity : (0 : ℝ) ≤ 1)
              exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
          _ = ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by ring
      have hsing_bound :
          ‖moserSingularFactor η u p v i x‖ ≤
            ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
        calc
          ‖moserSingularFactor η u p v i x‖ =
              |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ *
                |v x i| := by
                  simp [moserSingularFactor, hux, norm_mul, Real.norm_eq_abs, mul_assoc]
          _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
              have hmul :
                  |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                    1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
                exact mul_le_mul hη_abs_le hlimit_le (by positivity)
                  (by positivity : (0 : ℝ) ≤ 1)
              exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
          _ = ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by ring
      calc
        |moserExactSingularFactor η u N p v n i x -
            moserSingularFactor η u p v i x| ≤
            ‖moserExactSingularFactor η u N p v n i x‖ +
              ‖moserSingularFactor η u p v i x‖ := by
                simpa [Real.norm_eq_abs] using
                  norm_sub_le (moserExactSingularFactor η u N p v n i x)
                    (moserSingularFactor η u p v i x)
        _ ≤ 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by
            calc
              ‖moserExactSingularFactor η u N p v n i x‖ +
                    ‖moserSingularFactor η u p v i x‖ ≤
                  ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| +
                    ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| :=
                add_le_add hseq_bound hsing_bound
              _ = 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i| := by ring
    · have hgrad_zero : v x = 0 := hsublevel (le_of_not_gt hux)
      simp [moserExactSingularFactor, moserSingularFactor, hux, hgrad_zero]
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
    have hK_nonneg : 0 ≤ 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
      positivity
    simpa [moserExactSingularFactor, moserSingularFactor, hηx] using
      mul_nonneg hK_nonneg (abs_nonneg (v x i))

omit [NeZero d] in
private theorem moserExactSingularFactor_sub_le_of_lt_two
    {u η : E → ℝ} {p N : ℝ} (v : E → E) (n : ℕ) (i : Fin d) (x : E)
    (hp : 1 < p) (hp_lt2 : p < 2)
    (hη_nonneg : ∀ y, 0 ≤ η y)
    (hqual : x ∈ tsupport η → max (u x) 0 < N)
    (hsublevel : u x ≤ 0 → v x = 0) :
    |moserExactSingularFactor η u N p v n i x -
        moserSingularFactor η u p v i x| ≤
      ‖moserSingularFactor η u p v i x‖ := by
  by_cases hxη : x ∈ tsupport η
  · by_cases hux : 0 < u x
    · have hboundx : max (u x) 0 < N := hqual hxη
      have hcoeff_nonneg :
          0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
      have hderiv_nonneg :
          0 ≤ deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) := by
        have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 :=
          add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
        rw [moserExactRegPow_deriv_eq_shifted
          (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg hsum_nonneg _)
      have hcoeff_le :
          deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) ≤
            (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
        rw [moserExactRegPow_deriv_eq_shifted
          (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos
            (by simpa [max_eq_left hux.le] using hux)
            (by linarith [moserEpsSeq_pos n]) (by linarith))
          (by linarith)
      calc
        |moserExactSingularFactor η u N p v n i x -
            moserSingularFactor η u p v i x| =
            |η x| *
              |deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) -
                ((p / 2) * (max (u x) 0) ^ (p / 2 - 1))| *
              |v x i| := by
                have hfactor :
                    moserExactSingularFactor η u N p v n i x -
                        moserSingularFactor η u p v i x =
                      η x *
                          (deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) -
                            ((p / 2) * (max (u x) 0) ^ (p / 2 - 1))) *
                        v x i := by
                  simp only [moserExactSingularFactor, moserSingularFactor, if_pos hux]
                  ring
                rw [hfactor, abs_mul, abs_mul]
        _ = η x *
              (((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)) *
              |v x i| := by
                rw [abs_of_nonneg (hη_nonneg x), abs_of_nonpos (sub_nonpos.mpr hcoeff_le)]
                ring
        _ ≤ η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * |v x i| := by
              have hdiff_le :
                  ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                      deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) ≤
                    (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
                linarith
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hdiff_le (hη_nonneg x)) (abs_nonneg _)
        _ = ‖moserSingularFactor η u p v i x‖ := by
              rw [Real.norm_eq_abs]
              simp [moserSingularFactor, hux, abs_mul, abs_of_nonneg (hη_nonneg x),
                abs_of_nonneg hcoeff_nonneg]
    · have hgrad_zero : v x = 0 := hsublevel (le_of_not_gt hux)
      simp [moserExactSingularFactor, moserSingularFactor, hux, hgrad_zero]
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
    simp [moserExactSingularFactor, moserSingularFactor, hηx]

omit [NeZero d] in
private theorem tendsto_eLpNorm_moserExactSingularFactor
    {μ : Measure E} {u η : E → ℝ} {p N : ℝ}
    (v : E → E) (i : Fin d) (seq : ℕ → E → ℝ)
    (hp : 1 < p) (hN_pos : 0 < N)
    (hη_nonneg : ∀ x, 0 ≤ η x) (hη_bound : ∀ x, |η x| ≤ 1)
    (hqual : ∀ᵐ x ∂μ, x ∈ tsupport η → max (u x) 0 < N)
    (hsublevel : ∀ᵐ x ∂μ, u x ≤ 0 → v x = 0)
    (hv_memLp : MemLp (fun x => v x i) 2 μ)
    (hseq_formula :
      ∀ n x, seq n x = moserExactSingularFactor η u N p v n i x)
    (hseq_memLp : ∀ n, MemLp (seq n) 2 μ)
    (hlimit_memLp : MemLp (moserSingularFactor η u p v i) 2 μ)
    (htendsto :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => seq n x) atTop
          (nhds (moserSingularFactor η u p v i x))) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x => seq n x - moserSingularFactor η u p v i x) 2 μ)
      atTop (nhds 0) := by
  have hsub_memLp :
      ∀ n, MemLp (fun x => seq n x - moserSingularFactor η u p v i x) 2 μ :=
    fun n => (hseq_memLp n).sub hlimit_memLp
  by_cases hp_ge2 : 2 ≤ p
  · let K : ℝ := 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1))
    have hK_memLp : MemLp (fun x => K * |v x i|) 2 μ := by
      simpa only [Real.norm_eq_abs] using hv_memLp.norm.const_mul K
    apply moser_tendsto_eLpNorm_zero_of_dominated hK_memLp
      (fun n => (hsub_memLp n).aestronglyMeasurable)
    · intro n
      filter_upwards [hqual, hsublevel] with x hxqual hsublevelx
      rw [hseq_formula n x]
      change
        |moserExactSingularFactor η u N p v n i x -
            moserSingularFactor η u p v i x| ≤
          2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |v x i|
      exact moserExactSingularFactor_sub_le_of_two_le
        v n i x hp hp_ge2 hN_pos hη_nonneg hη_bound hxqual hsublevelx
    · filter_upwards [htendsto] with x hx
      simpa using hx.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => moserSingularFactor η u p v i x) atTop
          (nhds (moserSingularFactor η u p v i x)))
  · apply moser_tendsto_eLpNorm_zero_of_dominated hlimit_memLp.norm
      (fun n => (hsub_memLp n).aestronglyMeasurable)
    · intro n
      filter_upwards [hqual, hsublevel] with x hxqual hsublevelx
      rw [hseq_formula n x]
      exact moserExactSingularFactor_sub_le_of_lt_two
        v n i x hp (lt_of_not_ge hp_ge2) hη_nonneg hxqual hsublevelx
    · filter_upwards [htendsto] with x hx
      simpa using hx.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => moserSingularFactor η u p v i x) atTop
          (nhds (moserSingularFactor η u p v i x)))

/-! #### Sub-theorem A: Witness construction for `η · u₊^{p/2}`

Build `MemW1pWitness 2 (moserPowerCutoff η u p)` by taking L² limits of the
exact-on-support regularized witnesses `moserExactRegPowerCutoffWitness`
with fixed qualitative cutoff level `N` and ε → 0.
Uses `HasWeakPartialDeriv.of_eLpNormApprox_p` and dominated convergence,
simplified by the Chapter 05 a.e. boundedness of `u₊`. -/
theorem moserPowerCutoff_memW1pWitness
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 1 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (moserPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume := by
  classical
  let Ω : Set E := Metric.ball (0 : E) s
  let hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := MemW1p.someWitness hsub.1
  obtain ⟨N0, hN0_pos, hqual0⟩ :=
    qualitative_bound_on_tsupport_of_subsolution
      (d := d) hd A (u := u) (η := η) (s := s) hs hs1 hsub hu1 hη_sub_ball
  let N : ℝ := N0 + 1
  have hN_pos : 0 < N := by
    dsimp [N]
    linarith
  have hN : 0 ≤ N := hN_pos.le
  have hqual :
      ∀ᵐ x ∂(volume.restrict Ω),
        x ∈ tsupport η → max (u x) 0 < N := by
    filter_upwards [hqual0] with x hx hxη
    dsimp [N]
    linarith [hx hxη]
  obtain ⟨ρ, hρ, hρs, hη_sub_ρ⟩ :=
    exists_lt_one_ball_of_tsupport_subset_ball (η := η) (s := s) hs hs1 hη_sub_ball
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρs hs1
  let f : E → ℝ := moserPowerCutoff (d := d) η u p
  let fn : ℕ → E → ℝ := fun n => moserExactRegPowerCutoff η u (moserEpsSeq n) N p
  let wfnBig : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) (Metric.ball (0 : E) 1) := fun n =>
    by
      dsimp [fn]
      exact
        moserExactRegPowerCutoffWitness
          (d := d) (u := u) (η := η) (ε := moserEpsSeq n) (N := N) (p := p) (Cη := Cη)
          (moserEpsSeq_pos n) hN hu1 hη hη_bound hη_grad_bound
  let wfn : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) Ω := fun n =>
    (wfnBig n).restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let μ : Measure E := volume.restrict Ω
  let Ωρ : Set E := Metric.ball (0 : E) ρ
  let μρ : Measure E := volume.restrict Ωρ
  let huΩ : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let hwPos : MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
    (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict
      Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hΩρ_sub_Ω : Ωρ ⊆ Ω := Metric.ball_subset_ball (le_of_lt hρs)
  have hqualρ :
      ∀ᵐ x ∂μρ, x ∈ tsupport η → max (u x) 0 < N := by
    exact ae_restrict_of_ae_restrict_of_subset hΩρ_sub_Ω hqual
  have hsublevelΩ :
      ∀ᵐ x ∂μ, u x ≤ 0 → hwPos.weakGrad x = 0 := by
    simpa [μ, hwPos] using
      moserPosPartWitness_restrict_grad_zero_on_nonpos
        (d := d) (Ω := Ω) Metric.isOpen_ball (Metric.ball_subset_ball hs1) hu1
  let _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, Ω] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s))
  let _ : IsFiniteMeasure μρ := by
    refine ⟨?_⟩
    simpa [μρ, Ωρ] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := ρ))
  obtain ⟨hf_memLp, hfn_fun_memLp, hfn_tendsto⟩ :=
    moserPowerCutoff_functionApprox (d := d) (Ω := Ω) Metric.isOpen_ball
      (Metric.ball_subset_ball hs1) hp hN_pos hu1 hη hη_bound
      hη_grad_bound (by simpa [μ] using hqual)
  change MemLp f 2 μ at hf_memLp
  change (∀ n, MemLp (fun x => fn n x - f x) 2 μ) at hfn_fun_memLp
  change Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ)
    atTop (nhds 0) at hfn_tendsto
  have hCη_nonneg : 0 ≤ Cη := by
    have hgrad0 : ‖fderiv ℝ η (0 : E)‖ ≤ Cη := hη_grad_bound (0 : E)
    nlinarith [norm_nonneg (fderiv ℝ η (0 : E))]
  let Bn : ℕ → Fin d → E → ℝ := fun n i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) *
      moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
  let B : Fin d → E → ℝ := fun i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) * (max (u x) 0) ^ (p / 2)
  let CB : ℝ := 2 * Cη * (1 + N) ^ (p / 2)
  have hCB_nonneg : 0 ≤ CB := by
    dsimp [CB]
    have h1N_nonneg : 0 ≤ 1 + N := by linarith
    positivity
  have hCB_memLp : MemLp (fun _ : E => CB) 2 μ := by
    simpa [CB] using (memLp_const CB : MemLp (fun _ : E => CB) 2 μ)
  have hB_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => Bn n i x) atTop (nhds (B i x)) := by
    intro i
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hpow :=
        moserExactRegPow_tendsto_rpow_of_nonneg_lt_N
          (N := N) (p := p) (t := max (u x) 0)
          (le_max_right _ _) hboundx hp
      simpa [Bn, B, mul_assoc, mul_left_comm, mul_comm] using
        Tendsto.const_mul ((fderiv ℝ η x) (EuclideanSpace.single i 1)) hpow
    · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
      simp [Bn, B, hfderiv_zero]
  have hB_memLp :
      ∀ i : Fin d, MemLp (B i) 2 μ := by
    intro i
    refine hCB_memLp.of_le ?_ ?_
    · exact aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => by
          have hpow_meas :
              AEMeasurable (fun x => moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) μ := by
            exact
              (moserExactRegPow_contDiff (ε := moserEpsSeq n) (N := N) (p := p)
                (moserEpsSeq_pos n) hN).continuous.measurable.comp_aemeasurable
                  (huΩ.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable)
          exact
            (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
              hpow_meas.aestronglyMeasurable)
        ) (hB_tendsto_ae i)
    · filter_upwards [hqual] with x hx
      by_cases hxη : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hx hxη
        have hpow_le :
            (max (u x) 0) ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
            (by linarith) (by linarith)
        have hpow_norm_le :
            ‖(max (u x) 0) ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ max (u x) 0 by
            exact le_max_right _ _) _)]
          exact hpow_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖(max (u x) 0) ^ (p / 2)‖ := by
            simp [B, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
            exact mul_le_mul hfd_le hpow_norm_le (norm_nonneg _) hCη_nonneg
          _ ≤ CB := by
            calc
              Cη * (1 + N) ^ (p / 2) ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
                nlinarith [hCη_nonneg, hpow_nonneg]
              _ = CB := by ring
          _ = ‖CB‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg]
      · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
          exact fderiv_apply_zero_outside_of_tsupport_subset
            (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
        calc
          ‖B i x‖ = 0 := by simp [B, hfderiv_zero]
          _ ≤ ‖CB‖ := by
            simpa [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg] using hCB_nonneg
  have hBn_fun_memLp :
      ∀ n i, MemLp (fun x => Bn n i x - B i x) 2 μ := by
    intro n i
    have hpow_meas :
        AEMeasurable (fun x => moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) μ := by
      exact
        (moserExactRegPow_contDiff (ε := moserEpsSeq n) (N := N) (p := p)
          (moserEpsSeq_pos n) hN).continuous.measurable.comp_aemeasurable
            (huΩ.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable)
    have hBn_memLp : MemLp (Bn n i) 2 μ := by
      refine hCB_memLp.of_le ?_ ?_
      · exact
          (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
            hpow_meas.aestronglyMeasurable)
      · filter_upwards [hqual] with x hx
        by_cases hxη : x ∈ tsupport η
        · have hboundx : max (u x) 0 < N := hx hxη
          have hp_nonneg : 0 ≤ p := by linarith
          have hreg_le :
              moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
            have hbase :=
              moserExactRegPow_le_rpow_of_nonneg_le_N
                (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
                (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
            have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
              have := moserEpsSeq_le_one n
              linarith
            have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
              exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
            calc
              moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
                  ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
              _ ≤ (1 + N) ^ (p / 2) := by
                  exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
          have hreg_nonneg :
              0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
            exact moserExactRegPow_nonneg_of_nonneg_le_N
              (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
              (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
          have hreg_norm_le :
              ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
            exact hreg_le
          have hfd_le :
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
            calc
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
                simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                  (EuclideanSpace.single i (1 : ℝ)))
              _ ≤ Cη := hη_grad_bound x
          have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
            exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
          calc
            ‖Bn n i x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                    ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                      simp [Bn, norm_mul]
            _ ≤ Cη * (1 + N) ^ (p / 2) := by
                exact mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
            _ ≤ CB := by
                calc
                  Cη * (1 + N) ^ (p / 2) ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
                    nlinarith [hCη_nonneg, hpow_nonneg]
                  _ = CB := by ring
            _ = ‖CB‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg]
        · have hfderiv_zero :
            (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
            exact fderiv_apply_zero_outside_of_tsupport_subset
              (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
          calc
            ‖Bn n i x‖ = 0 := by simp [Bn, hfderiv_zero]
            _ ≤ ‖CB‖ := by
              simpa [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg] using hCB_nonneg
    exact hBn_memLp.sub (hB_memLp i)
  have hBn_meas : ∀ n i, AEStronglyMeasurable (fun x => Bn n i x - B i x) μ := by
    intro n i
    exact (hBn_fun_memLp n i).aestronglyMeasurable
  have hBn_dom :
      ∀ n i, ∀ᵐ x ∂μ, |Bn n i x - B i x| ≤ CB := by
    intro n i
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hp_nonneg : 0 ≤ p := by linarith
      have hBn_bound :
          ‖Bn n i x‖ ≤ Cη * (1 + N) ^ (p / 2) := by
        have hreg_le :
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
          have hbase :=
            moserExactRegPow_le_rpow_of_nonneg_le_N
              (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
              (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
          have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
            have := moserEpsSeq_le_one n
            linarith
          have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
            exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
          calc
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
                ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
            _ ≤ (1 + N) ^ (p / 2) := by
                exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
        have hreg_nonneg :
            0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
          exact moserExactRegPow_nonneg_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
            (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
        have hreg_norm_le :
            ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
          exact hreg_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖Bn n i x‖
              = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                  ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                    simp [Bn, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
              exact mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
      have hB_bound :
          ‖B i x‖ ≤ Cη * (1 + N) ^ (p / 2) := by
        have hpow_le :
            (max (u x) 0) ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
            (by linarith) (by linarith)
        have hpow_norm_le :
            ‖(max (u x) 0) ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ max (u x) 0 by
            exact le_max_right _ _) _)]
          exact hpow_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖(max (u x) 0) ^ (p / 2)‖ := by
            simp [B, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
              exact mul_le_mul hfd_le hpow_norm_le (norm_nonneg _) hCη_nonneg
      calc
        |Bn n i x - B i x| ≤ ‖Bn n i x‖ + ‖B i x‖ := by
          simpa [Real.norm_eq_abs] using norm_sub_le (Bn n i x) (B i x)
        _ ≤ CB := by
            have hsum_bound :
                ‖Bn n i x‖ + ‖B i x‖ ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
              linarith [hBn_bound, hB_bound]
            calc
              ‖Bn n i x‖ + ‖B i x‖ ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := hsum_bound
              _ = CB := by ring
    · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
      have hBn_zero : Bn n i x = 0 := by simp [Bn, hfderiv_zero]
      have hB_zero : B i x = 0 := by simp [B, hfderiv_zero]
      rw [hBn_zero, hB_zero, sub_self, abs_zero]
      exact hCB_nonneg
  have hB_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => Bn n i x - B i x) 2 μ) atTop (nhds 0) := by
    intro i
    exact moser_tendsto_eLpNorm_zero_of_dominated (hCB_memLp) (fun n => hBn_meas n i)
      (fun n => hBn_dom n i) <| by
        filter_upwards [hB_tendsto_ae i] with x hx
        have hconst : Tendsto (fun _ : ℕ => B i x) atTop (nhds (B i x)) := tendsto_const_nhds
        simpa using hx.sub hconst
  let Gn : ℕ → Fin d → E → ℝ := fun n i x => (wfn n).weakGrad x i
  let AsingSeq : ℕ → Fin d → E → ℝ := fun n i x => Gn n i x - Bn n i x
  let Asing : Fin d → E → ℝ :=
    fun i x => moserSingularFactor η u p hwPos.weakGrad i x
  have hBn_memLp :
      ∀ n i, MemLp (Bn n i) 2 μ := by
    intro n i
    convert (hBn_fun_memLp n i).add (hB_memLp i) using 1
    ext x
    simp [sub_eq_add_neg]
  have hAsingSeq_memLp :
      ∀ n i, MemLp (AsingSeq n i) 2 μ := by
    intro n i
    change MemLp (fun x => (wfn n).weakGrad x i - Bn n i x) 2 μ
    convert ((wfn n).weakGrad_component_memLp i).sub (hBn_memLp n i) using 1
    funext x
    rfl
  have hAsingSeq_formula :
      ∀ n i x,
        AsingSeq n i x =
          η x * deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) *
            hwPos.weakGrad x i := by
    intro n i x
    dsimp [AsingSeq, Gn, Bn, wfn, wfnBig, hwPos]
    simp only [MemW1pWitness.restrict]
    rw [moserExactRegPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := moserEpsSeq n)
      (N := N) (p := p) (Cη := Cη) (moserEpsSeq_pos n) hN hu1 hη hη_bound
      hη_grad_bound x i]
    ring
  have hAsing_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => AsingSeq n i x) atTop (nhds (Asing i x)) := by
    intro i
    filter_upwards [hqual, hsublevelΩ] with x hxqual hsublevelx
    by_cases hxη : x ∈ tsupport η
    · by_cases hux : 0 < u x
      · have hboundx : max (u x) 0 < N := hxqual hxη
        have hderiv :=
          moserExactRegPow_deriv_tendsto_of_pos_lt_N
            (N := N) (p := p) (t := max (u x) 0)
            (by simpa [max_eq_left hux.le] using hux) hboundx
        have hmul :
            Tendsto
              (fun n =>
                (η x * hwPos.weakGrad x i) *
                  deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0))
              atTop
              (nhds
                ((η x * hwPos.weakGrad x i) *
                  ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)))) := by
          exact Tendsto.const_mul (η x * hwPos.weakGrad x i) hderiv
        have hEq :
            (fun n => AsingSeq n i x) =
              (fun n =>
                (η x * hwPos.weakGrad x i) *
                  deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)) := by
          funext n
          rw [hAsingSeq_formula n i x]
          ring
        rw [hEq]
        simpa [Asing, moserSingularFactor, hux, mul_assoc, mul_left_comm, mul_comm] using hmul
      · have hunonpos : u x ≤ 0 := le_of_not_gt hux
        have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
        have hEq :
            ∀ n, AsingSeq n i x = 0 := by
          intro n
          rw [hAsingSeq_formula n i x, hgrad_zero]
          simp
        refine tendsto_const_nhds.congr' ?_
        exact Filter.Eventually.of_forall fun n => by
          simp [hEq n, Asing, moserSingularFactor, hux]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
      have hEq :
          ∀ n, AsingSeq n i x = 0 := by
        intro n
        rw [hAsingSeq_formula n i x, hηx]
        ring
      refine tendsto_const_nhds.congr' ?_
      exact Filter.Eventually.of_forall fun n => by
        simp [hEq n, Asing, moserSingularFactor, hηx]
  have hAsing_aestrong :
      ∀ i : Fin d, AEStronglyMeasurable (Asing i) μ := by
    intro i
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hAsingSeq_memLp n i).aestronglyMeasurable) (hAsing_tendsto_ae i)
  have hpIntρ_base :
      Integrable (fun x => |max (u x) 0| ^ p) μρ := by
    have hpIntΩ : Integrable (fun x => |max (u x) 0| ^ p) μ := by
      change Integrable
        (fun x => |max (u x) 0| ^ p)
        (volume.restrict (Metric.ball (0 : E) s))
      exact hpInt
    exact hpIntΩ.mono_measure (Measure.restrict_mono_set volume hΩρ_sub_Ω)
  have hRhsDom_int :
      Integrable (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p)) μρ := by
    have hone : Integrable (fun _ : E => (1 : ℝ)) μρ := by
      change IntegrableOn (fun _ : E => (1 : ℝ)) Ωρ volume
      exact
        integrableOn_const (s := Ωρ)
          ((measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := ρ)).ne)
    exact (hone.add hpIntρ_base).const_mul ((2 : ℝ) ^ p)
  have hpIntρ_eps :
      ∀ n, IntegrableOn (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) Ωρ volume := by
    intro n
    let huρw : MemW1pWitness 2 u Ωρ :=
      hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball (le_of_lt hρ1))
    have hmeas :
        AEStronglyMeasurable (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) μρ := by
      have hmax_meas : AEMeasurable (fun x => max (u x) 0) μρ :=
        huρw.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable
      have habs_meas : AEMeasurable (fun x => |max (u x) 0|) μρ := hmax_meas.norm
      have hsum_meas : AEMeasurable (fun x => moserEpsSeq n + |max (u x) 0|) μρ :=
        habs_meas.const_add (moserEpsSeq n)
      exact (hsum_meas.pow_const p).aestronglyMeasurable
    have hbound :
        ∀ᵐ x ∂μρ, ‖(moserEpsSeq n + |max (u x) 0|) ^ p‖ ≤
          (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
      exact Filter.Eventually.of_forall (fun x => by
        have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
        have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
          exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
        have hpt :
            |(moserEpsSeq n + |max (u x) 0|) ^ p| ≤
              (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
          calc
            |(moserEpsSeq n + |max (u x) 0|) ^ p|
                = (moserEpsSeq n + |max (u x) 0|) ^ p := by
                    rw [abs_of_nonneg (Real.rpow_nonneg hsum_nonneg _)]
            _ ≤ (1 + |max (u x) 0|) ^ p := by
                exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n])
                  (by linarith)
            _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
                exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
        simpa [Real.norm_eq_abs] using hpt)
    exact Integrable.mono' hRhsDom_int hmeas hbound
  have hGn_zero_outside_ρ :
      ∀ n, ∀ᵐ x ∂μ, x ∉ Ωρ → (wfn n).weakGrad x = 0 := by
    intro n
    filter_upwards with x hxρ
    have hxη : x ∉ tsupport η := fun hxt => hxρ (hη_sub_ρ hxt)
    have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
    apply PiLp.ext
    intro i
    have hfderiv_zero :
        (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
      exact fderiv_apply_zero_outside_of_tsupport_subset
        (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
    simp only [wfn, MemW1pWitness.restrict]
    simpa [wfnBig, fn, hηx, hfderiv_zero] using
      (moserExactRegPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := moserEpsSeq n)
        (N := N) (p := p) (Cη := Cη) (moserEpsSeq_pos n) hN hu1 hη hη_bound
        hη_grad_bound x i)
  have hGn_int_eq_ρ :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume =
          ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := by
    intro n
    have hEq_ind :
        (fun x => ‖(wfn n).weakGrad x‖ ^ 2) =ᵐ[μ]
          Set.indicator Ωρ (fun x => ‖(wfn n).weakGrad x‖ ^ 2) := by
      filter_upwards [hGn_zero_outside_ρ n] with x hx
      by_cases hxρ : x ∈ Ωρ
      · simp [Set.indicator_of_mem, hxρ]
      · simp [Set.indicator_of_notMem, hxρ, hx hxρ]
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ := by
              simp [μ]
      _ = ∫ x, Set.indicator Ωρ (fun x => ‖(wfn n).weakGrad x‖ ^ 2) x ∂μ := by
            exact integral_congr_ae hEq_ind
      _ = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ := by
            exact integral_indicator Metric.isOpen_ball.measurableSet
      _ = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := by
            simp [μ, Measure.restrict_restrict_of_subset hΩρ_sub_Ω]
  let CE : ℝ := 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1)
  have hCE_nonneg : 0 ≤ CE := by
    dsimp [CE]
    have hterm_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 + 1 := by
      have hratio_sq_nonneg : 0 ≤ (p / (p - 1)) ^ 2 := sq_nonneg _
      exact add_nonneg (mul_nonneg A.1.Λ_pos.le hratio_sq_nonneg) zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Cη)) hterm_nonneg
  have hGn_energy :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume := by
    intro n
    have hbound_pt :
        ∀ᵐ x ∂μρ,
          (moserEpsSeq n + |max (u x) 0|) ^ p ≤
            (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
      filter_upwards with x
      have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
      have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
        exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
      calc
        (moserEpsSeq n + |max (u x) 0|) ^ p
            ≤ (1 + |max (u x) 0|) ^ p := by
                exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n])
                  (by linarith)
        _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
            exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
    have hmainρ :
        ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
      have hmainρ_big :
          ∫ x in Ωρ, ‖(wfnBig n).weakGrad x‖ ^ 2 ∂volume ≤
            CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
        simpa [CE, Ωρ, wfnBig, fn] using
          (moserExactReg_energy_mainBall
            (d := d) (A := A) (u := u) (η := η) (p := p) (ρ := ρ)
            (Cη := Cη) (N := N) (hp := hp) (hρ := hρ) (hρ1 := hρ1) (hN := hN)
            (hsub := hsub) (hu1 := hu1) (hη := hη) (hη_nonneg := hη_nonneg)
            (hη_bound := hη_bound) (hη_grad_bound := hη_grad_bound)
            (hη_sub_ball := hη_sub_ρ) (hqual := hqualρ) (hpInt := hpIntρ_eps) n)
      change ∫ x in Ωρ, ‖(wfnBig n).weakGrad x‖ ^ 2 ∂volume ≤
        CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume
      exact hmainρ_big
    have hdom_int :
        Integrable (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p)) μρ := hRhsDom_int
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := hGn_int_eq_ρ n
      _ ≤ CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := hmainρ
      _ ≤ CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume := by
            refine mul_le_mul_of_nonneg_left ?_ hCE_nonneg
            exact integral_mono_ae (hpIntρ_eps n) hdom_int hbound_pt
  let CB0 : ℝ := Cη * (1 + N) ^ (p / 2)
  have hBn_sq_bound :
      ∀ n i,
        ∫ x in Ω, (Bn n i x) ^ 2 ∂volume ≤
          CB0 ^ 2 * (volume Ω).toReal := by
    intro n i
    change
      ∫ x in Metric.ball (0 : E) s,
          ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) ^ 2 ∂volume ≤
        (Cη * (1 + N) ^ (p / 2)) ^ 2 *
          (volume (Metric.ball (0 : E) s)).toReal
    exact moserRegularCutoffTerm_integral_sq_bound
      (d := d) hp hN hCη_nonneg hη hη_grad_bound
      (by simpa [μ, Ω] using huΩ.memLp.aestronglyMeasurable)
      (by simpa [μ, Ω] using hqual) n i
  have hAsingSeq_sq_bound :
      ∀ n i,
        ∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume ≤
          2 * (CE *
              ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
            2 * (CB0 ^ 2 * (volume Ω).toReal) := by
    intro n i
    exact integral_sq_sub_coordinate_le_on_set_of_bounds
      (d := d) (μ := volume) (s := Ω)
      (v := fun x => (wfn n).weakGrad x)
      (b := Bn n i) (c := AsingSeq n i) i
      (fun x => by rfl)
      (hAsingSeq_memLp n i) (wfn n).weakGrad_norm_memLp
      (hBn_memLp n i) (hGn_energy n) (hBn_sq_bound n i)
  have hAsing_memLp :
      ∀ i : Fin d, MemLp (Asing i) 2 μ := by
    intro i
    by_cases hp_ge2 : 2 ≤ p
    · exact
        memLp_moserSingularFactor_of_two_le
          (d := d) (μ := μ) (u := u) (η := η) (p := p) (N := N)
          hwPos.weakGrad i hp hp_ge2 hN_pos hη_nonneg hη_bound
          (hwPos.weakGrad_component_memLp i) (hAsing_aestrong i)
          hqual hsublevelΩ
    · refine memLp_two_of_ae_tendsto_of_uniform_integral_sq_bound
        (C :=
          2 * (CE *
              ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
            2 * (CB0 ^ 2 * (volume Ω).toReal))
        (hAsing_aestrong i) (fun n => hAsingSeq_memLp n i) (hAsing_tendsto_ae i) ?_
      intro n
      simpa [μ] using hAsingSeq_sq_bound n i
  have hAsing_fun_memLp :
      ∀ n i, MemLp (fun x => AsingSeq n i x - Asing i x) 2 μ := by
    intro n i
    exact (hAsingSeq_memLp n i).sub (hAsing_memLp i)
  have hAsing_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => AsingSeq n i x - Asing i x) 2 μ)
          atTop (nhds 0) := by
    intro i
    exact tendsto_eLpNorm_moserExactSingularFactor
      (d := d) (μ := μ) (u := u) (η := η) (p := p) (N := N)
      hwPos.weakGrad i (fun n x => AsingSeq n i x)
      hp hN_pos hη_nonneg hη_bound hqual hsublevelΩ
      (hwPos.weakGrad_component_memLp i)
      (fun n x => by
        rw [hAsingSeq_formula n i x]
        rfl)
      (fun n => hAsingSeq_memLp n i) (hAsing_memLp i)
      (hAsing_tendsto_ae i)
  let gComp : Fin d → E → ℝ := fun i x => Asing i x + B i x
  have hgComp_memLp :
      ∀ i : Fin d, MemLp (gComp i) 2 μ := by
    intro i
    exact (hAsing_memLp i).add (hB_memLp i)
  have hGn_fun_memLp :
      ∀ n i, MemLp (fun x => Gn n i x - gComp i x) 2 μ := by
    intro n i
    exact ((wfn n).weakGrad_component_memLp i).sub (hgComp_memLp i)
  have hGn_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => Gn n i x - gComp i x) 2 μ)
          atTop (nhds 0) := by
    intro i
    exact tendsto_eLpNorm_sub_of_component_decomposition
      (f := fun n x => Gn n i x) (g := gComp i)
      (f₁ := fun n x => AsingSeq n i x) (g₁ := Asing i)
      (f₂ := fun n x => Bn n i x) (g₂ := B i)
      (fun n x => by
        dsimp [Gn, gComp, AsingSeq]
        abel)
      (fun n => hAsing_fun_memLp n i) (fun n => hBn_fun_memLp n i)
      (hAsing_tendsto i) (hB_tendsto i)
  have hWeakComp :
      ∀ i : Fin d, HasWeakPartialDeriv i (gComp i) f Ω := by
    intro i
    have hf_memLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      simpa [μ] using hf_memLp
    have hgComp_memLp' : MemLp (gComp i) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      simpa [μ] using hgComp_memLp i
    have hGn_isWeak : ∀ n, HasWeakPartialDeriv i (Gn n i) (fn n) Ω := by
      intro n
      simpa [Gn] using (wfn n).isWeakGrad i
    have hfn_fun_memLp' :
        ∀ n, MemLp (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      intro n
      simpa [μ] using hfn_fun_memLp n
    have hfn_tendsto' :
        Tendsto
          (fun n => eLpNorm (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω))
          atTop (nhds 0) := by
      simpa [μ] using hfn_tendsto
    have hGn_fun_memLp' :
        ∀ n, MemLp (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict Ω) := by
      intro n
      simpa [μ] using hGn_fun_memLp n i
    have hGn_tendsto' :
        Tendsto
          (fun n => eLpNorm (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ))
            (volume.restrict Ω))
          atTop (nhds 0) := by
      simpa [μ] using hGn_tendsto i
    refine HasWeakPartialDeriv.of_eLpNormApprox_p
      (d := d) (Ω := Ω) (p := 2) (hΩ := Metric.isOpen_ball) (hp := by norm_num)
      (i := i) (f := f) (g := gComp i) (ψ := fn) (gψ := fun n => Gn n i)
      hf_memLp' hgComp_memLp'
      hGn_isWeak
      hfn_fun_memLp' hfn_tendsto'
      hGn_fun_memLp' hGn_tendsto'
  let G : E → E := fun x => WithLp.toLp 2 fun i => gComp i x
  let hwv : MemW1pWitness 2 f Ω := {
    memLp := hf_memLp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      simpa [G, gComp, PiLp.toLp_apply] using hgComp_memLp i
    isWeakGrad := by
      intro i
      simpa [G, gComp, PiLp.toLp_apply] using hWeakComp i }
  have hGn_comp_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => Gn n i x) atTop (nhds (gComp i x)) := by
    intro i
    filter_upwards [hAsing_tendsto_ae i, hB_tendsto_ae i] with x hA hB
    have hEq :
        (fun n => Gn n i x) = (fun n => AsingSeq n i x + Bn n i x) := by
      funext n
      dsimp [AsingSeq, Gn]
      ring
    rw [hEq]
    have hsum :
        Tendsto (fun n => AsingSeq n i x + Bn n i x) atTop
          (nhds (Asing i x + B i x)) := hA.add hB
    simpa [gComp] using hsum
  have hGn_vec_tendsto_ae :
      ∀ᵐ x ∂μ, Tendsto (fun n => (wfn n).weakGrad x) atTop (nhds (hwv.weakGrad x)) := by
    have hcoords :
        ∀ᵐ x ∂μ, ∀ i : Fin d, Tendsto (fun n => Gn n i x) atTop (nhds (gComp i x)) := by
      rw [ae_all_iff]
      intro i
      exact hGn_comp_tendsto_ae i
    filter_upwards [hcoords] with x hx
    have hpi :
        Tendsto (fun n : ℕ => fun i : Fin d => Gn n i x) atTop
          (nhds fun i : Fin d => gComp i x) := by
      rw [tendsto_pi_nhds]
      intro i
      exact hx i
    have htoLp :
        Tendsto (fun y : Fin d → ℝ => WithLp.toLp 2 y) (nhds fun i : Fin d => gComp i x)
          (nhds (WithLp.toLp 2 fun i : Fin d => gComp i x)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto (fun i : Fin d => gComp i x)
    have hseq :
        (fun n => (wfn n).weakGrad x) =
          fun n => WithLp.toLp 2 (fun i : Fin d => Gn n i x) := by
      funext n
      apply PiLp.ext
      intro i
      simp [Gn]
    have hlimit :
        hwv.weakGrad x = WithLp.toLp 2 (fun i : Fin d => gComp i x) := by
      apply PiLp.ext
      intro i
      simp [hwv, G]
    rw [hseq, hlimit]
    exact htoLp.comp hpi
  have hFatou :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ ≤
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) := by
    have hmeas :
        ∀ n, AEMeasurable (fun x => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) μ := by
      intro n
      have hsq_meas :
          AEMeasurable (fun x => ‖(wfn n).weakGrad x‖ ^ 2) μ := by
        exact (wfn n).weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow_const 2
      exact hsq_meas.ennreal_ofReal
    have hleft := MeasureTheory.lintegral_liminf_le'
      (μ := μ) (u := atTop)
      (f := fun n x => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) hmeas
    have hlim :
        (fun x =>
          Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop) =ᵐ[μ]
            (fun x => ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2)) := by
      filter_upwards [hGn_vec_tendsto_ae] with x hx
      have hsq :
          Tendsto (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop
            (nhds (ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2))) := by
        exact ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp hx
      exact hsq.liminf_eq
    calc
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ
          = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop ∂μ := by
              exact lintegral_congr_ae hlim.symm
      _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) := hleft
  have hGn_energy_exact :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
    intro n
    have hmainρ :
        ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
      simp only [wfn, MemW1pWitness.restrict]
      simpa [CE, Ωρ, wfnBig, fn] using
        (moser_regularized_energy_bound (d := d) A (u := u) (η := η) (p := p) (ρ := ρ)
          (Cη := Cη) (ε := moserEpsSeq n) (N := N) hp hρ hρ1 (moserEpsSeq_pos n) hN
          hsub hu1 hη hη_nonneg hη_bound hη_grad_bound hη_sub_ρ hqualρ
          (hpIntρ_eps n))
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := hGn_int_eq_ρ n
      _ ≤ CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := hmainρ
  have hRhs_meas :
      ∀ n, AEStronglyMeasurable (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) μρ := by
    intro n
    exact (hpIntρ_eps n).aestronglyMeasurable
  have hRhs_dom :
      ∀ n, ∀ᵐ x ∂μρ,
        |(moserEpsSeq n + |max (u x) 0|) ^ p| ≤
          (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
    intro n
    filter_upwards with x
    have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
    have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
      exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
    calc
      |(moserEpsSeq n + |max (u x) 0|) ^ p|
          = (moserEpsSeq n + |max (u x) 0|) ^ p := by
              rw [abs_of_nonneg (Real.rpow_nonneg hsum_nonneg _)]
      _ ≤ (1 + |max (u x) 0|) ^ p := by
          exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n]) (by linarith)
      _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
          exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
  have hRhs_tendsto :
      Tendsto
        (fun n => ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume)
        atTop
        (nhds (∫ x in Ωρ, |max (u x) 0| ^ p ∂volume)) := by
    have hpt :
        ∀ᵐ x ∂μρ,
          Tendsto (fun n => (moserEpsSeq n + |max (u x) 0|) ^ p) atTop
            (nhds (|max (u x) 0| ^ p)) := by
      filter_upwards with x
      have hp_nonneg : 0 ≤ p := by linarith
      simpa using
        (tendsto_moserEpsSeq.add tendsto_const_nhds).rpow_const (Or.inr hp_nonneg)
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p))
      hRhs_meas hRhsDom_int hRhs_dom hpt
  have hleft_eq :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) := by
    change
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖hwv.weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖hwv.weakGrad x‖ ^ 2)
        hwv.weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hright_eq :
      ∀ n,
        ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
          ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume) := by
    intro n
    change
      ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖(wfn n).weakGrad x‖ ^ 2)
        (wfn n).weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hmain_enn :
      ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) ≤
        ENNReal.ofReal (CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume) := by
    rw [← hleft_eq]
    refine le_trans hFatou ?_
    rw [Filter.liminf_congr (Eventually.of_forall hright_eq)]
    have hliminf_le :
        atTop.liminf (fun n => ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume)) ≤
          atTop.liminf
            (fun n =>
              ENNReal.ofReal
                (CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume)) := by
      refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_) ?_ ?_
      · exact ENNReal.ofReal_le_ofReal (hGn_energy_exact n)
      · exact isBounded_ge_of_bot
      · exact isCobounded_ge_of_top
    exact hliminf_le.trans_eq
      (((ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.const_mul CE hRhs_tendsto)).liminf_eq)
  have hpIntΩ :
      IntegrableOn (fun x => |max (u x) 0| ^ p) Ω volume := by
    change IntegrableOn (fun x => |max (u x) 0| ^ p)
      (Metric.ball (0 : E) s) volume
    exact hpInt
  have hρ_integral_le :
      ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume ≤
        ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    have hnonneg :
        0 ≤ᵐ[μ] fun x => |max (u x) 0| ^ p := by
      exact ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _
    exact integral_mono_set_of_ae_nonneg
      (μ := volume) hΩρ_sub_Ω hnonneg hpIntΩ
  have hmain_real :
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := by
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have hnonneg :
          0 ≤ ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := by
        exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
      exact mul_nonneg hCE_nonneg hnonneg)).mp hmain_enn
  refine ⟨hwv, ?_⟩
  change
    ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
      2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
        ∫ x in Ω, |max (u x) 0| ^ p ∂volume
  exact
    calc
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume
          ≤ CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := hmain_real
      _ ≤ CE * ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
          exact mul_le_mul_of_nonneg_left hρ_integral_le hCE_nonneg
      _ = 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := rfl


end DeGiorgi
