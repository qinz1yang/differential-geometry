import DifferentialGeometry.Analysis.ODE.QuadraticRadialCurve
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.ODE

noncomputable def saddleBandVectorField (z : ℝ × ℝ) : ℝ × ℝ :=
  (0, ((1 - z.1 ^ 2) * z.2)⁻¹)

noncomputable def saddleBandCurve (z : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (z.1, quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t)

@[simp]
theorem saddleBandCurve_zero (z : ℝ × ℝ) : saddleBandCurve z 0 = z := by
  simp [saddleBandCurve]

theorem saddleBandCurve_height {z : ℝ × ℝ} (hu : 1 - z.1 ^ 2 ≠ 0) (hv : z.2 ≠ 0)
    {t : ℝ} (ht : 0 ≤ 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) (c s : ℝ) :
    c + (1 - (saddleBandCurve z t).1 ^ 2) * ((saddleBandCurve z t).2 ^ 2 + 2 * s) / 2 =
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 + t := by
  have hn : (quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t) ^ 2 =
      z.2 ^ 2 + 2 * (1 - z.1 ^ 2)⁻¹ * t := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      norm_sq_quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ hv (by
        simpa only [Real.norm_eq_abs, sq_abs] using ht)
  change c + (1 - z.1 ^ 2) * ((quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t) ^ 2 + 2 * s) / 2 = _
  rw [hn]
  field_simp
  ring

theorem hasDerivAt_saddleBandCurve {z : ℝ × ℝ} (hv : z.2 ≠ 0) {t : ℝ}
    (ht : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) :
    HasDerivAt (saddleBandCurve z) (saddleBandVectorField (saddleBandCurve z t)) t := by
  have ht' : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / ‖z.2‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using ht
  have hne := quadraticRadialCurve_ne_zero (1 - z.1 ^ 2)⁻¹ hv ht'
  have hd := (hasDerivAt_const t z.1).prodMk
    (hasDerivAt_quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ hv ht')
  apply hd.congr_deriv
  dsimp only [saddleBandVectorField, saddleBandCurve]
  apply Prod.ext
  · rfl
  change ((1 - z.1 ^ 2)⁻¹ / ‖quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t‖ ^ 2) •
      quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t =
    ((1 - z.1 ^ 2) * quadraticRadialCurve (1 - z.1 ^ 2)⁻¹ z.2 t)⁻¹
  rw [smul_eq_mul, Real.norm_eq_abs, sq_abs, mul_inv_rev]
  field_simp

theorem contDiffOn_saddleBandVectorField : ContDiffOn ℝ ∞ saddleBandVectorField
    {z | (1 - z.1 ^ 2) * z.2 ≠ 0} := by
  exact contDiffOn_const.prodMk (((contDiffOn_const.sub (contDiffOn_fst.pow 2)).mul
    contDiffOn_snd).inv (fun _ hz => hz))

theorem contDiffOn_saddleBandCurve : ContDiffOn ℝ ∞
    (fun p : ℝ × (ℝ × ℝ) => saddleBandCurve p.2 p.1)
    {p | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * p.1 / p.2.2 ^ 2} := by
  intro p hp
  have hu : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (1 - q.2.1 ^ 2)⁻¹) p :=
    (contDiffAt_const.sub (contDiffAt_snd.fst.pow 2)).inv hp.1
  have hinner : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) =>
      1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * q.1 / q.2.2 ^ 2) p :=
    contDiffAt_const.add (((contDiffAt_const.mul hu).mul contDiffAt_fst).div
      (contDiffAt_snd.snd.pow 2) (pow_ne_zero 2 hp.2.1))
  have h := contDiffAt_snd.fst.prodMk ((hinner.sqrt hp.2.2.ne').mul contDiffAt_snd.snd)
  simpa only [saddleBandCurve, quadraticRadialCurve, smul_eq_mul, Real.norm_eq_abs, sq_abs] using
    h.contDiffWithinAt

open Filter
open scoped Topology

theorem saddleBandCurve_reverse_radicand {z : ℝ × ℝ} {t : ℝ}
    (ht : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) :
    1 + 2 * (1 - (saddleBandCurve z t).1 ^ 2)⁻¹ * (-t) /
        (saddleBandCurve z t).2 ^ 2 =
      (1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2)⁻¹ := by
  simpa only [saddleBandCurve, Real.norm_eq_abs, sq_abs] using
    quadraticRadialCurve_reverse_radicand (b := (1 - z.1 ^ 2)⁻¹) (x := z.2) (t := t)
      (by simpa only [Real.norm_eq_abs, sq_abs] using ht)

theorem saddleBandCurve_reverse {z : ℝ × ℝ} {t : ℝ}
    (ht : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) :
    saddleBandCurve (saddleBandCurve z t) (-t) = z := by
  apply Prod.ext
  · rfl
  · exact quadraticRadialCurve_reverse (b := (1 - z.1 ^ 2)⁻¹) (x := z.2) (t := t)
      (by simpa only [Real.norm_eq_abs, sq_abs] using ht)

theorem isOpen_saddleBandCurve_time_change_domain {A : Type*} [TopologicalSpace A]
    {ψ : A × ℝ → ℝ}
    (hψ : Continuous ψ) :
    IsOpen {p : A × (ℝ × ℝ) | (p.1, p.2.1) ∉ tsupport ψ ∨
      (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2)} := by
  apply IsOpen.union
  · exact (isClosed_tsupport ψ).isOpen_compl.preimage
      (continuous_fst.prodMk continuous_snd.fst)
  · change IsOpen {p : A × (ℝ × ℝ) | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2}
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hu : ∀ᶠ q : A × (ℝ × ℝ) in 𝓝 p, 1 - q.2.1 ^ 2 ≠ 0 :=
      (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hp.1
    have hv : ∀ᶠ q : A × (ℝ × ℝ) in 𝓝 p, q.2.2 ≠ 0 :=
      (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hp.2.1
    have hc : ContinuousAt (fun q : A × (ℝ × ℝ) =>
        1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * ψ (q.1, q.2.1) / q.2.2 ^ 2) p :=
      continuousAt_const.add (((continuousAt_const.mul
        ((continuousAt_const.sub (continuousAt_snd.fst.pow 2)).inv₀ hp.1)).mul
        (hψ.continuousAt.comp (continuousAt_fst.prodMk continuousAt_snd.fst))).div
        (continuousAt_snd.snd.pow 2) (pow_ne_zero 2 hp.2.1))
    have hr := hc.eventually (isOpen_Ioi.mem_nhds hp.2.2)
    filter_upwards [hu, hv, hr] with q hqu hqv hqr
    exact ⟨hqu, hqv, hqr⟩

theorem contDiffAt_saddleBandCurve_time_change
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {ψ : A × ℝ → ℝ} {p : A × (ℝ × ℝ)}
    (hψ : ContDiffAt ℝ ∞ ψ (p.1, p.2.1))
    (hp : (p.1, p.2.1) ∉ tsupport ψ ∨ (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2)) :
    ContDiffAt ℝ ∞ (fun q : A × (ℝ × ℝ) => saddleBandCurve q.2 (ψ (q.1, q.2.1))) p := by
  rcases hp with hp | hp
  · have hevent : ∀ᶠ q : A × (ℝ × ℝ) in 𝓝 p, ψ (q.1, q.2.1) = 0 := by
      filter_upwards [((isClosed_tsupport ψ).isOpen_compl.preimage
        (continuous_fst.prodMk continuous_snd.fst)).mem_nhds hp] with q hq
      exact image_eq_zero_of_notMem_tsupport hq
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [hevent] with q hq
    rw [hq, saddleBandCurve_zero]
  · have hu : ContDiffAt ℝ ∞ (fun q : A × (ℝ × ℝ) => (1 - q.2.1 ^ 2)⁻¹) p :=
      (contDiffAt_const.sub (contDiffAt_snd.fst.pow 2)).inv hp.1
    have htime := hψ.comp p (contDiffAt_fst.prodMk contDiffAt_snd.fst)
    have hinner : ContDiffAt ℝ ∞ (fun q : A × (ℝ × ℝ) =>
        1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * ψ (q.1, q.2.1) / q.2.2 ^ 2) p :=
      contDiffAt_const.add (((contDiffAt_const.mul hu).mul htime).div
        (contDiffAt_snd.snd.pow 2) (pow_ne_zero 2 hp.2.1))
    have h := contDiffAt_snd.fst.prodMk ((hinner.sqrt hp.2.2.ne').mul contDiffAt_snd.snd)
    simpa only [saddleBandCurve, quadraticRadialCurve, smul_eq_mul, Real.norm_eq_abs, sq_abs]
      using h

theorem isOpen_smul_saddleBandVectorField_domain {A : Type*} [TopologicalSpace A]
    (ψ : A × ℝ → ℝ) :
    IsOpen {p : A × (ℝ × ℝ) |
      (p.1, p.2.1) ∉ tsupport ψ ∨ (1 - p.2.1 ^ 2) * p.2.2 ≠ 0} := by
  exact ((isClosed_tsupport ψ).isOpen_compl.preimage
    (continuous_fst.prodMk continuous_snd.fst)).union
      (isOpen_ne_fun (by fun_prop) continuous_const)

theorem contDiffAt_smul_saddleBandVectorField
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {n : WithTop ℕ∞} {ψ : A × ℝ → ℝ} {p : A × (ℝ × ℝ)}
    (hψ : ContDiffAt ℝ n ψ (p.1, p.2.1))
    (hp : (p.1, p.2.1) ∉ tsupport ψ ∨ (1 - p.2.1 ^ 2) * p.2.2 ≠ 0) :
    ContDiffAt ℝ n (fun q : A × (ℝ × ℝ) =>
      ψ (q.1, q.2.1) • saddleBandVectorField q.2) p := by
  rcases hp with hp | hp
  · have hevent : ∀ᶠ q : A × (ℝ × ℝ) in 𝓝 p, ψ (q.1, q.2.1) = 0 := by
      filter_upwards [((isClosed_tsupport ψ).isOpen_compl.preimage
        (continuous_fst.prodMk continuous_snd.fst)).mem_nhds hp] with q hq
      exact image_eq_zero_of_notMem_tsupport hq
    apply (contDiffAt_const :
      ContDiffAt ℝ n (fun _ : A × (ℝ × ℝ) => (0 : ℝ × ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hevent] with q hq
    rw [hq, zero_smul]
  · have hfield : ContDiffAt ℝ n (fun q : A × (ℝ × ℝ) => saddleBandVectorField q.2) p :=
      contDiffAt_const.prodMk (((contDiffAt_const.sub (contDiffAt_snd.fst.pow 2)).mul
        contDiffAt_snd.snd).inv hp)
    exact (hψ.comp p (contDiffAt_fst.prodMk contDiffAt_snd.fst)).smul hfield

theorem contDiffOn_smul_saddleBandVectorField
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {n : WithTop ℕ∞} {ψ : A × ℝ → ℝ} (hψ : ContDiff ℝ n ψ) :
    ContDiffOn ℝ n (fun q : A × (ℝ × ℝ) =>
      ψ (q.1, q.2.1) • saddleBandVectorField q.2)
      {p | (p.1, p.2.1) ∉ tsupport ψ ∨ (1 - p.2.1 ^ 2) * p.2.2 ≠ 0} := by
  intro p hp
  exact (contDiffAt_smul_saddleBandVectorField hψ.contDiffAt hp).contDiffWithinAt

theorem hasDerivAt_saddleBandCurve_mul_const {z : ℝ × ℝ} {c r : ℝ}
    (hr : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (r * c) / z.2 ^ 2) :
    HasDerivAt (fun q => saddleBandCurve z (q * c))
      (c • saddleBandVectorField (saddleBandCurve z (r * c))) r := by
  by_cases hv : z.2 = 0
  · have hcurve (q : ℝ) : saddleBandCurve z (q * c) = z := by
      apply Prod.ext
      · rfl
      · simp only [saddleBandCurve, quadraticRadialCurve, hv, smul_zero]
    have hfield : saddleBandVectorField z = 0 := by
      simp only [saddleBandVectorField, hv, mul_zero, inv_zero, Prod.mk_zero_zero]
    simpa only [hcurve, hfield, smul_zero] using (hasDerivAt_const r z)
  · simpa only [Function.comp_def, id_eq, one_mul] using
      (hasDerivAt_saddleBandCurve hv hr).scomp r ((hasDerivAt_id r).mul_const c)

end DifferentialGeometry.Analysis.ODE
