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

end DifferentialGeometry.Analysis.ODE
