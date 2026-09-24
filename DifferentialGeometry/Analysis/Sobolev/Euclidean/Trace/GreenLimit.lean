import DifferentialGeometry.Analysis.Integration.L2Convergence
import DifferentialGeometry.Analysis.Integration.Integral.LipschitzGreen
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

private theorem inner_toLp_eq_integral_mul
    {P : Type*} [MeasurableSpace P] {μ : Measure P} {f g : P → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, real_inner_comm]
  rfl


theorem integral_mul_weak_deriv_snd_add_eq_boundary_of_tendsto
    {K : ℕ → ℝ≥0} {f : ℕ → ℝ × ℝ → ℝ} (hf : ∀ n, LipschitzWith (K n) (f n))
    {a b : ℝ → ℝ} {s : Set ℝ} (ha : Measurable a) (hb : Measurable b)
    (hs : MeasurableSet s) (hab : ∀ x ∈ s, a x ≤ b x)
    {v G : ℝ × ℝ → ℝ}
    (hfn : ∀ n, MemLp (f n) 2 (volume.restrict (regionBetween a b s)))
    (hGn : ∀ n, MemLp (fun p => fderiv ℝ (f n) p (0, 1))
      2 (volume.restrict (regionBetween a b s)))
    (hv : MemLp v 2 (volume.restrict (regionBetween a b s)))
    (hG : MemLp G 2 (volume.restrict (regionBetween a b s)))
    (hlim : Tendsto (fun n => eLpNorm (fun p => f n p - v p) 2
      (volume.restrict (regionBetween a b s))) atTop (𝓝 0))
    (hweak : ∀ z : Lp ℝ 2 (volume.restrict (regionBetween a b s)),
      Tendsto (fun n => inner ℝ ((hGn n).toLp (fun p => fderiv ℝ (f n) p (0, 1))) z)
        atTop (𝓝 (inner ℝ (hG.toLp G) z)))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g)
    (hgm : MemLp g 2 (volume.restrict (regionBetween a b s)))
    (hdgm : MemLp (fun p => fderiv ℝ g p (0, 1))
      2 (volume.restrict (regionBetween a b s)))
    {B : ℝ}
    (hboundary : Tendsto (fun n => ∫ x in s,
      f n (x, b x) * g (x, b x) - f n (x, a x) * g (x, a x)) atTop (𝓝 B)) :
    (∫ p in regionBetween a b s, G p * g p + v p * fderiv ℝ g p (0, 1)) = B := by
  have hgrad := hweak (hgm.toLp g)
  simp only [inner_toLp_eq_integral_mul] at hgrad
  have hfun := DifferentialGeometry.Analysis.Integration.tendsto_integral_mul_of_eLpNorm_two hfn hv hdgm hlim
  have hsum := hgrad.add hfun
  have hn (n : ℕ) :
      (∫ p in regionBetween a b s, fderiv ℝ (f n) p (0, 1) * g p) +
        (∫ p in regionBetween a b s, f n p * fderiv ℝ g p (0, 1)) =
          ∫ x in s, f n (x, b x) * g (x, b x) - f n (x, a x) * g (x, a x) := by
    have hi₁ : IntegrableOn (fun p => fderiv ℝ (f n) p (0, 1) * g p) (regionBetween a b s) :=
      (hGn n).integrable_mul hgm
    have hi₂ : IntegrableOn (fun p => f n p * fderiv ℝ g p (0, 1)) (regionBetween a b s) :=
      (hfn n).integrable_mul hdgm
    rw [← integral_add hi₁ hi₂]
    exact LipschitzWith.integral_mul_fderiv_snd_add_regionBetween (hf n) hg ha hb hs hab
      (((hGn n).integrable_mul hgm).add ((hfn n).integrable_mul hdgm))
  simp only [hn] at hsum
  have hi₁ : IntegrableOn (fun p => G p * g p) (regionBetween a b s) :=
    hG.integrable_mul hgm
  have hi₂ : IntegrableOn (fun p => v p * fderiv ℝ g p (0, 1)) (regionBetween a b s) :=
    hv.integrable_mul hdgm
  rw [integral_add hi₁ hi₂]
  exact tendsto_nhds_unique hsum hboundary

theorem integral_mul_weak_deriv_snd_add_eq_boundary_of_tendsto_L2_boundary
    {K : ℕ → ℝ≥0} {f : ℕ → ℝ × ℝ → ℝ} (hf : ∀ n, LipschitzWith (K n) (f n))
    {a b : ℝ → ℝ} {s : Set ℝ} (ha : Measurable a) (hb : Measurable b)
    (hs : MeasurableSet s) (hab : ∀ x ∈ s, a x ≤ b x)
    {v G : ℝ × ℝ → ℝ}
    (hfn : ∀ n, MemLp (f n) 2 (volume.restrict (regionBetween a b s)))
    (hGn : ∀ n, MemLp (fun p => fderiv ℝ (f n) p (0, 1))
      2 (volume.restrict (regionBetween a b s)))
    (hv : MemLp v 2 (volume.restrict (regionBetween a b s)))
    (hG : MemLp G 2 (volume.restrict (regionBetween a b s)))
    (hlim : Tendsto (fun n => eLpNorm (fun p => f n p - v p) 2
      (volume.restrict (regionBetween a b s))) atTop (𝓝 0))
    (hweak : ∀ z : Lp ℝ 2 (volume.restrict (regionBetween a b s)),
      Tendsto (fun n => inner ℝ ((hGn n).toLp (fun p => fderiv ℝ (f n) p (0, 1))) z)
        atTop (𝓝 (inner ℝ (hG.toLp G) z)))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g)
    (hgm : MemLp g 2 (volume.restrict (regionBetween a b s)))
    (hdgm : MemLp (fun p => fderiv ℝ g p (0, 1))
      2 (volume.restrict (regionBetween a b s)))
    {ηa ηb : ℝ → ℝ}
    (hfa : ∀ n, MemLp (fun x => f n (x, a x)) 2 (volume.restrict s))
    (hfb : ∀ n, MemLp (fun x => f n (x, b x)) 2 (volume.restrict s))
    (hηa : MemLp ηa 2 (volume.restrict s)) (hηb : MemLp ηb 2 (volume.restrict s))
    (hga : MemLp (fun x => g (x, a x)) 2 (volume.restrict s))
    (hgb : MemLp (fun x => g (x, b x)) 2 (volume.restrict s))
    (haLim : Tendsto (fun n => eLpNorm (fun x => f n (x, a x) - ηa x) 2
      (volume.restrict s)) atTop (𝓝 0))
    (hbLim : Tendsto (fun n => eLpNorm (fun x => f n (x, b x) - ηb x) 2
      (volume.restrict s)) atTop (𝓝 0)) :
    (∫ p in regionBetween a b s, G p * g p + v p * fderiv ℝ g p (0, 1)) =
      ∫ x in s, ηb x * g (x, b x) - ηa x * g (x, a x) := by
  apply integral_mul_weak_deriv_snd_add_eq_boundary_of_tendsto hf ha hb hs hab hfn hGn hv hG
    hlim hweak hg hgm hdgm
  have htop := DifferentialGeometry.Analysis.Integration.tendsto_integral_mul_of_eLpNorm_two hfb hηb hgb hbLim
  have hbot := DifferentialGeometry.Analysis.Integration.tendsto_integral_mul_of_eLpNorm_two hfa hηa hga haLim
  have hsub := htop.sub hbot
  have heq (n : ℕ) : (∫ x in s, f n (x, b x) * g (x, b x)) -
      (∫ x in s, f n (x, a x) * g (x, a x)) =
        ∫ x in s, f n (x, b x) * g (x, b x) - f n (x, a x) * g (x, a x) := by
    exact (integral_sub ((hfb n).integrable_mul hgb) ((hfa n).integrable_mul hga)).symm
  have heqLim : (∫ x in s, ηb x * g (x, b x)) - (∫ x in s, ηa x * g (x, a x)) =
      ∫ x in s, ηb x * g (x, b x) - ηa x * g (x, a x) := by
    exact (integral_sub (hηb.integrable_mul hgb) (hηa.integrable_mul hga)).symm
  simpa only [heq, heqLim] using hsub

end DifferentialGeometry.Analysis
