import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation
import DifferentialGeometry.Analysis.Asymptotics.PowerDecay
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Mathlib.Analysis.Calculus.ContDiff.WithLp

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Analysis
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_gradient_excess_power_bound_of_harmonic_error_power_bound
    {z : V → F} {R σ A q : ℝ} (hσ : 0 < σ) (hσR : 2 * σ ≤ R)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq4 : q < 4)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (happrox : ∀ c ∈ ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c r)),
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c r) φ →
          (∫ x in ball c r, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i, ∫ x in ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤ A * r ^ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c ∈ ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      (∑ i, ∫ x in ball c r,
        ‖(hz i).weakGrad x - ⨍ y in ball c r, (hz i).weakGrad y‖ ^ 2) ≤ K * r ^ q := by
  let M := ∑ i, ∫ x in ball (0 : V) R, ‖(hz i).weakGrad x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  obtain ⟨K, hK, hpower⟩ := exists_uniform_radius_power_bound_of_decay
    (M := M) (p := 4) (q := q) hσ (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (0 : ℝ) ≤ 16384) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16386) hA) hM hq hq4
  refine ⟨K, hK, ?_⟩
  intro c hc r hr hrσ
  have hball : ball c σ ⊆ ball (0 : V) R := by
    intro x hx
    have hxc := mem_ball.mp hx
    have hc0 := mem_ball_zero_iff.mp hc
    have hn : ‖x‖ ≤ dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    exact mem_ball_zero_iff.mpr (by linarith)
  let : IsFiniteMeasure (volume.restrict (ball c σ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let Ex (s : ℝ) := ∑ i, ∫ x in ball c s,
    ‖(hz i).weakGrad x - ⨍ y in ball c s, (hz i).weakGrad y‖ ^ 2
  have hLp (i : ι) : MemLp (hz i).weakGrad 2 (volume.restrict (ball c σ)) :=
    (hz i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hball)
  have hmono : MonotoneOn Ex (Ioc (0 : ℝ) σ) := by
    intro a ha b hb hab
    exact Finset.sum_le_sum fun i _ =>
      monotoneOn_integral_norm_sub_average_sq_ball (hLp i) ha hb hab
  have hEx : 0 ≤ Ex σ := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  have hExM : Ex σ ≤ M := by
    apply Finset.sum_le_sum
    intro i hi
    have h := integral_norm_sub_average_sq_le_integral_norm_sub_sq (hLp i) (0 : V)
    simp only [sub_zero] at h
    exact h.trans (setIntegral_mono_set (hz i).weakGrad_memLp.norm.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hball))
  apply hpower Ex hmono hEx hExM _ r ⟨hr, hrσ⟩
  intro a ha s hs hsa
  have haR : ball c a ⊆ ball (0 : V) R := (ball_subset_ball ha.2).trans hball
  let hza (i : ι) := (hz i).restrict isOpen_ball haR
  obtain ⟨h, hh, hEuler, herr⟩ := happrox c hc a ha.1 ha.2
  have hexcess := integral_weakGrad_sub_average_sq_le_of_harmonic_comparison
    ha.1 hs.le (by linarith : s ≤ a / 8) hza hh hEuler
  have hratio : 0 ≤ s / a ∧ s / a ≤ 1 :=
    ⟨div_nonneg hs.le ha.1.le, (div_le_one ha.1).mpr (by linarith)⟩
  have hcoef : 2 + 16384 * (s / a) ^ 4 ≤ 16386 := by
    have hp := pow_le_one₀ hratio.1 hratio.2 (n := 4)
    linarith
  have hD0 : 0 ≤ ∑ i, ∫ x in ball c a, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  have herror : (2 + 16384 * (s / a) ^ 4) *
      (∑ i, ∫ x in ball c a, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
      (16386 * A) * a ^ q := by
    exact ((mul_le_mul_of_nonneg_right hcoef hD0).trans
      (mul_le_mul_of_nonneg_left herr (by norm_num))).trans_eq (by ring)
  simpa only [Ex, hza, DeGiorgi.MemW1pWitness.restrict, Real.rpow_ofNat] using
    hexcess.trans (add_le_add le_rfl herror)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_contDiffOn_one_of_harmonic_error_power_bound
    {z : V → F} {R σ A q : ℝ} (hσ : 0 < σ) (hσR : 2 * σ ≤ R)
    (hA : 0 ≤ A) (hq2 : 2 < q) (hq4 : q < 4)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R))
    (happrox : ∀ c ∈ ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c r)),
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c r) φ →
          (∫ x in ball c r, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i, ∫ x in ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤ A * r ^ q) :
    ContDiffOn ℝ 1 z (ball (0 : V) (σ / 2)) ∧
      ∃ (G : ι → V → V) (C : ι → ℝ),
        (∀ i, 0 ≤ C i) ∧
        (∀ i, G i =ᵐ[volume.restrict (ball (0 : V) (σ / 2))] (hz i).weakGrad) ∧
        (∀ i, ∀ x ∈ ball (0 : V) (σ / 2),
          HasFDerivAt (fun y => z y i) (innerSL ℝ (G i x)) x) ∧
        ∀ i, ∀ x ∈ ball (0 : V) (σ / 2), ∀ y ∈ ball (0 : V) (σ / 2),
          ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ ((q - 2) / 2) := by
  obtain ⟨K, hK, hpower⟩ := exists_gradient_excess_power_bound_of_harmonic_error_power_bound
    hσ hσR hA (by linarith : 0 ≤ q) hq4 hz happrox
  have hσR' : σ ≤ R := by linarith
  have hball : ball (0 : V) σ ⊆ ball (0 : V) R := ball_subset_ball hσR'
  have hα : 0 < (q - 2) / 2 := by linarith
  have hα1 : (q - 2) / 2 ≤ 1 := by linarith
  obtain ⟨G, C, hC, hGae, hGc, hHolder⟩ := exists_holder_representative_of_gradient_excess_bound
    hσ hα hα1 hK
    (fun i => (hz i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hball))
    (by
      intro b
      have hb := hpower b.center (b.subset_ball (mem_ball_self b.radius_pos))
        b.radius b.radius_pos b.radius_le
      have he : 2 + 2 * ((q - 2) / 2) = q := by ring
      simpa only [he] using hb)
  have hhalf : ball (0 : V) (σ / 2) ⊆ ball (0 : V) σ := ball_subset_ball (by linarith)
  have hhalfR : ball (0 : V) (σ / 2) ⊆ ball (0 : V) R := hhalf.trans hball
  let hzh (i : ι) := (hz i).restrict isOpen_ball hhalfR
  have hG (i : ι) : G i =ᵐ[volume.restrict (ball (0 : V) (σ / 2))] (hzh i).weakGrad :=
    ae_restrict_of_ae_restrict_of_subset hhalf (hGae i)
  have hzi (i : ι) : ContinuousOn (fun x => z x i) (ball (0 : V) (σ / 2)) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn (hzc.mono hhalfR)
  have hdiff (i : ι) : ContDiffOn ℝ 1 (fun x => z x i) (ball (0 : V) (σ / 2)) :=
    (hzh i).contDiffOn_one_of_continuousOn_weakGrad isOpen_ball (hzi i) (hGc i) (hG i)
  refine ⟨PiLp.contDiff_toLp.comp_contDiffOn (contDiffOn_pi.mpr hdiff), G, C, hC, hG, ?_, hHolder⟩
  intro i x hx
  exact (hzh i).hasFDerivAt_of_continuousOn_weakGrad isOpen_ball (hzi i) (hGc i) (hG i) hx

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
