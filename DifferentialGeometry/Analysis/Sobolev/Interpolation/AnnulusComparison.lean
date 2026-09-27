import DifferentialGeometry.Analysis.Integration.PolarAnnulus
import DifferentialGeometry.Analysis.Sobolev.Interval.UniformConvergence
import DifferentialGeometry.Analysis.Integration.Integral.Selection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.Filter.IsBounded
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy
import DifferentialGeometry.Analysis.Sobolev.Interpolation.Cylinder
import DifferentialGeometry.Topology.MetricSpace.CompactInterpolation
import DifferentialGeometry.Analysis.Integration.Integral.QuadraticDerivative
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

private theorem lipschitzWith_circle_parameter (ρ : ℝ) :
    LipschitzWith ⟨2 * Real.pi * |ρ|, by positivity⟩
      (fun t : ℝ => circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => circleMap 0 ρ (2 * Real.pi * t - Real.pi))
      ((2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
    have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
    exact (hasDerivAt_circleMap 0 ρ (2 * Real.pi * t - Real.pi)).scomp t hθ
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  change ‖deriv (fun t : ℝ => circleMap 0 ρ (2 * Real.pi * t - Real.pi)) t‖ ≤ _
  rw [(hd t).deriv]
  simp [abs_of_pos Real.pi_pos]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem integrableOn_norm_deriv_sq_of_lipschitz
    {f : ℝ → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    IntegrableOn (fun t => ‖deriv f t‖ ^ 2) (Icc (0 : ℝ) 1) := by
  have hm : MemLp (deriv f) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) C
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf)
  exact hm.norm.integrable_sq

private theorem integrableOn_norm_fderiv_sq_annulus_of_lipschitz
    {f : ℂ → F} {C : ℝ≥0} (hf : LipschitzWith C f) (r R : ℝ) :
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) {z : ℂ | ‖z‖ ∈ Icc r R} := by
  have hs : {z : ℂ | ‖z‖ ∈ Icc r R} ⊆ Metric.closedBall 0 R := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
  apply IntegrableOn.of_bound
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable ((C : ℝ) ^ 2)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2

theorem exists_circle_radii_tendstoUniformlyOn_sub_zero
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hgap : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖u n z - v n z‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖fderiv ℝ (u n) z‖ ^ 2 + ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B) :
    ∃ (ρ : ℕ → ℝ) (D : ℝ), (∀ n, ρ n ∈ Icc r R) ∧
      Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
        ‖u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)) -
          v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0) ∧
      (∀ n, (∫ t in Icc (0 : ℝ) 1,
        ‖deriv (fun t => u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
          ‖deriv (fun t => v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D) ∧
      TendstoUniformlyOn (fun n t =>
        u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)) -
          v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)))
        (fun _ => 0) atTop (Icc (0 : ℝ) 1) := by
  let p (ρ t : ℝ) := circleMap 0 ρ (2 * Real.pi * t - Real.pi)
  let d (n : ℕ) (ρ : ℝ) := ∫ t in Icc (0 : ℝ) 1, ‖u n (p ρ t) - v n (p ρ t)‖ ^ 2
  let e (n : ℕ) (ρ : ℝ) := ∫ t in Icc (0 : ℝ) 1,
    ‖deriv (fun t => u n (p ρ t)) t‖ ^ 2 + ‖deriv (fun t => v n (p ρ t)) t‖ ^ 2
  have hR : 0 < R := hr.trans hrR
  let μ : Measure ℝ := volume.restrict (Icc r R)
  have hμ : μ ≠ 0 := by
    intro hz
    have h := congrArg (fun m : Measure ℝ => m univ) hz
    have hpos : 0 < volume (Icc r R) := by simp [Real.volume_Icc, hrR]
    apply hpos.ne'
    simpa [μ] using h
  let : NeZero μ := ⟨hμ⟩
  have hui (n : ℕ) (ρ : ℝ) :=
    integrableOn_norm_deriv_sq_of_lipschitz ((hu n).comp (lipschitzWith_circle_parameter ρ))
  have hvi (n : ℕ) (ρ : ℝ) :=
    integrableOn_norm_deriv_sq_of_lipschitz ((hv n).comp (lipschitzWith_circle_parameter ρ))
  have heq (n : ℕ) (ρ : ℝ) : e n ρ =
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun t => u n (p ρ t)) t‖ ^ 2) +
      ∫ t in Icc (0 : ℝ) 1, ‖deriv (fun t => v n (p ρ t)) t‖ ^ 2 :=
    integral_add (hui n ρ) (hvi n ρ)
  have he (n : ℕ) : Integrable (e n) μ := by
    change Integrable (fun ρ => e n ρ) μ
    simp_rw [heq]
    exact (integrableOn_integral_norm_sq_deriv_circleMap (hu n) hr hrR.le).add
      (integrableOn_integral_norm_sq_deriv_circleMap (hv n) hr hrR.le)
  have hd (n : ℕ) : Integrable (d n) μ :=
    integrableOn_integral_circleMap (fun z => ‖u n z - v n z‖ ^ 2)
      (((hu n).continuous.sub (hv n).continuous).norm.pow 2) r R
  have hE (n : ℕ) : (∫ ρ, e n ρ ∂μ) ≤ (2 * Real.pi * R) * B := by
    have h₁ := integral_norm_sq_deriv_circleMap_radial_le (hu n) hr hrR.le
    have h₂ := integral_norm_sq_deriv_circleMap_radial_le (hv n) hr hrR.le
    have hei := integrableOn_integral_norm_sq_deriv_circleMap (hu n) hr hrR.le
    have hej := integrableOn_integral_norm_sq_deriv_circleMap (hv n) hr hrR.le
    simp_rw [heq]
    rw [integral_add hei hej]
    apply (add_le_add h₁ h₂).trans
    rw [← mul_add, ← integral_add
      (integrableOn_norm_fderiv_sq_annulus_of_lipschitz (hu n) r R)
      (integrableOn_norm_fderiv_sq_annulus_of_lipschitz (hv n) r R)]
    exact mul_le_mul_of_nonneg_left (henergy n) (by positivity)
  have hD : Tendsto (fun n => ∫ ρ, d n ρ ∂μ) atTop (𝓝 0) :=
    tendsto_integral_circleMap_norm_sq_radial_zero
      (fun n => (hu n).continuous.sub (hv n).continuous) hr hgap
  obtain ⟨ρ, hρ, hlim, hbnd⟩ :=
    exists_tendsto_zero_and_eventually_le_of_finite_integral he hd
      (fun n => Eventually.of_forall fun ρ => integral_nonneg fun t => by positivity)
      (fun n => Eventually.of_forall fun ρ => integral_nonneg fun t => sq_nonneg _)
      (fun n => ae_restrict_mem measurableSet_Icc) hE hD
  obtain ⟨D, hDall⟩ := (Filter.isBoundedUnder_of_eventually_le hbnd).bddAbove_range
  have hEn (n : ℕ) : e n (ρ n) ≤ D := hDall (mem_range_self n)
  refine ⟨ρ, D, hρ, hlim, hEn, ?_⟩
  exact Sobolev.tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound
    (fun n t => u n (p (ρ n) t)) (fun n t => v n (p (ρ n) t))
    (fun n => Ku n * ⟨2 * Real.pi * |ρ n|, by positivity⟩)
    (fun n => Kv n * ⟨2 * Real.pi * |ρ n|, by positivity⟩)
    (fun n => (hu n).comp (lipschitzWith_circle_parameter (ρ n)))
    (fun n => (hv n).comp (lipschitzWith_circle_parameter (ρ n))) hEn hlim

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis.Sobolev
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_width_tendsto_annulus_energy_attachThinAnnulus_zero
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    (ρ : ℕ → ℝ) {r R : ℝ} (hr : 0 < r) (hρ : ∀ n, ρ n ∈ Icc r R)
    (hgap : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0))
    {D : ℝ} (hder : ∀ n, (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTu : ∀ n z, ‖z‖ = ρ n → T (u n z) = u n z)
    (hTv : ∀ n z, ‖z‖ = ρ n → T (v n z) = v n z) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, h n < ρ n / 2 ∧
        ∃ K : ℝ≥0, LipschitzWith K (attachThinAnnulus (u n) (v n) T (ρ n) (h n))) ∧
      (∀ n z, ρ n ≤ ‖z‖ → attachThinAnnulus (u n) (v n) T (ρ n) (h n) z = u n z) ∧
      Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (ρ n - h n) (ρ n)},
        (‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1‖ ^ 2 +
          ‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I‖ ^ 2) / 2)
        atTop (𝓝 0) := by
  let a (n : ℕ) (t : ℝ) := v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))
  let b (n : ℕ) (t : ℝ) := u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))
  let Ka (n : ℕ) := Kv n * ⟨2 * Real.pi * |ρ n|, by positivity⟩
  let Kb (n : ℕ) := Ku n * ⟨2 * Real.pi * |ρ n|, by positivity⟩
  have ha (n : ℕ) : LipschitzWith (Ka n) (a n) :=
    (hv n).comp (lipschitzWith_circle_parameter (ρ n))
  have hb (n : ℕ) : LipschitzWith (Kb n) (b n) :=
    (hu n).comp (lipschitzWith_circle_parameter (ρ n))
  let h (n : ℕ) := Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2) +
    1 / ((n : ℝ) + 1)
  obtain ⟨hh, hh0, _, he0⟩ :=
    tendsto_energy_affineCylinderInterpolation_of_tendsto_integral_norm_sub_sq
      a b Ka Kb ha hb hgap hder
  have hTl : LipschitzWith (Real.toNNReal L) T := by
    apply lipschitzWith_of_nnnorm_fderiv_le hT
    intro x
    change ‖fderiv ℝ T x‖ ≤ _
    exact (hL x).trans (Real.le_coe_toNNReal L)
  have hsmall : ∀ᶠ n in atTop, h n < r / 2 := hh0.eventually (gt_mem_nhds (half_pos hr))
  have hgood : ∀ᶠ n in atTop, h n < ρ n / 2 ∧
      ∃ K : ℝ≥0, LipschitzWith K (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) := by
    filter_upwards [hsmall] with n hn
    have hhalf : h n < ρ n / 2 := hn.trans_le (div_le_div_of_nonneg_right (hρ n).1 (by norm_num))
    have hnρ : h n < ρ n := by linarith [hh n]
    exact ⟨hhalf, attachThinAnnulus_lipschitz (hh n) hnρ (hu n) (hv n) hTl (hTu n) (hTv n)⟩
  refine ⟨h, hh, hh0, hgood, fun n z hz => attachThinAnnulus_outer _ _ _ (hh n) hz, ?_⟩
  let E (n : ℕ) : ℝ := ∫ p in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
    (‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) p (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) p (0, 1)‖ ^ 2) / 2
  let Er (n : ℕ) : ℝ := ∫ p in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
    (‖fderiv ℝ (T ∘ affineCylinderInterpolation (h n) (a n) (b n)) p (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (T ∘ affineCylinderInterpolation (h n) (a n) (b n)) p (0, 1)‖ ^ 2) / 2
  let C : ℝ := (2 * Real.pi) * max R (((2 * Real.pi) ^ 2 * (r / 2))⁻¹)
  have hR : 0 < R := hr.trans_le ((hρ 0).1.trans (hρ 0).2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun n => C * (L ^ 2 * E n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (he0.const_mul (L ^ 2)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun z => by positivity)
    ?_ hlim
  filter_upwards [hsmall] with n hn
  have hnρ : h n < ρ n := by linarith [(hρ n).1, hh n]
  have hAnn := integral_annulus_energy_attachThinAnnulus_le_of_lipschitz
    (hh n) hnρ (hu n) (hv n) hTl (hTu n) (hTv n)
  have hEr : Er n ≤ L ^ 2 * E n :=
    integral_energy_comp_affineCylinderInterpolation_le (h n) (ha n) (hb n) T hT hL
  have hcoef : (2 * Real.pi) * max (ρ n)
      (((2 * Real.pi) ^ 2 * (ρ n - h n))⁻¹) ≤ C := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max (hρ n).2
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
      (by linarith [(hρ n).1] : r / 2 ≤ ρ n - h n) (sq_nonneg _))
  exact hAnn.trans ((mul_le_mul_of_nonneg_right hcoef
    (integral_nonneg fun p => by positivity)).trans (mul_le_mul_of_nonneg_left hEr hC))

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

private theorem exists_circle_parameter_of_norm_eq
    {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : ‖z‖ = ρ) :
    ∃ t ∈ Icc (0 : ℝ) 1, circleMap 0 ρ (2 * Real.pi * t - Real.pi) = z := by
  have hmem : z ∈ range (circleMap 0 ρ) := by
    rw [range_circleMap, Metric.mem_sphere, dist_zero_right, abs_of_nonneg hρ]
    exact hz
  rw [← (periodic_circleMap 0 ρ).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
  obtain ⟨θ, hθ, hθz⟩ := hmem
  refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hθ.1]) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
  · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
      field_simp
      ring
    rwa [heq]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_target_valued_attachThinAnnulus_tendsto_annulus_energy_zero
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {r R Q : ℝ} (hr : 0 < r) (hrR : r < R) (hRQ : R ≤ Q)
    (hgap : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖u n z - v n z‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖fderiv ℝ (u n) z‖ ^ 2 + ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B)
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) Q) K)
    (hvK : ∀ n, MapsTo (v n) (Metric.closedBall (0 : ℂ) R) K)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTK : MapsTo T U K) (hfix : ∀ y ∈ K, T y = y) :
    ∃ (ρ h : ℕ → ℝ), (∀ n, ρ n ∈ Icc r R) ∧ (∀ n, 0 < h n) ∧
      Tendsto h atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, h n < ρ n / 2 ∧
        (∃ C : ℝ≥0, LipschitzWith C (attachThinAnnulus (u n) (v n) T (ρ n) (h n))) ∧
        MapsTo (attachThinAnnulus (u n) (v n) T (ρ n) (h n))
          (Metric.closedBall (0 : ℂ) Q) K) ∧
      (∀ n z, ρ n ≤ ‖z‖ → attachThinAnnulus (u n) (v n) T (ρ n) (h n) z = u n z) ∧
      Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (ρ n - h n) (ρ n)},
        (‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1‖ ^ 2 +
          ‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I‖ ^ 2) / 2)
        atTop (𝓝 0) := by
  obtain ⟨ρ, D, hρ, hgapρ, hderρ, hclose⟩ :=
    exists_circle_radii_tendstoUniformlyOn_sub_zero u v Ku Kv hu hv hr hrR hgap henergy
  have hρ0 (n : ℕ) : 0 < ρ n := hr.trans_le (hρ n).1
  have huvfix (n : ℕ) (z : ℂ) (hz : ‖z‖ = ρ n) : T (u n z) = u n z := by
    apply hfix _ (huK n ?_)
    simpa only [Metric.mem_closedBall, dist_zero_right, hz] using (hρ n).2.trans hRQ
  have hvvfix (n : ℕ) (z : ℂ) (hz : ‖z‖ = ρ n) : T (v n z) = v n z := by
    apply hfix _ (hvK n ?_)
    simpa only [Metric.mem_closedBall, dist_zero_right, hz] using (hρ n).2
  have hgapρ' : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_sub_rev] using hgapρ
  have hderρ' (n : ℕ) : (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D := by
    simpa only [add_comm] using hderρ n
  obtain ⟨h, hh, hh0, hgood, houter, he0⟩ :=
    exists_width_tendsto_annulus_energy_attachThinAnnulus_zero u v Ku Kv hu hv ρ hr hρ
      hgapρ' hderρ' T hT hL huvfix hvvfix
  have hclose' : TendstoUniformlyOn (fun n t =>
      v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)))
      (fun _ => 0) atTop (Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hclose ⊢
    intro ε hε
    filter_upwards [hclose ε hε] with n hn t ht
    simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev] using hn t ht
  have hseg : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      segment ℝ (v n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi)))
        (u n (circleMap 0 (ρ n) (2 * Real.pi * t - Real.pi))) ⊆ U := by
    apply hK.eventually_segment_subset_open_of_tendstoUniformlyOn_sub hU hKU
      (Eventually.of_forall fun n t ht => hvK n ?_) hclose'
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_pos (hρ0 n)] using (hρ n).2
  refine ⟨ρ, h, hρ, hh, hh0, ?_, houter, he0⟩
  filter_upwards [hgood, hseg] with n hn hsn
  have hhρ : h n < ρ n := by linarith [hn.1, hh n]
  refine ⟨hn.1, hn.2, ?_⟩
  intro z hz
  by_cases hi : ‖z‖ ≤ ρ n - h n
  · rw [attachThinAnnulus_inner (u n) (v n) T (ρ n) (h n) hi]
    apply hvK n
    have hnorm : ‖(ρ n / (ρ n - h n)) • z‖ ≤ ρ n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hρ0 n) (sub_pos.mpr hhρ))]
      exact (mul_le_mul_of_nonneg_left hi (div_nonneg (hρ0 n).le (sub_pos.mpr hhρ).le)).trans_eq
        (div_mul_cancel₀ (ρ n) (sub_pos.mpr hhρ).ne')
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hnorm.trans (hρ n).2)
  · by_cases ho : ρ n ≤ ‖z‖
    · rw [attachThinAnnulus_outer (u n) (v n) T (hh n) ho]
      exact huK n hz
    · have hs : ρ n - h n ≤ ‖z‖ ∧ ‖z‖ ≤ ρ n :=
        ⟨(lt_of_not_ge hi).le, (lt_of_not_ge ho).le⟩
      rw [attachThinAnnulus_shell (u n) (v n) T (hh n) hhρ (huvfix n) (hvvfix n) hs]
      apply hTK
      obtain ⟨t, ht, htp⟩ := exists_circle_parameter_of_norm_eq (hρ0 n).le
        (thinAnnulusProjection_norm (hρ0 n).le z)
      apply hsn t ht
      rw [htp]
      have hθ := thinAnnulusParameter_mem_Icc (hh n) hs
      simpa only [thinAnnulusInterpolation, AffineMap.lineMap_apply_module] using
        (lineMap_mem_segment ℝ (v n (thinAnnulusProjection (ρ n) z))
          (u n (thinAnnulusProjection (ρ n) z)) hθ)

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis



private theorem integral_closedBall_diff_eq_integral_norm_annulus
    (f : ℂ → ℝ) (a R : ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) a, f z) =
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc a R}, f z := by
  apply setIntegral_congr_set
  have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Metric.sphere (0 : ℂ) a := by
    apply ae_iff.mpr
    have heq : {z : ℂ | ¬z ∉ Metric.sphere (0 : ℂ) a} = Metric.sphere (0 : ℂ) a := by
      ext z
      simp
    rw [heq]
    exact Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) a
  filter_upwards [hnull] with z hz
  apply propext
  change (z ∈ Metric.closedBall (0 : ℂ) R ∧ z ∉ Metric.closedBall (0 : ℂ) a) ↔
    (a ≤ ‖z‖ ∧ ‖z‖ ≤ R)
  simp only [Metric.mem_closedBall, dist_zero_right, not_le]
  have hne : ‖z‖ ≠ a := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact ⟨fun h => ⟨h.2.le, h.1⟩, fun h => ⟨h.2, lt_of_le_of_ne h.1 hne.symm⟩⟩

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_target_valued_attachThinAnnulus_tendsto_quadratic_annulus_energy_zero
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {r R Q : ℝ} (hr : 0 < r) (hrR : r < R) (hRQ : R ≤ Q)
    (hgap : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖u n z - v n z‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖fderiv ℝ (u n) z‖ ^ 2 + ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B)
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) Q) K)
    (hvK : ∀ n, MapsTo (v n) (Metric.closedBall (0 : ℂ) R) K)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTK : MapsTo T U K) (hfix : ∀ y ∈ K, T y = y)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    ∃ (ρ h : ℕ → ℝ), (∀ n, ρ n ∈ Icc r R) ∧ (∀ n, 0 < h n) ∧
      Tendsto h atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, h n < ρ n / 2 ∧
        (∃ C : ℝ≥0, LipschitzWith C (attachThinAnnulus (u n) (v n) T (ρ n) (h n))) ∧
        MapsTo (attachThinAnnulus (u n) (v n) T (ρ n) (h n))
          (Metric.closedBall (0 : ℂ) Q) K) ∧
      (∀ n z, ρ n ≤ ‖z‖ → attachThinAnnulus (u n) (v n) T (ρ n) (h n) z = u n z) ∧
      Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (ρ n - h n) (ρ n)},
        (‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1‖ ^ 2 +
          ‖fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I‖ ^ 2) / 2)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc (ρ n - h n) (ρ n)},
        (A (attachThinAnnulus (u n) (v n) T (ρ n) (h n) z)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1) +
        A (attachThinAnnulus (u n) (v n) T (ρ n) (h n) z)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I)) / 2)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ z in
        Metric.closedBall (0 : ℂ) (ρ n) \ Metric.closedBall (0 : ℂ) (ρ n - h n),
        (A (attachThinAnnulus (u n) (v n) T (ρ n) (h n) z)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z 1) +
        A (attachThinAnnulus (u n) (v n) T (ρ n) (h n) z)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I)
          (fderiv ℝ (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z Complex.I)) / 2)
        atTop (𝓝 0) := by
  obtain ⟨ρ, h, hρ, hh, hh0, hgood, houter, he0⟩ :=
    exists_target_valued_attachThinAnnulus_tendsto_annulus_energy_zero u v Ku Kv hu hv
      hr hrR hRQ hgap henergy hK hU hKU huK hvK T hT hL hTK hfix
  refine ⟨ρ, h, hρ, hh, hh0, hgood, houter, he0, ?_⟩
  let S (n : ℕ) := {z : ℂ | ‖z‖ ∈ Icc (ρ n - h n) (ρ n)}
  have hsub (n : ℕ) : S n ⊆ Metric.closedBall (0 : ℂ) (ρ n) := by
    intro z hz
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.2)
  have hcompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_closedBall (0 : ℂ) (ρ n)).of_isClosed_subset
      (isClosed_Icc.preimage continuous_norm) (hsub n)
  have hquad := tendsto_integral_quadratic_fderiv_of_eventually_lipschitz
    (fun n => attachThinAnnulus (u n) (v n) T (ρ n) (h n)) S hcompact hK A hA
    (by
      filter_upwards [hgood] with n hn
      refine ⟨hn.2.1, hn.2.2.mono_left ?_⟩
      exact (hsub n).trans (Metric.closedBall_subset_closedBall ((hρ n).2.trans hRQ))) he0
  refine ⟨hquad, ?_⟩
  simpa only [integral_closedBall_diff_eq_integral_norm_annulus] using hquad

end DifferentialGeometry.Analysis

end
