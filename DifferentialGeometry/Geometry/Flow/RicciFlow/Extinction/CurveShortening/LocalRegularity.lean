import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IntegralBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Analysis.Integration.Periodic

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap


def arcLength (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.speed g x t

def arcTotalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.curvature g x t * c.speed g x t

def arcEnergy (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.curvatureSq g x t * c.speed g x t

structure SliceRegularity (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) : Prop where
  speed_continuous : Continuous fun x => c.speed g x t
  curvatureSq_continuous : Continuous fun x => c.curvatureSq g x t
  curvatureSq_speed_periodic : Function.Periodic (fun x => c.curvatureSq g x t * c.speed g x t) 1

omit [CompleteSpace E] in
theorem sliceRegularity [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    c.SliceRegularity g t where
  speed_continuous := (c.speed_contDiff g J hc hi t ht).continuous
  curvatureSq_continuous := (c.curvatureSq_contDiff g J hc hi t ht).continuous
  curvatureSq_speed_periodic := c.curvatureSq_speed_periodic g J hc hi t ht

end CurveMap

namespace ProductCurve

structure SliceRegularity (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda t : ℝ) : Prop where
  speed_continuous : Continuous fun x => c.speed g lambda x t
  curvatureSq_continuous : Continuous fun x => c.curvatureSq g lambda x t
  curvatureSq_speed_periodic :
    Function.Periodic (fun x => c.curvatureSq g lambda x t * c.speed g lambda x t) 1

end ProductCurve

variable [SigmaCompactSpace M] [t2M : T2Space M]

private theorem two_mul_mul_le (t f g : ℝ) (ht : 0 < t) : 2 * (f * g) ≤ t * f ^ 2 + g ^ 2 / t := by
  have h : t * f ^ 2 + g ^ 2 / t = (t ^ 2 * f ^ 2 + g ^ 2) / t := by
    field_simp
  rw [h, le_div_iff₀ ht]
  nlinarith [sq_nonneg (t * f - g)]

private theorem intervalIntegral_mul_le_sqrt_mul_sqrt {f g : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume p q)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume p q)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume p q) :
    (∫ x in p..q, f x * g x) ≤ Real.sqrt ((∫ x in p..q, f x ^ 2) * (∫ x in p..q, g x ^ 2)) := by
  set A := ∫ x in p..q, f x ^ 2
  set B := ∫ x in p..q, g x ^ 2
  set X := ∫ x in p..q, f x * g x
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg (f x)
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg (g x)
  have hkey : ∀ t : ℝ, 0 < t → 2 * X ≤ t * A + B / t := by
    intro t ht
    have hpt : ∀ x ∈ Icc p q, 2 * (f x * g x) ≤ t * f x ^ 2 + g x ^ 2 / t :=
      fun x _ => two_mul_mul_le t (f x) (g x) ht
    have h1 : IntervalIntegrable (fun x => 2 * (f x * g x)) volume p q := hfg.const_mul 2
    have h2 : IntervalIntegrable (fun x => t * f x ^ 2 + g x ^ 2 / t) volume p q :=
      (hf2.const_mul t).add (hg2.div_const t)
    have hmono := intervalIntegral.integral_mono_on hpq h1 h2 hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hf2.const_mul t) (hg2.div_const t),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hmono
    exact hmono
  have h2 : 2 * X ≤ 2 * Real.sqrt (A * B) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · have hA0' : A = 0 := hA0.symm
      have hzero : 2 * Real.sqrt (A * B) = 0 := by rw [hA0', zero_mul, Real.sqrt_zero, mul_zero]
      rw [hzero, zero_add]
      rcases eq_or_lt_of_le hB with hB0 | hBpos
      · have hB0' : B = 0 := hB0.symm
        have hb := hkey 1 one_pos
        rw [hA0', hB0', mul_zero, zero_div, add_zero] at hb
        exact hb.trans hε.le
      · have ht : 0 < B / ε := div_pos hBpos hε
        have hb := hkey (B / ε) ht
        have hdiv : B / (B / ε) = ε := by
          rw [div_eq_iff (ne_of_gt (div_pos hBpos hε))]
          field_simp
        rw [hA0', mul_zero, zero_add, hdiv] at hb
        exact hb
    · rcases eq_or_lt_of_le hB with hB0 | hBpos
      · have hB0' : B = 0 := hB0.symm
        have hzero : 2 * Real.sqrt (A * B) = 0 := by rw [hB0', mul_zero, Real.sqrt_zero, mul_zero]
        rw [hzero, zero_add]
        have ht : 0 < ε / A := div_pos hε hApos
        have hb := hkey (ε / A) ht
        have hmul : ε / A * A = ε := div_mul_cancel₀ ε (ne_of_gt hApos)
        rw [hB0', zero_div, add_zero, hmul] at hb
        exact hb
      · have hspA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
        have hspB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
        have ht : 0 < Real.sqrt B / Real.sqrt A := div_pos hspB hspA
        have hb := hkey (Real.sqrt B / Real.sqrt A) ht
        have hleft : Real.sqrt B / Real.sqrt A * A = Real.sqrt (A * B) := by
          rw [div_mul_eq_mul_div, Real.sqrt_mul hA, div_eq_iff (ne_of_gt hspA)]
          nlinarith [Real.sq_sqrt hA]
        have hright : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt (A * B) := by
          rw [div_div_eq_mul_div, Real.sqrt_mul hA, div_eq_iff (ne_of_gt hspB)]
          nlinarith [Real.sq_sqrt hB]
        rw [hleft, hright] at hb
        linarith
  linarith

private theorem intervalIntegral_le_integral_zero_one {f : ℝ → ℝ} {p q : ℝ}
    (hper : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    (hnn : ∀ x, 0 ≤ f x) (hqp : q ≤ p + 1) :
    (∫ x in p..q, f x) ≤ ∫ x in 0..1, f x := by
  simpa only [zero_add] using hper.intervalIntegral_le_period
    (a := 0) (by simpa only [zero_add] using hint) hnn hqp

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
theorem arc_totalCurvature_le_sqrt [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (p q t : ℝ) (hpq : p ≤ q) (hqp : q ≤ p + 1)
    (ht : t ∈ J) :
    c.arcTotalCurvature g p q t ≤ Real.sqrt (c.arcLength g p q t * c.arcEnergy g p q t) ∧
    c.arcEnergy g p q t ≤ c.energy g t := by
  have hslice' := c.sliceRegularity g J hc hi t ht
  have hspd : Continuous fun x => c.speed g x t := hslice'.speed_continuous
  have hcur : Continuous fun x => c.curvatureSq g x t := hslice'.curvatureSq_continuous
  have hcurv : Continuous fun x => c.curvature g x t := Real.continuous_sqrt.comp hcur
  have hroot : Continuous fun x => Real.sqrt (c.speed g x t) := hspd.sqrt
  let F : ℝ → ℝ := fun x => c.curvature g x t * Real.sqrt (c.speed g x t)
  let G : ℝ → ℝ := fun x => Real.sqrt (c.speed g x t)
  have hFc : Continuous F := hcurv.mul hroot
  have hGc : Continuous G := hroot
  constructor
  · have hcs := intervalIntegral_mul_le_sqrt_mul_sqrt (f := G) (g := F) hpq
      ((hGc.pow 2).intervalIntegrable p q) ((hFc.pow 2).intervalIntegrable p q)
      ((hGc.mul hFc).intervalIntegrable p q)
    have hGF : (fun x => G x * F x) = fun x => c.curvature g x t * c.speed g x t := by
      funext x
      change Real.sqrt (c.speed g x t) * (c.curvature g x t * Real.sqrt (c.speed g x t)) =
        c.curvature g x t * c.speed g x t
      rw [← mul_assoc, mul_comm (Real.sqrt (c.speed g x t)) (c.curvature g x t), mul_assoc,
        Real.mul_self_sqrt (c.speed_nonneg g x t)]
    have hG2 : (fun x => G x ^ 2) = fun x => c.speed g x t := by
      funext x
      exact Real.sq_sqrt (c.speed_nonneg g x t)
    have hF2 : (fun x => F x ^ 2) = fun x => c.curvatureSq g x t * c.speed g x t := by
      funext x
      change (c.curvature g x t * Real.sqrt (c.speed g x t)) ^ 2 =
        c.curvatureSq g x t * c.speed g x t
      rw [mul_pow, CurveMap.curvature_sq, Real.sq_sqrt (c.speed_nonneg g x t)]
    rw [hGF, hG2, hF2] at hcs
    simpa only [CurveMap.arcTotalCurvature, CurveMap.arcLength, CurveMap.arcEnergy] using hcs
  · have hper : Function.Periodic (fun x => c.curvatureSq g x t * c.speed g x t) 1 :=
      hslice'.curvatureSq_speed_periodic
    have hint : IntervalIntegrable (fun x => c.curvatureSq g x t * c.speed g x t) volume 0 1 :=
      (hcur.mul hspd).intervalIntegrable 0 1
    have hle := intervalIntegral_le_integral_zero_one hper hint
      (fun x => mul_nonneg (c.normSq_nonneg g (c.curvatureVector g) x t) (c.speed_nonneg g x t)) hqp
    simpa only [CurveMap.arcEnergy, CurveMap.energy, CurveMap.integral] using hle

private theorem volume_lt_le_of_integral_le {f : ℝ → ℝ} {s t B C : ℝ}
    (hst : s ≤ t) (hB : 0 < B)
    (hint : IntegrableOn f (Icc s t)) (hnn : 0 ≤ᵐ[volume.restrict (Icc s t)] f)
    (hE : (∫ v in s..t, f v) ≤ C) :
    volume {v : ℝ | v ∈ Icc s t ∧ B < f v} ≤ ENNReal.ofReal (C / B) := by
  have hmeas : AEMeasurable f (volume.restrict (Icc s t)) := hint.aestronglyMeasurable.aemeasurable
  have hmeas' : AEMeasurable (fun v => ENNReal.ofReal (f v)) (volume.restrict (Icc s t)) :=
    hmeas.ennreal_ofReal
  have hmark := MeasureTheory.meas_ge_le_lintegral_div (μ := volume.restrict (Icc s t)) hmeas'
    (ε := ENNReal.ofReal B) (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hB) ENNReal.ofReal_ne_top
  have hsub : {v : ℝ | v ∈ Icc s t ∧ B < f v} ⊆
      Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := fun v hv =>
    ⟨hv.1, ENNReal.ofReal_le_ofReal hv.2.le⟩
  have hnull : NullMeasurableSet {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}
      (volume.restrict (Icc s t)) := hmeas'.nullMeasurableSet_preimage measurableSet_Ici
  have hres : (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} =
      volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) := by
    rw [Measure.restrict_apply₀ hnull, Set.inter_comm]
  have hIcc : (∫ x, f x ∂(volume.restrict (Icc s t))) = ∫ v in s..t, f v :=
    integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le hst).symm
  have hlint : (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) =
      ENNReal.ofReal (∫ v in s..t, f v) := by
    rw [← hIcc, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  calc volume {v : ℝ | v ∈ Icc s t ∧ B < f v}
      ≤ volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) :=
        measure_mono hsub
    _ = (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := hres.symm
    _ ≤ (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) / ENNReal.ofReal B := hmark
    _ = ENNReal.ofReal (∫ v in s..t, f v) / ENNReal.ofReal B := by rw [hlint]
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal B := ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hE) _
    _ = ENNReal.ofReal (C / B) := (ENNReal.ofReal_div_of_pos hB).symm

private theorem zpow_neg_le_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (n : ℕ) :
    y ^ (-(n : ℤ)) ≤ x ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_neg]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hx hxy) n) (pow_pos hx n)).2
    (pow_le_pow_left₀ hx.le hxy n)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem productCurve_normSq_nonneg (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    0 ≤ c.normSq g lambda V x t := by
  rw [ProductCurve.normSq, ProductCurve.inner]
  refine add_nonneg (metric_inner_self_nonneg (g t) (c.projection.lift x t) (V x t).1) ?_
  nlinarith [sq_nonneg (V x t).2, sq_nonneg lambda]

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
private theorem productCurve_curvature_sq (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.curvature g lambda x t ^ 2 = c.curvatureSq g lambda x t :=
  Real.sq_sqrt (productCurve_normSq_nonneg c g lambda (c.curvatureVector g lambda) x t)

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
private theorem curveMap_energy_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (t : ℝ) : 0 ≤ c.energy g t :=
  intervalIntegral.integral_nonneg zero_le_one fun x _ =>
    mul_nonneg (c.normSq_nonneg g (c.curvatureVector g) x t) (c.speed_nonneg g x t)

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
theorem productCurve_energy_nonneg (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ) : 0 ≤ c.energy g lambda t :=
  intervalIntegral.integral_nonneg zero_le_one fun x _ =>
    mul_nonneg (productCurve_normSq_nonneg c g lambda (c.curvatureVector g lambda) x t)
      (c.speed_nonneg g lambda x t)

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
theorem productCurve_arcTotalCurvature_le_sqrt (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (c : ProductCurve M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (p q t : ℝ) (hpq : p ≤ q) (hqp : q ≤ p + 1)
    (ht : t ∈ J)
    (hslice : c.SmoothOn (I := I) J → c.ImmersedOn (I := I) J → t ∈ J →
      c.SliceRegularity g lambda t) :
    c.arcTotalCurvature g lambda p q t ≤
      Real.sqrt (c.arcLength g lambda p q t * c.arcEnergy g lambda p q t) ∧
    c.arcEnergy g lambda p q t ≤ c.energy g lambda t := by
  have hslice' := hslice hc hi ht
  have hspd : Continuous fun x => c.speed g lambda x t := hslice'.speed_continuous
  have hcur : Continuous fun x => c.curvatureSq g lambda x t := hslice'.curvatureSq_continuous
  have hcurv : Continuous fun x => c.curvature g lambda x t := Real.continuous_sqrt.comp hcur
  have hroot : Continuous fun x => Real.sqrt (c.speed g lambda x t) := hspd.sqrt
  let F : ℝ → ℝ := fun x => c.curvature g lambda x t * Real.sqrt (c.speed g lambda x t)
  let G : ℝ → ℝ := fun x => Real.sqrt (c.speed g lambda x t)
  have hFc : Continuous F := hcurv.mul hroot
  have hGc : Continuous G := hroot
  constructor
  · have hcs := intervalIntegral_mul_le_sqrt_mul_sqrt (f := G) (g := F) hpq
      ((hGc.pow 2).intervalIntegrable p q) ((hFc.pow 2).intervalIntegrable p q)
      ((hGc.mul hFc).intervalIntegrable p q)
    have hGF : (fun x => G x * F x) = fun x => c.curvature g lambda x t * c.speed g lambda x t := by
      funext x
      change Real.sqrt (c.speed g lambda x t) * (c.curvature g lambda x t * Real.sqrt (c.speed g lambda x t)) =
        c.curvature g lambda x t * c.speed g lambda x t
      rw [← mul_assoc, mul_comm (Real.sqrt (c.speed g lambda x t)) (c.curvature g lambda x t), mul_assoc,
        Real.mul_self_sqrt (c.speed_nonneg g lambda x t)]
    have hG2 : (fun x => G x ^ 2) = fun x => c.speed g lambda x t := by
      funext x
      exact Real.sq_sqrt (c.speed_nonneg g lambda x t)
    have hF2 : (fun x => F x ^ 2) = fun x => c.curvatureSq g lambda x t * c.speed g lambda x t := by
      funext x
      change (c.curvature g lambda x t * Real.sqrt (c.speed g lambda x t)) ^ 2 =
        c.curvatureSq g lambda x t * c.speed g lambda x t
      rw [mul_pow, productCurve_curvature_sq, Real.sq_sqrt (c.speed_nonneg g lambda x t)]
    rw [hGF, hG2, hF2] at hcs
    simpa only [ProductCurve.arcTotalCurvature, ProductCurve.arcLength, ProductCurve.arcEnergy] using hcs
  · have hper : Function.Periodic (fun x => c.curvatureSq g lambda x t * c.speed g lambda x t) 1 :=
      hslice'.curvatureSq_speed_periodic
    have hint : IntervalIntegrable (fun x => c.curvatureSq g lambda x t * c.speed g lambda x t) volume 0 1 :=
      (hcur.mul hspd).intervalIntegrable 0 1
    have hle := intervalIntegral_le_integral_zero_one hper hint
      (fun x => mul_nonneg (productCurve_normSq_nonneg c g lambda (c.curvatureVector g lambda) x t)
        (c.speed_nonneg g lambda x t)) hqp
    simpa only [ProductCurve.arcEnergy, ProductCurve.energy, ProductCurve.integral] using hle

private theorem zpow_neg_one_half_eq (d : ℝ) (hd : d ≠ 0) : (d / 2) ^ (-(1 : ℤ)) = 2 / d := by
  rw [zpow_neg_one]
  field_simp

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
theorem productCurve_iteratedDs_zero (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (V : c.Field (I := I)) :
    c.iteratedDs g lambda 0 V = V := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] t2M in
theorem productCurve_curvature_le_of_window {c : ProductCurve M}
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t w A d : ℝ) (hd : 0 < d) (hA : 0 ≤ A)
    (hlo : d / 2 ≤ t - w)
    (hbound : c.normSq g lambda (c.curvatureVector g lambda) x t ≤ A * (t - w) ^ (-(1 : ℤ))) :
    c.curvature g lambda x t ≤ Real.sqrt (2 * A / d) := by
  have hz : (t - w) ^ (-(1 : ℤ)) ≤ (d / 2) ^ (-(1 : ℤ)) :=
    zpow_neg_le_of_le (by linarith) hlo 1
  have h1 : A * (t - w) ^ (-(1 : ℤ)) ≤ A * (d / 2) ^ (-(1 : ℤ)) :=
    mul_le_mul_of_nonneg_left hz hA
  have h2 : (d / 2) ^ (-(1 : ℤ)) = 2 / d := zpow_neg_one_half_eq d (by linarith)
  have h3 : A * (2 / d) = 2 * A / d := by ring
  exact Real.sqrt_le_sqrt (hbound.trans (h1.trans_eq (by rw [h2, h3])))

variable [compactM : CompactSpace M] [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

structure CurveShorteningRegularityInput (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) where
  delta : ℝ
  radius : ℝ
  coefficient : ℕ → ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1
  coefficient_pos : ∀ m, 0 < coefficient m
  curve : ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
      c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
      ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ radius →
        r ≤ c.length B.family.metric tstar →
        (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric p q tstar = r →
          c.arcTotalCurvature B.family.metric p q tstar ≤ delta) →
        ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + delta * r ^ 2 →
          c.normSq B.family.metric
            (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
              coefficient m * (t - tstar) ^ (-((m : ℤ) + 1))
  product : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ radius →
        r ≤ c.length B.family.metric lambda tstar →
        (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric lambda p q tstar = r →
          c.arcTotalCurvature B.family.metric lambda p q tstar ≤ delta) →
        ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + delta * r ^ 2 →
          c.normSq B.family.metric lambda
            (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
              coefficient m * (t - tstar) ^ (-((m : ℤ) + 1))

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem rfs_csf_local_regularity (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀)
    (K : CurveShorteningRegularityInput B L₀ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      (∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
          c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric p q tstar = r →
              c.arcTotalCurvature B.family.metric p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric
                (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1))) ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
          c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric lambda tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric lambda p q tstar = r →
              c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric lambda
                (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1))) := by
  have hL₀' : 0 ≤ L₀ := hL₀
  have hΘ₀' : 0 ≤ Θ₀ := hΘ₀
  exact ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos, K.radius_le_one,
    K.coefficient_pos, K.curve, K.product⟩

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem local_regularity_base (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀)
    (K : CurveShorteningRegularityInput B L₀ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      ∀ (T : ℝ) (_hT : a < T) (_hTb : T ≤ b) (J : Set ℝ),
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
          c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric p q tstar = r →
              c.arcTotalCurvature B.family.metric p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric
                (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  have hL₀' : 0 ≤ L₀ := hL₀
  have hΘ₀' : 0 ≤ Θ₀ := hΘ₀
  exact ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos, K.radius_le_one,
    K.coefficient_pos, K.curve⟩

omit [CompleteSpace E] [SigmaCompactSpace M] compactM nonemptyM t2M in
theorem good_time_arc_bound (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) {δ r B : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hB : 0 < B) (hrB : r ≤ δ ^ 2 / B)
    (t : ℝ) (ht : t ∈ J) (hE : c.energy g t ≤ B) :
    ∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength g p q t = r →
      c.arcTotalCurvature g p q t ≤ δ := by
  intro p q hpq hqp hlen
  obtain ⟨hcs, he⟩ := arc_totalCurvature_le_sqrt g c hc hi p q t hpq hqp ht
  have hprod : c.arcLength g p q t * c.arcEnergy g p q t ≤ δ ^ 2 := by
    rw [hlen]
    exact (mul_le_mul_of_nonneg_left (he.trans hE) hr.le).trans
      ((le_div_iff₀ hB).mp hrB)
  exact hcs.trans ((Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq hδ.le))

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem bad_energy_times_measure (B : RicciBackground (I := I) (M := M) D a b)
    {u : ℝ} (hau : a < u) (hub : u ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a u))
    {L₀ threshold : ℝ} (hL₀ : c.length B.family.metric a ≤ L₀) (hB : 0 < threshold)
    (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htu : t ≤ u)
    (hinput : a < u → u ≤ b → c.IsSolutionOn B.family.metric (Icc a u) →
      c.length B.family.metric a ≤ L₀ → a ≤ s → s ≤ t → t ≤ u →
      IntegrableOn (c.energy B.family.metric) (Icc s t) ∧
        (∫ v in s..t, c.energy B.family.metric v) ≤ Real.exp (B.B₀ * (b - a)) * L₀) :
    volume {v : ℝ | v ∈ Icc s t ∧ threshold < c.energy B.family.metric v} ≤
      ENNReal.ofReal (Real.exp (B.B₀ * (b - a)) * L₀ / threshold) := by
  obtain ⟨hint, hE⟩ := hinput hau hub hc hL₀ has hst htu
  exact volume_lt_le_of_integral_le hst hB hint
    (Filter.Eventually.of_forall fun v => curveMap_energy_nonneg c B.family.metric v) hE

structure CurveShorteningEnergyInput (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ : ℝ) where
  slice_product : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ J, c.SliceRegularity B.family.metric lambda t
  energy : ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J → c.length B.family.metric a ≤ L₀ →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
        IntegrableOn (c.energy B.family.metric) (Icc s u) ∧
          (∫ v in s..u, c.energy B.family.metric v) ≤ Real.exp (B.B₀ * (b - a)) * L₀
  energy_product : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
        IntegrableOn (c.energy B.family.metric lambda) (Icc s u) ∧
          (∫ v in s..u, c.energy B.family.metric lambda v) ≤ Real.exp (B.B₀ * (b - a)) * L₀

omit [SigmaCompactSpace M] compactM nonemptyM in
theorem rfs_csf_good_times (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀)
    (K : CurveShorteningRegularityInput B L₀ Θ₀)
    (E : CurveShorteningEnergyInput B L₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      ∀ threshold : ℝ, 0 < threshold →
        let r := min r₀ (δ ^ 2 / threshold)
        let d := δ * r ^ 2
        let C_E := Real.exp (B.B₀ * (b - a)) * L₀
        (∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
          (J = Ico a T ∨ J = Icc a T) →
          ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
            c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
            (∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
              volume {v : ℝ | v ∈ Icc s u ∧ threshold < c.energy B.family.metric v} ≤
                ENNReal.ofReal (C_E / threshold)) ∧
            (∀ tstar ∈ Ico a T, c.energy B.family.metric tstar ≤ threshold →
              r ≤ c.length B.family.metric tstar →
              (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
                c.arcLength B.family.metric p q tstar = r →
                c.arcTotalCurvature B.family.metric p q tstar ≤ δ) ∧
              ∀ m x t, t ∈ J → t ∈ Icc (tstar + d / 2) (tstar + d) →
                c.normSq B.family.metric
                  (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                    A m * (d / 2) ^ (-((m : ℤ) + 1)))) ∧
        (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
          ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
          (J = Ico a T ∨ J = Icc a T) →
          ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
            c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
            (∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
              volume {v : ℝ | v ∈ Icc s u ∧ threshold < c.energy B.family.metric lambda v} ≤
                ENNReal.ofReal (C_E / threshold)) ∧
            (∀ tstar ∈ Ico a T, c.energy B.family.metric lambda tstar ≤ threshold →
              r ≤ c.length B.family.metric lambda tstar →
              (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
                c.arcLength B.family.metric lambda p q tstar = r →
                c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) ∧
              ∀ m x t, t ∈ J → t ∈ Icc (tstar + d / 2) (tstar + d) →
                c.normSq B.family.metric lambda
                  (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
                    A m * (d / 2) ^ (-((m : ℤ) + 1)))) := by
  have hL₀' : 0 ≤ L₀ := hL₀
  have hΘ₀' : 0 ≤ Θ₀ := hΘ₀
  refine ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos, K.radius_le_one,
    K.coefficient_pos, ?_⟩
  intro threshold hthreshold
  dsimp only
  constructor
  · intro T hT hTb J hJ c hc hlen hcurvature
    have htstarJ : ∀ tstar ∈ Ico a T, tstar ∈ J := by
      intro tstar htstar
      rcases hJ with h | h
      · rw [h]; exact htstar
      · rw [h]; exact ⟨htstar.1, htstar.2.le⟩
    constructor
    · intro s u has hst htu
      have hEu := E.energy T hT hTb J hJ c hc hlen s u has hst htu
      exact volume_lt_le_of_integral_le hst hthreshold hEu.1
        (Filter.Eventually.of_forall fun v => curveMap_energy_nonneg c B.family.metric v) hEu.2
    · intro tstar htstar henergy hlength
      have hrpos : 0 < min K.radius (K.delta ^ 2 / threshold) :=
        lt_min K.radius_pos (div_pos (pow_pos K.delta_pos 2) hthreshold)
      have hrle : min K.radius (K.delta ^ 2 / threshold) ≤ K.radius := min_le_left _ _
      have hrδ : min K.radius (K.delta ^ 2 / threshold) * threshold ≤ K.delta ^ 2 :=
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hthreshold.le).trans
          (div_mul_cancel₀ (K.delta ^ 2) hthreshold.ne').le
      have harc : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric p q tstar = min K.radius (K.delta ^ 2 / threshold) →
          c.arcTotalCurvature B.family.metric p q tstar ≤ K.delta := by
        intro p q hpq hqp hlen_eq
        have h1 := (arc_totalCurvature_le_sqrt B.family.metric c hc.smooth hc.immersed p q tstar
          hpq hqp (htstarJ tstar htstar)).1
        have h2 := (arc_totalCurvature_le_sqrt B.family.metric c hc.smooth hc.immersed p q tstar
          hpq hqp (htstarJ tstar htstar)).2
        calc c.arcTotalCurvature B.family.metric p q tstar
            ≤ Real.sqrt (c.arcLength B.family.metric p q tstar *
                c.arcEnergy B.family.metric p q tstar) := h1
          _ = Real.sqrt (min K.radius (K.delta ^ 2 / threshold) *
                c.arcEnergy B.family.metric p q tstar) := by rw [hlen_eq]
          _ ≤ Real.sqrt (min K.radius (K.delta ^ 2 / threshold) * threshold) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (h2.trans henergy) hrpos.le)
          _ ≤ K.delta := Real.sqrt_le_iff.2 ⟨K.delta_pos.le, hrδ⟩
      refine ⟨harc, ?_⟩
      intro m x t htJ hm
      have htstarJ' : tstar ∈ J := htstarJ tstar htstar
      have hd : 0 < K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 :=
        mul_pos K.delta_pos (pow_pos hrpos 2)
      have htd : tstar < t := by
        have hd2 : 0 < K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 / 2 := half_pos hd
        linarith [hm.1]
      have hle' : t ≤ tstar + K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 := hm.2
      have hK := K.curve T hT hTb J hJ c hc hlen hcurvature tstar htstar
        (min K.radius (K.delta ^ 2 / threshold)) hrpos hrle hlength harc m x t htJ htd hle'
      refine hK.trans (mul_le_mul_of_nonneg_left ?_ (K.coefficient_pos m).le)
      have hpow := zpow_neg_le_of_le (half_pos hd) (by linarith [hm.1] : K.delta *
        (min K.radius (K.delta ^ 2 / threshold)) ^ 2 / 2 ≤ t - tstar) (m + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using hpow
  · intro lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurvature
    have htstarJ : ∀ tstar ∈ Ico a T, tstar ∈ J := by
      intro tstar htstar
      rcases hJ with h | h
      · rw [h]; exact htstar
      · rw [h]; exact ⟨htstar.1, htstar.2.le⟩
    constructor
    · intro s u has hst htu
      have hEu := E.energy_product lambda hlambda hlambda_one T hT hTb J hJ c hc hlen s u has hst htu
      exact volume_lt_le_of_integral_le hst hthreshold hEu.1
        (Filter.Eventually.of_forall fun v => productCurve_energy_nonneg c B.family.metric lambda v) hEu.2
    · intro tstar htstar henergy hlength
      have hrslice := E.slice_product lambda hlambda hlambda_one T hT hTb J hJ c hc hlen tstar
        (htstarJ tstar htstar)
      have hrpos : 0 < min K.radius (K.delta ^ 2 / threshold) :=
        lt_min K.radius_pos (div_pos (pow_pos K.delta_pos 2) hthreshold)
      have hrle : min K.radius (K.delta ^ 2 / threshold) ≤ K.radius := min_le_left _ _
      have hrδ : min K.radius (K.delta ^ 2 / threshold) * threshold ≤ K.delta ^ 2 :=
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hthreshold.le).trans
          (div_mul_cancel₀ (K.delta ^ 2) hthreshold.ne').le
      have harc : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric lambda p q tstar = min K.radius (K.delta ^ 2 / threshold) →
          c.arcTotalCurvature B.family.metric lambda p q tstar ≤ K.delta := by
        intro p q hpq hqp hlen_eq
        have h1 := (productCurve_arcTotalCurvature_le_sqrt B.family.metric lambda c hc.smooth hc.immersed
          p q tstar hpq hqp (htstarJ tstar htstar) fun _ _ _ => hrslice).1
        have h2 := (productCurve_arcTotalCurvature_le_sqrt B.family.metric lambda c hc.smooth hc.immersed
          p q tstar hpq hqp (htstarJ tstar htstar) fun _ _ _ => hrslice).2
        calc c.arcTotalCurvature B.family.metric lambda p q tstar
            ≤ Real.sqrt (c.arcLength B.family.metric lambda p q tstar *
                c.arcEnergy B.family.metric lambda p q tstar) := h1
          _ = Real.sqrt (min K.radius (K.delta ^ 2 / threshold) *
                c.arcEnergy B.family.metric lambda p q tstar) := by rw [hlen_eq]
          _ ≤ Real.sqrt (min K.radius (K.delta ^ 2 / threshold) * threshold) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (h2.trans henergy) hrpos.le)
          _ ≤ K.delta := Real.sqrt_le_iff.2 ⟨K.delta_pos.le, hrδ⟩
      refine ⟨harc, ?_⟩
      intro m x t htJ hm
      have htstarJ' : tstar ∈ J := htstarJ tstar htstar
      have hd : 0 < K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 :=
        mul_pos K.delta_pos (pow_pos hrpos 2)
      have htd : tstar < t := by
        have hd2 : 0 < K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 / 2 := half_pos hd
        linarith [hm.1]
      have hle' : t ≤ tstar + K.delta * (min K.radius (K.delta ^ 2 / threshold)) ^ 2 := hm.2
      have hK := K.product lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurvature tstar htstar
        (min K.radius (K.delta ^ 2 / threshold)) hrpos hrle hlength harc m x t htJ htd hle'
      refine hK.trans (mul_le_mul_of_nonneg_left ?_ (K.coefficient_pos m).le)
      have hpow := zpow_neg_le_of_le (half_pos hd) (by linarith [hm.1] : K.delta *
        (min K.radius (K.delta ^ 2 / threshold)) ^ 2 / 2 ≤ t - tstar) (m + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using hpow

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
