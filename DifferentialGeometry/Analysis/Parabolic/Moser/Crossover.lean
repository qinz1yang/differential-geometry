import DifferentialGeometry.Analysis.Integration.Measure.ExponentialTail
import DifferentialGeometry.Analysis.Integration.Measure.LevelSetDecay
import DifferentialGeometry.Analysis.Parabolic.ExponentialRescaling
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.Moser

theorem exp_centered_log_eq_rpow
    {r : ℝ} (hr : 0 < r) (p c : ℝ) :
    Real.exp (p * (Real.log r - c)) =
      Real.exp (-p * c) * r ^ p := by
  rw [mul_sub, Real.exp_sub]
  have hrpow : Real.exp (p * Real.log r) = r ^ p := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    ring
  rw [hrpow, div_eq_mul_inv, ← Real.exp_neg]
  have harg : -(p * c) = -p * c := by ring
  rw [harg]
  ring

theorem exp_neg_centered_log_eq_rpow
    {r : ℝ} (hr : 0 < r) (p c : ℝ) :
    Real.exp (-p * (Real.log r - c)) =
      Real.exp (p * c) * r ^ (-p) := by
  simpa only [neg_mul, neg_neg] using exp_centered_log_eq_rpow hr (-p) c

variable {α : Type*} [MeasurableSpace α]

theorem integral_exp_centered_log_eq_rpow
    (μ : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) (p c : ℝ) :
    (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μ) =
      Real.exp (-p * c) * ∫ x, u x ^ p ∂μ := by
  calc
    (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μ) =
        ∫ x, Real.exp (-p * c) * u x ^ p ∂μ := by
          exact integral_congr_ae (ae_of_all μ fun x =>
            exp_centered_log_eq_rpow (hpos x) p c)
    _ = Real.exp (-p * c) * ∫ x, u x ^ p ∂μ := integral_const_mul _ _

theorem integral_exp_neg_centered_log_eq_rpow
    (μ : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) (p c : ℝ) :
    (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μ) =
      Real.exp (p * c) * ∫ x, u x ^ (-p) ∂μ := by
  calc
    (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μ) =
        ∫ x, Real.exp (p * c) * u x ^ (-p) ∂μ := by
          exact integral_congr_ae (ae_of_all μ fun x =>
            exp_neg_centered_log_eq_rpow (hpos x) p c)
    _ = Real.exp (p * c) * ∫ x, u x ^ (-p) ∂μ := integral_const_mul _ _

theorem crossover_of_centered_exponential_bounds
    (μplus μminus : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) {p c Aplus Aminus : ℝ}
    (hAplus : 0 ≤ Aplus)
    (hplus : (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μplus) ≤ Aplus)
    (hminus : (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μminus) ≤ Aminus) :
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) ≤
      Aplus * Aminus := by
  have hplus' :
      Real.exp (-p * c) * (∫ x, u x ^ p ∂μplus) ≤ Aplus := by
    rw [← integral_exp_centered_log_eq_rpow μplus u hpos p c]
    exact hplus
  have hminus' :
      Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus) ≤ Aminus := by
    rw [← integral_exp_neg_centered_log_eq_rpow μminus u hpos p c]
    exact hminus
  have hmoment_minus : 0 ≤ ∫ x, u x ^ (-p) ∂μminus :=
    integral_nonneg fun x => Real.rpow_nonneg (hpos x).le _
  have hleft_minus :
      0 ≤ Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus) :=
    mul_nonneg (Real.exp_pos _).le hmoment_minus
  have hmul := mul_le_mul hplus' hminus' hleft_minus hAplus
  have hexp : Real.exp (-p * c) * Real.exp (p * c) = 1 := by
    rw [← Real.exp_add]
    have : -p * c + p * c = 0 := by ring
    rw [this, Real.exp_zero]
  calc
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) =
        (Real.exp (-p * c) * Real.exp (p * c)) *
          ((∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus)) := by
            rw [hexp, one_mul]
    _ = (Real.exp (-p * c) * (∫ x, u x ^ p ∂μplus)) *
          (Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus)) := by ring
    _ ≤ Aplus * Aminus := hmul

theorem crossover_of_centered_exponential_tails
    (μplus μminus : Measure α)
    [IsFiniteMeasure μplus] [IsFiniteMeasure μminus]
    (u : α → ℝ) (hpos : ∀ x, 0 < u x)
    {p c decay Bplus Bminus : ℝ}
    (hp : 0 < p) (hpdecay : p < decay)
    (hBplus : 0 ≤ Bplus) (hBminus : 0 ≤ Bminus)
    (hmeasPlus : AEMeasurable (fun x => Real.log (u x) - c) μplus)
    (hmeasMinus : AEMeasurable (fun x => Real.log (u x) - c) μminus)
    (htailPlus : ∀ level : ℝ, 0 < level →
      μplus {x | level < Real.log (u x) - c} ≤
        ENNReal.ofReal (Bplus * Real.exp (-decay * level)))
    (htailMinus : ∀ level : ℝ, 0 < level →
      μminus {x | level < -(Real.log (u x) - c)} ≤
        ENNReal.ofReal (Bminus * Real.exp (-decay * level))) :
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) ≤
      (μplus.real Set.univ + Bplus * p / (decay - p)) *
        (μminus.real Set.univ + Bminus * p / (decay - p)) := by
  have hplus :=
    DifferentialGeometry.Analysis.Measure.integrable_exp_and_integral_le_of_exponential_tail
      μplus (fun x => Real.log (u x) - c) hmeasPlus hp hpdecay hBplus htailPlus
  have hminus :=
    DifferentialGeometry.Analysis.Measure.integrable_exp_and_integral_le_of_exponential_tail
      μminus (fun x => -(Real.log (u x) - c)) hmeasMinus.neg
        hp hpdecay hBminus htailMinus
  apply crossover_of_centered_exponential_bounds μplus μminus u hpos
    (by
      apply add_nonneg ENNReal.toReal_nonneg
      exact div_nonneg (mul_nonneg hBplus hp.le) (sub_nonneg.mpr hpdecay.le))
    hplus.2
  simpa only [mul_neg, neg_mul] using hminus.2

theorem crossover_of_centered_level_set_decay
    (μplus μminus : Measure α)
    [IsFiniteMeasure μplus] [IsFiniteMeasure μminus]
    (u : α → ℝ) (hpos : ∀ x, 0 < u x)
    {basePlus baseMinus : Set α}
    {p c step ratio : ℝ}
    (hstep : 0 < step) (hratio_pos : 0 < ratio) (hratio_lt : ratio < 1)
    (hp : 0 < p) (hpdecay : p < -Real.log ratio / step)
    (hmeasPlus : AEMeasurable (fun x => Real.log (u x) - c) μplus)
    (hmeasMinus : AEMeasurable (fun x => Real.log (u x) - c) μminus)
    (hsubPlus : ∀ level,
      {x | level < Real.log (u x) - c} ⊆ basePlus)
    (hsubMinus : ∀ level,
      {x | level < -(Real.log (u x) - c)} ⊆ baseMinus)
    (hdecayPlus : ∀ level : ℝ, step ≤ level →
      μplus {x | level + step < Real.log (u x) - c} ≤
        ENNReal.ofReal ratio * μplus {x | level < Real.log (u x) - c})
    (hdecayMinus : ∀ level : ℝ, step ≤ level →
      μminus {x | level + step < -(Real.log (u x) - c)} ≤
        ENNReal.ofReal ratio * μminus {x | level < -(Real.log (u x) - c)}) :
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) ≤
      (μplus.real Set.univ +
          (1 / ratio ^ 2 * μplus.real basePlus) * p /
            (-Real.log ratio / step - p)) *
        (μminus.real Set.univ +
          (1 / ratio ^ 2 * μminus.real baseMinus) * p /
            (-Real.log ratio / step - p)) := by
  have htailPlus : ∀ level : ℝ, 0 < level →
      μplus {x | level < Real.log (u x) - c} ≤
        ENNReal.ofReal
          ((1 / ratio ^ 2 * μplus.real basePlus) *
            Real.exp (-(-Real.log ratio / step) * level)) := by
    intro level hlevel
    have h :=
      DifferentialGeometry.Analysis.Measure.level_set_exponential_decay_from_base_real
        μplus hsubPlus hstep hratio_pos hratio_lt hdecayPlus level
    have harg :
        -level * (-Real.log ratio / step) =
          -(-Real.log ratio / step) * level := by
      ring
    rw [harg] at h
    exact h
  have htailMinus : ∀ level : ℝ, 0 < level →
      μminus {x | level < -(Real.log (u x) - c)} ≤
        ENNReal.ofReal
          ((1 / ratio ^ 2 * μminus.real baseMinus) *
            Real.exp (-(-Real.log ratio / step) * level)) := by
    intro level hlevel
    have h :=
      DifferentialGeometry.Analysis.Measure.level_set_exponential_decay_from_base_real
        μminus hsubMinus hstep hratio_pos hratio_lt hdecayMinus level
    have harg :
        -level * (-Real.log ratio / step) =
          -(-Real.log ratio / step) * level := by
      ring
    rw [harg] at h
    exact h
  exact crossover_of_centered_exponential_tails μplus μminus u hpos hp hpdecay
    (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    hmeasPlus hmeasMinus htailPlus htailMinus

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_le_exponentialTimeRescale
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b : ℝ} (hp : 0 < p) (hrate : 0 ≤ rate) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      Real.exp (center - rate * a) *
        localizedSpacetimeRpowNorm (I := I) (M := M) cutoff
          (exponentialTimeRescale rate center u) p a b := by
  let v := exponentialTimeRescale rate center u
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  apply localizedSpacetimeRpowNorm_le_const_mul_of_ae
    (I := I) (M := M) cutoff u v hu.continuous hv.continuous hpos hvpos
      hp (Real.exp_pos _)
  filter_upwards [ae_localizedSpacetimeMeasure_fst_mem_Ioc
    (I := I) (M := M) cutoff a b] with z hz
  have hfactor : 1 ≤
      Real.exp (center - rate * a) * Real.exp (rate * z.1 - center) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have := mul_nonneg hrate (sub_nonneg.mpr hz.1.le)
    nlinarith
  calc
    u z.1 z.2 = 1 * u z.1 z.2 := (one_mul _).symm
    _ ≤ (Real.exp (center - rate * a) * Real.exp (rate * z.1 - center)) *
        u z.1 z.2 := mul_le_mul_of_nonneg_right hfactor (hpos z.1 z.2).le
    _ = Real.exp (center - rate * a) * v z.1 z.2 := by
      simp only [v, exponentialTimeRescale]
      ring

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_inv_le_exponentialTimeRescale_inv
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b : ℝ} (hp : 0 < p) (hrate : 0 ≤ rate) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff
        (fun t x => (u t x)⁻¹) p a b ≤
      Real.exp (-center + rate * b) *
        localizedSpacetimeRpowNorm (I := I) (M := M) cutoff
          (fun t x => (exponentialTimeRescale rate center u t x)⁻¹) p a b := by
  let v := exponentialTimeRescale rate center u
  let uinv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  let vinv : ℝ → M → ℝ := fun t x => (v t x)⁻¹
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have huinv : Continuous (fun z : ℝ × M => uinv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hvinv : Continuous (fun z : ℝ × M => vinv z.1 z.2) :=
    hv.continuous.inv₀ fun z => (hvpos z.1 z.2).ne'
  change localizedSpacetimeRpowNorm (I := I) (M := M) cutoff uinv p a b ≤
    Real.exp (-center + rate * b) *
      localizedSpacetimeRpowNorm (I := I) (M := M) cutoff vinv p a b
  apply localizedSpacetimeRpowNorm_le_const_mul_of_ae
    (I := I) (M := M) cutoff uinv vinv huinv hvinv
      (fun t x => inv_pos.mpr (hpos t x))
      (fun t x => inv_pos.mpr (hvpos t x)) hp (Real.exp_pos _)
  filter_upwards [ae_localizedSpacetimeMeasure_fst_mem_Ioc
    (I := I) (M := M) cutoff a b] with z hz
  have hfactor : 1 ≤
      Real.exp (-center + rate * b) * Real.exp (center - rate * z.1) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have := mul_nonneg hrate (sub_nonneg.mpr hz.2)
    nlinarith
  have hvinv_eq : vinv z.1 z.2 =
      Real.exp (center - rate * z.1) * uinv z.1 z.2 := by
    dsimp only [vinv, v, uinv, exponentialTimeRescale]
    rw [mul_inv_rev, ← Real.exp_neg,
      show -(rate * z.1 - center) = center - rate * z.1 by ring]
    ring
  rw [hvinv_eq]
  calc
    uinv z.1 z.2 = 1 * uinv z.1 z.2 := (one_mul _).symm
    _ ≤ (Real.exp (-center + rate * b) * Real.exp (center - rate * z.1)) *
        uinv z.1 z.2 :=
      mul_le_mul_of_nonneg_right hfactor (inv_nonneg.mpr (hpos z.1 z.2).le)
    _ = Real.exp (-center + rate * b) *
        (Real.exp (center - rate * z.1) * uinv z.1 z.2) := by ring

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_le_of_exponentialTimeRescale_bound_of_inv_bound
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (x : M) {p a b t D A B : ℝ}
    (hp : 0 < p) (hrate : 0 ≤ rate) (htD : t ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnorm : localizedSpacetimeRpowNorm (I := I) (M := M) cutoff
      (exponentialTimeRescale rate center u) p a b ≤ A)
    (hinv : (exponentialTimeRescale rate center u t x)⁻¹ ≤ B) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      Real.exp (rate * (D - a)) * (A * B) * u t x := by
  let v := exponentialTimeRescale rate center u
  have hvpos : 0 < v t x := exponentialTimeRescale_pos rate center u hpos t x
  have hrescale := localizedSpacetimeRpowNorm_le_exponentialTimeRescale
    (I := I) (M := M) cutoff rate center u hu hpos
      (a := a) (b := b) hp hrate
  have hnorm' : localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      Real.exp (center - rate * a) * A :=
    hrescale.trans (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)
  have hone : 1 ≤ B * v t x := by
    calc
      1 = (v t x)⁻¹ * v t x := (inv_mul_cancel₀ hvpos.ne').symm
      _ ≤ B * v t x := mul_le_mul_of_nonneg_right hinv hvpos.le
  have hfirst : Real.exp (center - rate * a) * A ≤
      Real.exp (center - rate * a) * A * (B * v t x) := by
    calc
      Real.exp (center - rate * a) * A =
          Real.exp (center - rate * a) * A * 1 := (mul_one _).symm
      _ ≤ Real.exp (center - rate * a) * A * (B * v t x) :=
        mul_le_mul_of_nonneg_left hone
          (mul_nonneg (Real.exp_pos _).le hA)
  have hexp : Real.exp (center - rate * a) * A * (B * v t x) =
      Real.exp (rate * (t - a)) * (A * B) * u t x := by
    dsimp only [v, exponentialTimeRescale]
    calc
      Real.exp (center - rate * a) * A *
          (B * (Real.exp (rate * t - center) * u t x)) =
        (Real.exp (center - rate * a) * Real.exp (rate * t - center)) *
          (A * B) * u t x := by ring
      _ = Real.exp ((center - rate * a) + (rate * t - center)) *
          (A * B) * u t x := by rw [Real.exp_add]
      _ = Real.exp (rate * (t - a)) * (A * B) * u t x := by
        congr 1
        ring_nf
  have htime : Real.exp (rate * (t - a)) ≤ Real.exp (rate * (D - a)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (sub_le_sub_right htD a) hrate)
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
        Real.exp (center - rate * a) * A := hnorm'
    _ ≤ Real.exp (center - rate * a) * A * (B * v t x) := hfirst
    _ = Real.exp (rate * (t - a)) * (A * B) * u t x := hexp
    _ ≤ Real.exp (rate * (D - a)) * (A * B) * u t x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htime (mul_nonneg hA hB)) (hpos t x).le

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_mul_inv_le_of_exponentialTimeRescale
    {g : SmoothRiemannianMetric I M}
    (earlyCutoff lateCutoff : SmoothScalar g)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d A : ℝ} (hp : 0 < p) (hrate : 0 ≤ rate)
    (hrescaled :
      localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff
          (exponentialTimeRescale rate center u) p a b *
        localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
          (fun t x => (exponentialTimeRescale rate center u t x)⁻¹) p c d ≤ A) :
    localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff u p a b *
        localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
          (fun t x => (u t x)⁻¹) p c d ≤
      Real.exp (rate * (d - a)) * A := by
  have hearly := localizedSpacetimeRpowNorm_le_exponentialTimeRescale
    (I := I) (M := M) earlyCutoff rate center u hu hpos
      (a := a) (b := b) hp hrate
  have hlate := localizedSpacetimeRpowNorm_inv_le_exponentialTimeRescale_inv
    (I := I) (M := M) lateCutoff rate center u hu hpos
      (a := c) (b := d) hp hrate
  have hrescaledEarlyNonneg := localizedSpacetimeRpowNorm_nonneg
    (I := I) (M := M) earlyCutoff (exponentialTimeRescale rate center u)
      (fun t x => (exponentialTimeRescale_pos rate center u hpos t x).le) p a b
  have hproduct := mul_le_mul hearly hlate
    (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M) lateCutoff
      (fun t x => (u t x)⁻¹) (fun t x => (inv_pos.mpr (hpos t x)).le) p c d)
    (mul_nonneg (Real.exp_pos _).le hrescaledEarlyNonneg)
  have hexp : Real.exp (center - rate * a) * Real.exp (-center + rate * d) =
      Real.exp (rate * (d - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff u p a b *
          localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
            (fun t x => (u t x)⁻¹) p c d ≤
        (Real.exp (center - rate * a) *
          localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff
            (exponentialTimeRescale rate center u) p a b) *
          (Real.exp (-center + rate * d) *
            localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
              (fun t x => (exponentialTimeRescale rate center u t x)⁻¹)
                p c d) := hproduct
    _ = (Real.exp (center - rate * a) * Real.exp (-center + rate * d)) *
        (localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff
            (exponentialTimeRescale rate center u) p a b *
          localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
            (fun t x => (exponentialTimeRescale rate center u t x)⁻¹)
              p c d) := by ring
    _ = Real.exp (rate * (d - a)) *
        (localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff
            (exponentialTimeRescale rate center u) p a b *
          localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
            (fun t x => (exponentialTimeRescale rate center u t x)⁻¹)
              p c d) := by rw [hexp]
    _ ≤ Real.exp (rate * (d - a)) * A :=
      mul_le_mul_of_nonneg_left hrescaled (Real.exp_pos _).le

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_mul_inv_le_of_exponentialTimeRescale_bounds
    {g : SmoothRiemannianMetric I M}
    (earlyCutoff lateCutoff : SmoothScalar g)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d Aplus Aminus : ℝ} (hp : 0 < p) (hrate : 0 ≤ rate)
    (hAplus : 0 ≤ Aplus)
    (hplus : localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff
      (exponentialTimeRescale rate center u) p a b ≤ Aplus)
    (hminus : localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
      (fun t x => (exponentialTimeRescale rate center u t x)⁻¹) p c d ≤ Aminus) :
    localizedSpacetimeRpowNorm (I := I) (M := M) earlyCutoff u p a b *
        localizedSpacetimeRpowNorm (I := I) (M := M) lateCutoff
          (fun t x => (u t x)⁻¹) p c d ≤
      Real.exp (rate * (d - a)) * (Aplus * Aminus) := by
  apply localizedSpacetimeRpowNorm_mul_inv_le_of_exponentialTimeRescale
    (I := I) (M := M) earlyCutoff lateCutoff rate center u hu hpos hp hrate
  exact mul_le_mul hplus hminus
    (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M) lateCutoff
      (fun t x => (exponentialTimeRescale rate center u t x)⁻¹)
      (fun t x => (inv_pos.mpr
        (exponentialTimeRescale_pos rate center u hpos t x)).le) p c d)
    hAplus

theorem weak_harnack_power_of_crossover
    {u A D B C p : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hp : 0 < p)
    (hcrossover : A * D ≤ C)
    (hreciprocal : u⁻¹ ≤ B * D ^ (1 / p)) :
    A ≤ C * B ^ p * u ^ p := by
  have hDne : D ≠ 0 := by
    intro hzero
    subst D
    rw [Real.zero_rpow (div_pos one_pos hp).ne', mul_zero] at hreciprocal
    exact (not_le_of_gt (inv_pos.mpr hu)) hreciprocal
  have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr hu.le) hreciprocal hp.le
  have hrpow' : (u ^ p)⁻¹ ≤ B ^ p * D := by
    rw [Real.inv_rpow hu.le, Real.mul_rpow hB (Real.rpow_nonneg hD _)] at hrpow
    have hpinv : 1 / p = p⁻¹ := one_div p
    rw [hpinv, Real.rpow_inv_rpow hD hp.ne'] at hrpow
    exact hrpow
  have hup : 0 < u ^ p := Real.rpow_pos_of_pos hu p
  have hone : 1 ≤ B ^ p * D * u ^ p := by
    calc
      1 = (u ^ p)⁻¹ * u ^ p := (inv_mul_cancel₀ hup.ne').symm
      _ ≤ (B ^ p * D) * u ^ p :=
        mul_le_mul_of_nonneg_right hrpow' hup.le
      _ = B ^ p * D * u ^ p := rfl
  have hA_le : A ≤ A * (B ^ p * D * u ^ p) := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * (B ^ p * D * u ^ p) := mul_le_mul_of_nonneg_left hone hA
  have hfactor : 0 ≤ B ^ p * u ^ p :=
    mul_nonneg (Real.rpow_nonneg hB _) hup.le
  calc
    A ≤ A * (B ^ p * D * u ^ p) := hA_le
    _ = (A * D) * (B ^ p * u ^ p) := by ring
    _ ≤ C * (B ^ p * u ^ p) :=
      mul_le_mul_of_nonneg_right hcrossover hfactor
    _ = C * B ^ p * u ^ p := by ring

theorem weak_harnack_of_crossover
    {u A D B C p : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hp : 0 < p)
    (hcrossover : A * D ≤ C)
    (hreciprocal : u⁻¹ ≤ B * D ^ (1 / p)) :
    A ^ (1 / p) ≤ C ^ (1 / p) * B * u := by
  have hpower := weak_harnack_power_of_crossover
    hu hA hD hB hp hcrossover hreciprocal
  have hexponent : 0 ≤ 1 / p := (div_pos one_pos hp).le
  have hroot := Real.rpow_le_rpow hA hpower hexponent
  have hup : 0 ≤ u := hu.le
  have hright : 0 ≤ C * B ^ p :=
    mul_nonneg hC (Real.rpow_nonneg hB _)
  rw [show C * B ^ p * u ^ p = (C * B ^ p) * (u ^ p) by ring,
    Real.mul_rpow hright (Real.rpow_nonneg hup _),
    Real.mul_rpow hC (Real.rpow_nonneg hB _)] at hroot
  rw [← Real.rpow_mul hB, ← Real.rpow_mul hup] at hroot
  have hcancel : p * (1 / p) = 1 := by field_simp [hp.ne']
  rw [hcancel, Real.rpow_one, Real.rpow_one] at hroot
  simpa only [mul_assoc] using hroot

end DifferentialGeometry.Analysis.Parabolic.Moser

end
