import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Truncated ratio-of-integrals inequality

Pure measure-theoretic input for capped relative Bishop–Gromov volume
comparison (brick B4 of the A0′ volume lane).  For two `ℝ≥0∞`-valued densities
`f g` on a window `(0, R]` whose cross products satisfy `f b * g a ≤ f a * g b`
for `0 < a ≤ b ≤ R` — the division-free encoding of "`f / g` is antitone" — the
truncated integrals obey

`(∫ f over (0,R]) * (∫ g over (0,s]) ≤ (∫ f over (0,s]) * (∫ g over (0,R])`

for every `0 ≤ s ≤ R`.  The multiplicative `ℝ≥0∞` form sidesteps division and
integrability side conditions.

The file also provides the two feeder lemmas used downstream: `crossAnti_ofReal`
translates the antitone real ratio produced by the radial density comparison
into the `CrossAnti` predicate, and `crossAnti_indicator` shows the predicate is
stable under cutting the numerator density off above any threshold (the cut-time
truncation).  No geometry is imported.
-/

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}

/-- Division-free `ℝ≥0∞` form of "`f / g` is antitone on `(0, R]`":
`f b * g a ≤ f a * g b` whenever `0 < a ≤ b ≤ R`. -/
def CrossAnti (R : ℝ) (f g : ℝ → ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b

/-- Truncated ratio-of-integrals inequality: if `f g` are cross-antitone on the
window `(0, R]` (i.e. `f / g` is antitone there) and `0 ≤ s ≤ R`, then
`(∫ f over (0,R]) * (∫ g over (0,s]) ≤ (∫ f over (0,s]) * (∫ g over (0,R])`. -/
theorem lintegral_cross_le {s : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0:ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0:ℝ) R)))
    (hcross : CrossAnti R f g) (hs : 0 ≤ s) (hsR : s ≤ R) :
    (∫⁻ t in Ioc (0:ℝ) R, f t ∂μ) * (∫⁻ t in Ioc (0:ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0:ℝ) s, f t ∂μ) * ∫⁻ t in Ioc (0:ℝ) R, g t ∂μ := by
  have hAm : MeasurableSet (Ioc (0:ℝ) s) := measurableSet_Ioc
  have hBm : MeasurableSet (Ioc s R) := measurableSet_Ioc
  have hdisj : Disjoint (Ioc (0:ℝ) s) (Ioc s R) := Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Ioc (0:ℝ) s ∪ Ioc s R = Ioc (0:ℝ) R := Ioc_union_Ioc_eq_Ioc hs hsR
  have hAsub : Ioc (0:ℝ) s ⊆ Ioc (0:ℝ) R := Ioc_subset_Ioc le_rfl hsR
  have hBsub : Ioc s R ⊆ Ioc (0:ℝ) R := Ioc_subset_Ioc hs le_rfl
  have hfA : AEMeasurable f (μ.restrict (Ioc (0:ℝ) s)) :=
    hf.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hfB : AEMeasurable f (μ.restrict (Ioc s R)) :=
    hf.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hgA : AEMeasurable g (μ.restrict (Ioc (0:ℝ) s)) :=
    hg.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hgB : AEMeasurable g (μ.restrict (Ioc s R)) :=
    hg.mono_measure (Measure.restrict_mono hBsub le_rfl)
  -- Additive split of each `(0,R]`-integral into the `(0,s]` and `(s,R]` pieces.
  have hf_split : ∫⁻ t in Ioc (0:ℝ) R, f t ∂μ
      = (∫⁻ t in Ioc (0:ℝ) s, f t ∂μ) + ∫⁻ t in Ioc s R, f t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  have hg_split : ∫⁻ t in Ioc (0:ℝ) R, g t ∂μ
      = (∫⁻ t in Ioc (0:ℝ) s, g t ∂μ) + ∫⁻ t in Ioc s R, g t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  -- Off-diagonal cross claim on `(0,s] × (s,R]`, compared pointwise by `hcross`.
  have hstar : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0:ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0:ℝ) s, f t ∂μ) * ∫⁻ t in Ioc s R, g t ∂μ := by
    have e1 : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0:ℝ) s, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0:ℝ) s, f b * g a ∂μ ∂μ := by
      rw [← lintegral_mul_const'' _ hfB]
      exact lintegral_congr fun b => (lintegral_const_mul'' _ hgA).symm
    have e2 : (∫⁻ t in Ioc (0:ℝ) s, f t ∂μ) * (∫⁻ t in Ioc s R, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0:ℝ) s, f a * g b ∂μ ∂μ := by
      rw [← lintegral_const_mul'' _ hgB]
      exact lintegral_congr fun b => (lintegral_mul_const'' _ hfA).symm
    rw [e1, e2]
    refine lintegral_mono_ae ((ae_restrict_mem hBm).mono fun b hb => ?_)
    exact lintegral_mono_ae ((ae_restrict_mem hAm).mono fun a ha =>
      hcross a b ha.1 (ha.2.trans hb.1.le) hb.2)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar

/-- Bridge from the antitone real ratio produced by the radial density
comparison: if `F / G` is antitone on `(0, R]` with `F` nonnegative and `G`
positive there, then the `ℝ≥0∞`-valued densities `ofReal ∘ F`, `ofReal ∘ G` are
cross-antitone. -/
theorem crossAnti_ofReal {F G : ℝ → ℝ}
    (hanti : AntitoneOn (fun t => F t / G t) (Ioc (0:ℝ) R))
    (hF : ∀ ⦃t⦄, t ∈ Ioc (0:ℝ) R → 0 ≤ F t)
    (hG : ∀ ⦃t⦄, t ∈ Ioc (0:ℝ) R → 0 < G t) :
    CrossAnti R (fun t => ENNReal.ofReal (F t)) (fun t => ENNReal.ofReal (G t)) := by
  intro a b ha hab hbR
  have hbmem : b ∈ Ioc (0:ℝ) R := ⟨ha.trans_le hab, hbR⟩
  have hamem : a ∈ Ioc (0:ℝ) R := ⟨ha, hab.trans hbR⟩
  have hdiv : F b / G b ≤ F a / G a := hanti hamem hbmem hab
  have hcross : F b * G a ≤ F a * G b :=
    (div_le_div_iff₀ (hG hbmem) (hG hamem)).1 hdiv
  calc ENNReal.ofReal (F b) * ENNReal.ofReal (G a)
      = ENNReal.ofReal (F b * G a) := (ENNReal.ofReal_mul (hF hbmem)).symm
    _ ≤ ENNReal.ofReal (F a * G b) := ENNReal.ofReal_le_ofReal hcross
    _ = ENNReal.ofReal (F a) * ENNReal.ofReal (G b) := ENNReal.ofReal_mul (hF hamem)

/-- Truncation stability: cross-antitonicity is preserved when the numerator
density `f` is cut off above a threshold `τ`.  Downstream this inserts the
per-direction cut time into the numerator. -/
theorem crossAnti_indicator (h : CrossAnti R f g) (τ : ℝ) :
    CrossAnti R (Set.indicator (Iio τ) f) g := by
  intro a b ha hab hbR
  by_cases hbτ : b ∈ Iio τ
  · have haτ : a ∈ Iio τ := lt_of_le_of_lt hab hbτ
    rw [Set.indicator_of_mem hbτ, Set.indicator_of_mem haτ]
    exact h a b ha hab hbR
  · rw [Set.indicator_of_notMem hbτ, zero_mul]
    exact zero_le _

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
