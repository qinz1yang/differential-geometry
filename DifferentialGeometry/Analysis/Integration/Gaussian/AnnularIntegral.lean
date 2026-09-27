import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set

private theorem radial_inner_annuli_cover {X : Type*} (d : X → ℝ)
    {r : ℝ} (hr : 0 < r) :
    {x | d x < r} ∪
      (⋃ j : ℕ, {x | r * ((j : ℝ) + 1) ≤ d x ∧ d x < r * ((j : ℝ) + 2)}) = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : d x < r
    · exact Or.inl hx
    · have hdr : r ≤ d x := le_of_not_gt hx
      have hratio : 1 ≤ d x / r := (le_div_iff₀ hr).mpr (by simpa using hdr)
      have hfloor : 1 ≤ ⌊d x / r⌋₊ := (Nat.one_le_floor_iff _).mpr hratio
      let j : ℕ := ⌊d x / r⌋₊ - 1
      have hj : (j : ℝ) + 1 = (⌊d x / r⌋₊ : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hfloor
      have hlower : r * ((j : ℝ) + 1) ≤ d x := by
        rw [hj, mul_comm]
        exact (le_div_iff₀ hr).mp (Nat.floor_le (by linarith))
      have hupper : d x < r * ((j : ℝ) + 2) := by
        calc
          d x < ((⌊d x / r⌋₊ : ℝ) + 1) * r :=
            (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (d x / r))
          _ = r * ((j : ℝ) + 2) := by rw [← hj]; ring
      exact Or.inr (mem_iUnion.mpr ⟨j, hlower, hupper⟩)


theorem radial_lintegral_le_inner_add_annuli
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (d : X → ℝ)
    {r : ℝ} (hr : 0 < r) (f : X → ENNReal) (inner : ENNReal) (annular : ℕ → ENNReal)
    (hinner : ∀ x, d x < r → f x ≤ inner)
    (hannular : ∀ j : ℕ, ∀ x, r * ((j : ℝ) + 1) ≤ d x →
      d x < r * ((j : ℝ) + 2) → f x ≤ annular j) :
    (∫⁻ x, f x ∂mu) ≤ inner * mu {x | d x < r} +
      ∑' j : ℕ, annular j * mu {x | r * ((j : ℝ) + 1) ≤ d x ∧
        d x < r * ((j : ℝ) + 2)} := by
  let A : ℕ → Set X := fun j =>
    {x | r * ((j : ℝ) + 1) ≤ d x ∧ d x < r * ((j : ℝ) + 2)}
  have hfirst : (∫⁻ x in {x | d x < r}, f x ∂mu) ≤ inner * mu {x | d x < r} := by
    have h := setLIntegral_mono (μ := mu) (s := {x | d x < r}) measurable_const hinner
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  have hshell (j : ℕ) : (∫⁻ x in A j, f x ∂mu) ≤ annular j * mu (A j) := by
    have h := setLIntegral_mono (μ := mu) (s := A j) measurable_const
      (fun x hx => hannular j x hx.1 hx.2)
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  calc
    (∫⁻ x, f x ∂mu) = ∫⁻ x in {x | d x < r} ∪ ⋃ j, A j, f x ∂mu := by
      rw [radial_inner_annuli_cover d hr, Measure.restrict_univ]
    _ ≤ (∫⁻ x in {x | d x < r}, f x ∂mu) + ∫⁻ x in ⋃ j, A j, f x ∂mu :=
      lintegral_union_le f _ _
    _ ≤ inner * mu {x | d x < r} + ∑' j, annular j * mu (A j) :=
      add_le_add hfirst ((lintegral_iUnion_le A f).trans (ENNReal.tsum_le_tsum hshell))

private theorem gaussian_cost_annular_bound {X : Type*}
    (d ell : X → ℝ) {r theta B : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    (hcoercive : ∀ x, collapsedVolumeChi * (d x) ^ 2 / (theta * r ^ 2) - B ≤ ell x)
    (j : ℕ) (x : X) (hx : r * ((j : ℝ) + 1) ≤ d x) :
    Real.exp (-ell x) ≤ Real.exp B *
      Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hradial : 0 ≤ r * ((j : ℝ) + 1) := by positivity
  have hsquare := pow_le_pow_left₀ hradial hx 2
  have hratio : ((j : ℝ) + 1) ^ 2 / theta ≤ (d x) ^ 2 / (theta * r ^ 2) := by
    apply (div_le_div_iff₀ htheta (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare htheta.le]
  have hscaled : collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta ≤
      collapsedVolumeChi * (d x) ^ 2 / (theta * r ^ 2) := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hratio collapsedVolumeChi_pos.le
  have hcost := hcoercive x
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_mul, neg_div]
  linarith


theorem gaussian_lintegral_le_inner_add_cubic_tail
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (d ell : X → ℝ)
    {r theta A B v W : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hnonneg : ∀ x, 0 ≤ ell x)
    (hcoercive : ∀ x, collapsedVolumeChi * (d x) ^ 2 / (theta * r ^ 2) - B ≤ ell x)
    (hinnerVolume : mu {x | d x < r} ≤ ENNReal.ofReal (v * r ^ 3))
    (houterVolume : ∀ j : ℕ,
      mu {x | d x < r * ((j : ℝ) + 2)} ≤ ENNReal.ofReal (W * ((j : ℝ) + 2) ^ 3 * r ^ 3)) :
    (∫⁻ x, ENNReal.ofReal (A * Real.exp (-ell x)) ∂mu) ≤
      ENNReal.ofReal (A * v * r ^ 3) +
        ENNReal.ofReal (A * Real.exp B * W * r ^ 3 *
          ∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
            Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) := by
  let a : ℕ → ENNReal := fun j => ENNReal.ofReal
    (A * Real.exp B * Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta))
  have hsum := radial_lintegral_le_inner_add_annuli mu d hr
    (fun x => ENNReal.ofReal (A * Real.exp (-ell x))) (ENNReal.ofReal A) a
    (fun x _hx => ENNReal.ofReal_le_ofReal (by
      have he : Real.exp (-ell x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hnonneg x])
      nlinarith [mul_le_mul_of_nonneg_left he hA]))
    (fun j x hx _hupper => ENNReal.ofReal_le_ofReal (by
      have h := mul_le_mul_of_nonneg_left
        (gaussian_cost_annular_bound d ell hr htheta hcoercive j x hx) hA
      simpa only [mul_assoc] using h))
  apply hsum.trans
  apply add_le_add
  · have h := mul_le_mul_of_nonneg_left hinnerVolume (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal A)
    simpa only [← ENNReal.ofReal_mul hA, mul_assoc] using h
  · have hterm (j : ℕ) :
        a j * mu {x | r * ((j : ℝ) + 1) ≤ d x ∧ d x < r * ((j : ℝ) + 2)} ≤
        ENNReal.ofReal (A * Real.exp B * W * r ^ 3) * ENNReal.ofReal
          (((j : ℝ) + 2) ^ 3 * Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) := by
      have hvolume : mu {x | r * ((j : ℝ) + 1) ≤ d x ∧ d x < r * ((j : ℝ) + 2)} ≤
          ENNReal.ofReal (W * ((j : ℝ) + 2) ^ 3 * r ^ 3) :=
        (measure_mono (fun _ hx => hx.2)).trans (houterVolume j)
      have h := mul_le_mul_of_nonneg_left hvolume (bot_le : (0 : ENNReal) ≤ a j)
      dsimp only [a] at h ⊢
      rw [← ENNReal.ofReal_mul (by positivity)] at h
      rw [← ENNReal.ofReal_mul (by positivity)]
      convert h using 1 <;> congr 1
      ring
    have h := ENNReal.tsum_le_tsum hterm
    rw [ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        (collapsedVolumeTail_summable htheta),
      ← ENNReal.ofReal_mul (by positivity)] at h
    exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
