import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

private def stretchTransition (s t : ℝ) : ℝ :=
  Real.smoothTransition ((t - s / 3) / (s / 3))

/-- A relative height stretch, smooth on `(-∞,s)`, which fixes heights at
most `s/3` and tends to infinity at the finite upper endpoint. -/
def halfLineStretch (s t : ℝ) : ℝ :=
  t + stretchTransition s t * (t ^ 2 / (s - t))

private theorem contDiff_stretchTransition (s : ℝ) :
    ContDiff ℝ ∞ (stretchTransition s) := by
  unfold stretchTransition
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)

private theorem stretchTransition_zero {s t : ℝ} (hs : 0 < s)
    (ht : t ≤ s / 3) : stretchTransition s t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))

private theorem stretchTransition_one {s t : ℝ} (hs : 0 < s)
    (ht : 2 * s / 3 ≤ t) : stretchTransition s t = 1 :=
  Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (by positivity : 0 < s / 3)).mpr (by linarith))

private theorem stretchTransition_monotone {s : ℝ} (hs : 0 < s) :
    Monotone (stretchTransition s) :=
  Real.smoothTransition.monotone.comp fun _ _ hxy =>
    div_le_div_of_nonneg_right (sub_le_sub_right hxy _) (by positivity)

private theorem stretch_eq_self {s t : ℝ} (hs : 0 < s) (ht : t ≤ s / 3) :
    halfLineStretch s t = t := by
  rw [halfLineStretch, stretchTransition_zero hs ht, zero_mul, add_zero]

private theorem stretch_eq_tail {s t : ℝ} (hs : 0 < s)
    (ht : 2 * s / 3 ≤ t) (hts : t < s) :
    halfLineStretch s t = s * t / (s - t) := by
  rw [halfLineStretch, stretchTransition_one hs ht, one_mul]
  field_simp [(sub_pos.mpr hts).ne']
  ring

private theorem contDiffAt_stretch {s t : ℝ} (ht : t < s) :
    ContDiffAt ℝ ∞ (halfLineStretch s) t :=
  contDiffAt_id.add ((contDiff_stretchTransition s).contDiffAt.mul
    ((contDiffAt_id.pow 2).div (contDiffAt_const.sub contDiffAt_id)
      (sub_pos.mpr ht).ne'))

private theorem hasDerivAt_stretch {s t : ℝ} (ht : t < s) :
    HasDerivAt (halfLineStretch s)
      (1 + deriv (stretchTransition s) t * (t ^ 2 / (s - t)) +
        stretchTransition s t * (t * (2 * s - t) / (s - t) ^ 2)) t := by
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 / (s - y))
      (t * (2 * s - t) / (s - t) ^ 2) t := by
    have hquot := ((hasDerivAt_id t).fun_pow 2).fun_div
      ((hasDerivAt_const t s).fun_sub (hasDerivAt_id t)) (sub_pos.mpr ht).ne'
    simp only [id_eq] at hquot
    (convert hquot using 1; first | rfl | ring)
  have hχ := ((contDiff_stretchTransition s).differentiable (by simp) t).hasDerivAt
  convert (hasDerivAt_id t).add (hχ.mul hq) using 1 <;> first | rfl | ring

private theorem stretch_deriv_pos {s : ℝ} (hs : 0 < s)
    {t : ℝ} (ht : t < s) : 0 < deriv (halfLineStretch s) t := by
  rw [(hasDerivAt_stretch ht).deriv]
  have hχ : 0 ≤ stretchTransition s t := Real.smoothTransition.nonneg _
  by_cases hlo : t ≤ s / 3
  · have hmin : IsLocalMin (stretchTransition s) t :=
      Filter.Eventually.of_forall fun y => by
        change stretchTransition s t ≤ stretchTransition s y
        rw [stretchTransition_zero hs hlo]
        exact Real.smoothTransition.nonneg _
    rw [hmin.deriv_eq_zero, stretchTransition_zero hs hlo]
    norm_num
  · have htpos : 0 < t := by linarith [lt_of_not_ge hlo]
    have hχd : 0 ≤ deriv (stretchTransition s) t :=
      (stretchTransition_monotone hs).deriv_nonneg
    have hq : 0 ≤ t ^ 2 / (s - t) :=
      div_nonneg (sq_nonneg t) (sub_pos.mpr ht).le
    have hq' : 0 ≤ t * (2 * s - t) / (s - t) ^ 2 :=
      div_nonneg (mul_nonneg htpos.le (by linarith)) (sq_nonneg _)
    linarith [mul_nonneg hχd hq, mul_nonneg hχ hq']

private theorem stretch_strictMonoOn {s : ℝ} (hs : 0 < s) :
    StrictMonoOn (halfLineStretch s) (Iio s) :=
  strictMonoOn_of_deriv_pos (convex_Iio s)
    (fun _ ht => (contDiffAt_stretch ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      have hts : t ∈ Iio s := interior_subset ht
      exact stretch_deriv_pos hs hts)

private theorem stretch_surjective {s : ℝ} (hs : 0 < s) (y : ℝ) :
    ∃ t, t < s ∧ halfLineStretch s t = y := by
  let l := min (y - 1) (s / 3)
  let r := s * (|y| + 2 * s) / (s + (|y| + 2 * s))
  have hd : 0 < s + (|y| + 2 * s) := by positivity
  have hrlow : 2 * s / 3 ≤ r := by
    dsimp only [r]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg hs.le (abs_nonneg y)]
  have hrs : r < s := by
    dsimp only [r]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [sq_pos_of_pos hs]
  have hlr : l ≤ r := by
    dsimp only [l]
    linarith [min_le_right (y - 1) (s / 3)]
  have hfl : halfLineStretch s l = l := stretch_eq_self hs (min_le_right _ _)
  have hfr : halfLineStretch s r = |y| + 2 * s := by
    rw [stretch_eq_tail hs hrlow hrs]
    apply (div_eq_iff (sub_pos.mpr hrs).ne').mpr
    dsimp only [r]
    field_simp [hd.ne']
    ring
  have hcont : ContinuousOn (halfLineStretch s) (Icc l r) := fun t ht =>
    (contDiffAt_stretch (ht.2.trans_lt hrs)).continuousAt.continuousWithinAt
  have hbetween : y ∈ Icc (halfLineStretch s l) (halfLineStretch s r) := by
    rw [hfl, hfr]
    constructor
    · dsimp only [l]
      linarith [min_le_left (y - 1) (s / 3)]
    · linarith [le_abs_self y]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hlr hcont hbetween
  exact ⟨t, ht.2.trans_lt hrs, hft⟩

/-- Stretch a finite upper height to infinity while fixing a neighborhood of
zero. The original real coordinate, its order, and both inverse laws are
retained in the bundled smooth diffeomorphism. -/
theorem exists_diffeomorph_Iio_eq_halfLineStretch {s : ℝ} (hs : 0 < s) :
    ∃ D : Diffeomorph 𝓘(ℝ) 𝓘(ℝ)
      (⟨Iio s, isOpen_Iio⟩ : TopologicalSpace.Opens ℝ) ℝ ∞,
      (∀ x, D x = halfLineStretch s x.val) ∧ StrictMono D ∧
      (∀ x, x.val ≤ s / 3 → D x = x.val) ∧
      (∀ y, y ≤ s / 3 → (D.symm y).val = y) ∧
      (∀ y, 0 ≤ (D.symm y).val ↔ 0 ≤ y) ∧
      (∀ x, 2 * s / 3 ≤ x.val → D x = s * x.val / (s - x.val)) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Iio s, isOpen_Iio⟩
  let f : U → ℝ := fun x => halfLineStretch s x.val
  have hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ f := by
    intro x
    change ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun y : U => halfLineStretch s y.val) x
    rw [contMDiffAt_subtype_iff]
    exact (contDiffAt_stretch x.property).contMDiffAt
  have hmono : StrictMono f := fun x y hxy =>
    stretch_strictMonoOn hs x.property y.property hxy
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht, hft⟩ := stretch_surjective hs y
    exact ⟨⟨t, ht⟩, hft⟩
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ f := by
    intro x
    have hp : 0 < deriv (halfLineStretch s) x.val := stretch_deriv_pos hs x.property
    let A := ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 (deriv (halfLineStretch s) x.val) hp.ne')
    have ha : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (halfLineStretch s) x.val
        (A : ℝ →L[ℝ] ℝ) := by
      have hd := ((contDiffAt_stretch x.property).differentiableAt (by simp)).hasDerivAt
      exact (hd.hasFDerivAt_equiv hp.ne').hasMFDerivAt
    have hfa : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) f x (A : ℝ →L[ℝ] ℝ) := by
      have hcomp := ha.comp x (hasMFDerivAt_subtype_val (I := 𝓘(ℝ)) U x)
      change HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) f x
        ((A : ℝ →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ ℝ)) at hcomp
      have hid : (A : ℝ →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ ℝ) =
          (A : ℝ →L[ℝ] ℝ) := ContinuousLinearMap.comp_id _
      exact hid ▸ hcomp
    exact Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv f hf x A hfa
  let D := hlocal.diffeomorphOfBijective ⟨hmono.injective, hsurj⟩
  have hD (x : U) : D x = halfLineStretch s x.val := rfl
  have hDmono : StrictMono D := hmono
  have hsmall (x : U) (hx : x.val ≤ s / 3) : D x = x.val :=
    (hD x).trans (stretch_eq_self hs hx)
  have hinv (y : ℝ) (hy : y ≤ s / 3) : (D.symm y).val = y := by
    have hys : y < s := by linarith
    have hyU : y ∈ U := hys
    have hpoint : D.symm y = (⟨y, hyU⟩ : U) := by
      calc
        D.symm y = D.symm (D (⟨y, hyU⟩ : U)) :=
          congrArg D.symm (hsmall (⟨y, hyU⟩ : U) hy).symm
        _ = _ := D.symm_apply_apply _
    exact congrArg Subtype.val hpoint
  refine ⟨D, hD, hDmono, hsmall, hinv, ?_, ?_⟩
  · intro y
    have hzU : (0 : ℝ) ∈ U := hs
    let z : U := ⟨0, hzU⟩
    have hzero : D z = 0 := hsmall z (by change 0 ≤ s / 3; positivity)
    calc
      0 ≤ (D.symm y).val ↔ z ≤ D.symm y := Iff.rfl
      _ ↔ D z ≤ D (D.symm y) := hDmono.le_iff_le.symm
      _ ↔ 0 ≤ y := by rw [hzero, D.apply_symm_apply]
  · intro x hx
    exact (hD x).trans (stretch_eq_tail hs hx x.property)

end DifferentialGeometry.Analysis
