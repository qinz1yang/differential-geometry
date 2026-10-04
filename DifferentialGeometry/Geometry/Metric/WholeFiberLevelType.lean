import DifferentialGeometry.Topology.Ehresmann.CompactTransverseTransport
import DifferentialGeometry.Geometry.Metric.WholePreimageLocalization

/-! GAF07 (master207B, B:6049), fibre type: the straight-line family `h_τ = (1-τ) η + τ g` from the
original coordinate `η` to the adjusted coordinate `g` on the original chart `Y` is regular at
every level point (least singular value `> 9/10`, i.e. a right inverse of norm `≤ 10/9`, and
`‖Dg - Dη‖ < c₃ < 1/1000`), and all its level points lie in the compact original slab
`{‖η‖ ≤ 4.01 ℓ}`. FC34a (`nonempty_diffeomorph_levelSet_of_compact_transport`) then identifies the
whole adjusted level set with the original one. -/

set_option autoImplicit false
open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace GC.MetricGeometry

/-- A perturbation of an operator with a right inverse stays surjective (finite-dimensional
target). -/
theorem surjective_of_right_inverse_perturbation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T T' : E →L[ℝ] F) (R : F →L[ℝ] E) (hTR : T.comp R = ContinuousLinearMap.id ℝ F)
    (hsmall : ‖T' - T‖ * ‖R‖ < 1) : Surjective T' := by
  let S : F →L[ℝ] F := T'.comp R
  have hS (v : F) : S v = v + (T' - T) (R v) := by
    have h := congrArg (fun A : F →L[ℝ] F => A v) hTR
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    simp only [S, ContinuousLinearMap.comp_apply, sub_apply, h]
    abel
  have hinj : Injective (S : F →ₗ[ℝ] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : S v = 0 := hv
    rw [hS] at hv'
    have heq : v = -((T' - T) (R v)) := eq_neg_of_add_eq_zero_left hv'
    have hle : ‖v‖ ≤ ‖T' - T‖ * ‖R‖ * ‖v‖ := by
      calc ‖v‖ = ‖(T' - T) (R v)‖ := by rw [heq, norm_neg]; rw [← heq]
        _ ≤ ‖T' - T‖ * ‖R v‖ := (T' - T).le_opNorm _
        _ ≤ ‖T' - T‖ * (‖R‖ * ‖v‖) := mul_le_mul_of_nonneg_left (R.le_opNorm _) (norm_nonneg _)
        _ = ‖T' - T‖ * ‖R‖ * ‖v‖ := by ring
    by_contra hne
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
    nlinarith
  have hsurj : Surjective (S : F →ₗ[ℝ] F) := LinearMap.injective_iff_surjective.mp hinj
  intro y
  obtain ⟨w, hw⟩ := hsurj y
  exact ⟨R w, hw⟩

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y]

theorem contMDiff_straightLine {η g : Y → F} (hη : ContMDiff I 𝓘(ℝ, F) ∞ η)
    (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) :
    ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ (fun x : Y × ℝ => (1 - x.2) • η x.1 + x.2 • g x.1) :=
  ((contMDiff_const.sub contMDiff_snd).smul (hη.comp contMDiff_fst)).add
    (contMDiff_snd.smul (hg.comp contMDiff_fst))

/-- Every slice of the straight-line family is regular at every point. -/
theorem straightLine_slice_regular [FiniteDimensional ℝ F] {η g : Y → F} (hη : ContMDiff I 𝓘(ℝ, F) ∞ η)
    (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) {c₃ : ℝ} (hc₃ : c₃ < 1 / 1000)
    (hright : ∀ y, ∃ R : F →L[ℝ] E,
      (mfderiv I 𝓘(ℝ, F) η y : E →L[ℝ] F).comp R = ContinuousLinearMap.id ℝ F ∧ ‖R‖ ≤ 10 / 9)
    (hDg : ∀ y, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y)‖ < c₃) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y : Y,
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => (1 - τ) • η z + τ • g z) y) := by
  intro τ hτ y
  have hηd : HasMFDerivAt I 𝓘(ℝ, F) η y (mfderiv I 𝓘(ℝ, F) η y) :=
    (hη.mdifferentiableAt (by simp)).hasMFDerivAt
  have hgd : HasMFDerivAt I 𝓘(ℝ, F) g y (mfderiv I 𝓘(ℝ, F) g y) :=
    (hg.mdifferentiableAt (by simp)).hasMFDerivAt
  have hd := (hηd.const_smul (1 - τ)).add (hgd.const_smul τ)
  rw [show (fun z => (1 - τ) • η z + τ • g z) = (1 - τ) • η + τ • g from rfl, hd.mfderiv]
  obtain ⟨R, hR, hRn⟩ := hright y
  set Dη : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) η y
  set Dg : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) g y
  apply surjective_of_right_inverse_perturbation Dη ((1 - τ) • Dη + τ • Dg) R hR
  have hdiff : (1 - τ) • Dη + τ • Dg - Dη = τ • (Dg - Dη) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  have h1 : τ * ‖Dg - Dη‖ < 1 / 1000 := by
    have := mul_le_of_le_one_left (norm_nonneg (Dg - Dη)) hτ.2
    have hD : ‖Dg - Dη‖ < c₃ := hDg y
    linarith
  have h2 := mul_le_mul_of_nonneg_left hRn (mul_nonneg hτ.1 (norm_nonneg (Dg - Dη)))
  nlinarith [norm_nonneg R]

variable [IsManifold I ∞ Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless]
  [T2Space Y] [SigmaCompactSpace Y]

/-- GAF07 fibre type: the WHOLE adjusted level set `g⁻¹(a)` is homeomorphic (indeed
diffeomorphic, by FC34a) to the original level set `η⁻¹(a)` of the SAME original coordinate. -/
theorem nonempty_homeomorph_level_of_straightLine {η g : Y → F}
    (hη : ContMDiff I 𝓘(ℝ, F) ∞ η) (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) {a : F} {ℓ c₃ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hc₃ : c₃ < 1 / 1000)
    (hgη : ∀ y, ‖g y - η y‖ < 1 / 800)
    (hright : ∀ y, ∃ R : F →L[ℝ] E,
      (mfderiv I 𝓘(ℝ, F) η y : E →L[ℝ] F).comp R = ContinuousLinearMap.id ℝ F ∧ ‖R‖ ≤ 10 / 9)
    (hDg : ∀ y, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y)‖ < c₃)
    (hQ : IsCompact {y | ‖η y‖ ≤ 401 / 100 * ℓ}) :
    Nonempty ({y | η y = a} ≃ₜ {y | g y = a}) := by
  let h : Y × ℝ → F := fun x => (1 - x.2) • η x.1 + x.2 • g x.1
  have hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h := contMDiff_straightLine hη hg
  have hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y) :=
    fun τ hτ y _ => straightLine_slice_regular hη hg hc₃ hright hDg τ hτ y
  have hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → y ∈ {y | ‖η y‖ ≤ 401 / 100 * ℓ} :=
    fun τ hτ y hy => (norm_lt_of_level_of_straight_line hτ hℓ ha (hgη y) hy).le
  let _ := regularFiberChartedSpace (fun y => h (y, 0)) a (contMDiff_familySlice hh 0)
    (hreg 0 (left_mem_Icc.mpr zero_le_one))
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a (contMDiff_familySlice hh 1)
    (hreg 1 (right_mem_Icc.mpr zero_le_one))
  obtain ⟨φ⟩ := nonempty_diffeomorph_levelSet_of_compact_transport h hh a hreg hQ hloc
  have h0 : {y | h (y, 0) = a} = {y | η y = a} := by
    ext y
    change (1 - 0 : ℝ) • η y + (0 : ℝ) • g y = a ↔ η y = a
    rw [sub_zero, one_smul, zero_smul, add_zero]
  have h1 : {y | h (y, 1) = a} = {y | g y = a} := by
    ext y
    change (1 - 1 : ℝ) • η y + (1 : ℝ) • g y = a ↔ g y = a
    rw [sub_self, zero_smul, one_smul, zero_add]
  exact ⟨((Homeomorph.setCongr h0).symm.trans φ.toHomeomorph).trans (Homeomorph.setCongr h1)⟩

end GC.MetricGeometry
