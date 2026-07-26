import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatD1GaussianSplit
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxKern
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateTail

/-!
# Gaussian tails for the terminal Koch--Lamm flux kernel

The split first-derivative Gaussian is scaled without changing the exact
parabolic power appearing in `klD1Exp`.  This file then integrates its
off-diagonal factor on a selected terminal spatial set.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Scaled half-Gaussian remainder for the first heat-derivative majorant. -/
def heatD1Half (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1Half ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The scaled half-Gaussian remainder is nonnegative. -/
theorem heatD1Half_nonneg (t : ℝ) (x : V) : 0 ≤ heatD1Half t x := by
  unfold heatD1Half
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (baseD1Half_nonneg (V := V) _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise power factorization of the scaled half-Gaussian remainder. -/
theorem heatD1Half_pow {t p : ℝ} (ht : 0 < t) (x : V) :
    (heatD1Half t x) ^ p =
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
        (baseD1Half ((heatScale t)⁻¹ • x)) ^ p := by
  unfold heatD1Half
  rw [Real.mul_rpow
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD1Half_nonneg (V := V) _)]

/-- The scaled half-Gaussian remainder has an integrable real `p`-th power. -/
theorem heatD1Half_rpow {t p : ℝ} (ht : 0 < t)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Integrable (fun x : V ↦ (heatD1Half t x) ^ p) := by
  simp_rw [heatD1Half_pow (V := V) ht]
  exact ((baseD1Half_rpow (V := V) hp1 hp2).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne')).const_mul _

omit [Nontrivial V] in
/-- The translated half-Gaussian power mass has the same exact parabolic
scale exponent as the full first-derivative majorant. -/
theorem heatD1Half_shift {t p : ℝ} (ht : 0 < t) (x : V) :
    ∫ y : V, (heatD1Half t (x - y)) ^ p =
      t ^ (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
        baseD1HalfMass V p := by
  rw [integral_sub_left_eq_self
    (fun y : V ↦ (heatD1Half t y) ^ p) (volume : Measure V) x]
  simp_rw [heatD1Half_pow (V := V) ht]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
      (fun y : V ↦ (baseD1Half y) ^ p) (heatScale_pos ht).le]
  simp only [smul_eq_mul, baseD1HalfMass]
  calc
    ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
          ((heatScale t) ^ Module.finrank ℝ V * baseD1HalfMass V p) =
        (((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
          (heatScale t) ^ Module.finrank ℝ V) * baseD1HalfMass V p := by ring
    _ = t ^ (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
        baseD1HalfMass V p := by rw [heatD1Pow_scale (V := V) ht]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- A scaled distance lower bound extracts the Gaussian factor from the
first-derivative majorant power. -/
theorem heatD1Tail_pow {t k p : ℝ} (ht : 0 < t) (hk : 0 ≤ k)
    (hp : 0 ≤ p) {x : V}
    (hx : k ≤ ‖(heatScale t)⁻¹ • x‖) :
    (heatD1Maj t x) ^ p ≤
      (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
        (heatD1Half t x) ^ p := by
  have hbase := baseD1Tail_pow (V := V) hk hp hx
  rw [heatD1Maj_pow (V := V) ht, heatD1Half_pow (V := V) ht]
  have hfront : 0 ≤
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale t)⁻¹) ^ p) :=
    Real.rpow_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (heatScale_pos ht).le)) p
  calc
    ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
          (baseD1Maj ((heatScale t)⁻¹ • x)) ^ p ≤
        ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
          ((Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
            (baseD1Half ((heatScale t)⁻¹ • x)) ^ p) :=
      mul_le_mul_of_nonneg_left hbase hfront
    _ = (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
        (((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
            (baseD1Half ((heatScale t)⁻¹ • x)) ^ p) := by ring

/-- Spatial first-derivative power on one selected terminal slice, with a
far-field Gaussian factor and the unchanged parabolic scale exponent. -/
theorem klFluxSlice_pow {R k s p : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hs : s ∈ Ioc (R ^ 2 / 2) (R ^ 2)) (hst : s ≠ R ^ 2)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ y : V, (heatD1Maj (R ^ 2 - s) (x - y)) ^ p
      ∂(volume : Measure V).restrict S) ≤
      (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
        ((R ^ 2 - s) ^
          (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
            baseD1HalfMass V p) := by
  let u : ℝ := R ^ 2 - s
  let D : ℝ := (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p
  have hu : 0 < u := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  have hp0 : 0 ≤ p := zero_le_one.trans hp1
  have hmajor : Integrable
      (fun y : V ↦ (heatD1Maj u (x - y)) ^ p)
      ((volume : Measure V).restrict S) := by
    have hfull : Integrable (fun y : V ↦ (heatD1Maj u y) ^ p) := by
      simp_rw [heatD1Maj_pow (V := V) hu]
      exact ((baseD1Maj_rpow (V := V) hp1 hp2).comp_smul
        (inv_ne_zero (heatScale_pos hu).ne')).const_mul _
    exact (hfull.comp_sub_left x).mono_measure Measure.restrict_le_self
  have hhalf : Integrable
      (fun y : V ↦ D * (heatD1Half u (x - y)) ^ p) :=
    ((heatD1Half_rpow (V := V) hu hp1 hp2).comp_sub_left x).const_mul _
  have hpoint :
      (fun y : V ↦ (heatD1Maj u (x - y)) ^ p) ≤ᵐ[
        (volume : Measure V).restrict S]
      (fun y : V ↦ D * (heatD1Half u (x - y)) ^ p) := by
    filter_upwards [ae_restrict_mem hSm] with y hy
    have hstrong := klTerm_scaled (V := V) hR hk hs hst (hfar y hy)
    have hkroot : k ≤ Real.sqrt 2 * k := by
      calc
        k = 1 * k := by ring
        _ ≤ Real.sqrt 2 * k :=
          mul_le_mul_of_nonneg_right Real.one_lt_sqrt_two.le hk
    have hscaled : k ≤ ‖(heatScale u)⁻¹ • (x - y)‖ :=
      hkroot.trans hstrong
    simpa only [D, u] using
      (heatD1Tail_pow (V := V) hu hk hp0 hscaled)
  calc
    (∫ y : V, (heatD1Maj (R ^ 2 - s) (x - y)) ^ p
        ∂(volume : Measure V).restrict S) =
        ∫ y : V, (heatD1Maj u (x - y)) ^ p
          ∂(volume : Measure V).restrict S := by rfl
    _ ≤ ∫ y : V, D * (heatD1Half u (x - y)) ^ p
          ∂(volume : Measure V).restrict S :=
      integral_mono_ae hmajor
        (hhalf.mono_measure Measure.restrict_le_self) hpoint
    _ ≤ ∫ y : V, D * (heatD1Half u (x - y)) ^ p :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y ↦
          mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le p)
            (Real.rpow_nonneg (heatD1Half_nonneg (V := V) u (x - y)) p))
        hhalf
    _ = D * (u ^
          (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
            baseD1HalfMass V p) := by
      rw [integral_const_mul, heatD1Half_shift (V := V) hu x]
    _ = (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
        ((R ^ 2 - s) ^
          (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
            baseD1HalfMass V p) := rfl

/-- Real `klPDual`-power mass of the radial flux majorant on a selected
terminal spatial set. -/
def klFluxTailPow (R : ℝ) (x : V) (S : Set V) : ℝ :=
  ∫ z : ℝ × V, ‖klFluxMajor (R ^ 2) x z‖ ^ klPDual V
    ∂klTailMeasure (V := V) R S

/-- A lower radius `kR` on the selected terminal set yields the Gaussian
flux-tail factor while preserving the exact `klD1Exp` time power. -/
theorem klFluxTail_pow {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    klFluxTailPow (V := V) R x S ≤
      (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ klPDual V *
        (((R ^ 2 / 2) ^ (klD1Exp V + 1) /
          (klD1Exp V + 1)) * baseD1HalfMass V (klPDual V)) := by
  let p : ℝ := klPDual V
  let D : ℝ := (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p
  have hp : 0 < p := (klP_holder (V := V)).pos
  have hμ : klTailMeasure (V := V) R S ≤
      klTermMeasure (V := V) (R ^ 2) := by
    unfold klTailMeasure klTermMeasure
    rw [Measure.prod_restrict, Measure.restrict_prod_eq_prod_univ]
    exact Measure.restrict_mono
      (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖klFluxMajor (R ^ 2) x z‖ ^ p)
      (klTailMeasure (V := V) R S) := by
    have hg := (klFluxMajor_memLp (V := V) (sq_pos_of_pos hR) x).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    have hg' : Integrable
        (fun z : ℝ × V ↦ ‖klFluxMajor (R ^ 2) x z‖ ^ p)
        (klTermMeasure (V := V) (R ^ 2)) := by
      simpa only [ENNReal.toReal_ofReal hp.le, p] using hg
    exact hg'.mono_measure hμ
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ R ^ 2 := by
    simp [ae_iff, measure_singleton]
  have hslice : ∀ᵐ s ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2)),
      (∫ y : V, ‖klFluxMajor (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S) ≤
        D * ((R ^ 2 - s) ^ klD1Exp V * baseD1HalfMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hu : 0 < R ^ 2 - s :=
      sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hslice' := klFluxSlice_pow (V := V) hR hk
      (klPDual_one (V := V)) (klPDual_two (V := V)) hs hst x hSm hfar
    calc
      (∫ y : V, ‖klFluxMajor (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S) =
          ∫ y : V, (heatD1Maj (R ^ 2 - s) (x - y)) ^ p
            ∂(volume : Measure V).restrict S := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_of_nonneg
          (klFluxMajor_nonneg (V := V) (R ^ 2) x (s, y))]
        rfl
      _ ≤ (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)) ^ p *
          ((R ^ 2 - s) ^
            (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
              baseD1HalfMass V p) := hslice'
      _ = D * ((R ^ 2 - s) ^ klD1Exp V *
          baseD1HalfMass V p) := by
        simp only [D, p, klD1Exp]
  have hright : Integrable
      (fun s : ℝ ↦ D *
        ((R ^ 2 - s) ^ klD1Exp V * baseD1HalfMass V p))
      (volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))) :=
    (((klD1Time_intble (V := V) (sq_pos_of_pos hR)).1.mul_const _).const_mul _)
  have hi' : Integrable
      (fun z : ℝ × V ↦ ‖klFluxMajor (R ^ 2) x z‖ ^ p)
      ((volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))).prod
        ((volume : Measure V).restrict S)) := by
    simpa only [klTailMeasure] using hi
  change
    (∫ z : ℝ × V, ‖klFluxMajor (R ^ 2) x z‖ ^ p
      ∂((volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))).prod
        ((volume : Measure V).restrict S))) ≤
      D * (((R ^ 2 / 2) ^ (klD1Exp V + 1) /
        (klD1Exp V + 1)) * baseD1HalfMass V p)
  rw [integral_prod _ hi']
  calc
    (∫ s : ℝ, ∫ y : V, ‖klFluxMajor (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S
        ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))) ≤
        ∫ s : ℝ, D *
          ((R ^ 2 - s) ^ klD1Exp V * baseD1HalfMass V p)
          ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2)) :=
      integral_mono_ae hi'.integral_prod_left hright hslice
    _ = D * (((R ^ 2 / 2) ^ (klD1Exp V + 1) /
          (klD1Exp V + 1)) * baseD1HalfMass V p) := by
      rw [integral_const_mul, integral_mul_const,
        klD1Time_set (V := V) (sq_pos_of_pos hR)]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
