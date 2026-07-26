import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateKern
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateTime
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammTailGauss
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Terminal-slab integration of the Koch--Lamm Gaussian tail

This file converts a lower radius `k * R` on the terminal slab at time
`R^2` into the scaled lower radius `sqrt 2 * k` consumed by
`klHeatPow_tail`.  It then integrates the resulting far-field bound over an
arbitrary measurable spatial set.  No finite cover is chosen here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Product measure on a terminal half-slab and a selected spatial set. -/
def klTailMeasure (R : ℝ) (S : Set V) : Measure (ℝ × V) :=
  (volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))).prod
    ((volume : Measure V).restrict S)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- On the terminal half-slab, a radius `kR` is at least `sqrt 2 * k` in
the current heat scale. -/
theorem klTerm_scaled {R k s : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (hs : s ∈ Ioc (R ^ 2 / 2) (R ^ 2)) (hst : s ≠ R ^ 2)
    {x y : V} (hxy : k * R ≤ ‖x - y‖) :
    Real.sqrt 2 * k ≤
      ‖(heatScale (R ^ 2 - s))⁻¹ • (x - y)‖ := by
  have hu : 0 < R ^ 2 - s :=
    sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  have huhi : R ^ 2 - s ≤ R ^ 2 / 2 := by linarith [hs.1]
  let ρ : ℝ := heatScale (R ^ 2 - s)
  have hρ : 0 < ρ := heatScale_pos hu
  have hρsq : ρ ^ 2 = R ^ 2 - s := by
    dsimp [ρ, heatScale]
    exact Real.sq_sqrt hu.le
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hρR_sq : (ρ * Real.sqrt 2) ^ 2 ≤ R ^ 2 := by
    nlinarith
  have hρR : ρ * Real.sqrt 2 ≤ R :=
    (sq_le_sq₀
      (mul_nonneg hρ.le (Real.sqrt_nonneg _)) hR.le).1 hρR_sq
  have hmul : (Real.sqrt 2 * k) * ρ ≤ ‖x - y‖ := by
    calc
      (Real.sqrt 2 * k) * ρ = k * (ρ * Real.sqrt 2) := by ring
      _ ≤ k * R := mul_le_mul_of_nonneg_left hρR hk
      _ ≤ ‖x - y‖ := hxy
  have hdiv : Real.sqrt 2 * k ≤ ‖x - y‖ / ρ :=
    (le_div_iff₀ hρ).2 hmul
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
  simpa only [ρ, div_eq_mul_inv, mul_comm] using hdiv

/-- Integrability of the translated split-Gaussian majorant. -/
theorem klTailKernel_mem {u p : ℝ} (hu : 0 < u) (hp : 0 < p) (x : V) :
    Integrable (fun y : V ↦ klTailKernel u p (x - y)) := by
  unfold klTailKernel
  exact (((klTailGauss_mem (V := V) hp).comp_smul
    (inv_ne_zero (heatScale_pos hu).ne')).const_mul _).comp_sub_left x

/-- The terminal heat-kernel power over an arbitrary spatial set. -/
def klTermTailPow (R : ℝ) (x : V) (S : Set V) : ℝ :=
  ∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
    ∂(klTailMeasure (V := V) R S)

/-- A lower radius `kR` on `S` gives an exponentially decaying terminal
kernel-power bound. -/
theorem klTermTail_pow {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    klTermTailPow (V := V) R x S ≤
      Real.exp (-(klQDual V * k ^ 2) / 4) *
        (((R ^ 2 / 2) ^ (klHeatExp V + 1) /
            (klHeatExp V + 1)) * klTailMass V (klQDual V)) := by
  let p : ℝ := klQDual V
  let D : ℝ := Real.exp (-(p * k ^ 2) / 4)
  have hp : 0 < p := (klQ_holder (V := V)).pos
  have hμ : klTailMeasure (V := V) R S ≤
      klTermMeasure (V := V) (R ^ 2) := by
    unfold klTailMeasure klTermMeasure
    rw [Measure.prod_restrict, Measure.restrict_prod_eq_prod_univ]
    exact Measure.restrict_mono
      (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖klTermKernel (R ^ 2) x z‖ ^ p)
      (klTailMeasure (V := V) R S) := by
    have hg :=
      (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    have hg' : Integrable
        (fun z : ℝ × V ↦ ‖klTermKernel (R ^ 2) x z‖ ^ p)
        (klTermMeasure (V := V) (R ^ 2)) := by
      simpa only [ENNReal.toReal_ofReal hp.le, p] using hg
    exact hg'.mono_measure hμ
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ R ^ 2 := by
    simp [ae_iff, measure_singleton]
  have hslice : ∀ᵐ s ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2)),
      (∫ y : V, ‖klTermKernel (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S) ≤
        D * ((R ^ 2 - s) ^ klHeatExp V * klTailMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hu : 0 < R ^ 2 - s :=
      sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hpow : Integrable
        (fun y : V ↦ (heatKernel (R ^ 2 - s) (x - y)) ^ p)
        ((volume : Measure V).restrict S) :=
      ((heatKernelPow_mem (V := V) hu hp).comp_sub_left x).mono_measure
        Measure.restrict_le_self
    have htail : Integrable
        (fun y : V ↦ D * klTailKernel (R ^ 2 - s) p (x - y)) :=
      (klTailKernel_mem (V := V) hu hp x).const_mul _
    have hpoint :
        (fun y : V ↦ (heatKernel (R ^ 2 - s) (x - y)) ^ p) ≤ᵐ[
          (volume : Measure V).restrict S]
        (fun y : V ↦ D * klTailKernel (R ^ 2 - s) p (x - y)) := by
      filter_upwards [ae_restrict_mem hSm] with y hy
      have hscaled := klTerm_scaled (V := V) hR hk hs hst (hfar y hy)
      simpa only [D, p] using
        (klHeatPow_tail (V := V) hu hp hk hscaled)
    calc
      (∫ y : V, ‖klTermKernel (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S) =
          ∫ y : V, (heatKernel (R ^ 2 - s) (x - y)) ^ p
            ∂(volume : Measure V).restrict S := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_of_nonneg (klTermKernel_nonneg (V := V)
          (R ^ 2) x (s, y))]
        rfl
      _ ≤ ∫ y : V, D * klTailKernel (R ^ 2 - s) p (x - y)
          ∂(volume : Measure V).restrict S :=
        integral_mono_ae hpow (htail.mono_measure Measure.restrict_le_self) hpoint
      _ ≤ ∫ y : V, D * klTailKernel (R ^ 2 - s) p (x - y) :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y ↦ mul_nonneg (Real.exp_pos _).le
            (by
              unfold klTailKernel klTailGauss
              exact mul_nonneg
                (Real.rpow_nonneg
                  (inv_nonneg.mpr (pow_nonneg (heatScale_pos hu).le _)) _)
                (mul_nonneg
                  (Real.rpow_nonneg
                    (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le) _)
                  (Real.rpow_nonneg (baseHeat_nonneg _) _)))) htail
      _ = D * ((R ^ 2 - s) ^ klHeatExp V * klTailMass V p) := by
        rw [integral_const_mul, klTailKernel_int (V := V) hu hp x]
        rfl
  have hright : Integrable
      (fun s : ℝ ↦ D *
        ((R ^ 2 - s) ^ klHeatExp V * klTailMass V p))
      (volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))) :=
    (((klTimePow_intble (V := V) (sq_pos_of_pos hR)).1.mul_const _).const_mul _)
  have hi' : Integrable
      (fun z : ℝ × V ↦ ‖klTermKernel (R ^ 2) x z‖ ^ p)
      ((volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))).prod
        ((volume : Measure V).restrict S)) := by
    simpa only [klTailMeasure] using hi
  change
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z‖ ^ p
        ∂((volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))).prod
          ((volume : Measure V).restrict S))) ≤
      D * (((R ^ 2 / 2) ^ (klHeatExp V + 1) /
        (klHeatExp V + 1)) * klTailMass V p)
  rw [integral_prod _ hi']
  calc
    (∫ s : ℝ, ∫ y : V, ‖klTermKernel (R ^ 2) x (s, y)‖ ^ p
          ∂(volume : Measure V).restrict S
        ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2))) ≤
        ∫ s : ℝ, D * ((R ^ 2 - s) ^ klHeatExp V * klTailMass V p)
          ∂volume.restrict (Ioc (R ^ 2 / 2) (R ^ 2)) :=
      integral_mono_ae hi'.integral_prod_left hright hslice
    _ = D * (((R ^ 2 / 2) ^ (klHeatExp V + 1) /
          (klHeatExp V + 1)) * klTailMass V p) := by
      rw [integral_const_mul, integral_mul_const,
        klTermTime_set (V := V) (sq_pos_of_pos hR)]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
