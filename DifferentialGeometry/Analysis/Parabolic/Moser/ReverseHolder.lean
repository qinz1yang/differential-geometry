import DifferentialGeometry.Analysis.Parabolic.Moser.Power

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def positiveRpowEnergyBound (q t₁ b K L : ℝ) : ℝ :=
  (timeCutoffDerivConstant / (b - t₁) + (2 * q / (1 - q)) * K) * L

def positiveRpowCommonEnergyBound (q t₁ b K L : ℝ) : ℝ :=
  max 1 (q / (2 * (1 - q))) * positiveRpowEnergyBound q t₁ b K L

theorem positive_rpow_reverse_holder_step
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a t₁ b K L : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (hat₁ : a ≤ t₁) (ht₁b : t₁ < b)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hcutoff : ∀ x : M, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (houterMass_le :
      (∫ t in a..b,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) ≤ L) :
    (∫ t in a..t₁, ∫ x,
        |cutoff.toFun x * u t x ^ (q / 2)| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - a + 1) * positiveRpowCommonEnergyBound q t₁ b K L + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let outerMass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) outer
      (smoothScalarSlice (I := I) g w huHalf t)
  let C := 2 * q / (1 - q)
  let D := timeCutoffDerivConstant / (b - t₁)
  let A := positiveRpowEnergyBound q t₁ b K L
  let k := q / (2 * (1 - q))
  let B := positiveRpowCommonEnergyBound q t₁ b K L
  have hab : a ≤ b := hat₁.trans ht₁b.le
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (mul_nonneg (by norm_num) hq_pos.le)
      (sub_nonneg.mpr hq_one.le)
  have hD : 0 ≤ D := by
    exact div_nonneg timeCutoffDerivConstant_nonneg (sub_nonneg.mpr ht₁b.le)
  have hA : 0 ≤ A := by
    dsimp only [A, positiveRpowEnergyBound]
    exact mul_nonneg (add_nonneg hD (mul_nonneg hC hK)) hL
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg hq_pos.le
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq_one.le))
  have hone_le : 1 ≤ max 1 k := le_max_left _ _
  have hk_le : k ≤ max 1 k := le_max_right _ _
  have hB : 0 ≤ B := by
    exact mul_nonneg (le_trans (by norm_num) hone_le) hA
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using
      (contDiff_localizedL2Mass (I := I) (M := M) cutoff w huHalf)
        |>.continuous.continuousOn
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using
      (contDiff_cutoffGradientError (I := I) (M := M) cutoff w huHalf)
        |>.continuous.continuousOn
  have houter_cont : ContinuousOn outerMass (Icc a b) := by
    simpa only [outerMass] using
      (contDiff_localizedL2Mass (I := I) (M := M) outer w huHalf)
        |>.continuous.continuousOn
  have hmass_le : ∀ t ∈ Icc a b, mass t ≤ outerMass t := by
    intro t _
    exact localizedL2Mass_le_of_sq_le (I := I) (M := M) cutoff outer
      (smoothScalarSlice (I := I) g w huHalf t) hcutoff
  have herror_le : ∀ t ∈ Icc a b, error t ≤ K * outerMass t := by
    intro t _
    exact cutoffGradientError_le_localizedL2Mass (I := I) (M := M)
      cutoff outer (smoothScalarSlice (I := I) g w huHalf t) hgrad
  have hrhs_le : ∀ t ∈ Icc a t₁,
      (∫ s in t..b,
        (-backwardTimeCutoffDeriv t₁ b s) * mass s +
          backwardTimeCutoff t₁ b s * (C * error s)) ≤ A := by
    intro t ht
    have h := backwardTimeCutoff_mass_error_intervalIntegral_le
      (mass := mass) (error := error) (outerMass := outerMass)
      ht.1 ht.2 ht₁b hC hD hK hmass_cont herror_cont houter_cont
      (fun s _ => localizedL2Mass_nonneg (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf s))
      (fun s _ => cutoffGradientError_nonneg (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf s))
      (fun s _ => localizedL2Mass_nonneg (I := I) (M := M) outer
        (smoothScalarSlice (I := I) g w huHalf s))
      hmass_le herror_le
      (fun s _ => neg_backwardTimeCutoffDeriv_le ht₁b s)
      (by simpa only [outerMass, w, huHalf] using houterMass_le)
    simpa only [A, C, D, positiveRpowEnergyBound] using h
  have henergy := backward_caccioppoli_inner_energy_positive_rpow_of_supersolution
    (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one hat₁ ht₁b.le
    (contDiff_backwardTimeCutoffDeriv t₁ b).continuous.continuousOn
    (fun t _ => hasDerivAt_backwardTimeCutoff t₁ b t)
    (fun t _ => (backwardTimeCutoff_mem_Icc t₁ b t).1)
    (backwardTimeCutoff_eq_zero b ht₁b)
    (fun t ht => backwardTimeCutoff_eq_one_of_le ht₁b ht.2)
    hpde
    (by simpa only [mass, error, C, A, w, huHalf] using hrhs_le)
  have hmass_inner : ∀ t ∈ Icc a t₁, mass t ≤ B := by
    intro t ht
    have hm : mass t ≤ A := by simpa only [mass, w, huHalf] using henergy.1 t ht
    apply hm.trans
    change A ≤ max 1 k * A
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hone_le hA
  have hdirichlet_inner :
      (∫ t in a..t₁,
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g w huHalf t)) ≤ B := by
    have hd := henergy.2
    change (∫ t in a..t₁,
      localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf t)) ≤ k * A at hd
    exact hd.trans (mul_le_mul_of_nonneg_right hk_le hA)
  have hdirichlet_cont : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf t)) (Icc a t₁) :=
    (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff w huHalf)
      |>.continuous.continuousOn
  have houter_inner : (∫ t in a..t₁, outerMass t) ≤ L := by
    have houter_int : IntervalIntegrable outerMass volume a b := by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le hab] using houter_cont
    have hmono : (∫ t in a..t₁, outerMass t) ≤ ∫ t in a..b, outerMass t := by
      exact intervalIntegral.integral_mono_interval le_rfl hat₁ ht₁b.le
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact localizedL2Mass_nonneg (I := I) (M := M) outer
            (smoothScalarSlice (I := I) g w huHalf t))
        houter_int
    exact hmono.trans (by simpa only [outerMass, w, huHalf] using houterMass_le)
  have hresult := localized_parabolic_sobolev_of_nested_cutoffs_le
    (I := I) (M := M) g hdim cutoff outer w huHalf hat₁ hB hK
    (by simpa only [mass] using hmass_inner)
    hdirichlet_cont hdirichlet_inner hgrad
    (by simpa only [outerMass] using houter_inner)
  simpa only [w, huHalf, B] using hresult

end DifferentialGeometry.Analysis.Parabolic.Moser

end
