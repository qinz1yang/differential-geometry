import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingPower
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def evolvingPositiveRpowEnergyBound
    (q t₁ b K B L : ℝ) : ℝ :=
  (timeCutoffDerivConstant / (b - t₁) +
      (2 * q / (1 - q)) * K + (1 / 2) * B) * L

def evolvingPositiveRpowCommonEnergyBound
    (q t₁ b K B L : ℝ) : ℝ :=
  max 1 (q / (2 * (1 - q))) *
    evolvingPositiveRpowEnergyBound q t₁ b K B L

theorem evolving_positive_rpow_reverse_holder_step
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a t₁ b C K B L t₀ : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (hat₁ : a ≤ t₁) (ht₁b : t₁ < b)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hcutoff_le : ∀ x : M, cutoff x ^ 2 ≤ outer x ^ 2)
    (hgrad : ∀ t ∈ Icc a b, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t) cutoff x)
          (gradientFun (I := I) (g t) cutoff x) ≤
        K * outer x ^ 2)
    (houterMass_le :
      (∫ t in a..b,
        evolvingLocalizedL2Mass
          (I := I) (M := M) g outer (fun s x => u s x ^ (q / 2)) t) ≤ L) :
    (∫ t in a..t₁, ∫ x,
        |cutoff x * u t x ^ (q / 2)| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * (((t₁ - a + 1) *
          evolvingPositiveRpowCommonEnergyBound q t₁ b K B L + K * L) ^
        (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff w
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff w
  let outerMass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g outer w
  let e := 2 * q / (1 - q)
  let v := (1 / 2) * B
  let D := timeCutoffDerivConstant / (b - t₁)
  let combinedError : ℝ → ℝ := fun t => e * error t + v * mass t
  let A := evolvingPositiveRpowEnergyBound q t₁ b K B L
  let k := q / (2 * (1 - q))
  let common := evolvingPositiveRpowCommonEnergyBound q t₁ b K B L
  have hab : a ≤ b := hat₁.trans ht₁b.le
  have he : 0 ≤ e := by
    dsimp only [e]
    exact div_nonneg (mul_nonneg (by norm_num) hq_pos.le)
      (sub_nonneg.mpr hq_one.le)
  have hv : 0 ≤ v := mul_nonneg (by norm_num) hB
  have hD : 0 ≤ D :=
    div_nonneg timeCutoffDerivConstant_nonneg (sub_nonneg.mpr ht₁b.le)
  have hcombinedK : 0 ≤ e * K + v := add_nonneg (mul_nonneg he hK) hv
  have hA : 0 ≤ A := by
    dsimp only [A, evolvingPositiveRpowEnergyBound, D, e, v]
    exact mul_nonneg (add_nonneg (add_nonneg hD (mul_nonneg he hK)) hv) hL
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg hq_pos.le
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq_one.le))
  have hone_le : 1 ≤ max 1 k := le_max_left _ _
  have hk_le : k ≤ max 1 k := le_max_right _ _
  have hcommon : 0 ≤ common := by
    exact mul_nonneg (zero_le_one.trans hone_le) hA
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg
        hcutoff.continuous huHalf.continuous
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg hgram hcutoff huHalf
  have houter_cont : ContinuousOn outerMass (Icc a b) := by
    simpa only [outerMass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g outer w isCompact_Icc hg
        houter.continuous huHalf.continuous
  have hcombined_cont : ContinuousOn combinedError (Icc a b) :=
    (continuousOn_const.mul herror_cont).add
      (continuousOn_const.mul hmass_cont)
  have hmass_le : ∀ t ∈ Icc a b, mass t ≤ outerMass t := by
    intro t _
    exact evolvingLocalizedL2Mass_le_of_sq_le
      (I := I) (M := M) g cutoff outer hcutoff houter w huHalf t hcutoff_le
  have herror_le : ∀ t ∈ Icc a b, error t ≤ K * outerMass t := by
    intro t ht
    exact evolvingCutoffGradientError_le_evolvingLocalizedL2Mass
      (I := I) (M := M) g cutoff outer hcutoff houter w huHalf t (hgrad t ht)
  have hcombined_le : ∀ t ∈ Icc a b,
      combinedError t ≤ (e * K + v) * outerMass t := by
    intro t ht
    dsimp only [combinedError]
    calc
      e * error t + v * mass t ≤
          e * (K * outerMass t) + v * outerMass t :=
        add_le_add
          (mul_le_mul_of_nonneg_left (herror_le t ht) he)
          (mul_le_mul_of_nonneg_left (hmass_le t ht) hv)
      _ = (e * K + v) * outerMass t := by ring
  have hrhs_le : ∀ t ∈ Icc a t₁,
      (∫ s in t..b,
        (-backwardTimeCutoffDeriv t₁ b s) * mass s +
          backwardTimeCutoff t₁ b s * combinedError s) ≤ A := by
    intro t ht
    have h := backwardTimeCutoff_mass_error_intervalIntegral_le
      (mass := mass) (error := combinedError) (outerMass := outerMass)
      (C := 1) (D := D) (K := e * K + v) (L := L)
      ht.1 ht.2 ht₁b (by norm_num) hD hcombinedK
      hmass_cont hcombined_cont houter_cont
      (fun s _ => evolvingLocalizedL2Mass_nonneg
        (I := I) (M := M) g cutoff w s)
      (fun s hs => add_nonneg
        (mul_nonneg he (evolvingCutoffGradientError_nonneg
          (I := I) (M := M) g cutoff w s))
        (mul_nonneg hv (evolvingLocalizedL2Mass_nonneg
          (I := I) (M := M) g cutoff w s)))
      (fun s _ => evolvingLocalizedL2Mass_nonneg
        (I := I) (M := M) g outer w s)
      hmass_le hcombined_le
      (fun s _ => neg_backwardTimeCutoffDeriv_le ht₁b s)
      (by simpa only [outerMass, w] using houterMass_le)
    have hbound_eq : (D + (e * K + v)) * L = A := by
      dsimp only [A, D, e, v, evolvingPositiveRpowEnergyBound]
      ring
    simp only [one_mul] at h
    rw [hbound_eq] at h
    exact h
  have henergy :=
    backward_caccioppoli_evolving_inner_energy_positive_rpow_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one hg hgram hcutoff
        hat₁ ht₁b.le
          (contDiff_backwardTimeCutoffDeriv t₁ b).continuous.continuousOn
          (fun t _ => hasDerivAt_backwardTimeCutoff t₁ b t)
          (fun t _ => (backwardTimeCutoff_mem_Icc t₁ b t).1)
          (backwardTimeCutoff_eq_zero b ht₁b)
          (fun t ht => backwardTimeCutoff_eq_one_of_le ht₁b ht.2)
          htrace hpde
          (by simpa only [mass, error, e, v, w, combinedError] using hrhs_le)
  have hmass_inner : ∀ t ∈ Icc a t₁, mass t ≤ common := by
    intro t ht
    have hm : mass t ≤ A := by simpa only [mass, w] using henergy.1 t ht
    apply hm.trans
    change A ≤ max 1 k * A
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hone_le hA
  have hdirichlet_inner :
      (∫ t in a..t₁,
        evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff w t) ≤ common := by
    have hd := henergy.2
    change (∫ t in a..t₁,
      evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g cutoff w t) ≤ k * A at hd
    exact hd.trans (mul_le_mul_of_nonneg_right hk_le hA)
  have houter_inner : (∫ t in a..t₁, outerMass t) ≤ L := by
    have houter_int : IntervalIntegrable outerMass volume a b := by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le hab] using houter_cont
    have hmono : (∫ t in a..t₁, outerMass t) ≤ ∫ t in a..b, outerMass t := by
      exact intervalIntegral.integral_mono_interval le_rfl hat₁ ht₁b.le
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact evolvingLocalizedL2Mass_nonneg
            (I := I) (M := M) g outer w t)
        houter_int
    exact hmono.trans (by simpa only [outerMass, w] using houterMass_le)
  have hresult := evolving_localized_parabolic_sobolev_of_nested_cutoffs_le
    (I := I) (M := M) g hdim cutoff outer hcutoff houter w huHalf
      hat₁ hcommon hC hK hg hgram hSobolev
      (by simpa only [mass] using hmass_inner)
      hdirichlet_inner
      (fun t ht => hgrad t ⟨ht.1, ht.2.trans ht₁b.le⟩)
      (by simpa only [outerMass] using houter_inner)
  simpa only [w, common] using hresult

end DifferentialGeometry.Analysis.Parabolic.Moser

end
