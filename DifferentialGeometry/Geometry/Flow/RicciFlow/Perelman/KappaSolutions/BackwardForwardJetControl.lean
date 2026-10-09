import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardUniformJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology


theorem backwardForwardErrorJet_control
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hcoeff : ∀ q ≤ Nat.ceil epsilon⁻¹, |c * (-c⁻¹) ^ q| ≤ 2)
    (hmodel : |c - 1| * (3 * Real.sqrt 3) ≤ epsilon / 4)
    (hclose : ∀ a q : ℕ, a + 2 * q ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J q theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤
            epsilon / (8 * max 1 (Real.sqrt ((3 : ℝ) ^ (Nat.ceil epsilon⁻¹ + 2))))) :
    StrongNeckJetControl epsilon (backwardForwardErrorJet epsilon c J) := by
  let K : ℝ := max 1 (Real.sqrt ((3 : ℝ) ^ (Nat.ceil epsilon⁻¹ + 2)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbudget : (2 * K) * (epsilon / (8 * K)) = epsilon / 4 := by
    field_simp [hK.ne']
    ring
  refine ⟨epsilon / 2, by positivity, by linarith, ?_⟩
  intro a q haq s hs x hx
  have hao : a ≤ Nat.ceil epsilon⁻¹ := by omega
  have hqo : q ≤ Nat.ceil epsilon⁻¹ := by omega
  have hrank : Real.sqrt ((3 : ℝ) ^ (a + 2)) ≤ K :=
    (Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (Nat.add_le_add_right hao 2))).trans (le_max_right _ _)
  have hfactor : |c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2)) ≤ 2 * K :=
    mul_le_mul (hcoeff q hqo) hrank (Real.sqrt_nonneg _) (by norm_num)
  have herror := hclose a q haq (1 - s / c) (backwardForward_time_mapsTo hc hs) x hx
  have hfirst :
      (|c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2))) *
        tensor02CovDerivNormWith a (J q (1 - s / c))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c)))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c))) x ≤ epsilon / 4 := by
    apply (mul_le_mul hfactor herror (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) hK.le)).trans_eq
    exact hbudget
  exact (backwardForwardErrorJet_covNorm_le epsilon c hc J a q s hs x).trans
    ((add_le_add hfirst hmodel).trans_eq (by ring))


theorem backwardForwardErrorJet_eventually_control
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (J : ℕ → ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 (1 : ℝ)))
    (hconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
      ∀ a q : ℕ, a + 2 * q ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J i q theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤ eta) :
    ∀ᶠ i in atTop,
      StrongNeckJetControl epsilon (backwardForwardErrorJet epsilon (c i) (J i)) := by
  let order := Nat.ceil epsilon⁻¹
  let K : ℝ := max 1 (Real.sqrt ((3 : ℝ) ^ (order + 2)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hhalf : ∀ᶠ i in atTop, (1 : ℝ) / 2 ≤ c i :=
    ((tendsto_order.1 hc).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcoeff (q : ℕ) : ∀ᶠ i in atTop, |c i * (-(c i)⁻¹) ^ q| ≤ 2 := by
    have hlim : Tendsto (fun i => |c i * (-(c i)⁻¹) ^ q|) atTop (𝓝 (1 : ℝ)) := by
      simpa only [abs_pow, abs_neg, abs_one, one_pow] using
        (backwardForward_jet_coefficient_tendsto hc q).abs
    exact ((tendsto_order.1 hlim).2 2 (by norm_num)).mono fun _ hi => hi.le
  have hcoeffs : ∀ᶠ i in atTop,
      ∀ q ∈ Finset.range (order + 1), |c i * (-(c i)⁻¹) ^ q| ≤ 2 :=
    (eventually_all_finset (Finset.range (order + 1))).2 (fun q _hq => hcoeff q)
  have hmodelLimit : Tendsto (fun i => |c i - 1| * (3 * Real.sqrt 3)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      ((hc.sub_const 1).abs.mul_const (3 * Real.sqrt 3))
  have hmodel : ∀ᶠ i in atTop, |c i - 1| * (3 * Real.sqrt 3) ≤ epsilon / 4 :=
    ((tendsto_order.1 hmodelLimit).2 (epsilon / 4) (by positivity)).mono fun _ hi => hi.le
  have heta : 0 < epsilon / (8 * K) := div_pos hepsilon (mul_pos (by norm_num) hK)
  filter_upwards [hhalf, hcoeffs, hmodel, hconv (epsilon / (8 * K)) heta]
    with i hhalf_i hcoeff_i hmodel_i hconv_i
  apply backwardForwardErrorJet_control epsilon hepsilon (c i) hhalf_i (J i) ?_ hmodel_i hconv_i
  intro q hq
  exact hcoeff_i q (Finset.mem_range.mpr (by dsimp only [order]; omega))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
