import DifferentialGeometry.Analysis.Integration.Gaussian.DistanceCoercivity
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.EndpointRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientDistanceContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostLocalRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PhysicalSpeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)

local instance geometricDistanceTopology : TopologicalSpace F.M := F.topology
local instance geometricDistanceCharted : ChartedSpace H F.M := F.charted
local instance geometricDistanceSmooth : IsManifold I ∞ F.M := F.smooth
local instance geometricDistanceT2 : T2Space F.M := F.t2
local instance geometricDistanceSigma : SigmaCompactSpace F.M := F.sigmaCompact

omit [I.Boundaryless] in
private theorem ancient_reduced_length_nonneg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) : 0 ≤ redLength F.S 0 p q tau := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  apply div_nonneg _ (by positivity)
  apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
  intro s hs z
  simpa only [zero_sub] using (hC (-s) (by
    rw [ancientTimeInterval_carrier]
    exact neg_nonpos.mpr hs.1) z).1

private theorem physicalSpeed_of_ancient_minimizer
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p q : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hstart : alpha 0 = p) (hend : alpha (Real.sqrt tau) = q)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    Real.sqrt ((F.S.base.metric (-s)).inner (squareRootReparametrization alpha s)
      (mfderiv 𝓘(ℝ, ℝ) I (squareRootReparametrization alpha) s 1)
      (mfderiv 𝓘(ℝ, ℝ) I (squareRootReparametrization alpha) s 1)) ≤
        Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * s ^ (-(3 / 4) : ℝ) *
          Real.sqrt (redLength F.S 0 p q tau) := by
  have hspeed := lSpeedSq_squareRootReparametrization_le_of_ancient_action_eq_lCost F hF
    alpha halpha p q hs hst hstart hend (fun r hr => hgeo r ⟨hr.1, hr.2.le⟩)
    (by simpa only [hstart] using hcost)
  have hL := ancient_reduced_length_nonneg F hF p q (hs.trans_le hst)
  have h := Real.sqrt_le_sqrt hspeed
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at h
  have hquarter : Real.sqrt (Real.sqrt tau) = tau ^ ((1 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (hs.trans_le hst).le]
    norm_num
  have hthreequarter : Real.sqrt (s ^ ((3 / 2) : ℝ)) = s ^ ((3 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    norm_num
  rw [hquarter, hthreequarter] at h
  change Real.sqrt _ ≤ _ at h
  calc
    _ ≤ (Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * Real.sqrt (redLength F.S 0 p q tau)) /
        s ^ ((3 / 4) : ℝ) := h
    _ = _ := by rw [div_eq_mul_inv, ← Real.rpow_neg hs.le]; ring

private theorem exists_reduced_minimizing_curves_with_endpoint_controls
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q₁ q₂ : F.M) {tau : ℝ} (htau : 0 < tau) :
    let L₁ := redLength F.S 0 p q₁ tau
    let L₂ := redLength F.S 0 p q₂ tau
    let B := fun s : ℝ => 1 + tau ^ ((1 / 4) : ℝ) * s ^ (-(1 / 4) : ℝ) *
      (Real.sqrt L₁ + Real.sqrt L₂)
    ∃ gamma₁ gamma₂ : ℝ → F.M,
      gamma₁ 0 = p ∧ gamma₂ 0 = p ∧ gamma₁ tau = q₁ ∧ gamma₂ tau = q₂ ∧
      ContinuousOn (fun s => (riemannianEDistOf (F.S.base.metric (-s))
        (gamma₁ s) (gamma₂ s)).toReal) (Icc 0 tau) ∧
      (∀ s ∈ Ioc 0 tau, ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma₁ s ∧
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma₂ s) ∧
      (∀ s ∈ Ioc 0 tau,
        Real.sqrt ((F.S.base.metric (-s)).inner (gamma₁ s)
          (mfderiv 𝓘(ℝ, ℝ) I gamma₁ s 1) (mfderiv 𝓘(ℝ, ℝ) I gamma₁ s 1)) ≤
          Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * s ^ (-(3 / 4) : ℝ) * Real.sqrt L₁) ∧
      (∀ s ∈ Ioc 0 tau,
        Real.sqrt ((F.S.base.metric (-s)).inner (gamma₂ s)
          (mfderiv 𝓘(ℝ, ℝ) I gamma₂ s 1) (mfderiv 𝓘(ℝ, ℝ) I gamma₂ s 1)) ≤
          Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * s ^ (-(3 / 4) : ℝ) * Real.sqrt L₂) ∧
      (∀ s ∈ Ioc 0 tau, ∀ z : F.M, ∀ w : TangentSpace I z,
        (riemannianEDistOf (F.S.base.metric (-s)) (gamma₁ s) z <
            ENNReal.ofReal (Real.sqrt s / B s) ∨
          riemannianEDistOf (F.S.base.metric (-s)) (gamma₂ s) z <
            ENNReal.ofReal (Real.sqrt s / B s)) →
        ricciTensor (F.S.base.metric (-s)) z w w ≤
          3 * (B s) ^ 2 / s * (F.S.base.metric (-s)).inner z w w) := by
  obtain ⟨alpha₁, ha₁, h0₁, ht₁, hg₁, hc₁⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q₁ htau
  obtain ⟨alpha₂, ha₂, h0₂, ht₂, hg₂, hc₂⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q₂ htau
  let gamma₁ := squareRootReparametrization alpha₁
  let gamma₂ := squareRootReparametrization alpha₂
  have hsmooth₁ : ∀ s ∈ Ioc 0 tau, ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma₁ s := by
    intro s hs
    exact ha₁.contMDiffAt.comp s (Real.contDiffAt_sqrt hs.1.ne').contMDiffAt
  have hsmooth₂ : ∀ s ∈ Ioc 0 tau, ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma₂ s := by
    intro s hs
    exact ha₂.contMDiffAt.comp s (Real.contDiffAt_sqrt hs.1.ne').contMDiffAt
  have hgamma₁0 : gamma₁ 0 = p := by
    simp only [gamma₁, squareRootReparametrization, Real.sqrt_zero, h0₁]
  have hgamma₂0 : gamma₂ 0 = p := by
    simp only [gamma₂, squareRootReparametrization, Real.sqrt_zero, h0₂]
  refine ⟨gamma₁, gamma₂, hgamma₁0, hgamma₂0, ht₁, ht₂, ?_, ?_, ?_, ?_, ?_⟩
  · apply continuousOn_moving_distance_from_common_initial_point F hF gamma₁ gamma₂
      (ha₁.continuous.comp Real.continuous_sqrt).continuousAt
      (ha₂.continuous.comp Real.continuous_sqrt).continuousAt
      (hgamma₁0.trans hgamma₂0.symm) hsmooth₁ hsmooth₂
  · exact fun s hs => ⟨hsmooth₁ s hs, hsmooth₂ s hs⟩
  · intro s hs
    exact physicalSpeed_of_ancient_minimizer F hF alpha₁ ha₁ p q₁ hs.1 hs.2 h0₁ ht₁ hg₁ hc₁
  · intro s hs
    exact physicalSpeed_of_ancient_minimizer F hF alpha₂ ha₂ p q₂ hs.1 hs.2 h0₂ ht₂ hg₂ hc₂
  · intro s hs
    apply ricciTensor_le_on_endpoint_balls_of_sqrt_redLength_lipschitz F hF p
      (gamma₁ s) (gamma₂ s) q₁ q₂ hs.1 htau
      (redLength_prefix_le_of_ancient_action_eq_lCost F hF alpha₁ ha₁ p q₁ hs.1 hs.2 h0₁ ht₁ hc₁)
      (redLength_prefix_le_of_ancient_action_eq_lCost F hF alpha₂ ha₂ p q₂ hs.1 hs.2 h0₂ ht₂ hc₂)
    · intro z
      obtain ⟨alpha, ha, h0, ht, hg, hc⟩ :=
        exists_lRegularized_minimizer_of_ancient F hF p z hs.1
      have hh := scalar_le_three_mul_redLength_of_ancient_action_eq_lCost F hF alpha ha p hs.1
        (fun r hr => hg r ⟨hr.1, hr.2.le⟩) hc
      simpa only [ht] using hh
    · let _ : NeZero (Module.finrank ℝ E) := by
        obtain ⟨t, ht, z, hz⟩ := hF.notFlat
        exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
          (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
      exact fun x y => sqrt_redLength_sub_le_distance_of_continuous_and_minimizers F hF p x y hs.1
        (continuous_redLength_of_ancient F hF p hs.1)
        (fun z => exists_lRegularized_minimizer_of_ancient F hF p z hs.1)


theorem ancientKappa_reducedCost_two_point_between
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q₁ q₂ : F.M) {tau : ℝ} (htau : 0 < tau) :
    (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
        ((riemannianEDistOf (F.S.base.metric (-tau)) q₁ q₂).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p q₁ tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q₂ tau / (2 * Real.sqrt tau) := by
  have hdim : 2 ≤ Module.finrank ℝ E := by
    by_contra hdim
    have hsmall : Module.finrank ℝ E ≤ 1 := by omega
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    apply hx
    change Tensor0SBundle.normSq0S (F.S.base.metric t) x 4
      (metricRm04At (F.S.base.metric t) x) = 0
    rw [metricRm04At_eq_zero_of_finrank_le_one _ hsmall]
    exact ((Tensor0SBundle.tensor0SMetricData (F.S.base.metric t) x 4).inner_self_eq_zero_iff
      0).2 rfl
  let _ : ConnectedSpace F.M := hF.connected
  let L₁ := redLength F.S 0 p q₁ tau
  let L₂ := redLength F.S 0 p q₂ tau
  have hL₁ : 0 ≤ L₁ := ancient_reduced_length_nonneg F hF p q₁ htau
  have hL₂ : 0 ≤ L₂ := ancient_reduced_length_nonneg F hF p q₂ htau
  obtain ⟨gamma₁, gamma₂, h0₁, h0₂, ht₁, ht₂, hcont, hsmooth, hspeed₁, hspeed₂, hRic⟩ :=
    exists_reduced_minimizing_curves_with_endpoint_controls F hF p q₁ q₂ htau
  let d := fun s : ℝ => (riemannianEDistOf (F.S.base.metric (-s)) (gamma₁ s) (gamma₂ s)).toReal
  have hac : ∀ c ∈ Ioc (0 : ℝ) tau, AbsolutelyContinuousOnInterval d c tau := by
    intro c hc
    exact KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance
      F hF hc.1 hc.2 gamma₁ gamma₂
      (fun s hs => (hsmooth s ⟨hc.1.trans_le hs.1, hs.2⟩).1.contMDiffWithinAt)
      (fun s hs => (hsmooth s ⟨hc.1.trans_le hs.1, hs.2⟩).2.contMDiffWithinAt)
  have hzero : d 0 = 0 := by simp [d, h0₁, h0₂, riemannianEDistOf_self]
  have hnonneg : 0 ≤ d tau := ENNReal.toReal_nonneg
  have hdini : ∀ t ∈ Ioo (0 : ℝ) tau, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
      slope d t s ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1)) * t ^ (-(1 / 2) : ℝ) +
        (2 * ((Module.finrank ℝ E : ℝ) + 1) + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂) *
          tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) + ε := by
    intro t ht
    let B := 1 + tau ^ ((1 / 4) : ℝ) * t ^ (-(1 / 4) : ℝ) *
      (Real.sqrt L₁ + Real.sqrt L₂)
    have hB : 0 < B := by
      dsimp only [B]
      have hp₁ := Real.rpow_nonneg htau.le ((1 / 4) : ℝ)
      have hp₂ := Real.rpow_nonneg ht.1.le (-(1 / 4) : ℝ)
      positivity
    have htreg : (0 : ℝ) - t ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, mem_Iio, zero_sub] using neg_neg_of_pos ht.1
    have hcomplete : RiemannianMetricComplete (F.S.base.metric (0 - t)) :=
      ⟨hF.complete (0 - t) (ancientTimeInterval.regular_subset htreg)⟩
    have hh := upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds_of_two_le_finrank
      F.S F.isSolution hdim
      ht.1 hB htreg hcomplete gamma₁ gamma₂ (hsmooth t ⟨ht.1, ht.2.le⟩).1
      (hsmooth t ⟨ht.1, ht.2.le⟩).2 (by simpa only [zero_sub] using hspeed₁ t ⟨ht.1, ht.2.le⟩)
      (by simpa only [zero_sub] using hspeed₂ t ⟨ht.1, ht.2.le⟩)
      (by simpa only [zero_sub, B, L₁, L₂] using hRic t ⟨ht.1, ht.2.le⟩)
    have hrpow : t ^ (-(1 / 4) : ℝ) / Real.sqrt t = t ^ (-(3 / 4) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht.1]
      norm_num
    have hinv : 1 / Real.sqrt t = t ^ (-(1 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg ht.1.le]
    have hcoef : 2 * ((Module.finrank ℝ E : ℝ) + 1) * B / Real.sqrt t +
        Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) * Real.sqrt L₁ +
        Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) * Real.sqrt L₂ =
        (2 * ((Module.finrank ℝ E : ℝ) + 1)) * t ^ (-(1 / 2) : ℝ) +
          (2 * ((Module.finrank ℝ E : ℝ) + 1) + Real.sqrt 3) *
          (Real.sqrt L₁ + Real.sqrt L₂) * tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) := by
      dsimp only [B]
      calc
        _ = 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 / Real.sqrt t) +
            2 * ((Module.finrank ℝ E : ℝ) + 1) * tau ^ ((1 / 4) : ℝ) *
            (Real.sqrt L₁ + Real.sqrt L₂) * (t ^ (-(1 / 4) : ℝ) / Real.sqrt t) +
            Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) * Real.sqrt L₁ +
            Real.sqrt 3 * tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) * Real.sqrt L₂ := by ring
        _ = _ := by rw [hrpow, hinv]; ring
    simpa only [UpperRightDiniLE, zero_sub, hcoef, L₁, L₂, d] using hh
  have ha : Real.sqrt 3 ≤ (Module.finrank ℝ E : ℝ) + 1 := by
    have hn : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    have hs : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  have hh := two_point_coercivity_of_upper_dini_sum_bound_interval_scaled ha htau hL₁ hL₂
    hcont hac hzero hnonneg hdini
  dsimp only [d, L₁, L₂, redLength] at hh
  rw [ht₁, ht₂] at hh
  linarith

theorem ancientKappa_reducedCost_two_point
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  exact ancientKappa_reducedCost_two_point_between F hF p p q htau

theorem ancientKappaThree_reducedCost_two_point_between
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q₁ q₂ : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) q₁ q₂).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p q₁ tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q₂ tau / (2 * Real.sqrt tau) := by
  simpa only [hdim, Nat.cast_ofNat, collapsedVolumeChi] using
    ancientKappa_reducedCost_two_point_between F hF p q₁ q₂ htau

theorem ancientKappaThree_reducedCost_two_point
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  exact ancientKappaThree_reducedCost_two_point_between F hF hdim p p q htau

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
