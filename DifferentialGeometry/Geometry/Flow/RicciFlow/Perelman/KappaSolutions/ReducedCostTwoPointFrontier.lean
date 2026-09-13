import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance twoPointCostFrontierTopology : TopologicalSpace F.M := F.topology
local instance twoPointCostFrontierCharted : ChartedSpace H F.M := F.charted
local instance twoPointCostFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance twoPointCostFrontierT2 : T2Space F.M := F.t2
local instance twoPointCostFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact


def reducedCostTwoPointDistanceBound : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
    ∀ (_hdim : Module.finrank ℝ E = 3), ∀ (p q : F.M) {tau : ℝ}, 0 < tau →
      ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
        9216 * tau * (lCost F.S 0 p p tau / (2 * Real.sqrt tau) + 1 +
          lCost F.S 0 p q tau / (2 * Real.sqrt tau))


def reducedCostTwoPointFarBound : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
    ∀ (_hdim : Module.finrank ℝ E = 3), ∀ (p q : F.M) {tau : ℝ}, 0 < tau →
      1 + lCost F.S 0 p p tau / (2 * Real.sqrt tau) <
          collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau →
        collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau -
            1 - lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
          lCost F.S 0 p q tau / (2 * Real.sqrt tau)


omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_distanceBound
    (hfrontier : reducedCostTwoPointDistanceBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hb := hfrontier hF hdim p q htau
  have hc : collapsedVolumeChi = 1 / 9216 := by norm_num [collapsedVolumeChi]
  rw [hc]
  have hdiv : ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
      9216 * (lCost F.S 0 p p tau / (2 * Real.sqrt tau) + 1 +
        lCost F.S 0 p q tau / (2 * Real.sqrt tau)) := by
    rw [div_le_iff₀ htau]
    nlinarith [hb]
  have hscaled : (1 / 9216 : ℝ) *
      (((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau) ≤
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) + 1 +
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
    have hstep := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 1 / 9216)
    have hcancel : (1 / 9216 : ℝ) * (9216 * (lCost F.S 0 p p tau / (2 * Real.sqrt tau) + 1 +
        lCost F.S 0 p q tau / (2 * Real.sqrt tau))) =
        lCost F.S 0 p p tau / (2 * Real.sqrt tau) + 1 +
          lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
      ring
    linarith [hstep, hcancel]
  have hre : (1 / 9216 : ℝ) * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau =
      (1 / 9216 : ℝ) * (((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau) := by
    ring
  rw [hre]
  linarith [hscaled]


omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_farBound
    (hfrontier : reducedCostTwoPointFarBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  by_cases hfar : 1 + lCost F.S 0 p p tau / (2 * Real.sqrt tau) <
      collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau
  · exact hfrontier hF hdim p q htau hfar
  · have hnear : collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
        1 + lCost F.S 0 p p tau / (2 * Real.sqrt tau) := le_of_not_gt hfar
    have hsqrt : 0 < 2 * Real.sqrt tau := by positivity
    have hq : 0 ≤ lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
      div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le (fun s hs x => by
        obtain ⟨C, hC⟩ := hF.globalScalarBound
        exact (hC (0 - s) (by change 0 - s ≤ 0; linarith [hs.1]) x).1) p q) hsqrt.le
    linarith [hnear, hq]


omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_self
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p p).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p p tau / (2 * Real.sqrt tau) := by
  have hself : (riemannianEDistOf (F.S.base.metric (-tau)) p p).toReal = 0 := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero]
  have hsqrt : 0 < 2 * Real.sqrt tau := by positivity
  have hp : 0 ≤ lCost F.S 0 p p tau / (2 * Real.sqrt tau) :=
    div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le (fun s hs x => by
      obtain ⟨C, hC⟩ := hF.globalScalarBound
      exact (hC (0 - s) (by change 0 - s ≤ 0; linarith [hs.1]) x).1) p p) hsqrt.le
  rw [hself]
  have hzero : collapsedVolumeChi * (0 : ℝ) ^ 2 / tau = 0 := by ring
  rw [hzero]
  linarith [hp]


omit [I.Boundaryless] in
theorem reducedCostTwoPointDistanceBound_of_twoPoint
    (h : ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (_hdim : Module.finrank ℝ E = 3), ∀ (p q : F.M) {tau : ℝ}, 0 < tau →
        collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau -
            1 - lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
          lCost F.S 0 p q tau / (2 * Real.sqrt tau)) :
    reducedCostTwoPointDistanceBound (I := I) F := by
  intro kappa hF hdim p q tau htau
  set lp : ℝ := lCost F.S 0 p p tau / (2 * Real.sqrt tau) with hlp
  set lq : ℝ := lCost F.S 0 p q tau / (2 * Real.sqrt tau) with hlq
  set D : ℝ := ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 with hD
  have hb := h hF hdim p q htau
  have hc : collapsedVolumeChi = 1 / 9216 := by norm_num [collapsedVolumeChi]
  rw [hc, ← hlp, ← hlq, ← hD] at hb
  have hmul := mul_le_mul_of_nonneg_right hb htau.le
  have he : ((1 / 9216 : ℝ) * D / tau - 1 - lp) * tau =
      (1 / 9216) * D - tau - tau * lp := by
    field_simp
  rw [he] at hmul
  nlinarith [hmul]


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
