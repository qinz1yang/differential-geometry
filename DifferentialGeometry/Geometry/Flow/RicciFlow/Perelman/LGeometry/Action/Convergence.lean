import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.KineticConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Operator.Family.Gram.KineticEnergy
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open PDE.RicciFlow.Perelman (lDensity lLength lSpeedSq lVelocity)

universe u uE uH

section AlmostEverywhere

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem PointedCGHMaps.tendsto_lLength_map_of_tendsto_ae
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (T a b : Real) (alpha : Real → L.M) :
    let scalarSeq : Nat → Real → Real := fun k s =>
      let : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      let : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      let : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      let : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      (X.term (subseq k)).S.scalar (T - s) (Phi.map k (alpha s))
    let kineticSeq : Nat → Real → Real := fun k s =>
      let : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      let : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      let : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      let : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      ((X.term (subseq k)).S.base.metric (T - s)).inner
        (Phi.map k (alpha s))
        (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
        (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
    let scalarLim : Real → Real := fun s =>
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : T2Space L.M := L.t2
      let : IsManifold I ∞ L.M := L.smooth
      let : SigmaCompactSpace L.M := L.sigmaCompact
      L.S.scalar (T - s) (alpha s)
    let kineticLim : Real → Real := fun s =>
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : T2Space L.M := L.t2
      let : IsManifold I ∞ L.M := L.smooth
      let : SigmaCompactSpace L.M := L.sigmaCompact
      (L.S.base.metric (T - s)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
    let densitySeq : Nat → Real → Real := fun k s =>
      Real.sqrt s * (scalarSeq k s + kineticSeq k s)
    (∀ᵐ s ∂volume.restrict (uIoc a b),
      Tendsto (fun k => scalarSeq k s) atTop (𝓝 (scalarLim s))) →
      (∀ᵐ s ∂volume.restrict (uIoc a b),
      Tendsto (fun k => kineticSeq k s) atTop (𝓝 (kineticLim s))) →
        (∀ᶠ k in atTop, AEStronglyMeasurable (densitySeq k)
          (volume.restrict (uIoc a b))) →
          (∃ bound : Real → Real, Integrable bound (volume.restrict (uIoc a b)) ∧
            ∀ᶠ k in atTop, ∀ᵐ s ∂volume.restrict (uIoc a b),
              ‖densitySeq k s‖ ≤ bound s) →
            Tendsto
              (fun k =>
                let : TopologicalSpace (X.term (subseq k)).M :=
                  (X.term (subseq k)).topology
                let : ChartedSpace H (X.term (subseq k)).M :=
                  (X.term (subseq k)).charted
                let : T2Space (X.term (subseq k)).M :=
                  (X.term (subseq k)).t2
                let : IsManifold I ∞ (X.term (subseq k)).M :=
                  (X.term (subseq k)).smooth
                let : SigmaCompactSpace (X.term (subseq k)).M :=
                  (X.term (subseq k)).sigmaCompact
                lLength (I := I) (X.term (subseq k)).S T
                  (fun r => Phi.map k (alpha r)) a b)
              atTop
              (𝓝 <|
                let : TopologicalSpace L.M := L.topology
                let : ChartedSpace H L.M := L.charted
                let : T2Space L.M := L.t2
                let : IsManifold I ∞ L.M := L.smooth
                let : SigmaCompactSpace L.M := L.sigmaCompact
                lLength (I := I) L.S T alpha a b) := by
  let scalarSeq : Nat → Real → Real := fun k s =>
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (X.term (subseq k)).S.scalar (T - s) (Phi.map k (alpha s))
  let kineticSeq : Nat → Real → Real := fun k s =>
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    ((X.term (subseq k)).S.base.metric (T - s)).inner
      (Phi.map k (alpha s))
      (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
      (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
  let scalarLim : Real → Real := fun s =>
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : T2Space L.M := L.t2
    let : IsManifold I ∞ L.M := L.smooth
    let : SigmaCompactSpace L.M := L.sigmaCompact
    L.S.scalar (T - s) (alpha s)
  let kineticLim : Real → Real := fun s =>
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : T2Space L.M := L.t2
    let : IsManifold I ∞ L.M := L.smooth
    let : SigmaCompactSpace L.M := L.sigmaCompact
    (L.S.base.metric (T - s)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  let densitySeq : Nat → Real → Real := fun k s =>
    Real.sqrt s * (scalarSeq k s + kineticSeq k s)
  let densityLim : Real → Real := fun s =>
    Real.sqrt s * (scalarLim s + kineticLim s)
  let actionSeq : Nat → Real := fun k =>
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    lLength (I := I) (X.term (subseq k)).S T
      (fun r => Phi.map k (alpha r)) a b
  let actionLim : Real :=
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : T2Space L.M := L.t2
    let : IsManifold I ∞ L.M := L.smooth
    let : SigmaCompactSpace L.M := L.sigmaCompact
    lLength (I := I) L.S T alpha a b
  change (∀ᵐ s ∂volume.restrict (uIoc a b),
      Tendsto (fun k => scalarSeq k s) atTop (𝓝 (scalarLim s))) →
    (∀ᵐ s ∂volume.restrict (uIoc a b),
      Tendsto (fun k => kineticSeq k s) atTop (𝓝 (kineticLim s))) →
      (∀ᶠ k in atTop, AEStronglyMeasurable (densitySeq k)
        (volume.restrict (uIoc a b))) →
        (∃ bound : Real → Real, Integrable bound (volume.restrict (uIoc a b)) ∧
          ∀ᶠ k in atTop, ∀ᵐ s ∂volume.restrict (uIoc a b),
            ‖densitySeq k s‖ ≤ bound s) →
          Tendsto actionSeq atTop (𝓝 actionLim)
  intro hScalar hKinetic hmeas hbound
  let mu : Measure Real := volume.restrict (uIoc a b)
  have hlim : ∀ᵐ s ∂mu,
      Tendsto (fun k => densitySeq k s) atTop (𝓝 (densityLim s)) := by
    filter_upwards [hScalar, hKinetic] with s hR hQ
    exact tendsto_const_nhds.mul (hR.add hQ)
  obtain ⟨bound, hboundInt, hbound⟩ := hbound
  have hint := tendsto_integral_filter_of_dominated_convergence
    (μ := mu) bound hmeas hbound hboundInt hlim
  simpa only [actionSeq, actionLim, lLength,
    intervalIntegral.intervalIntegral_eq_integral_uIoc, densitySeq, densityLim,
    scalarSeq, scalarLim, kineticSeq, kineticLim, lDensity, lSpeedSq, mu]
    using hint.const_smul (if a ≤ b then (1 : ℝ) else -1)

end AlmostEverywhere

section Geometric

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

open PDE.RicciFlow (SolutionOn)
open PDE.RicciFlow.Perelman (lSpeedSq_contOn aestronglyMeasurable_lDensity)
open Geometry.Curvature (metricScalarAt)

variable [I.Boundaryless]

private theorem density_ae_bound
    {rSeq qSeq : Nat → Real → Real} {rLim qLim : Real → Real}
    {a b : Real}
    (hr : TendstoUniformlyOn rSeq rLim atTop (Icc a b))
    (hq : TendstoUniformlyOn qSeq qLim atTop (Icc a b))
    (hrc : ContinuousOn rLim (Icc a b))
    (hqc : ContinuousOn qLim (Icc a b)) :
    ∃ C : Real, ∀ᶠ k in atTop,
      ∀ᵐ s ∂volume.restrict (Ioc a b),
        ‖Real.sqrt s * (rSeq k s + qSeq k s)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hrc.add hqc).norm
  obtain ⟨Cs, hCs⟩ := isCompact_Icc.bddAbove_image
    Real.continuous_sqrt.norm.continuousOn
  have hseq := TendstoUniformlyOn.eventually_norm_le (hr.add hq)
    (fun s hs => hC ⟨s, hs, rfl⟩)
  refine ⟨max Cs 0 * (C + 1), ?_⟩
  filter_upwards [hseq] with k hk
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsIcc : s ∈ Icc a b := ⟨hs.1.le, hs.2⟩
  rw [norm_mul]
  exact mul_le_mul ((hCs ⟨s, hsIcc, rfl⟩).trans (le_max_left _ _))
    (hk s hsIcc) (norm_nonneg _) (le_max_right _ _)


theorem FlowMetricConvergenceData.tendsto_lLength_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * R.inner (y : (L.atTime 0).M) v v ≤
            let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (sourceMetric (I := I) Phi hsrc htgt k t).inner y v v)
    (hcovTail : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Phi R bf hsrc htgt beta psi)
    (htime : Icc beta psi ⊆ X.D.carrier)
    (hLmetric : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
        let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (T a b : Real) (alpha : Real → (L.atTime 0).M)
    (halpha : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (uIcc a b) (Icc beta psi)) :
    Tendsto
      (fun k ↦
        let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : T2Space (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).t2
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).sigmaCompact
        lLength (I := I) (X.term (subseq (co.φ k))).S T
          (fun r ↦ Phi.map (co.φ k) (alpha r)) a b)
      atTop
      (𝓝 <|
        let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
        let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
        lLength (I := I) L.S T alpha a b) := by
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : T2Space (L.atTime 0).M := (L.atTime 0).t2
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (L.atTime 0).M := by
    change IsManifold I ∞ (L.atTime 0).M
    infer_instance
  let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let Phi' := Phi.compSubseq co.φ co.strictMono
  let scalarSeq : Nat → Real → Real := fun k s ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    (X.term (subseq (co.φ k))).S.scalar (T - s)
      (Phi.map (co.φ k) (alpha s))
  let kineticSeq : Nat → Real → Real := fun k s ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    ((X.term (subseq (co.φ k))).S.family.metric (T - s)).inner
      (Phi.map (co.φ k) (alpha s))
      (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s)
      (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s)
  let scalarLim : Real → Real := fun s ↦ L.S.scalar (T - s) (alpha s)
  let kineticLim : Real → Real := fun s ↦
    (L.S.base.metric (T - s)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  let densitySeq : Nat → Real → Real := fun k s ↦
    Real.sqrt s * (scalarSeq k s + kineticSeq k s)
  let K : Set L.M := alpha '' uIcc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn halpha.continuous.continuousOn
  have hScalarRaw : TendstoUniformlyOn scalarSeq
      (fun s ↦ metricScalarAt (I := I) (co.gInf (T - s)) (alpha s))
      atTop (uIcc a b) := by
    have h := co.tendstoUniformlyOn_scalar Phi R bf hsrc htgt beta psi
      cLow hcLow hbound hcovTail K hK
    exact (h.comp (fun s => (T - s, alpha s))).mono
      (fun s hs => ⟨hback hs, ⟨s, hs, rfl⟩⟩)
  have hScalar : TendstoUniformlyOn scalarSeq scalarLim atTop (uIcc a b) :=
    hScalarRaw.congr_right fun s hs ↦ by
      change metricScalarAt (I := I) (co.gInf (T - s)) (alpha s) =
        metricScalarAt (I := I) (L.S.base.metric (T - s)) (alpha s)
      rw [← SolutionOn.family_metric, hLmetric (T - s) (hback hs)]
      rfl
  have hKineticRaw := FlowMetricConvergenceData.tendstoUniformlyOn_inner_lVelocity_map (I := I) Phi R bf hsrc htgt
    beta psi co T (min a b) (max a b) alpha halpha hback
  have hKinetic : TendstoUniformlyOn kineticSeq kineticLim atTop (uIcc a b) := by
    simpa only [kineticSeq, kineticLim, Function.comp_apply, Set.uIcc] using
      hKineticRaw.congr_right (fun s hs ↦ by
        change (co.gInf (T - s)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
          (L.S.base.metric (T - s)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
        rw [← SolutionOn.family_metric, hLmetric (T - s) (hback hs)]
        rfl)
  have hbackCarrier : MapsTo (fun s ↦ T - s) (uIcc a b) X.D.carrier :=
    fun _ hs ↦ htime (hback hs)
  have hScalarCont : ContinuousOn scalarLim (uIcc a b) := by
    have hpair : ContinuousOn (fun s : Real ↦ (T - s, alpha s)) (uIcc a b) :=
      ((continuous_const.sub continuous_id).prodMk halpha.continuous).continuousOn
    have hmaps : MapsTo (fun s : Real ↦ (T - s, alpha s)) (uIcc a b)
        (X.D.carrier ×ˢ (univ : Set L.M)) :=
      fun _ hs ↦ ⟨hbackCarrier hs, mem_univ _⟩
    have h := L.isSolution.scalarCont.comp hpair hmaps
    apply h.congr
    intro s hs
    rfl
  have hKineticCont : ContinuousOn kineticLim (uIcc a b) := by
    have hcont := lSpeedSq_contOn L.S T a b alpha L.isSolution.smoothMetric
      halpha hbackCarrier
    change ContinuousOn (lSpeedSq L.S T alpha) (uIcc a b)
    exact hcont
  have hDensityBound : ∃ C : Real, ∀ᶠ k in atTop,
      ∀ᵐ s ∂volume.restrict (uIoc a b), ‖densitySeq k s‖ ≤ C := by
    simpa only [densitySeq, Set.uIoc] using
      density_ae_bound hScalar hKinetic hScalarCont hKineticCont
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hK
  have hDensityMeas : ∀ᶠ k in atTop,
      AEStronglyMeasurable (densitySeq k) (volume.restrict (uIoc a b)) := by
    filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    have hphi : kgrow ≤ co.φ k := hk.trans (co.strictMono.id_le k)
    have hsrcCurve : MapsTo alpha (Ioo (min a b) (max a b)) (Phi.source (co.φ k)) := by
      intro s hs
      exact bf.grow_subset (co.φ k)
        (hkgrow (co.φ k) hphi ⟨s, (show s ∈ uIcc a b from ⟨hs.1.le, hs.2.le⟩), rfl⟩)
    have hcurve : ContMDiffOn 𝓘(Real, Real) I 1
        (fun r ↦ Phi.map (co.φ k) (alpha r)) (Ioo (min a b) (max a b)) :=
      ((Phi.partialDiffeomorph (co.φ k)).contMDiffOn_toFun.of_le
        (by exact_mod_cast le_top)).comp
        halpha.contMDiffOn hsrcCurve
    have hmeas := aestronglyMeasurable_lDensity (I := I)
      (X.term (subseq (co.φ k))).S T (min a b) (max a b)
      (fun r ↦ Phi.map (co.φ k) (alpha r))
      (X.term (subseq (co.φ k))).isSolution.smoothMetric
      (X.term (subseq (co.φ k))).isSolution.scalarCont
      hcurve (fun s hs ↦ htime (hback ((show s ∈ uIcc a b from ⟨hs.1.le, hs.2.le⟩))))
    change AEStronglyMeasurable
      (lDensity (X.term (subseq (co.φ k))).S T
        (fun r => Phi.map (co.φ k) (alpha r))) (volume.restrict (uIoc a b))
    exact hmeas
  have hfinal := Phi'.tendsto_lLength_map_of_tendsto_ae T a b alpha
  apply (by simpa only [Phi', PointedCGHMaps.compSubseq_map, Function.comp_apply] using hfinal)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact hScalar.tendsto_at ⟨hs.1.le, hs.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact hKinetic.tendsto_at ⟨hs.1.le, hs.2⟩
  · exact hDensityMeas
  · obtain ⟨C, hC⟩ := hDensityBound
    let : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
      change IsFiniteMeasure (volume.restrict (Ioc (min a b) (max a b)))
      infer_instance
    exact ⟨fun _ => C, integrable_const C, hC⟩


end Geometric

section Sobolev

open Bundle Function
open scoped Interval

open Analysis.Parabolic.TimeSobolev Geometry.Curvature PDE.RicciFlow PDE.RicciFlow.Perelman

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem FlowMetricConvergenceData.lRegularizedAction_le_liminf_of_timeH1
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi cLow : Real) (hcLow : 0 < cLow)
    (hBound : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * R.inner (y : (L.atTime 0).M) v v ≤
            let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (sourceMetric (I := I) Phi hSrc hTgt k t).inner y v v)
    (hCovTail : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hSrc hTgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (hReg : Icc beta psi ⊆ X.D.regular)
    (hLMetric : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (T a b : Real) (hab : a ≤ b) (p : L.M)
    (alpha : Nat → Real → L.M) (alphaLim : Real → L.M)
    (u : Nat → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (hChart : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hRep : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hLimChart : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc a b) (chartAt H p).source)
    (hLimRep : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I p (alphaLim (a + r))) (Icc (0 : Real) (b - a)))
    (K : Set E) (hKc : IsCompact K)
    (hKChart : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : IsManifold I ∞ L.M := L.smooth
      K ⊆ (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (hBack : MapsTo (fun s ↦ T - s ^ 2) (Icc a b) (Icc beta psi)) :
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : T2Space L.M := L.t2
    let : IsManifold I ∞ L.M := L.smooth
    let : SigmaCompactSpace L.M := L.sigmaCompact
    lRegularizedAction L.S T alphaLim a b ≤ liminf (fun k ↦
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      lRegularizedAction (X.term (subseq (co.φ k))).S T
        (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b) atTop := by
  classical
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : T2Space (L.atTime 0).M := (L.atTime 0).t2
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let Q : Set L.M := (extChartAt I p).symm '' K
  have hQc : IsCompact Q :=
    hKc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hKChart)
  have huLimK : ∀ r : Icc (0 : Real) (b - a), uLim.toFun r.1 ∈ K := by
    intro r
    apply hKc.isClosed.mem_of_tendsto (hu.tendsto_at r)
    exact Eventually.of_forall fun n ↦ huK n r
  let shift : Icc a b → Icc (0 : ℝ) (b - a) := fun s =>
    ⟨s.1 - a, sub_nonneg.mpr s.2.1, sub_le_sub_right s.2.2 a⟩
  have hrepInv (n : ℕ) (s : Icc a b) :
      (extChartAt I p).symm ((u n).toFun (shift s)) = alpha n s.1 := by
    rw [hRep n (shift s).2]
    change (extChartAt I p).symm (extChartAt I p (alpha n (a + (shift s : ℝ)))) = _
    rw [show a + (shift s : ℝ) = s.1 by dsimp [shift]; ring]
    exact (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hChart n s.2)
  have hrepInvLim (s : Icc a b) :
      (extChartAt I p).symm (uLim.toFun (shift s)) = alphaLim s.1 := by
    rw [hLimRep (shift s).2]
    change (extChartAt I p).symm (extChartAt I p (alphaLim (a + (shift s : ℝ)))) = _
    rw [show a + (shift s : ℝ) = s.1 by dsimp [shift]; ring]
    exact (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hLimChart s.2)
  have hQ (n : ℕ) (s : Icc a b) : alpha n s.1 ∈ Q :=
    ⟨(u n).toFun (shift s), huK n (shift s), hrepInv n s⟩
  have hLimQ (s : Icc a b) : alphaLim s.1 ∈ Q :=
    ⟨uLim.toFun (shift s), huLimK (shift s), hrepInvLim s⟩
  let : TopologicalSpace.MetrizableSpace L.M := Manifold.metrizableSpace I L.M
  let uP : UniformSpace L.M := TopologicalSpace.pseudoMetrizableSpaceUniformity L.M
  have hTop : uP.toTopologicalSpace = L.topology := rfl
  have halphaLim : let : UniformSpace L.M := uP
      TendstoUniformly (fun n (s : Icc a b) => alpha n s.1)
        (fun s => alphaLim s.1) atTop := by
    let : UniformSpace L.M := uP
    have huc : UniformContinuousOn (extChartAt I p).symm K :=
      hKc.uniformContinuousOn_of_continuous ((continuousOn_extChartAt_symm p).mono hKChart)
    have hc := UniformContinuousOn.comp_tendstoUniformly
      (fun n s => huK n (shift s)) (fun s => huLimK (shift s)) huc (hu.comp shift)
    simpa only [Function.comp_apply, hrepInv, hrepInvLim] using hc
  let len : Real := b - a
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let GSeq : Nat → MetricConnectionFamilyOn (I := I) (M := (L.atTime 0).M) X.D := fun n ↦
    (lcMetricFamily (I := I) (M := (L.atTime 0).M)
      (fun t ↦ gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ n) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := (L.atTime 0).M) X.D :=
    (lcMetricFamily (I := I) (M := (L.atTime 0).M) co.gInf).restrict X.D
  let mapped (n : Nat) : Real → (X.term (subseq (co.φ n))).M :=
    fun s ↦ Phi.map (co.φ n) (alpha n s)
  let kinChart : Nat → Real := fun n ↦
    ∫ r in (0 : Real)..len, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) (GSeq n) p
        (tau r, (u n).toFun r) ((u n).deriv r)) ((u n).deriv r)
  let kinLimChart : Real :=
    ∫ r in (0 : Real)..len, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) GInf p
        (tau r, uLim.toFun r) (uLim.deriv r)) (uLim.deriv r)
  let kinFun : Nat → Real → Real := fun n ↦
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    fun s ↦ (1 / 2 : Real) *
      ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
        (mapped n s) (lVelocity (I := I) (mapped n) s)
        (lVelocity (I := I) (mapped n) s)
  let kin : Nat → Real := fun n ↦ ∫ s in a..b, kinFun n s
  let pot : Nat → Real := fun n ↦
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    ∫ s in a..b, 2 * s ^ 2 *
      (X.term (subseq (co.φ n))).S.scalar (T - s ^ 2) (mapped n s)
  let act : Nat → Real := fun n ↦
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    lRegularizedAction (X.term (subseq (co.φ n))).S T (mapped n) a b
  let kinLim : Real := ∫ s in a..b, (1 / 2 : Real) *
    (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
      (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s)
  let potLim : Real := ∫ s in a..b,
    2 * s ^ 2 * L.S.scalar (T - s ^ 2) (alphaLim s)
  have hLen : 0 ≤ len := by simpa only [len] using sub_nonneg.mpr hab
  have hTauCont : ContinuousOn tau (Icc (0 : Real) len) := by
    exact continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hTau : MapsTo tau (Icc (0 : Real) len) (Icc beta psi) := by
    intro r hr
    apply hBack
    exact ⟨le_add_of_nonneg_right hr.1, by dsimp only [len] at hr; linarith [hr.2]⟩
  have hTime : Icc beta psi ⊆ X.D.carrier :=
    fun _ ht ↦ X.D.regular_subset (hReg ht)
  have hDiff (n : Nat) : ∀ᵐ r ∂timeMeasure len,
      MDifferentiableAt 𝓘(Real, Real) I (alpha n) (a + r) := by
    simpa only [len] using
      curve_mdiff_local I p (alpha n) (u n) hab (hChart n) (hRep n)
  have hAlphaCont (n : ℕ) : ContinuousOn (alpha n) (Icc a b) :=
    curve_cont_local I p (alpha n) (u n) hab (hChart n) (hRep n)
  have hLimCont : ContinuousOn alphaLim (Icc a b) :=
    curve_cont_local I p alphaLim uLim hab hLimChart hLimRep
  have hKinRaw := FlowMetricConvergenceData.integral_inner_chartGramOp_le_liminf (I := I) (X := X)
    Phi R bf hSrc hTgt beta psi co hTime p hLen tau hTauCont hTau
    hKc hKChart u uLim (by simpa only [len] using huK)
    huLimK (by simpa only [len] using hu) (by simpa only [len] using hdu)
  have hKinRaw' : kinLimChart ≤ liminf kinChart atTop := by
    simpa only [kinLimChart, kinChart, GInf, GSeq, tau, len] using hKinRaw
  have hLimMetric : kinLim = kinLimChart := by
    have hMetricEq : (∫ s in a..b, (1 / 2 : Real) *
        (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
          (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s)) =
        ∫ s in a..b, (1 / 2 : Real) *
          (co.gInf (T - s ^ 2)).inner (alphaLim s)
            (lVelocity (I := I) alphaLim s)
            (lVelocity (I := I) alphaLim s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply congrArg ((1 / 2 : Real) * ·)
      change (L.S.family.metric (T - s ^ 2)).inner _ _ _ = _
      rw [hLMetric (T - s ^ 2) (hBack (by
        simpa only [uIcc_of_le hab] using hs))]
      rfl
    dsimp only [kinLim]
    rw [hMetricEq]
    convert
      (integral_mul_inner_mfderiv_eq_integral_chartGramOp_of_timeH1
        GInf (fun s ↦ T - s ^ 2) (fun _ => (1 / 2 : ℝ))
        alphaLim p a b hab uLim hLimChart hLimRep) using 1
    rfl
  obtain ⟨kGrow, hkGrow⟩ := bf.grow_cover Q hQc
  have hGrow : ∀ᶠ n in atTop,
      ∀ s : Icc a b, alpha n s.1 ∈ bf.grow (co.φ n) := by
    filter_upwards [eventually_ge_atTop kGrow] with n hn
    intro s
    exact hkGrow (co.φ n) (hn.trans (co.strictMono.id_le n)) (hQ n s)
  have hKinEqInt : ∀ᶠ n in atTop, kinChart n = kin n ∧
      IntervalIntegrable (kinFun n) volume a b := by
    filter_upwards [hGrow] with n hn
    let : TopologicalSpace (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomTop (I := I) Phi (co.φ n)
    let : ChartedSpace H (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomCharted (I := I) Phi (co.φ n)
    let : T2Space (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomT2 (I := I) Phi (co.φ n)
    let : IsManifold I ∞ (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomSmooth (I := I) Phi (co.φ n)
    let : SigmaCompactSpace (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomSigmaOf (I := I) Phi (co.φ n) (hSrc (co.φ n))
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    obtain ⟨W, _hWOpen, hGrowW, hOne⟩ := bf.chi_one (co.φ n)
    have hChartAE := chartGramOp_inner_deriv_ae_of_timeH1 (GSeq n) (fun s ↦ T - s ^ 2)
      (alpha n) p a b (u n) (hChart n) (hRep n)
    have hMem : ∀ᵐ r ∂timeMeasure len, r ∈ Ioo (0 : Real) len := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    have hPoint :
        (fun r ↦ (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) (GSeq n) p
            (tau r, (u n).toFun r) ((u n).deriv r)) ((u n).deriv r))
          =ᵐ[timeMeasure len]
        fun r ↦ (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
            (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
            (lVelocity (I := I) (mapped n) (r + a)) := by
      filter_upwards [hChartAE, hDiff n, hMem] with r hChartR hDiffR hr
      have hrcc : r ∈ Icc (0 : Real) len := ⟨hr.1.le, hr.2.le⟩
      have hsab : r + a ∈ Icc a b := by
        constructor
        · linarith [hrcc.1]
        · dsimp only [len] at hrcc
          linarith [hrcc.2]
      have hGrowAt := hn ⟨r + a, hsab⟩
      have hSource := bf.grow_subset (co.φ n) hGrowAt
      have hChi : bf.chi (co.φ n) (alpha n (r + a)) = 1 :=
        hOne _ (hGrowW hGrowAt)
      have hDiffR' : MDiffAt (alpha n) (r + a) := by
        simpa only [add_comm r a] using hDiffR
      have hExt := gSeqExt_inner_of_mem (I := I) Phi R bf hSrc hTgt
        (co.φ n) (T - (r + a) ^ 2) (alpha n (r + a)) hSource
        (lVelocity (I := I) (alpha n) (r + a))
        (lVelocity (I := I) (alpha n) (r + a))
      have hMap := PointedCGHMaps.sourceMetric_inner_lVelocity (I := I) Phi hSrc hTgt
        (co.φ n) (T - (r + a) ^ 2)
        (alpha n) (r + a) hSource hDiffR'
      have hExt' :
          (gSeqExt (I := I) Phi R bf hSrc hTgt
            (co.φ n) (T - (r + a) ^ 2)).inner
              (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) =
            (sourceMetric (I := I) Phi hSrc hTgt
              (co.φ n) (T - (r + a) ^ 2)).inner
              ⟨alpha n (r + a), hSource⟩
              (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) := by
        simpa only [hChi, one_smul, sub_self, zero_smul, add_zero] using hExt
      have hPhys :
          ((GSeq n).metric (T - (r + a) ^ 2)).inner
              (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) =
            ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
              (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
              (lVelocity (I := I) (mapped n) (r + a)) := by
        simpa only [GSeq, mapped, MetricConnectionFamily.restrict_metric,
          lcMetricFamily, SolutionOn.family_metric] using hExt'.trans hMap
      have hChartR' :
          inner Real
              (((1 / 2 : Real) • chartGramOp (I := I) (GSeq n) p
                ((fun s ↦ T - s ^ 2) (a + r), (u n).toFun r)) ((u n).deriv r))
              ((u n).deriv r) =
            (1 / 2 : Real) *
              ((GSeq n).metric (T - (r + a) ^ 2)).inner
                (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
                (lVelocity (I := I) (alpha n) (r + a)) := by
        rw [add_comm r a]
        convert (congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) hChartR) using 1 <;>
          first | rfl | simp only [smul_apply, real_inner_smul_left]
      simpa only [tau, smul_apply, real_inner_smul_left,
        Function.comp_apply] using
        hChartR'.trans (congrArg ((1 / 2 : Real) * ·) hPhys)
    have hInt : kinChart n =
        ∫ r in (0 : Real)..len, (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
            (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
            (lVelocity (I := I) (mapped n) (r + a)) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simpa only [kinChart, timeMeasure, uIoc_of_le hLen,
        restrict_Ioc_eq_restrict_Icc] using hPoint
    let A : ℝ → E →L[ℝ] E := fun r =>
      (1 / 2 : ℝ) • chartGramOp (I := I) (GSeq n) p (tau r, (u n).toFun r)
    have hACont : ContinuousOn A (Icc (0 : ℝ) len) := by
      have h := (continuousOn_chartGramOp_gSeqExt (I := I) (X := X)
        Phi R bf hSrc hTgt (co.φ n) p hKChart).comp
        (hTauCont.prodMk (u n).continuousOn_toFun)
        (fun r hr => ⟨hTime (hTau hr), huK n ⟨r, hr⟩⟩)
      exact h.fun_const_smul (1 / 2 : ℝ)
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hACont.norm
    let C' : NNReal := ⟨max C 0, le_max_right _ _⟩
    have hBoundA : ∀ᵐ r ∂timeMeasure len, ‖A r‖ ≤ (C' : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hC ⟨r, hr, rfl⟩).trans (le_max_left _ _)
    have hQuad := timeQuad_int A
      (hACont.aestronglyMeasurable measurableSet_Icc) C' hBoundA hLen (u n).deriv
    have hPoint' :
        (fun r => inner ℝ (A r ((u n).deriv r)) ((u n).deriv r))
          =ᵐ[volume.restrict (Ι (0 : ℝ) len)] fun r => kinFun n (r + a) := by
      rw [uIoc_of_le hLen, restrict_Ioc_eq_restrict_Icc]
      simpa only [A, smul_apply, real_inner_smul_left, timeMeasure, kinFun] using hPoint
    have hShiftInt := hQuad.congr_ae hPoint'
    refine ⟨?_, ?_⟩
    · rw [hInt]
      change (∫ r in (0 : Real)..len, kinFun n (r + a)) = ∫ s in a..b, kinFun n s
      simpa only [zero_add, len, sub_add_cancel] using
        (intervalIntegral.integral_comp_add_right (kinFun n)
          (a := 0) (b := b - a) a)
    · have hOriginal := (IntervalIntegrable.comp_add_right_iff
        (f := kinFun n) (a := 0) (b := len) (c := a)).mp hShiftInt
      simpa only [zero_add, len, sub_add_cancel] using hOriginal
  have hKinEq : kinChart =ᶠ[atTop] kin := hKinEqInt.mono fun _ h => h.1
  have hKin : kinLim ≤ liminf kin atTop := by
    rw [hLimMetric]
    rw [Filter.liminf_congr hKinEq] at hKinRaw'
    exact hKinRaw'
  let scalarSeq : Nat → Icc a b → Real := fun n s ↦
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    (X.term (subseq (co.φ n))).S.scalar (T - s.1 ^ 2) (mapped n s.1)
  let scalarLim : Icc a b → Real := fun s ↦
    L.S.scalar (T - s.1 ^ 2) (alphaLim s.1)
  have hScalarRaw := FlowMetricConvergenceData.tendstoUniformly_scalar (I := I) Phi R bf hSrc hTgt
    beta psi cLow hcLow hBound hCovTail co
    (fun s : Icc a b ↦ T - s.1 ^ 2) (fun n s ↦ alpha n s.1) (fun s ↦ alphaLim s.1)
    uP hTop halphaLim Q hQc (Eventually.of_forall hQ) hLimQ
    (fun s ↦ hBack s.2) hTime
  have hScalarEq :
      (fun s : Icc a b ↦
        metricScalarAt (I := I) (co.gInf (T - s.1 ^ 2)) (alphaLim s.1)) =
        scalarLim := by
    funext s
    change metricScalarAt (I := I) (co.gInf (T - s.1 ^ 2)) (alphaLim s.1) =
      metricScalarAt (I := I) (L.S.base.metric (T - s.1 ^ 2)) (alphaLim s.1)
    rw [← SolutionOn.family_metric,
      hLMetric (T - s.1 ^ 2) (hBack s.2)]
    rfl
  have hScalar : TendstoUniformly scalarSeq scalarLim atTop := by
    rw [← hScalarEq]
    simpa only [scalarSeq, mapped, Function.comp_apply] using hScalarRaw
  let F : Nat → Real → Real := fun n s ↦
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    2 * s ^ 2 * (X.term (subseq (co.φ n))).S.scalar
      (T - s ^ 2) (mapped n s)
  let f : Real → Real := fun s ↦
    2 * s ^ 2 * L.S.scalar (T - s ^ 2) (alphaLim s)
  have hScalarLimCont : ContinuousOn
      (fun s : Real ↦ L.S.scalar (T - s ^ 2) (alphaLim s)) (Icc a b) := by
    have hPair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alphaLim s))
        (Icc a b) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk hLimCont
    have hMaps : MapsTo (fun s : Real ↦ (T - s ^ 2, alphaLim s))
        (Icc a b) (X.D.carrier ×ˢ (univ : Set L.M)) :=
      fun _ hs ↦ ⟨hTime (hBack hs), mem_univ _⟩
    simpa only [Function.comp_def] using
      L.isSolution.scalarCont.comp hPair hMaps
  have hPotLimInt : IntervalIntegrable f volume a b := by
    have hCont : ContinuousOn f (Icc a b) := by
      exact (continuous_const.mul (continuous_id.pow 2)).continuousOn.mul
        hScalarLimCont
    have hCont' : ContinuousOn f [[a, b]] := by
      simpa only [uIcc_of_le hab] using hCont
    exact hCont'.intervalIntegrable
  have hFMeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (F n) (volume.restrict (uIoc a b)) := by
    filter_upwards [hGrow] with n hn
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    have hSource : MapsTo (alpha n) (Icc a b) (Phi.source (co.φ n)) :=
      fun s hs ↦ bf.grow_subset (co.φ n) (hn ⟨s, hs⟩)
    have hMapCont : ContinuousOn (mapped n) (Icc a b) := by
      convert (Phi.partialDiffeomorph (co.φ n)).contMDiffOn_toFun.continuousOn.comp
        (hAlphaCont n) hSource using 1
      rfl
    have hPair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, mapped n s))
        (Icc a b) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk
        hMapCont
    have hMaps : MapsTo (fun s : Real ↦ (T - s ^ 2, mapped n s))
        (Icc a b)
        (X.D.carrier ×ˢ (univ : Set (X.term (subseq (co.φ n))).M)) :=
      fun _ hs ↦ ⟨hTime (hBack hs), mem_univ _⟩
    have hScCont : ContinuousOn
        (fun s : Real ↦ (X.term (subseq (co.φ n))).S.scalar
          (T - s ^ 2) (mapped n s)) (Icc a b) := by
      simpa only [Function.comp_def] using
        (X.term (subseq (co.φ n))).isSolution.scalarCont.comp hPair hMaps
    have hCont : ContinuousOn (F n) (Icc a b) := by
      convert (continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hScCont using 1 <;> rfl
    simpa only [uIoc_of_le hab, F, mapped] using
      (hCont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨cSc, hcSc⟩ := isCompact_Icc.bddAbove_image hScalarLimCont.norm
  let CSc : Real := max cSc 0
  have hCSc : ∀ s : Icc a b, ‖scalarLim s‖ ≤ CSc := by
    intro s
    exact (hcSc ⟨s.1, s.2, rfl⟩).trans (le_max_left _ _)
  let weight : Real → Real := fun s ↦ 2 * s ^ 2
  have hWeightCont : ContinuousOn weight (Icc a b) :=
    (continuous_const.mul (continuous_id.pow 2)).continuousOn
  obtain ⟨cW, hcW⟩ := isCompact_Icc.bddAbove_image hWeightCont.norm
  let CW : Real := max cW 0
  have hCW0 : 0 ≤ CW := le_max_right _ _
  have hCW : ∀ s : Icc a b, ‖weight s.1‖ ≤ CW := by
    intro s
    exact (hcW ⟨s.1, s.2, rfl⟩).trans (le_max_left _ _)
  let dom : Real → Real := fun _ ↦ CW * (CSc + 1)
  have hDomInt : IntervalIntegrable dom volume a b := intervalIntegrable_const
  have hClose := (Metric.tendstoUniformly_iff.mp hScalar) 1 zero_lt_one
  have hDom : ∀ᶠ n in atTop, ∀ᵐ s ∂volume,
      s ∈ uIoc a b → ‖F n s‖ ≤ dom s := by
    filter_upwards [hClose] with n hn
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      let ss : Icc a b := ⟨s, hsIcc⟩
      have hd := (hn ss).le
      have hSeq : ‖scalarSeq n ss‖ ≤ CSc + 1 := by
        calc
          ‖scalarSeq n ss‖ ≤ ‖scalarLim ss‖ +
              ‖scalarSeq n ss - scalarLim ss‖ := norm_le_norm_add_norm_sub' _ _
          _ ≤ CSc + 1 := add_le_add (hCSc ss) (by
            simpa only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hd)
      change ‖weight s * scalarSeq n ss‖ ≤ CW * (CSc + 1)
      rw [norm_mul]
      exact mul_le_mul (hCW ss) hSeq (norm_nonneg _) hCW0
  have hPointPot : ∀ᵐ s ∂volume, s ∈ uIoc a b →
      Tendsto (fun n ↦ F n s) atTop (nhds (f s)) := by
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      let ss : Icc a b := ⟨s, hsIcc⟩
      have hAt := hScalar.tendsto_at ss
      change Tendsto (fun n ↦ weight s * scalarSeq n ss) atTop
        (nhds (weight s * scalarLim ss))
      exact tendsto_const_nhds.mul hAt
  have hPot : Tendsto pot atTop (nhds potLim) := by
    change Tendsto (fun n ↦ ∫ s in a..b, F n s) atTop
      (nhds (∫ s in a..b, f s))
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) dom hFMeas hDom hDomInt hPointPot
  have hSplit : act =ᶠ[atTop] fun n ↦ kin n + pot n := by
    filter_upwards [hGrow, hKinEqInt] with n hn hkin
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    let : TopologicalSpace.MetrizableSpace
        (X.term (subseq (co.φ n))).M :=
      Manifold.metrizableSpace I (X.term (subseq (co.φ n))).M
    let : UniformSpace (X.term (subseq (co.φ n))).M :=
      TopologicalSpace.pseudoMetrizableSpaceUniformity
        (X.term (subseq (co.φ n))).M
    have hSource : MapsTo (alpha n) (Icc a b) (Phi.source (co.φ n)) :=
      fun s hs ↦ bf.grow_subset (co.φ n) (hn ⟨s, hs⟩)
    have hMapCont : ContinuousOn (mapped n) (Icc a b) := by
      convert (Phi.partialDiffeomorph (co.φ n)).contMDiffOn_toFun.continuousOn.comp
        (hAlphaCont n) hSource using 1
      rfl
    have hSc : ScalarSTContOn (I := I)
        (M := (X.term (subseq (co.φ n))).M)
        (X.term (subseq (co.φ n))).S :=
      ⟨(X.term (subseq (co.φ n))).isSolution.scalarCont⟩
    have hPotInt := lScalar_int (I := I) (X.term (subseq (co.φ n))).S
      hSc T a b (mapped n)
      (fun s hs ↦ hTime (hBack (by simpa only [uIcc_of_le hab] using hs)))
      (by simpa only [uIcc_of_le hab] using hMapCont)
    have hKinInt : IntervalIntegrable
        (fun s ↦ (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
            (mapped n s) (lVelocity (I := I) (mapped n) s)
            (lVelocity (I := I) (mapped n) s)) volume a b := by
      exact hkin.2
    simpa only [act, kin, pot, lRegularizedAction, lRegularizedLagrangian] using
      intervalIntegral.integral_add hKinInt hPotInt
  have hKinNonneg : ∀ n, 0 ≤ kin n := by
    intro n
    let : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    let : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    let : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    change 0 ≤ ∫ s in a..b, (1 / 2 : Real) *
      ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
        (mapped n s) (lVelocity (I := I) (mapped n) s)
        (lVelocity (I := I) (mapped n) s)
    apply intervalIntegral.integral_nonneg hab
    intro s _hs
    exact mul_nonneg (by norm_num)
      (by
        by_cases hv : lVelocity (I := I) (mapped n) s = 0
        · simp only [hv, map_zero]
          exact le_rfl
        · exact (((X.term (subseq (co.φ n))).S.base.metric
            (T - s ^ 2)).pos (mapped n s)
              (lVelocity (I := I) (mapped n) s) hv).le)
  have hKinLo : IsBoundedUnder (· ≥ ·) atTop kin :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hKinNonneg)
  have hKinHi : IsBoundedUnder (· ≤ ·) atTop kin := by
    let A : ℕ → ℝ → E →L[ℝ] E := fun n r =>
      (1 / 2 : ℝ) • chartGramOp (I := I) (GSeq n) p (tau r, (u n).toFun r)
    let ALim : ℝ → E →L[ℝ] E := fun r =>
      (1 / 2 : ℝ) • chartGramOp (I := I) GInf p (tau r, uLim.toFun r)
    have hACont (n : ℕ) : ContinuousOn (A n) (Icc (0 : ℝ) len) := by
      have h := (continuousOn_chartGramOp_gSeqExt (I := I) (X := X)
        Phi R bf hSrc hTgt (co.φ n) p hKChart).comp
        (hTauCont.prodMk (u n).continuousOn_toFun)
        (fun r hr => ⟨hTime (hTau hr), huK n ⟨r, hr⟩⟩)
      exact h.fun_const_smul (1 / 2 : ℝ)
    have hGInfCont : ContinuousOn (chartGramOp (I := I) GInf p) (Icc beta psi ×ˢ K) :=
      co.continuousOn_chartGramOp Phi R bf hSrc hTgt beta psi p hKChart hKc hTime
    have hALimCont : ContinuousOn ALim (Icc (0 : ℝ) len) := by
      have h := hGInfCont.comp (hTauCont.prodMk uLim.continuousOn_toFun)
        (fun r hr => ⟨hTau hr, huLimK ⟨r, hr⟩⟩)
      exact h.fun_const_smul (1 / 2 : ℝ)
    have hGramUnif : TendstoUniformly
        (fun n (r : Icc (0 : ℝ) len) =>
          chartGramOp (I := I) (GSeq n) p (tau r.1, (u n).toFun r.1))
        (fun r => chartGramOp (I := I) GInf p (tau r.1, uLim.toFun r.1)) atTop := by
      simpa only [GSeq, GInf] using
        (co.tendstoUniformly_chartGramOp Phi R bf hSrc hTgt beta psi p hKChart hKc hGInfCont
          (tau := fun r : Icc (0 : ℝ) len => tau r.1)
          (u := fun n r => (u n).toFun r.1) (uLim := fun r => uLim.toFun r.1)
          (fun r => hTau r.2) (Eventually.of_forall huK) huLimK hu)
    have hconv : TendstoUniformlyOn A ALim atTop (Icc (0 : ℝ) len) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      simpa only [A, ALim, Function.comp_def] using
        (uniformContinuous_const_smul (1 / 2 : ℝ)).comp_tendstoUniformly hGramUnif
    have hb := isBoundedUnder_norm_integral_inner_of_tendstoUniformlyOn
      A ALim hACont hALimCont hconv hLen (fun n => (u n).deriv) uLim.deriv hdu
    have hb' : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖kinChart n‖) := by
      simpa only [kinChart, A, smul_apply, real_inner_smul_left] using hb
    obtain ⟨B, hB⟩ := hb'
    refine ⟨B, ?_⟩
    change ∀ᶠ n in atTop, kin n ≤ B
    filter_upwards [hB, hKinEq] with n hn heq
    rw [← heq]
    exact (le_abs_self (kinChart n)).trans hn
  have hSum : kinLim + potLim ≤ liminf (fun n => kin n + pot n) atTop := by
    calc
      kinLim + potLim ≤ liminf kin atTop + potLim := add_le_add_left hKin potLim
      _ = liminf kin atTop + liminf pot atTop := by rw [hPot.liminf_eq]
      _ ≤ liminf (fun n => kin n + pot n) atTop := by
        convert (le_liminf_add hKinLo hKinHi
          hPot.isBoundedUnder_ge hPot.isCoboundedUnder_ge) using 1 <;> rfl
  have hLiminfAct : liminf act atTop =
      liminf (fun n ↦ kin n + pot n) atTop :=
    Filter.liminf_congr hSplit
  rw [← hLiminfAct] at hSum
  have hKinLimInt : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
          (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s))
      volume a b :=
    intervalIntegrable_lKinetic_of_chartH1 L.S L.isSolution.smoothMetric T alphaLim p a b hab uLim
      hLimChart hLimRep (fun s hs ↦ hReg (hBack hs))
  have hLimSplit : lRegularizedAction L.S T alphaLim a b = kinLim + potLim := by
    simpa only [lRegularizedAction, lRegularizedLagrangian, kinLim, potLim] using
      intervalIntegral.integral_add hKinLimInt hPotLimInt
  change lRegularizedAction L.S T alphaLim a b ≤ liminf act atTop
  rw [hLimSplit]
  exact hSum

end Sobolev

end DifferentialGeometry.CheegerGromovCompactness
