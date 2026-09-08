import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.KineticConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularity
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

end DifferentialGeometry.CheegerGromovCompactness
