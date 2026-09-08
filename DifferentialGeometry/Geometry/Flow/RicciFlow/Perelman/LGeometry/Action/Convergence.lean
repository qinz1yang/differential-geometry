import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open PDE.RicciFlow.Perelman (lDensity lLength lSpeedSq lVelocity)

universe u uE uH

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

end DifferentialGeometry.CheegerGromovCompactness
