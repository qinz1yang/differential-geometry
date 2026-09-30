import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def SpatialCrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧ εbar ≤ coneAccuracy ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ Cx : ℝ, 1 ≤ Cx ∧
  ∀ B : ℝ, 0 < B →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi → 0 < θ →
  ∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ →
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η₃ →
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η₃ →
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ H.time j.succ ∧
            ∀ (y : (H.stage j.castSucc).Carrier) (t : ℝ),
            H.time j.castSucc < t → t₀ ≤ t → t < t₀ + η → t < H.time j.succ →
            qs < (H.toHistory.event j).incoming.flow.scalar t y →
            (H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc) < θ →
            ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness
                ((H.toHistory.event j).incoming.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ → G.DerivativeBoundOn Ctime qcan t₀ η₃ →
            G.GradientBoundOn Cgrad qcan t₀ η₃ → G.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ s ∧
            ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
            H.time (Fin.last H.eventCount) < t → t₀ ≤ t → t < t₀ + η → t < s →
            qs < G.flow.scalar t y →
            G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ →
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
