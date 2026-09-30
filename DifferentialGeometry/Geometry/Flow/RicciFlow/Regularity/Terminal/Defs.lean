import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def TerminalJetContinuous (F : PointedFlowData.{u, uE, uH} (I := I) D) (b : ℝ) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ (k : ℕ) (x : F.M) (v : Fin (4 + k) → TangentSpace I x),
    ContinuousWithinAt (fun t : ℝ => nablaKRm04Field (I := I) F.S t k x v) (Set.Iic b) b

structure IsAncientKappaSolutionTerminal (kappa : ℝ)
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop where
  toAncient : IsAncientKappaSolution (I := I) kappa F
  terminalJets : TerminalJetContinuous (I := I) F 0

theorem IsAncientKappaSolutionTerminal.ancient {kappa : ℝ}
    {F : PointedFlowData.{u, uE, uH} (I := I) D}
    (h : IsAncientKappaSolutionTerminal (I := I) kappa F) :
    IsAncientKappaSolution (I := I) kappa F :=
  h.toAncient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
