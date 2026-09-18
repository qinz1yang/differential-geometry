import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientCanonicalNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalClassificationNormalization

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

def AncientModelClassificationDichotomy : Prop :=
  ∀ (kappa : ℝ), 0 < kappa →
    ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
      IsAncientKappaSolution (I := I3) kappa P →
        IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
          IsAncientKappaSolution (I := I3) universalKappaConstant P

def RoundModelCanonicalWitness : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsShrinkingSphericalSpaceFormFlow (I := I3) P →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0)

def UniversalKappaModelCanonicalWitness : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) universalKappaConstant P →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0)

def ModelCanonicalWitnessBranches : Prop :=
  RoundModelCanonicalWitness.{u} ∧ UniversalKappaModelCanonicalWitness.{u}

theorem modelCanonicalWitness_of_branches (hbranches : ModelCanonicalWitnessBranches.{u}) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0) := by
  intro eps heps hsmall
  obtain ⟨hround, huniversal⟩ := hbranches
  obtain ⟨A1, A2, hA1, hA2, hmainA⟩ := hround eps heps hsmall
  obtain ⟨B1, B2, hB1, hB2, hmainB⟩ := huniversal eps heps hsmall
  refine ⟨max A1 B1, max A2 B2, hA1.trans (le_max_left _ _),
    hA2.trans (le_max_left _ _), ?_⟩
  intro P hbranch hbase
  rcases hbranch with hspherical | hkappa
  · obtain ⟨W⟩ := hmainA P hspherical hbase
    exact ⟨W.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩
  · obtain ⟨W⟩ := hmainB P hkappa hbase
    exact ⟨W.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩

theorem kappaUniformCanonicalClassification_of_modelBranches
    (hdichotomy : AncientModelClassificationDichotomy.{u})
    (hbranches : ModelCanonicalWitnessBranches.{u})
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    kappaUniformCanonicalClassification.{u} :=
  kappaUniformCanonicalClassification_of_ancientModelClassification_halfWindow
    hdichotomy (modelCanonicalWitness_of_branches hbranches) htransfer

theorem ancientCanonicalNeighborhood_of_modelBranches
    (hdichotomy : AncientModelClassificationDichotomy.{u})
    (hbranches : ModelCanonicalWitnessBranches.{u})
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          IsAncientKappaSolution (I := I3) kappa P →
            PointedFlowScalarAtBase (I := I3) P 1 →
              TangentOrientationSection P.M →
                Nonempty (CanonicalWitness P.S eps C1 C2 P.basepoint 0) := by
  obtain ⟨epsCan, hepsCan, hpullback⟩ :=
    buffered_canonical_pullback_of_classification
      (kappaUniformCanonicalClassification_of_modelBranches hdichotomy hbranches htransfer)
  refine ⟨epsCan, hepsCan, fun eps heps hsmall => ?_⟩
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hpullback eps heps hsmall
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa P hanc hbase o => ?_⟩
  obtain ⟨delta, hdelta, hdelta1, htransfer'⟩ := hmain kappa hkappa
  exact htransfer' (M := P.M) (D := ancientTimeInterval) (S := P.S) P.isSolution
    (o := o) (x := P.basepoint) (t := 0) (fun _ hs => hs.2)
    (orientedWitness_self P hanc hbase o hdelta hdelta1)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
