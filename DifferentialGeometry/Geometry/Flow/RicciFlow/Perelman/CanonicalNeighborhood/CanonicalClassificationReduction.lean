import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientModelClassification

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem kappaUniformCanonicalClassification_of_buffered_canonical_pullback
    (hpb : ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t)) :
    kappaUniformCanonicalClassification.{u} := by
  intro eps heps heps44
  obtain ⟨epsCan, hepsCan, hmain⟩ := hpb
  obtain ⟨C1, C2, hC1, hC2, hfinal⟩ :=
    hmain (min (eps / 2) epsCan) (lt_min (by linarith) hepsCan) (min_le_right _ _)
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  obtain ⟨delta, hdelta, hdelta1, hmain'⟩ := hfinal kappa hkappa
  refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W⟩ := hmain' M D S hS o x t hreg hw
  exact ⟨W.mono_eps (min_le_left _ _) (by linarith)⟩

theorem buffered_canonical_pullback_iff_kappaUniformCanonicalClassification :
    kappaUniformCanonicalClassification.{u} ↔
      (∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
        ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S eps C1 C2 x t)) :=
  ⟨fun hclass => buffered_canonical_pullback_of_classification hclass,
    fun hpb => kappaUniformCanonicalClassification_of_buffered_canonical_pullback hpb⟩

theorem kappaUniformCanonicalClassification_iff_witness_tolerance :
    kappaUniformCanonicalClassification.{u} ↔
      (∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
        ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S eps C1 C2 x t)) := by
  constructor
  · intro hclass eps heps heps11
    obtain ⟨C1, C2, hC1, hC2, hfinal⟩ :=
      hclass (min eps (1 / 44)) (lt_min heps (by norm_num)) (min_le_right _ _)
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, hmain⟩ := hfinal kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := hmain M D S hS o x t hreg hw
    have hmin : min eps (1 / 44) ≤ eps := min_le_left _ _
    exact ⟨W.mono_eps (by linarith) heps11⟩
  · intro hclass eps heps heps44
    obtain ⟨C1, C2, hC1, hC2, hfinal⟩ := hclass (eps / 2) (by linarith) (by linarith)
    exact ⟨C1, C2, hC1, hC2, fun kappa hkappa => hfinal kappa hkappa⟩

theorem kappaUniformCanonicalClassification_iff_tolerance_half :
    kappaUniformCanonicalClassification.{u} ↔
      (∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
        ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) := by
  constructor
  · intro hclass eps heps heps11
    obtain ⟨C1, C2, hC1, hC2, hfinal⟩ :=
      hclass (min eps (1 / 44)) (lt_min heps (by norm_num)) (min_le_right _ _)
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, hmain⟩ := hfinal kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := hmain M D S hS o x t hreg hw
    have hmin : min eps (1 / 44) ≤ eps := min_le_left _ _
    exact ⟨W.mono_eps (by linarith) (by linarith)⟩
  · intro hclass eps heps heps44
    exact hclass eps heps (by linarith)

theorem buffered_canonical_pullback_of_ancientModelClassification
    (hgap : ∀ (kappa : ℝ), 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
          IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P)
    (hclass : ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0))
    (htransfer : ∀ (eps C1 C2 kappa delta : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness delta kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t) :=
  buffered_canonical_pullback_of_classification
    (kappaUniformCanonicalClassification_of_ancientModelClassification hgap hclass htransfer)

theorem kappaUniformCanonicalClassification_iff_single_constant :
    kappaUniformCanonicalClassification.{u} ↔
      (∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ kappa : ℝ, 0 < kappa →
          ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
              [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
              (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
              IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
              Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
              OrientedWitness S o delta kappa x t →
                Nonempty (CanonicalWitness S (eps / 2) C C x t)) := by
  constructor
  · intro hclass eps heps heps44
    obtain ⟨C1, C2, hC1, hC2, hfinal⟩ := hclass eps heps heps44
    refine ⟨max C1 C2, hC1.trans (le_max_left C1 C2), fun kappa hkappa => ?_⟩
    obtain ⟨delta, hdelta, hdelta1, hmain⟩ := hfinal kappa hkappa
    refine ⟨delta, hdelta, hdelta1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
    obtain ⟨W⟩ := hmain M D S hS o x t hreg hw
    exact ⟨W.enlarge_constants (le_max_left C1 C2) (le_max_right C1 C2)⟩
  · intro hclass eps heps heps44
    obtain ⟨C, hC, hfinal⟩ := hclass eps heps heps44
    exact ⟨C, C, hC, hC, fun kappa hkappa => hfinal kappa hkappa⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
