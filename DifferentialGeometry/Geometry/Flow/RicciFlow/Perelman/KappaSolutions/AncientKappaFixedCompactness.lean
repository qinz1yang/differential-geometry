import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimThreeDimensionalBounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact


def ancientPointedFlowSeq
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    PointedFlowSeq.{u, 0, 0} (I := I3) where
  D := ancientTimeInterval
  term := X


def ancientFlowSequence
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    FlowSequence.{u} where
  interval := fun _ => ancientTimeInterval
  term := X


@[simp] theorem ancientFlowSequence_atTime_zero
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    (ancientFlowSequence X).atTime 0 = (ancientPointedFlowSeq X).atTime (I := I3) 0 :=
  rfl


theorem exists_ancientKappa_fixed_kappa_compactness {kappa : ℝ}
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) (ancientPointedFlowSeq X)
        (L.atTime (I := I3) 0) phi,
        IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        KLim (I := I3) kappa L ∧
        (∀ t : ℝ, t ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3)
            (Phi.atTime (X := ancientPointedFlowSeq X) (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3) (Phi.atTime (X := ancientPointedFlowSeq X) (L := L) t) k) ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
            Nonempty (MetricComparisonOn
              (fun t => L.S.base.metric t) (fun t => (X (phi i)).S.base.metric t)
              (Phi.map i) K (Icc a b) order ε)) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, hanc⟩ :=
    exists_fixed_kappa_compactness (ancientPointedFlowSeq X) rfl
      (fun i => ancientKappaThree_toKLim (X i) (hX i) hdim) hbase
  exact ⟨L, phi, hphi, Phi, hanc, hbaseL, hKL, hconv, hcmp⟩


theorem exists_ancientKappa_fixed_kappa_convergesOn {kappa : ℝ}
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (f : ℕ → ℕ),
      StrictMono f ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
          (L.atTime (I := I3) 0) f, ConvergesOn F L.S := by
  obtain ⟨L, phi, hphi, Phi, hanc, hbaseL, _, _, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness X hX hbase
  refine ⟨L, phi, hphi, hanc, hbaseL,
    Phi.atTime (X := ancientPointedFlowSeq X) (L := L) 0, ?_⟩
  intro K hK a b hab hsub order eps heps
  have hb0 : b ≤ 0 := by
    have hb := hsub (Set.right_mem_Icc.mpr hab)
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using hb
  obtain ⟨k0, hk0⟩ := Phi.source_subset hK
  filter_upwards [hcmp a b hab hb0 K hK order eps heps,
    eventually_ge_atTop k0] with i hi hik
  exact ⟨hsub, hk0 i hik, hi⟩


theorem ancientKappa_fixed_kappa_compactness_of_capture {kappa : ℝ}
    (_hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1)
    (hcapture : ∀ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
      (f : ℕ → ℕ) (F : PointedRiemannianConvergenceMaps (I := I3)
        ((ancientFlowSequence X).atTime 0) (L.atTime (I := I3) 0) f),
      IsAncientKappaSolution (I := I3) kappa L → ConvergesOn F L.S →
        MetricSourceCapture F) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (f : ℕ → ℕ),
      StrictMono f ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
          (L.atTime (I := I3) 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  obtain ⟨L, f, hf, hanc, hbaseL, F, hconv⟩ :=
    exists_ancientKappa_fixed_kappa_convergesOn X hX hbase
  exact ⟨L, f, hf, hanc, hbaseL, F, hcapture L f F hanc hconv, hconv⟩


private theorem chapter25_fixed_kappa_compactness_slot {kappa : ℝ} (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (X i) 1)
    (hcapture : ∀ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
      (f : ℕ → ℕ) (F : PointedRiemannianConvergenceMaps (I := I3)
        ((ancientFlowSequence X).atTime 0) (L.atTime (I := I3) 0) f),
      IsAncientKappaSolution (I := I3) kappa L → ConvergesOn F L.S →
        MetricSourceCapture F) :
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (f : ℕ → ℕ), StrictMono f ∧ IsAncientKappaSolution kappa L ∧
        PointedFlowScalarAtBase L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps
          (({ interval := fun _ => ancientTimeInterval, term := X } : FlowSequence).atTime 0)
          (L.atTime 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S :=
  ancientKappa_fixed_kappa_compactness_of_capture hkappa X hX hbase hcapture

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
