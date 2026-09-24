import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactnessReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

noncomputable def constantAncientFlowSeq
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    PointedFlowSeq.{u, uE, uH} (I := I) :=
  ⟨ancientTimeInterval, fun _ => F⟩

noncomputable def constantAncientFlowCGHMaps
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    PointedCGHMaps (I := I) (constantAncientFlowSeq (I := I) F)
      (F.atTime (I := I) 0) id where
  partialDiffeomorph := fun _ => PartialDiffeomorph.refl (I := I) F.M
  source_exhausts := by
    refine ⟨fun k => ?_, fun k => ?_, fun K hK => ⟨0, fun k hk => ?_⟩⟩
    · simp only [PartialDiffeomorph.refl]
      exact isOpen_univ
    · simp only [PartialDiffeomorph.refl]
      exact Set.subset_univ _
    · simp only [PartialDiffeomorph.refl]
      exact Set.subset_univ _
  base_mem := fun k => by
    simp only [PartialDiffeomorph.refl]
    exact Set.mem_univ _
  basepoint_map := fun k => rfl

noncomputable def constantAncientFlowMaps
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (t : ℝ) :
    PointedRiemannianConvergenceMaps (I := I)
      ((constantAncientFlowSeq (I := I) F).atTime (I := I) t)
      (F.atTime (I := I) t) id :=
  (constantAncientFlowCGHMaps (I := I) F).atTime (X := constantAncientFlowSeq (I := I) F)
    (L := F) t

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem ancientFlowLimitExtension_of_localAncientFlowLimit
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    (hconn : let _ : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M)
    (hcomp : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) ∧
        (∀ k,
          let D := C.domain k
          let _ : TopologicalSpace
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
          let _ : ChartedSpace H
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
          let _ : IsManifold I ∞
            (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
          D.referenceMetric = D.limitMetric)) :
    ∃ P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) ∧
      AncientFlowLimitExtension (I := I) X P phi L Phi := by
  have h0 : (0 : ℝ) ∈ X.D.carrier := by
    simp only [hD, ancientTimeInterval_carrier, Set.mem_Iic, le_refl]
  obtain ⟨C0, hC0, href0⟩ := hconv 0 h0
  let P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)) :=
    ⟨phi, hphi, L.atTime (I := I) 0, hcomp 0 h0,
      Phi.atTime (X := X) (L := L) (phi := phi) 0, ⟨C0⟩⟩
  refine ⟨P, fun k => hC0 k, fun k => href0 k, hconn, ?_⟩
  exact
    { atTime_zero := rfl
      slice_complete := hcomp
      slice_convergence :=
        (ancientFlowLimitExtension_slice_convergence_iff (I := I) X phi L Phi).mpr hconv }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
