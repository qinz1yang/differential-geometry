import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCarrier
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

/-!
The same actual sphere-capping quotient has a connected closed oriented model when no tori remain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

instance sphereCapQuotientConnected [ConnectedSpace C.Carrier] :
    ConnectedSpace B.SphereCapQuotient := by
  let : PreconnectedSpace (ClosedCell 3) := by
    apply Subtype.preconnectedSpace
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ))
    exact hconv.isPreconnected
  let a : C.Carrier := Classical.choice inferInstance
  let A : Option (Fin B.sphereCount) → Set B.SphereCapQuotient := fun i =>
    match i with
    | none => range B.sphereCapCore
    | some j => range B.sphereCapCore ∪ range (B.sphereCapBall j)
  have hcore : IsPreconnected (range B.sphereCapCore) :=
    isPreconnected_range B.sphereCapCore.continuous
  have hA : ∀ i, IsPreconnected (A i) := by
    intro i
    cases i with
    | none => exact hcore
    | some j =>
      apply hcore.union' ?_ (isPreconnected_range (B.sphereCapBall j).continuous)
      let z : ClosureSphere.{u} := Classical.choice inferInstance
      exact ⟨B.sphereCapCore (B.sphereMap j z), ⟨B.sphereMap j z, rfl⟩,
        ⟨closureSphereToBall z, (B.sphereCap_attachment j z).symm⟩⟩
  have hcommon : (⋂ i, A i).Nonempty := by
    refine ⟨B.sphereCapCore a, mem_iInter.mpr ?_⟩
    intro i
    cases i with
    | none => exact mem_range_self a
    | some j => exact Or.inl (mem_range_self a)
  have hcover : (⋃ i, A i) = univ := by
    apply subset_antisymm (subset_univ _)
    intro x hx
    have hxc : x ∈ range B.sphereCapCore ∪ (⋃ i, range (B.sphereCapBall i)) := by
      rw [B.sphereCap_covers]
      exact hx
    rcases hxc with hc | hb
    · exact mem_iUnion.mpr ⟨none, hc⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      exact mem_iUnion.mpr ⟨some i, Or.inr hi⟩
  apply connectedSpace_iff_univ.mpr
  refine ⟨⟨B.sphereCapCore a, mem_univ _⟩, ?_⟩
  rw [← hcover]
  exact isPreconnected_iUnion hcommon hA

theorem sphereCapCarrier_boundary_eq_empty (hn : B.torusCount = 0) :
    B.sphereCapCarrier.model.boundary B.sphereCapCarrier.Carrier = ∅ := by
  rw [B.sphereCapRetained_exhausted]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact Fin.elim0 (Fin.cast hn i)

@[reducible]
private def capClosedAtlas (hn : B.torusCount = 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) B.SphereCapQuotient := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  let : BoundarylessManifold (𝓡∂ 3) B.SphereCapQuotient :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty
      (B.sphereCapCarrier_boundary_eq_empty hn)
  exact DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞

private theorem capClosedSmooth (hn : B.torusCount = 0) :
    letI := capClosedAtlas B hn
    IsManifold (𝓡 3) ∞ B.SphereCapQuotient := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  let : BoundarylessManifold (𝓡∂ 3) B.SphereCapQuotient :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty
      (B.sphereCapCarrier_boundary_eq_empty hn)
  exact DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞

private def capClosedIdentity (hn : B.torusCount = 0) :
    letI := B.sphereCapQuotientChartedSpace
    letI := capClosedAtlas B hn
    B.SphereCapQuotient ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ B.SphereCapQuotient := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  let : BoundarylessManifold (𝓡∂ 3) B.SphereCapQuotient :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty
      (B.sphereCapCarrier_boundary_eq_empty hn)
  exact DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞
    (M := B.SphereCapQuotient)

private theorem capClosedOriented (hn : B.torusCount = 0) :
    letI := B.sphereCapQuotientChartedSpace
    letI := B.sphereCapQuotientIsManifold
    letI := capClosedAtlas B hn
    letI := capClosedSmooth B hn
    ∃ O : ManifoldOrientation (𝓡 3) B.SphereCapQuotient 3,
      (capClosedIdentity B hn).symm.preservesOrientation O B.sphereCapQuotientOrientation := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  let := capClosedAtlas B hn
  let := capClosedSmooth B hn
  let F := (capClosedIdentity B hn).symm
  let so := Manifold.smoothOrientationOfManifoldOrientation (𝓡∂ 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡∂ 3)
      (finCongr B.sphereCapQuotientOrientation.dimension_eq.symm)
      B.sphereCapQuotientOrientation)
  let pb := Manifold.pullbackSmoothOrientation (𝓡 3) (𝓡∂ 3) F F.contMDiff
    (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) so
  let O := Classical.choose (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) pb)
  let O3 := OrientationAssembly.reindexManifoldOrientation (𝓡 3)
    (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)) O
  refine ⟨O3, ?_⟩
  apply Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation F F.contMDiff
    (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) so
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3)) _ (O.orientation x) = _
    rw [Classical.choose_spec
      (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) pb)]

def sphereCapClosedCarrier [ConnectedSpace C.Carrier] (hn : B.torusCount = 0) :
    ConnectedClosedOrientedManifold.{u} 3 := by
  let := capClosedAtlas B hn
  exact {
    Carrier := B.SphereCapQuotient
    smooth := capClosedSmooth B hn
    orientation := (capClosedOriented B hn).choose }

def sphereCapClosedDiffeomorph [ConnectedSpace C.Carrier] (hn : B.torusCount = 0) :
    B.sphereCapCarrier.Carrier ≃ₘ⟮B.sphereCapCarrier.model, 𝓡 3⟯
      (B.sphereCapClosedCarrier hn).Carrier := capClosedIdentity B hn

theorem sphereCapClosedDiffeomorph_apply [ConnectedSpace C.Carrier]
    (hn : B.torusCount = 0) (x : B.SphereCapQuotient) :
    B.sphereCapClosedDiffeomorph hn x = x := rfl

theorem sphereCapClosedDiffeomorph_symm_apply [ConnectedSpace C.Carrier]
    (hn : B.torusCount = 0) (x : B.SphereCapQuotient) :
    (B.sphereCapClosedDiffeomorph hn).symm x = x := rfl

theorem sphereCapClosedDiffeomorph_preservesOrientation [ConnectedSpace C.Carrier]
    (hn : B.torusCount = 0) :
    (B.sphereCapClosedDiffeomorph hn).preservesOrientation
      B.sphereCapCarrier.orientation (B.sphereCapClosedCarrier hn).orientation := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  let := capClosedAtlas B hn
  let := capClosedSmooth B hn
  change (capClosedIdentity B hn).preservesOrientation B.sphereCapQuotientOrientation
    (capClosedOriented B hn).choose
  have h := Diffeomorph.preservesOrientation_symm (capClosedOriented B hn).choose_spec
  have he : (capClosedIdentity B hn).symm.symm = capClosedIdentity B hn := by
    ext x
    rfl
  rw [he] at h
  exact h

end GC.GraphManifold.MixedBoundaryCertificate
