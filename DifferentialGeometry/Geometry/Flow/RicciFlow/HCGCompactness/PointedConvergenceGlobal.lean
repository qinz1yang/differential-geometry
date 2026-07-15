import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Headlines
import DifferentialGeometry.Geometry.Comparison.TangentNormDiamond
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Global comparison maps from compact pointed limits

For a compact pointed Cheeger--Gromov limit, the exhausting sources of the
comparison maps are eventually the whole limit manifold.  If the corresponding
sequence manifold is connected, the open target of such a comparison map is
also the whole manifold: it is the continuous image of a compact source, hence
closed, and it is nonempty.  The resulting everywhere-defined partial
diffeomorphism is promoted to a global `Diffeomorph`.
-/

noncomputable section

universe u

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

namespace PointedRiemannianManifold

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Bonnet--Myers compactness for the metric and completeness stored by a
pointed Riemannian manifold.  This helper reconciles the project's default
tangent norm with the `RiemannianBundle` norm in one low-level place. -/
theorem compact_of_ricci
    [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    {P : PointedRiemannianManifold.{u} (I := I)}
    (hconn :
      letI : TopologicalSpace P.M := P.topology
      ConnectedSpace P.M)
    (hdim : 2 <= Module.finrank Real E)
    {K : Real} (hK : 0 < K)
    (hRic :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) P.metric (((Module.finrank Real E : Real) - 1) * K))
    (hcomplete : MetricComplete (I := I) P) :
    letI : TopologicalSpace P.M := P.topology
    CompactSpace P.M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : ConnectedSpace P.M := hconn
  let g := P.metric
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : P.M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : P.M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI : TopologicalSpace.MetrizableSpace P.M :=
    Manifold.metrizableSpace I P.M
  letI : T3Space P.M := inferInstance
  have hComplete :
      letI : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I P.M
      CompleteSpace P.M := by
    simpa [MetricComplete] using hcomplete
  letI : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I P.M
  letI : IsRiemannianManifold I P.M := inferInstance
  letI : CompleteSpace P.M := hComplete
  exact
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_ricci_bound
      (E := E) g hdim hK hRic (fun x v =>
        DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) g x v)

end PointedRiemannianManifold

namespace PointedCGHMaps

/-- On a compact limit manifold, the exhausting comparison-map sources are
eventually the whole manifold. -/
theorem exists_source_univ
    {X : PointedFlowSeq.{u} (I := I)}
    {P : PointedRiemannianManifold.{u} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (hcompact :
      letI : TopologicalSpace P.M := P.topology
      IsCompact (Set.univ : Set P.M)) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> Phi.source k = Set.univ := by
  letI : TopologicalSpace P.M := P.topology
  obtain ⟨k0, hk0⟩ := Phi.source_subset (K := Set.univ) hcompact
  refine ⟨k0, fun k hk => ?_⟩
  exact Set.eq_univ_of_univ_subset (hk0 k hk)

/-- If a comparison map has the whole compact limit manifold as source and its
sequence manifold is connected, then its target is the whole sequence
manifold. -/
theorem target_univ
    {X : PointedFlowSeq.{u} (I := I)}
    {P : PointedRiemannianManifold.{u} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hcompact :
      letI : TopologicalSpace P.M := P.topology
      IsCompact (Set.univ : Set P.M))
    (hconn :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      ConnectedSpace (X.term (subseq k)).M)
    (hsource : Phi.source k = Set.univ) :
    Phi.target k = Set.univ := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  letI : ConnectedSpace (X.term (subseq k)).M := hconn
  let phi := Phi.partialDiffeomorph k
  have hsource' : phi.source = Set.univ := by
    simpa [phi, PointedCGHMaps.source] using hsource
  have hsource_compact : IsCompact phi.source := by
    rw [hsource']
    exact hcompact
  have htarget_compact : IsCompact phi.target := by
    rw [← phi.toPartialEquiv.image_source_eq_target]
    exact hsource_compact.image_of_continuousOn phi.contMDiffOn.continuousOn
  have htarget_nonempty : phi.target.Nonempty := by
    have hbase : P.basepoint ∈ phi.source := by simp [hsource']
    exact ⟨phi P.basepoint, phi.map_source hbase⟩
  have htarget_univ : phi.target = Set.univ :=
    IsClopen.eq_univ ⟨htarget_compact.isClosed, phi.open_target⟩ htarget_nonempty
  simpa [phi, PointedCGHMaps.target] using htarget_univ

/-- Promote a comparison partial diffeomorphism with full source and target to
a global diffeomorphism. -/
noncomputable def globalDiffeomorph
    {X : PointedFlowSeq.{u} (I := I)}
    {P : PointedRiemannianManifold.{u} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hsource : Phi.source k = Set.univ)
    (htarget : Phi.target k = Set.univ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    Diffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let phi := Phi.partialDiffeomorph k
  have hsource' : phi.source = Set.univ := by
    simpa [phi, PointedCGHMaps.source] using hsource
  have htarget' : phi.target = Set.univ := by
    simpa [phi, PointedCGHMaps.target] using htarget
  have hlocal : IsLocalDiffeomorph I I (∞ : WithTop ℕ∞) phi := by
    intro x
    apply phi.isLocalDiffeomorphAt
    rw [hsource']
    exact Set.mem_univ x
  have hbijective : Function.Bijective phi :=
    ⟨phi.toPartialEquiv.injective_of_source_eq_univ hsource',
      phi.toPartialEquiv.surjective_of_target_eq_univ htarget'⟩
  exact hlocal.diffeomorphOfBijective hbijective

end PointedCGHMaps
end HCGCompactness
end DifferentialGeometry
