import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BonnetMyers

import Mathlib.Topology.Connected.Clopen
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}


namespace PointedCGHMaps

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
