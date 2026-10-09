import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Strong
import DifferentialGeometry.Geometry.Collapse.Inhabitants.BoundaryComponentCount

/-!
# FC39 producer, gate 1 (review 49, F.8): the provable parts of the whole-product shape

Review 49 asks to revise the whole-product target (frozen targets T:214–228) in three points: the
canonical EMPTY `CircleRegion`; an equivalence of the two ends with `B`'s numbering such that
`B.component i` is the end torus that the GIVEN product diffeomorphism `e` sends; shape and
`RimProduct` on the SAME strong certificate. The revised target is in the lane's targets file
(`build-logs/scratch/FC39-FIX2/TargetsV2.lean`); the two parts that are provable now are here:

* `exists_productEndEquiv` — for ANY nearly cuspidal boundary `B` of `W` and any diffeomorphism
  `e : annulus × S¹ ≃ W`, an equivalence `σ : Fin B.count ≃ Fin 2` with
  `B.component i = e '' doubleCuspBoundary (σ i)` (the pattern of
  `NearlyCuspidalBoundary.annulusComponentEquiv`, transported by `e`: components connected and
  closed, disjoint, covering `∂W = e '' ∂(annulus × S¹)` by `Diffeomorph.image_boundary`); hence
  `count_eq_two_of_productDiffeomorph`;
* `strongOfHandleCount` — a certificate without handles is strong (its rim-product clause is
  vacuous), with `strongOfHandleCount_val`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The end equivalence with `B`'s numbering**: the components of any nearly cuspidal boundary of
`W` are the images under the given product diffeomorphism `e` of the two end tori. -/
theorem exists_productEndEquiv {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ σ : Fin B.count ≃ Fin 2, ∀ i, B.component i = e '' doubleCuspBoundary.{u} (σ i) := by
  refine DifferentialGeometry.Topology.finite_connected_partitions_equiv B.component
    (fun j => e '' doubleCuspBoundary.{u} j) B.connected
    (fun j => (doubleCuspBoundary_connected j).image _ e.continuous.continuousOn)
    B.closed (fun j => e.toHomeomorph.isClosedMap _ (doubleCuspBoundary_closed j))
    B.disjoint
    (fun i j hij => (Set.disjoint_image_iff e.injective).2 (doubleCuspBoundary_disjoint hij)) ?_
  have h1 : (⋃ j, e '' doubleCuspBoundary.{u} j) =
      e '' annulusCircleCarrier.{u}.model.boundary annulusCircleCarrier.{u}.Carrier :=
    calc (⋃ j, e '' doubleCuspBoundary.{u} j) = e '' (⋃ j, doubleCuspBoundary.{u} j) :=
          image_iUnion.symm
      _ = e '' annulusCircleCarrier.{u}.model.boundary annulusCircleCarrier.{u}.Carrier :=
          congrArg (e '' ·) doubleCuspBoundary_cover
  rw [h1, Diffeomorph.image_boundary (by simp) e]
  exact B.covers

/-- A nearly cuspidal boundary of a carrier diffeomorphic to `annulus × S¹` has two components. -/
theorem count_eq_two_of_productDiffeomorph {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    B.count = 2 := by
  obtain ⟨σ, -⟩ := exists_productEndEquiv B e
  simpa only [Fintype.card_fin] using Fintype.card_congr σ

variable {W : CompactCarrier.{u}}

/-- A certificate without handles satisfies the rim-product clause (vacuously). -/
theorem rimProduct_of_handleCount_eq_zero {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (h : D.handleCount = 0) : D.RimProduct :=
  fun k => (Fin.cast h k).elim0

/-- **A certificate without handles is strong.** -/
def strongOfHandleCount {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
    (h : D.handleCount = 0) : StrongCertificate W E :=
  ⟨D, rimProduct_of_handleCount_eq_zero D h⟩

/-- The strong certificate of a handle-free certificate is that certificate. -/
theorem strongOfHandleCount_val {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
    (h : D.handleCount = 0) : (strongOfHandleCount D h).1 = D :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
