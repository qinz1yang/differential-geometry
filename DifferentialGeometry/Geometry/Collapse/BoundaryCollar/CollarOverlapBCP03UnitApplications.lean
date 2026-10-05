import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapBCP03Unit
import DifferentialGeometry.Geometry.Collapse.BoundaryProductPresentationApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy

/-!
# BCF04 in BCP03's product alternative, on actual data

BCF04 (B:9886–9966) begins: "Together with BCP03's whole-product alternative, this covers both
cases" — in the product case the carrier is one circle-bundle piece over an annulus
(`exists_boundary_presentation_of_product`, C14-ASM, which takes the diffeomorphism from the
model `annulusCircleCarrier` as data). This module PRODUCES that diffeomorphism from BCP03:

* `annulusCircleDiffeomorphOfTorusUnit`: `annulusCircleCarrier ≃ T² × [0, 1] ≃ W` through the
  polar diffeomorphism of the graph-manifold library (`torusMonodromyPolarDiffeomorph`);
* `NearlyCuspidalBoundary.bcf04_product_or_disjoint`: for a nearly cuspidal boundary on a
  connected carrier (`K ≥ 1`, `0 ≤ δ ≤ 1/1000`), EITHER the carrier has a raw graph presentation
  with one piece, no pairing torus and two external tori matched with the two boundary
  components (and then `B.count = 2`), OR every two enlarged collars are disjoint and the
  BCP01.c inner collars are disjoint at distance `≥ 1` (BCP03.b) — the input of BCF01–BCF03;
* `NearlyCuspidalBoundary.exists_boundary_graph_conclusion_of_overlap` (consumer): two
  overlapping enlarged collars give the labelled conclusion of `exists_boundary_graph_threshold`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.GraphManifold
  GC.Seifert DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- The graph-manifold model `annulusCircleCarrier` (annulus × circle) mapped onto `W` through
a diffeomorphism `T² × [0, 1] ≃ W`. -/
def annulusCircleDiffeomorphOfTorusUnit
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞) :
    annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier :=
  torusMonodromyPolarDiffeomorph.{u}.trans D

/-- **BCF04 with BCP03's alternative.** Either a labelled raw graph presentation of `W` with one
piece and two external tori (product case), or the separated collars of BCP03.b. -/
theorem NearlyCuspidalBoundary.bcf04_product_or_disjoint [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) :
    (B.count = 2 ∧ ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 2 ∧
      ∃ e' : Fin B.count ≃ Fin G.externalCount,
        ∀ i, Set.range (G.external.torusMap (e' i)) = B.component i) ∨
    ∀ i j : Fin B.count, i ≠ j →
      Disjoint ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      ∃ Fi Fj : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi ∧
        ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj ∧ (∀ x ∈ B.component i, Fi x ≤ 90) ∧
        (∀ x ∈ B.component j, Fj x ≤ 90) ∧ Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
        ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  rcases B.bcp03_unit hK hδ0 hδ with ⟨-, -, -, D, -, -⟩ | hdisj
  · left
    exact ⟨B.count_eq_two_of_torusProduct (annulusCircleDiffeomorphOfTorusUnit D),
      exists_boundary_presentation_of_product B (annulusCircleDiffeomorphOfTorusUnit D)⟩
  · exact Or.inr hdisj

/-- Two overlapping enlarged collars give the labelled conclusion of
`exists_boundary_graph_threshold` (`Geometry/Collapse/GraphManifold.lean`), verbatim. -/
theorem NearlyCuspidalBoundary.exists_boundary_graph_conclusion_of_overlap
    [ConnectedSpace W.Carrier] (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {i j : Fin B.count} (hij : i ≠ j)
    (hover : ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} ∩
      (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}).Nonempty) :
    ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ k, Set.range (G.external.torusMap (e k)) = B.component k := by
  obtain ⟨-, -, -, -, -, -, D, -, -, -⟩ := B.bcp03_product_unit hK hδ0 hδ hij hover
  exact exists_boundary_graph_conclusion_of_product B (annulusCircleDiffeomorphOfTorusUnit D)

end DifferentialGeometry.Geometry.Collapse
