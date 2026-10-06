import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinAlternativesFinite_S27

/-!
# CH12-S27: `HyperbolicOrThin.nonnegative` and the per-block trichotomy (C4 G3, part 2)

* closed block with `sec ≥ 0`, not marked thin: `HyperbolicOrThin.nonnegative`;
* closed block with `thin i ↔ ¬ sec ≥ 0`: the dichotomy (collapse input only in the thin case);
* a per-block trichotomy (hyperbolic / thin / nonnegative) yields `HyperbolicOrThin`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

open GC.LongTime

/-- Closed sectionally nonnegative block, not marked thin. -/
def hyperbolicOrThin_nonnegative_S27 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (metric : (i : Fin D.components.count) →
      SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ) (i : Fin D.components.count)
    (hnot : ¬ thin i) (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (hnn : SectionalBoundedBelow (metric i) 0) : HyperbolicOrThin D metric thin K w i :=
  .nonnegative hnot hclosed hnn

/-- A closed block, marked thin exactly when it is not sectionally nonnegative: `nonnegative`
when `sec ≥ 0`; otherwise thin, the volume-collapse being the only input. -/
def hyperbolicOrThin_of_closed_dichotomy_S27 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (metric : (i : Fin D.components.count) →
      SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ) (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (hthin : thin i ↔ ¬ SectionalBoundedBelow (metric i) 0)
    (hcoll : ¬ SectionalBoundedBelow (metric i) 0 →
      ∀ p, volumeCollapsedAtCurvatureScale (metric i) w p) :
    HyperbolicOrThin D metric thin K w i := by
  by_cases h : SectionalBoundedBelow (metric i) 0
  · exact .nonnegative (fun ht => (hthin.mp ht) h) hclosed h
  · exact .thin (hthin.mpr h) (Or.inl ⟨hclosed, hcoll h⟩)

/-- Pointwise trichotomy gives `HyperbolicOrThin`. -/
theorem hyperbolicOrThin_of_trichotomy_S27 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (metric : (i : Fin D.components.count) →
      SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ) (i : Fin D.components.count)
    (h : (¬ thin i ∧ ∃ geometry : D.carrier.InteriorGeometry (D.components.piece i),
            isHyperbolicInteriorGeometry geometry) ∨
         (thin i ∧ hasThinVolumeGeometry (D.component i) (metric i) K w) ∨
         (¬ thin i ∧ (D.component i).model.boundary (D.component i).Carrier = ∅ ∧
            SectionalBoundedBelow (metric i) 0)) :
    Nonempty (HyperbolicOrThin D metric thin K w i) := by
  rcases h with ⟨hn, g, hg⟩ | ⟨ht, hg⟩ | ⟨hn, hc, hs⟩
  · exact ⟨.hyperbolic hn g hg⟩
  · exact ⟨.thin ht hg⟩
  · exact ⟨.nonnegative hn hc hs⟩

end GC.LongTime.Ch12
