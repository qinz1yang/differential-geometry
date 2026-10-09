import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPremises

/-!
# Consumers of the LC88 premise layer

* `BoundaryCollapsePremises.boundary_centre_of_hypotheses`: under the tree's boundary collapse
  hypotheses, every boundary point is the face image of the collar of exactly one labelled
  component, and its first volume scale is positive and attained for `0 < w < ω₃/2`.
* `BoundaryCollapsePremises.staticCollapseHypotheses`: the premise record gives the boundary
  alternative of the static hypotheses, and `exists_rawGraph_matching` composes it with the static
  theorem at `(K, A, w₀)` (explicit input): a raw graph presentation whose external tori match the
  labelled boundary components.
* `CuspEmbedding.isOpen_image_depth_pos_subset_interior`: the positive-depth part of a pair collar
  is an open subset of the manifold interior (with X87's open-image theorem).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

namespace BoundaryCollapsePremises

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}

/-- Under the boundary collapse hypotheses, every boundary point `x` is the face image of the
collar of exactly one labelled component of the chosen premise data, and its first volume scale is
positive and attained for `0 < w < ω₃/2`. -/
theorem boundary_centre_of_hypotheses (h : boundaryCollapseHypotheses W g K A w₀)
    {x : W.Carrier} (hx : x ∈ W.model.boundary W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) :
    (∃ i : Fin (ofHypotheses h).cusp.count, x ∈ (ofHypotheses h).cusp.component i ∧
        (∃ t : Torus, ((ofHypotheses h).cusp.collar i).toFun (t, halfZero) = x) ∧
        ∀ j : Fin (ofHypotheses h).cusp.count, x ∈ (ofHypotheses h).cusp.component j → j = i) ∧
      0 < firstVolumeScale g x w ∧
      (ballVolume g x (firstVolumeScale g x w)).toReal = w * firstVolumeScale g x w ^ 3 :=
  (ofHypotheses h).cusp.boundary_centre hx hw hwc

/-- The premise record gives the boundary alternative of the static hypotheses. -/
theorem staticCollapseHypotheses (P : BoundaryCollapsePremises W g K A w₀) :
    Collapse.staticCollapseHypotheses W g K A w₀ :=
  Or.inr (nonempty_iff.mp ⟨P⟩)

/-- LC88 into LC90, interface form: with the static theorem at `(K, A, w₀)` as an explicit input,
premise data on a connected carrier give a raw graph presentation whose external tori match the
labelled boundary components of the collar data. -/
theorem exists_rawGraph_matching [ConnectedSpace W.Carrier]
    (P : BoundaryCollapsePremises W g K A w₀)
    (static : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      Collapse.staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ G : RawGraphPresentation W, ∃ e : Fin P.cusp.count ≃ Fin G.externalCount,
      ∀ k, Set.range (G.external.torusMap (e k)) = P.cusp.component k := by
  obtain ⟨G⟩ := static W g P.staticCollapseHypotheses
  exact ⟨G, G.external_matching P.cusp⟩

end BoundaryCollapsePremises

/-- The positive-depth part of a pair collar is an open subset of the manifold interior. -/
theorem CuspEmbedding.isOpen_image_depth_pos_subset_interior {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) :
    IsOpen (e.toFun '' {p | p ∈ cuspDomain ∧ 0 < p.2.val 0}) ∧
      e.toFun '' {p | p ∈ cuspDomain ∧ 0 < p.2.val 0} ⊆ W.model.interior W.Carrier := by
  refine ⟨e.isOpen_image_positive_cuspDomain, ?_⟩
  rintro y ⟨p, ⟨hp, hz⟩, rfl⟩
  exact e.mem_interior_of_depth_pos hp hz

end DifferentialGeometry.Geometry.Collapse
