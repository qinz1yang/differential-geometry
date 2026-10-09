import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdFinalRM1
import DifferentialGeometry.Geometry.Collapse.BoundaryMemberModelV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawLiftAlongUL

/-!
# The boundary endpoint input A01 at every universe (lane S-ULIFT, G3, suffix `_UL`)

`exists_boundary_graph_threshold_final_RM1` is the admitted ledger input A01 at universe `0`. For
`u > 0` a member `(W, g, B)` is lowered to a universe-`0` model with the standing hypotheses
transported (`BoundaryModelV2_BQ3`, `BoundaryModel.*_iff_BQ3`); the universe-`0` theorem gives a Raw
presentation of the model with labelled external tori, which `RawGraphPresentation.liftAlong_UL`
lifts back along `ψ`. The model produced by `nonempty_boundaryModelV2_BQ3` does not record that `ψ`
preserves the orientation (the construction discards it); `nonempty_boundaryModelV2_oriented_UL`
repeats that construction and keeps the fact (no new field: a pair existence statement).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The universe-`0` boundary model of `nonempty_boundaryModelV2_BQ3`, with the orientation
preservation of `ψ` kept. -/
theorem nonempty_boundaryModelV2_oriented_UL (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) :
    ∃ M : BoundaryModelV2_BQ3 W g B,
      M.ψ.preservesOrientation M.W₀.orientation W.orientation := by
  let S : SmallManifoldModel (I := W.model) W.Carrier := smallManifoldModel
  have kS : CompactSpace S.Carrier := S.diffeo.toHomeomorph.symm.compactSpace
  obtain ⟨o₀, ho⟩ := S.exists_orientation W.orientation
  let W₀ : CompactCarrier.{0} := { kind := W.kind, Carrier := S.Carrier, orientation := o₀ }
  let ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier := S.diffeo
  have cS : ConnectedSpace W₀.Carrier := (ψ.toHomeomorph.connectedSpace_iff).mpr inferInstance
  refine ⟨{
    W₀ := W₀
    connected₀ := cS
    ψ := ψ
    g₀ := Diffeomorph.pullbackMetricCross g ψ
    metric_eq := rfl
    B₀ := B.pullback_BQ3 ψ
    count_eq := rfl
    component_eq := fun i => image_preimage_eq _ ψ.surjective
    collar_toFun := fun i => by
      funext q
      exact ψ.apply_symm_apply _
    collar_cusp := fun i => rfl }, ?_⟩
  have h' := Diffeomorph.preservesOrientation_symm ho
  have he : S.diffeo.symm.symm = S.diffeo := by
    ext x
    rfl
  rw [he] at h'
  exact h'

/-- **The boundary endpoint input at every universe, as a transfer from universe `0`**: the
threshold `w₀` of the universe-`0` statement works for every universe. -/
theorem a01_boundary_lift_UL (K : ℕ) (A : ℝ → ℝ)
    (h0 : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  obtain ⟨w₀, hw₀, hwu, H⟩ := h0
  refine ⟨w₀, hw₀, hwu, fun W _ g B hvc hcd => ?_⟩
  obtain ⟨M, hψ⟩ := nonempty_boundaryModelV2_oriented_UL W g B
  have := M.connected₀
  obtain ⟨G₀, e₀, he₀⟩ := H M.W₀ M.g₀ M.B₀ (BoundaryModel.boundaryVolumeCollapsed_iff_BQ3.mpr hvc)
    (BoundaryModel.curvatureDerivativesControlled_iff_BQ3.mpr hcd)
  refine ⟨G₀.liftAlong_UL M.ψ hψ, (finCongr M.count_eq.symm).trans e₀, fun i => ?_⟩
  refine (RawGraphPresentation.liftAlong_UL_range G₀ M.ψ hψ
    (e₀ (finCongr M.count_eq.symm i))).trans ?_
  rw [he₀ (finCongr M.count_eq.symm i), M.component_eq (finCongr M.count_eq.symm i)]
  exact congrArg B.component (Fin.ext rfl)

/-- **The boundary endpoint input A01 at every universe**: the statement of the admitted
`exists_boundary_graph_threshold.{u}`, from the unconditional universe-`0` theorem
`exists_boundary_graph_threshold_final_RM1`. -/
theorem a01_boundary_univ_UL (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i :=
  a01_boundary_lift_UL K A (exists_boundary_graph_threshold_final_RM1 K hK A hA)

end DifferentialGeometry.Geometry.Collapse
