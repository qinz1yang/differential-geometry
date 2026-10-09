import DifferentialGeometry.Geometry.Collapse.SmallGeometry
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# The normalized model of a closed member (lane FC39-VAL, adapter A0)

Design `build-logs/resume/design-FC39-VAL.md` §2 A0 (external review 49, T49-4: "adapters for
normalized metric / carrier / sequence index"). The final chapter-13 family `LocalChartPacketsC14`
and its producer `eventually_nonempty_localChartPacketsC14` live on a `Type` (universe `0`) with a
boundaryless `𝓘(ℝ, E3)` atlas whose distance IS the Riemannian distance. A closed member
`W : CompactCarrier.{u}` of the standing sequence has the carrier model `W.model` (possibly `𝓡∂ 3`
with empty boundary) and a universe `u`.

* `ClosedMemberFacts W`: the standing facts used here (empty model boundary, connected).
* `ClosedModel W g`: a `Type` with a metric space, an `E3` atlas, compactness, a diffeomorphism
  `ψ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier` and the metric `gX = ψ^* g` (the genuine pullback, field
  `metric_eq`), whose distance is the Riemannian distance (`hmetric`).
* `nonempty_closedModel_VAL`: such a model exists for every closed member — the interior atlas of
  the boundaryless carrier (`interiorChartedSpace`), X122's small model (`smallManifoldModel`) and
  the induced metric space of the pulled-back metric.
* transport: Riemannian distance, ball volumes, first volume scales, curvature scales and curvature
  derivative norms of `gX` are those of `g` at `ψ x`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The standing facts of a closed member used by the carrier adapter: empty model boundary (part of
`closedCollapseHypotheses`) and connectedness (an instance argument of every wrapper). -/
structure ClosedMemberFacts (W : CompactCarrier.{u}) : Prop where
  boundary_empty : W.model.boundary W.Carrier = ∅
  connected : ConnectedSpace W.Carrier

/-- **A0, the normalized model of a closed member**: a `Type` with an `E3` atlas, compact, with a
diffeomorphism `ψ` onto the member, the pulled-back metric `gX = ψ^* g`, and the Riemannian distance
of `gX` as its distance. -/
structure ClosedModel (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) where
  /-- The small carrier. -/
  X : Type
  [mX : MetricSpace X]
  [cX : ChartedSpace E3 X]
  [sX : IsManifold 𝓘(ℝ, E3) ∞ X]
  [kX : CompactSpace X]
  /-- The identification with the member. -/
  ψ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier
  /-- The metric of the model. -/
  gX : SmoothRiemannianMetric 𝓘(ℝ, E3) X
  /-- It is the genuine pullback of the member's metric. -/
  metric_eq : gX = Diffeomorph.pullbackMetricCross g ψ
  /-- The distance is the Riemannian distance. -/
  hmetric : ∀ a b : X, riemannianEDistOf gX a b = ENNReal.ofReal (dist a b)

attribute [instance] ClosedModel.mX ClosedModel.cX ClosedModel.sX ClosedModel.kX

/-- **Existence of the normalized model** of every closed member. -/
theorem nonempty_closedModel_VAL (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (h : ClosedMemberFacts W) :
    Nonempty (ClosedModel W g) := by
  have : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty h.boundary_empty
  have := h.connected
  let cI : ChartedSpace E3 W.Carrier := interiorChartedSpace W.model ∞
  have sI : IsManifold 𝓘(ℝ, E3) ∞ W.Carrier := interiorIsManifold W.model ∞
  let S : SmallManifoldModel (I := 𝓘(ℝ, E3)) W.Carrier := smallManifoldModel
  let ψ : S.Carrier ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier :=
    S.diffeo.trans (interiorAtlasDiffeomorph W.model ∞).symm
  have kS : CompactSpace S.Carrier := ψ.toHomeomorph.symm.compactSpace
  have cS : ConnectedSpace S.Carrier := (ψ.toHomeomorph.connectedSpace_iff).mpr inferInstance
  let gX : SmoothRiemannianMetric 𝓘(ℝ, E3) S.Carrier := Diffeomorph.pullbackMetricCross g ψ
  let mS : MetricSpace S.Carrier := inducedMetricSpace gX
  exact ⟨⟨S.Carrier, ψ, gX, rfl, inducedMetricSpace_hmetric gX⟩⟩

namespace ClosedModel

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  (M : ClosedModel W g)

private local instance measurableMember : MeasurableSpace W.Carrier := borel W.Carrier
private local instance borelMember : BorelSpace W.Carrier := ⟨rfl⟩
private local instance measurableModel : MeasurableSpace M.X := borel M.X
private local instance borelModel : BorelSpace M.X := ⟨rfl⟩

/-- The Riemannian distance of the model is that of the member. -/
theorem edist_eq (a b : M.X) :
    riemannianEDistOf M.gX a b = riemannianEDistOf g (M.ψ a) (M.ψ b) := by
  rw [M.metric_eq]
  exact riemannianEDistOf_pullbackMetricCross g M.ψ a b

/-- The inner products of the model are those of the member through `dψ`. -/
theorem inner_eq (x : M.X) (v w : TangentSpace 𝓘(ℝ, E3) x) :
    M.gX.inner x v w =
      g.inner (M.ψ x) (mfderiv 𝓘(ℝ, E3) W.model M.ψ x v) (mfderiv 𝓘(ℝ, E3) W.model M.ψ x w) := by
  rw [M.metric_eq]
  exact Diffeomorph.pullbackMetricCross_inner g M.ψ x v w

/-- Riemannian balls of the model are the preimages of those of the member. -/
theorem ball_eq_preimage (p : M.X) (r : ℝ) :
    riemannianBallOf M.gX p r = M.ψ ⁻¹' riemannianBallOf g (M.ψ p) r := by
  ext x
  change riemannianEDistOf M.gX p x < ENNReal.ofReal r ↔
    riemannianEDistOf g (M.ψ p) (M.ψ x) < ENNReal.ofReal r
  rw [M.edist_eq]

/-- Ball volumes of the model are those of the member. -/
theorem ballVolume_eq (p : M.X) (r : ℝ) :
    ballVolume M.gX p r = ballVolume g (M.ψ p) r := by
  rw [ballVolume, M.metric_eq, riemannianVolumeMeasure_pullback_cross]
  rw [Measure.map_apply M.ψ.symm.continuous.measurable]
  · congr 1
    ext x
    change riemannianEDistOf (Diffeomorph.pullbackMetricCross g M.ψ) p (M.ψ.symm x) <
        ENNReal.ofReal r ↔ riemannianEDistOf g (M.ψ p) x < ENNReal.ofReal r
    rw [riemannianEDistOf_pullbackMetricCross, M.ψ.apply_symm_apply]
  · exact (isOpen_lt (Riemannian.continuous_riemannianEDist
      (Diffeomorph.pullbackMetricCross g M.ψ) p) continuous_const).measurableSet

/-- First volume scales of the model are those of the member. -/
theorem firstVolumeScale_eq (p : M.X) (w : ℝ) :
    firstVolumeScale M.gX p w = firstVolumeScale g (M.ψ p) w := by
  unfold firstVolumeScale
  simp only [M.ballVolume_eq]

/-- Curvature scales of the model are those of the member. -/
theorem curvatureRadius_eq (p : M.X) :
    curvatureRadius M.gX p = curvatureRadius g (M.ψ p) := by
  have hback : Diffeomorph.pullbackMetricCross M.gX M.ψ.symm = g := by
    rw [M.metric_eq, Diffeomorph.pullbackMetricCross_trans, Diffeomorph.symm_trans_self,
      Diffeomorph.pullbackMetricCross_refl]
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf g (M.ψ p) r,
        SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹) := by
      intro y hy
      have hyS : M.ψ.symm y ∈ riemannianBallOf M.gX p r := by
        rw [M.ball_eq_preimage]
        simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using hy
      have hbS := hb (M.ψ.symm y) hyS
      simpa only [hback, Diffeomorph.apply_symm_apply] using
        sectionalBoundedBelowAt_pullbackMetricCross M.gX M.ψ.symm y hbS
    exact le_iSup_of_le hbd le_rfl
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf M.gX p r,
        SectionalBoundedBelowAt M.gX y (-(r ^ 2)⁻¹) := by
      intro y hy
      rw [M.metric_eq]
      apply sectionalBoundedBelowAt_pullbackMetricCross g M.ψ y
      exact hb (M.ψ y) ((M.ball_eq_preimage p r).le hy)
    exact le_iSup_of_le hbd le_rfl

/-- Curvature derivative norms of the model are those of the member. -/
theorem curvatureDerivativeNorm_eq (k : ℕ) (p : M.X) :
    curvatureDerivativeNorm M.gX k p = curvatureDerivativeNorm g k (M.ψ p) :=
  curvatureDerivativeNorm_of_injective_local_isometry M.gX g M.ψ M.ψ.isLocalDiffeomorph
    M.ψ.injective M.inner_eq k p

end ClosedModel

end DifferentialGeometry.Geometry.Collapse
