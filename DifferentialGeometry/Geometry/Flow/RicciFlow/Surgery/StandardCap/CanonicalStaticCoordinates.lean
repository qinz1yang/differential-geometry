import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticCapWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε)

/-- The actual canonical window realizes the same retained sphere label and height. -/
theorem window_eq_retainedMap (x : neckRetainedCollar δ)
    (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D) :
    w.window ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩ =
      w.retainedMap x := by
  change w.data.windowMap _ = w.data.retainedInclusion (x.val.1, ⟨x.val.2, x.property⟩)
  rw [w.properties.windowMap_eq, w.properties.retainedInclusion_eq]
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos
    (inv_pos.mpr d.precision_pos)).injective
  apply Subtype.ext
  have hwindow := congrArg (fun y : insertionBall δ⁻¹ => (y : ThreeSpace))
    (modelWindowMap_realization (inv_pos.mpr d.precision_pos) w.properties.window_fit
      ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩)
  exact hwindow.trans
    (radialCapAttachmentHomeomorph_retained transitionEnd_pos
      (inv_pos.mpr d.precision_pos) (x.val.1, ⟨x.val.2, x.property⟩)).symm

/-- Both coordinate equations hold for the very same lifted witness selected by
`toStaticCapWitness`; no independent chart or cap is chosen. -/
theorem toStaticCapWitness_hasRadialCoordinates (hD : 0 < D) :
    (w.toStaticCapWitness hD).HasRadialCoordinates := by
  constructor
  · intro x hx hc
    change ULift.up (w.window ⟨x, hx⟩) = ULift.up (w.capChart ⟨x, hc⟩)
    exact congrArg ULift.up (w.windowMap_eq_capChart x hx hc)
  · intro x hx
    change ULift.up (w.window ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
      ULift.up (w.retainedMap x)
    exact congrArg ULift.up (w.window_eq_retainedMap x hx)

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
