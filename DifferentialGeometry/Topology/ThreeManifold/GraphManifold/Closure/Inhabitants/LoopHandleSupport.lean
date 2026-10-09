import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleRimInverse

/-!
The original handle radial and time cutoffs have compact support inside its genuine wide chart.
The closed pullback to the whole actual base permits a smooth constant outer extension.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem handleSupport_source :
    (closedBall (0 : ModelPlane) (5 / 4) ×ˢ Set.Icc (-3 / 16 : ℝ) (19 / 16)) ⊆
      loopActualHandleChart.source := by
  rw [loopActualHandleChart_source]
  rintro ⟨w, t⟩ h
  have hw := mem_closedBall_zero_iff.mp h.1
  have ht := h.2
  refine ⟨?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2]

def loopHandleSupport : Set SphereCarrier.{0} := loopActualHandleChart ''
  (closedBall (0 : ModelPlane) (5 / 4) ×ˢ Set.Icc (-3 / 16 : ℝ) (19 / 16))

theorem loopHandleSupport_compact : IsCompact loopHandleSupport :=
  ((isCompact_closedBall _ _).prod isCompact_Icc).image_of_continuousOn
    (loopActualHandleChart.contMDiffOn_toFun.continuousOn.mono handleSupport_source)

theorem loopHandleSupport_closed : IsClosed loopHandleSupport := loopHandleSupport_compact.isClosed

theorem loopHandleSupport_target : loopHandleSupport ⊆ loopActualHandleChart.target := by
  rintro p ⟨x, hx, rfl⟩
  exact loopActualHandleChart.map_source (handleSupport_source hx)

def loopHandleBaseSupport : Set loopCircleBase := loopCircleSection ⁻¹' loopHandleSupport

theorem loopHandleBaseSupport_closed : IsClosed loopHandleBaseSupport :=
  loopHandleSupport_closed.preimage loopCircleSection_smooth.continuous

theorem loopHandleBaseSupport_target {z : loopCircleBase} (hz : z ∈ loopHandleBaseSupport) :
    loopCircleSection z ∈ loopActualHandleChart.target := loopHandleSupport_target hz

theorem loopHandleInverse_outside {z : loopCircleBase} (hz : z ∉ loopHandleBaseSupport)
    (ht : loopCircleSection z ∈ loopActualHandleChart.target) :
    5 / 4 ≤ ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖ ∨
    (loopActualHandleChart.symm (loopCircleSection z)).2 ≤ -3 / 16 ∨
    19 / 16 ≤ (loopActualHandleChart.symm (loopCircleSection z)).2 := by
  by_contra hn
  push Not at hn
  apply hz
  refine ⟨loopActualHandleChart.symm (loopCircleSection z), ?_, ?_⟩
  · exact ⟨mem_closedBall_zero_iff.mpr hn.1.le, hn.2.1.le, hn.2.2.le⟩
  · exact loopActualHandleChart.right_inv ht

end GC.GraphManifold.Assembly
