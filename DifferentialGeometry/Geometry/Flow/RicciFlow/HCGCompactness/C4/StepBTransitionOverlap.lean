import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

set_option autoImplicit false

/-!
# Domain adapters for normal-coordinate transitions

The transition compactness layer asks for chart-overlap, image, and cancellation
facts separately.  For the canonical framed normal-coordinate transition these facts
come from one exponential-image containment together with the two coordinate
radius containments.  This file records those reusable low-level adapters.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private theorem mem_framed_src
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {z : E}
    (hz :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      z ∈ Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    z ∈ (framedExpDiffeo (I := I) Y.metric x).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [Metric.mem_ball, dist_zero_right] at hz
  rw [framedExp_source]
  apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
  apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
  simpa only [normalFrame_sqrt] using hz

/-- Exponential-image containment between two coordinate balls implies the
chart-overlap predicate used by transition compactness. -/
theorem normalOverlap_of_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x))
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => framedExpDiffeo (I := I) Y.metric x z) U
        (framedExpMap (I := I) Y.metric y '' V)) :
    NormalOverlapOn (I := I) Y x y U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  have hzx : z ∈ (framedExpDiffeo (I := I) Y.metric x).source :=
    mem_framed_src (I := I) Y x (hUx hz)
  refine ⟨hzx, ?_⟩
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change framedExpMap (I := I) Y.metric y v =
    framedExpDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (framedExpDiffeo (I := I) Y.metric y).source :=
    mem_framed_src (I := I) Y y (hVy hv)
  change framedExpDiffeo (I := I) Y.metric x z ∈
    (framedExpDiffeo (I := I) Y.metric y).target
  rw [← hvz, ← framedExp_eq_expMap (I := I) Y.metric y hvy]
  exact (framedExpDiffeo (I := I) Y.metric y).map_source hvy

/-- The same exponential-image containment makes the normal-coordinate
transition map land in the target coordinate set. -/
theorem normalTrans_mapsTo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => framedExpDiffeo (I := I) Y.metric x z) U
        (framedExpMap (I := I) Y.metric y '' V)) :
    Set.MapsTo (normalTransition (I := I) Y x y) U V := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change framedExpMap (I := I) Y.metric y v =
    framedExpDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (framedExpDiffeo (I := I) Y.metric y).source :=
    mem_framed_src (I := I) Y y (hVy hv)
  have hvTarget : v ∈ (framedChartAt (I := I) Y.metric y).target := by
    change v ∈ (framedExpDiffeo (I := I) Y.metric y).source
    exact hvy
  change framedChartAt (I := I) Y.metric y
      (framedExpDiffeo (I := I) Y.metric x z) ∈ V
  rw [← hvz, ← framedExp_eq_expMap (I := I) Y.metric y hvy]
  change framedChartAt (I := I) Y.metric y
      ((framedChartAt (I := I) Y.metric y).symm v) ∈ V
  have hyInv : framedChartAt (I := I) Y.metric y
      ((framedChartAt (I := I) Y.metric y).symm v) = v :=
    (framedChartAt (I := I) Y.metric y).right_inv hvTarget
  exact hyInv.symm ▸ hv

/-- On a verified overlap, decoding a normal transition in the target chart
returns the same manifold point as decoding its input in the source chart. -/
theorem NormalOverlapOn.decode
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x y : Y.M}
    {U : Set E} (h : NormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (framedChartAt (I := I) Y.metric y).symm
        (framedTransition (I := I) Y.metric x y z) =
      (framedChartAt (I := I) Y.metric x).symm z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨_hzx, hzy⟩ := h z hz
  change (framedChartAt (I := I) Y.metric y).symm
      (framedChartAt (I := I) Y.metric y
        ((framedChartAt (I := I) Y.metric x).symm z)) =
    (framedChartAt (I := I) Y.metric x).symm z
  exact (framedChartAt (I := I) Y.metric y).left_inv hzy

/-- On its overlap domain, reversing a normal-coordinate transition cancels
the forward transition. -/
theorem NormalOverlapOn.cancel
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x y : Y.M}
    {U : Set E} (h : NormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    normalTransition (I := I) Y y x
        (normalTransition (I := I) Y x y z) = z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨hzx, hzy⟩ := h z hz
  have hzt : z ∈ (framedChartAt (I := I) Y.metric x).target := by
    change z ∈ (framedExpDiffeo (I := I) Y.metric x).source
    exact hzx
  change framedChartAt (I := I) Y.metric x
      ((framedChartAt (I := I) Y.metric y).symm
        (framedChartAt (I := I) Y.metric y
          ((framedChartAt (I := I) Y.metric x).symm z))) = z
  have hyInv := (framedChartAt (I := I) Y.metric y).left_inv hzy
  have hxInv := (framedChartAt (I := I) Y.metric x).right_inv hzt
  exact (congrArg (fun q => framedChartAt (I := I) Y.metric x q) hyInv).trans hxInv

end HCGCompactness
end DifferentialGeometry
