import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.FramedNormalMetric
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

section Raw

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem normalOverlap_of_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x))
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) Y.metric x z) U
        ((fun v : E =>
          (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) '' V)) :
    NormalOverlapOn (I := I) Y x y U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  have hzx : z ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x (by
      simpa only [Metric.mem_ball, dist_zero_right] using hUx hz)
  refine ⟨hzx, ?_⟩
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M) =
    expMapDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (expMapDiffeo (I := I) Y.metric y).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric y (by
      simpa only [Metric.mem_ball, dist_zero_right] using hVy hv)
  rw [normalChartAt_source_eq]
  rw [← hvz, ← expMapDiffeo_apply_eq (I := I) Y.metric y hvy]
  exact (expMapDiffeo (I := I) Y.metric y).map_source hvy

theorem normalTrans_mapsTo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) Y.metric x z) U
        ((fun v : E =>
          (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) '' V)) :
    Set.MapsTo (normalTransition (I := I) Y x y) U V := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M) =
    expMapDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (normalChartAt (I := I) Y.metric y).target :=
    ball_subset_normalChartAt_target (I := I) Y.metric y (by
      simpa only [Metric.mem_ball, dist_zero_right] using hVy hv)
  change normalChartAt (I := I) Y.metric y
      (expMapDiffeo (I := I) Y.metric x z) ∈ V
  rw [← hvz, ← normalChartAt_symm_apply (I := I) Y.metric y hvy]
  rw [normalChartAt_right_inv (I := I) Y.metric y hvy]
  exact hv

omit [NeZero (Module.finrank Real E)] in
theorem NormalOverlapOn.decode
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x y : Y.M}
    {U : Set E} (h : NormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalChartAt (I := I) Y.metric y).symm
        (normalTransition (I := I) Y x y z) =
      (normalChartAt (I := I) Y.metric x).symm z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨_hzx, hzy⟩ := h z hz
  change (normalChartAt (I := I) Y.metric x).symm z ∈
    (normalChartAt (I := I) Y.metric y).source at hzy
  change (normalChartAt (I := I) Y.metric y).symm
      (normalChartAt (I := I) Y.metric y
        ((normalChartAt (I := I) Y.metric x).symm z)) =
    (normalChartAt (I := I) Y.metric x).symm z
  exact normalChartAt_left_inv (I := I) Y.metric y hzy

omit [NeZero (Module.finrank Real E)] in
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
  change (normalChartAt (I := I) Y.metric x).symm z ∈
    (normalChartAt (I := I) Y.metric y).source at hzy
  have hzt : z ∈ (normalChartAt (I := I) Y.metric x).target := by
    rwa [normalChartAt_target_eq]
  change normalChartAt (I := I) Y.metric x
      ((normalChartAt (I := I) Y.metric y).symm
        (normalChartAt (I := I) Y.metric y
          ((normalChartAt (I := I) Y.metric x).symm z))) = z
  rw [normalChartAt_left_inv (I := I) Y.metric y hzy]
  exact normalChartAt_right_inv (I := I) Y.metric x hzt

end Raw

section Framed

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def FramedNormalOverlapOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) (U : Set E) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ∀ z : E, z ∈ U →
    z ∈ (framedExpDiffeo (I := I) Y.metric x).source ∧
      framedExpDiffeo (I := I) Y.metric x z ∈
        (framedChartAt (I := I) Y.metric y).source

private theorem mem_framed_src
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) {z : E}
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

theorem framedOverlap_of_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) {U V : Set E}
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
    FramedNormalOverlapOn (I := I) Y x y U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  have hzx : z ∈ (framedExpDiffeo (I := I) Y.metric x).source :=
    mem_framed_src (I := I) Y x (hUx hz)
  refine ⟨hzx, ?_⟩
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  have hvy : v ∈ (framedExpDiffeo (I := I) Y.metric y).source :=
    mem_framed_src (I := I) Y y (hVy hv)
  have heq : framedExpDiffeo (I := I) Y.metric y v =
      framedExpDiffeo (I := I) Y.metric x z :=
    (framedExp_eq_expMap (I := I) Y.metric y hvy).trans hvz
  rw [← heq]
  exact (framedExpDiffeo (I := I) Y.metric y).map_source hvy

theorem framedTrans_mapsTo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) {U V : Set E}
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
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Set.MapsTo (framedTransition (I := I) Y.metric x y) U V := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  have hvy : v ∈ (framedExpDiffeo (I := I) Y.metric y).source :=
    mem_framed_src (I := I) Y y (hVy hv)
  have hvTarget : v ∈ (framedChartAt (I := I) Y.metric y).target := by
    change v ∈ (framedExpDiffeo (I := I) Y.metric y).source
    exact hvy
  have heq : framedExpDiffeo (I := I) Y.metric y v =
      framedExpDiffeo (I := I) Y.metric x z :=
    (framedExp_eq_expMap (I := I) Y.metric y hvy).trans hvz
  rw [framedTrans_apply]
  rw [← heq]
  change framedChartAt (I := I) Y.metric y
      ((framedChartAt (I := I) Y.metric y).symm v) ∈ V
  exact (framedChartAt (I := I) Y.metric y).right_inv hvTarget |>.symm ▸ hv

omit [NeZero (Module.finrank Real E)] in
theorem FramedNormalOverlapOn.decode
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {x y : Y.M} {U : Set E}
    (h : FramedNormalOverlapOn (I := I) Y x y U)
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

omit [NeZero (Module.finrank Real E)] in
theorem FramedNormalOverlapOn.cancel
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {x y : Y.M} {U : Set E}
    (h : FramedNormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedTransition (I := I) Y.metric y x
        (framedTransition (I := I) Y.metric x y z) = z := by
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
  exact (congrArg (fun q => framedChartAt (I := I) Y.metric x q) hyInv).trans
    hxInv

end Framed

end HCGCompactness
end DifferentialGeometry
