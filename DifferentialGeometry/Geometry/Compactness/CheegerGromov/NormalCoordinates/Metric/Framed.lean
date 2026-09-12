import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.CompactBounds
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.IntrinsicGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Basic
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Smoothness


import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

noncomputable def framedCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  NormalCoordinates.framedMetric (I := I) Y.metric x

def FramedCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) : Prop :=
  ∀ z ∈ U, ∀ v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤ framedCoordMetric (I := I) Y x z v v ∧
      framedCoordMetric (I := I) Y x z v v ≤ 2 * ‖v‖ ^ 2

omit [NeZero (Module.finrank Real E)] in
theorem framedCoordMetric_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedCoordMetric (I := I) Y x z v w =
      Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I
          (fun u => framedExpDiffeo (I := I) Y.metric x u) z v)
        (mfderiv 𝓘(Real, E) I
          (fun u => framedExpDiffeo (I := I) Y.metric x u) z w) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact NormalCoordinates.framedMetric_apply (I := I) Y.metric x z v w

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedCoordMetric_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedCoordMetric (I := I) Y c 0 =
      (innerSL Real : E →L[Real] E →L[Real] Real) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact NormalCoordinates.framedMetric_zero (I := I) Y.metric c

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem radialEnorm_framed
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    ∀ t : Real, ‖t • v‖ < metricCoerciveExpRadius (I := I) Y.metric x →
      ‖mfderiv 𝓘(Real, Real) I
          (fun s : Real => (expMap (I := I) Y.metric x
            (show TangentSpace I x from
              s • (show E from normalFrame (I := I) Y.metric x v)) : Y.M))
          t (1 : Real)‖ₑ =
        ENNReal.ofReal
          (Real.sqrt (framedCoordMetric (I := I) Y x (t • v) v v)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro t ht
  let a : E := show E from normalFrame (I := I) Y.metric x v
  have hraw : ‖t • a‖ < expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt
      (I := I) Y.metric x (x := t • a)
    have ha : t • a =
        (show E from normalFrame (I := I) Y.metric x (t • v)) := by
      change t • (normalFrame (I := I) Y.metric x v) =
        normalFrame (I := I) Y.metric x (t • v)
      exact (map_smul (normalFrame (I := I) Y.metric x) t v).symm
    rw [ha, normalFrame_sqrt]
    exact ht
  have hsrcRaw : t • a ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hraw
  have hsrc : t • v ∈ (framedExpDiffeo (I := I) Y.metric x).source := by
    rw [framedExp_source]
    change tangentSpaceModelContinuousLinearEquiv (I := I) x
        (normalFrame (I := I) Y.metric x (t • v)) ∈
      (expMapDiffeo (I := I) Y.metric x).source
    simpa only [a, map_smul, tangentSpaceModelContinuousLinearEquiv_apply] using hsrcRaw
  have hev : expMapDiffeo (I := I) Y.metric x =ᶠ[nhds (t • a)]
      (fun z : E => (expMap (I := I) Y.metric x
        (show TangentSpace I x from z) : Y.M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hsrcRaw) ?_
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x hz
  simp only [a] at hev
  rw [mfderiv_exp_radial (I := I) Y.metric x a t hraw]
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  have hinner :
      (inner Real
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • a) a)
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • a) a) : Real) =
        Y.metric.inner
          (expMap (I := I) Y.metric x (show TangentSpace I x from t • a))
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • a) a)
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • a) a) := rfl
  rw [hinner, framedCoordMetric_apply (I := I)]
  simp only [a] at hsrcRaw ⊢
  rw [mfderiv_framedExp (I := I) Y.metric x hsrc]
  rw [framedExp_apply]
  rw [map_smul (normalFrame (I := I) Y.metric x) t v]
  let dRaw := mfderiv 𝓘(Real, E) I
    (fun u : E => expMapDiffeo (I := I) Y.metric x u)
    (t • (show E from normalFrame (I := I) Y.metric x v))
  change _ = ENNReal.ofReal (Real.sqrt
    (Y.metric.inner
      (expMapDiffeo (I := I) Y.metric x
        (t • (show E from normalFrame (I := I) Y.metric x v)))
      ((dRaw.comp (normalFrame (I := I) Y.metric x).toContinuousLinearMap) v)
      ((dRaw.comp (normalFrame (I := I) Y.metric x).toContinuousLinearMap) v)))
  have hcomp :
      (dRaw.comp (normalFrame (I := I) Y.metric x).toContinuousLinearMap) v =
        dRaw (show E from normalFrame (I := I) Y.metric x v) := rfl
  rw [hcomp]
  rw [expMapDiffeo_apply_eq (I := I) Y.metric x hsrcRaw]
  dsimp only [dRaw]
  rw [hev.mfderiv_eq]

theorem framedExp_smoothOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) I ∞
      (fun z => framedExpDiffeo (I := I) Y.metric x z)
      (Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hmap : ContMDiffOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) Y.metric x)
      (Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x)) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hzRaw : ‖(show E from normalFrame (I := I) Y.metric x z)‖ <
        expMapC2Radius (I := I) Y.metric x := by
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
      simpa only [normalFrame_sqrt] using hz
    have hexp := expMap_contMDiffAt_infty_of_norm_lt_radius
      (I := I) Y.metric x hzRaw
    have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
        (fun w : E => (show E from normalFrame (I := I) Y.metric x w)) z :=
      (normalFrame (I := I) Y.metric x).toContinuousLinearMap.contMDiff.contMDiffAt
    have hcomp := hexp.comp z hframe
    have hfun :
        ((fun u : E ↦ expMap (I := I) Y.metric x (show TangentSpace I x from u)) ∘
            fun w : E ↦ (show E from normalFrame (I := I) Y.metric x w)) =
          framedExpMap (I := I) Y.metric x := by
      funext w
      rfl
    rw [← hfun]
    exact hcomp.contMDiffWithinAt
  refine hmap.congr (fun z hz => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzRaw : ‖(show E from normalFrame (I := I) Y.metric x z)‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hz
  exact framedExp_eq_expMap (I := I) Y.metric x
    (by
      rw [framedExp_source]
      exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzRaw)

omit [NeZero (Module.finrank Real E)] in
private theorem framedPush_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {U : Set E}
    (hU : IsOpen U)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞
            (fun w => framedExpDiffeo (I := I) Y.metric x w) U)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E)) ∞
      (fun z => TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
        (framedExpDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I
          (fun u => framedExpDiffeo (I := I) Y.metric x u) z v)) U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have htm := hf.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn
  have hσ : ContMDiff 𝓘(Real, E) (𝓘(Real, E)).tangent ∞
      (fun z : E => (TotalSpace.mk' E z v : TangentBundle 𝓘(Real, E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => v)).mpr contDiff_const
  have hcomp : ContMDiffOn 𝓘(Real, E) I.tangent ∞
      (fun z => tangentMapWithin 𝓘(Real, E) I
        (fun w => framedExpDiffeo (I := I) Y.metric x w) U
        (TotalSpace.mk' E z v)) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun z hz => hz)
  refine hcomp.congr ?_
  intro z hz
  have hmf : mfderivWithin 𝓘(Real, E) I
      (fun w => framedExpDiffeo (I := I) Y.metric x w) U z =
      mfderiv 𝓘(Real, E) I
        (fun w => framedExpDiffeo (I := I) Y.metric x w) z :=
    mfderivWithin_of_isOpen hU hz
  change TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
      (framedExpDiffeo (I := I) Y.metric x z)
      (mfderiv 𝓘(Real, E) I
        (fun u => framedExpDiffeo (I := I) Y.metric x u) z v) =
      tangentMapWithin 𝓘(Real, E) I
        (fun w => framedExpDiffeo (I := I) Y.metric x w) U
          (TotalSpace.mk' E z v)
  dsimp only [tangentMapWithin]
  rw [hmf]

omit [NeZero (Module.finrank Real E)] in
theorem framedCoordMetric_contDiffOn_of_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {S : Set E}
    (hU : IsOpen S)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞
            (fun w => framedExpDiffeo (I := I) Y.metric x w) S) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (framedCoordMetric (I := I) Y x) S := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hscalar : ∀ v w : E, ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun z => Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z)
          (mfderiv 𝓘(Real, E) I
            (fun u => framedExpDiffeo (I := I) Y.metric x u) z v)
          (mfderiv 𝓘(Real, E) I
            (fun u => framedExpDiffeo (I := I) Y.metric x u) z w))
      S := by
    intro v w
    have hg : ContMDiffOn 𝓘(Real, E)
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun z => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : Y.M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (framedExpDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z)))
        S :=
      Y.metric.contMDiff.comp_contMDiffOn hf
    have hv := framedPush_smooth (I := I) Y x hU hf v
    have hw := framedPush_smooth (I := I) Y x hU hf w
    have htotal : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, Real)) ∞
        (fun z => TotalSpace.mk' Real (E := Bundle.Trivial Y.M Real)
          (framedExpDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z)
            (mfderiv 𝓘(Real, E) I
              (fun u => framedExpDiffeo (I := I) Y.metric x u) z v)
            (mfderiv 𝓘(Real, E) I
              (fun u => framedExpDiffeo (I := I) Y.metric x u) z w)))
        S :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := fun b : Y.M => TangentSpace I b)
        (E₂ := fun b : Y.M => TangentSpace I b)
        (E₃ := fun _ : Y.M => Real)
        (b := fun z => framedExpDiffeo (I := I) Y.metric x z)
        (ψ := fun z => Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z))
        (v := fun z => mfderiv 𝓘(Real, E) I
          (fun u => framedExpDiffeo (I := I) Y.metric x u) z v)
        (w := fun z => mfderiv 𝓘(Real, E) I
          (fun u => framedExpDiffeo (I := I) Y.metric x u) z w)
        hg hv hw
    intro z hz
    have h_at := htotal z hz
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.2
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  rw [← contMDiffOn_iff_contDiffOn]
  exact (hscalar v w).congr
    (fun z _ => framedCoordMetric_apply (I := I) Y x z v w)

theorem framedCoordMetric_contDiffOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : Real, 0 < δ ∧
      ContDiffOn Real (⊤ : ℕ∞) (framedCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) δ ∩
          (framedExpDiffeo (I := I) Y.metric x).source) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  refine ⟨metricCoerciveExpRadius (I := I) Y.metric x,
    metricCoerciveExpRadius_pos (I := I) Y.metric x, ?_⟩
  exact (framedCoordMetric_contDiffOn_of_smooth (I := I) Y x
    Metric.isOpen_ball (framedExp_smoothOn (I := I) Y x)).mono Set.inter_subset_left

theorem framedCoordMetric_contDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ∃ r : Real, 0 < r ∧
      ContDiffOn Real (⊤ : ℕ∞) (framedCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) r) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hsm⟩ := framedCoordMetric_contDiffOn (I := I) Y x
  obtain ⟨r₀, hr₀, hsub⟩ :=
    Metric.isOpen_iff.mp (framedExpDiffeo (I := I) Y.metric x).open_source 0
      (zero_mem_framedExp_source (I := I) Y.metric x)
  refine ⟨min δ r₀, lt_min hδ hr₀, hsm.mono fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine ⟨Metric.mem_ball.mpr ?_, hsub (Metric.mem_ball.mpr ?_)⟩
  · rw [dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  · rw [dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_right _ _)

theorem framedCoordMetric_contDiffOn_expBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (framedCoordMetric (I := I) Y x)
      (Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact framedCoordMetric_contDiffOn_of_smooth (I := I) Y x Metric.isOpen_ball
    (framedExp_smoothOn (I := I) Y x)

theorem contDiffOn_framedCoordMetric_of_subset_expBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (c : ∀ k : ℕ, (X.obj k).M) {U : Set E}
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (metricCoerciveExpRadius (I := I) (X.obj k).metric (c k))) :
    ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (framedCoordMetric (I := I) (X.obj k) (c k)) U :=
  fun k =>
    (framedCoordMetric_contDiffOn_expBall (I := I) (X.obj k) (c k)).mono (hsub k)

theorem framedChart_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn I 𝓘(Real, E) ∞ (framedChartAt (I := I) Y.metric x)
      (framedExpMap (I := I) Y.metric x ''
        Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rintro _ ⟨v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  have hvRaw : ‖(show E from normalFrame (I := I) Y.metric x v)‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hv
  have hchart := normal_chart_at_cont_mdiff_at_infty (I := I) Y.metric x hvRaw
  have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (fun w : E => (normalFrame (I := I) Y.metric x).symm w)
      (normalChartAt (I := I) Y.metric x
        (framedExpMap (I := I) Y.metric x v)) :=
    (normalFrame (I := I) Y.metric x).symm.toContinuousLinearMap.contMDiff.contMDiffAt
  have hcomp := hframe.comp (framedExpMap (I := I) Y.metric x v) hchart
  have hfun :
      ((fun w : E ↦ (normalFrame (I := I) Y.metric x).symm w) ∘
          fun q : Y.M ↦ normalChartAt (I := I) Y.metric x q) =
        (framedChartAt (I := I) Y.metric x : Y.M → E) := by
    funext q
    rfl
  rw [← hfun]
  exact hcomp.contMDiffWithinAt

theorem contDiffOn_framedTransition
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) {U : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => framedExpDiffeo (I := I) Y.metric x z) U
        (framedExpMap (I := I) Y.metric y ''
          Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric y))) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (framedTransition (I := I) Y.metric x y) U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun z => framedExpDiffeo (I := I) Y.metric x z) U :=
    (framedExp_smoothOn (I := I) Y x).mono hUx
  exact (framedChart_smooth (I := I) Y y).comp hexp hmaps

local instance framedMetricFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance framedMetricFormNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem normalCoordMetric_eq_pullback_framedMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u : E}
    (hu : letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      u ∈ (expMapDiffeo (I := I) Y.metric x).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let L : E ≃L[ℝ] E :=
      (normalFrame (I := I) Y.metric x).trans
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
    normalCoordMetric (I := I) Y x u =
      pullbackForm (framedMetric (I := I) Y.metric x (L.symm u), (L.symm : E →L[ℝ] E)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L : E ≃L[ℝ] E :=
    (normalFrame (I := I) Y.metric x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  change normalCoordMetric (I := I) Y x u =
    pullbackForm (framedMetric (I := I) Y.metric x (L.symm u), (L.symm : E →L[ℝ] E))
  have hLc : ((tangentSpaceModelContinuousLinearEquiv (I := I) x : TangentSpace I x →L[ℝ] E) ∘SL
      (normalFrame (I := I) Y.metric x : E →L[ℝ] TangentSpace I x)) = (L : E →L[ℝ] E) := rfl
  have hLs : L.symm u ∈ (framedExpDiffeo (I := I) Y.metric x).source := by
    rw [framedExp_source]
    change L (L.symm u) ∈ (expMapDiffeo (I := I) Y.metric x).source
    rw [L.apply_symm_apply]
    exact hu
  have hb := framedMetric_eq_pullback_normalCoordMetric (I := I) Y x (L.symm u) hLs
  rw [hLc] at hb
  dsimp only at hb
  have happ : (↑L : E →L[ℝ] E) (L.symm u) = u := by simp
  rw [happ] at hb
  rw [hb]
  ext v w
  simp [pullbackForm_apply]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalCoordMetric_eq_pullback_framedCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u : E}
    (hu : letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      u ∈ (expMapDiffeo (I := I) Y.metric x).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y x u =
      pullbackForm (framedCoordMetric (I := I) Y x
          (((normalFrame (I := I) Y.metric x).trans
            (tangentSpaceModelContinuousLinearEquiv (I := I) x)).symm u),
        (((normalFrame (I := I) Y.metric x).trans
            (tangentSpaceModelContinuousLinearEquiv (I := I) x)).symm : E →L[ℝ] E)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L : E ≃L[ℝ] E :=
    (normalFrame (I := I) Y.metric x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  change normalCoordMetric (I := I) Y x u =
    pullbackForm (framedMetric (I := I) Y.metric x (L.symm u), (L.symm : E →L[ℝ] E))
  exact normalCoordMetric_eq_pullback_framedMetric (I := I) Y x hu

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedFDeriv_normalCoordMetric_le_of_framedCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {s U : Set E} (hs : IsOpen s)
    (hsmooth : letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ContDiffOn ℝ ∞ (framedCoordMetric (I := I) Y x) s)
    (hUsrc : ∀ u ∈ U,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      u ∈ (expMapDiffeo (I := I) Y.metric x).source)
    (hsU : ∀ u ∈ U,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      (((normalFrame (I := I) Y.metric x).trans
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)).symm u) ∈ s)
    (p : ℕ) {C : ℝ}
    (hC : ∀ u ∈ U,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ‖iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x)
        (((normalFrame (I := I) Y.metric x).trans
          (tangentSpaceModelContinuousLinearEquiv (I := I) x)).symm u)‖ ≤ C) :
    ∀ u ∈ U,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ‖iteratedFDeriv ℝ p (normalCoordMetric (I := I) Y x) u‖ ≤
        C * ‖(((normalFrame (I := I) Y.metric x).trans
          (tangentSpaceModelContinuousLinearEquiv (I := I) x)).symm : E →L[ℝ] E)‖ ^ (p + 2) := by
  intro u hu
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L : E ≃L[ℝ] E :=
    (normalFrame (I := I) Y.metric x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  change ‖iteratedFDeriv ℝ p (normalCoordMetric (I := I) Y x) u‖ ≤
    C * ‖(L.symm : E →L[ℝ] E)‖ ^ (p + 2)
  let Ls : E →L[ℝ] E := (L.symm : E →L[ℝ] E)
  let T : (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip Ls
  let F : (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let S : (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    F.comp (T.comp (F.comp T))
  have hT : ∀ X : E →L[ℝ] E →L[ℝ] ℝ, T X = X ∘SL Ls := by
    intro X
    simp only [T, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  have hF : ∀ X : E →L[ℝ] E →L[ℝ] ℝ, F X = X.flip := fun X => rfl
  have hS_form : ∀ B : E →L[ℝ] E →L[ℝ] ℝ, S B = pullbackForm (B, Ls) := by
    intro B
    ext a b
    change F (T (F (T B))) a b = pullbackForm (B, Ls) a b
    rw [hF, hT, hF, hT, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      pullbackForm_apply]
  have hSnorm : ‖S‖ ≤ ‖Ls‖ ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound S (by positivity) fun B => ?_
    rw [hS_form B]
    refine ContinuousLinearMap.opNorm_le_bound (pullbackForm (B, Ls)) (by positivity) fun a => ?_
    refine ContinuousLinearMap.opNorm_le_bound (pullbackForm (B, Ls) a) (by positivity) fun b => ?_
    calc ‖pullbackForm (B, Ls) a b‖ = ‖B (Ls a) (Ls b)‖ := by rw [pullbackForm_apply]
      _ ≤ ‖B‖ * ‖Ls a‖ * ‖Ls b‖ := ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * (‖Ls‖ * ‖a‖) * (‖Ls‖ * ‖b‖) := by
            gcongr <;> exact ContinuousLinearMap.le_opNorm Ls _
      _ = (‖Ls‖ ^ 2 * ‖B‖) * ‖a‖ * ‖b‖ := by ring
  have hbridge : ∀ w ∈ (expMapDiffeo (I := I) Y.metric x).source,
      normalCoordMetric (I := I) Y x w =
        pullbackForm (framedCoordMetric (I := I) Y x (L.symm w), Ls) := by
    intro w hw
    change normalCoordMetric (I := I) Y x w =
      pullbackForm (framedMetric (I := I) Y.metric x (L.symm w), (L.symm : E →L[ℝ] E))
    exact normalCoordMetric_eq_pullback_framedMetric (I := I) Y x hw
  have hV : IsOpen (expMapDiffeo (I := I) Y.metric x).source :=
    (expMapDiffeo (I := I) Y.metric x).open_source
  have hiter : iteratedFDeriv ℝ p (normalCoordMetric (I := I) Y x) u =
      iteratedFDeriv ℝ p
        (fun w : E => pullbackForm (framedCoordMetric (I := I) Y x (Ls w), Ls)) u := by
    rw [← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) p hV) (hUsrc u hu),
      ← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) p hV) (hUsrc u hu)]
    exact iteratedFDerivWithin_congr (fun w hw => hbridge w hw) (hUsrc u hu) p
  have hScomp : (fun w : E => pullbackForm (framedCoordMetric (I := I) Y x (Ls w), Ls)) =
      (⇑S ∘ fun w : E => framedCoordMetric (I := I) Y x (Ls w)) := by
    funext w
    rw [Function.comp_apply, hS_form]
  have hsmooth_p : ContDiffOn ℝ (p : WithTop ℕ∞) (framedCoordMetric (I := I) Y x) s :=
    hsmooth.of_le (by exact_mod_cast le_top)
  have hx : (0 : E) + Ls u ∈ s := by
    rw [zero_add]
    exact hsU u hu
  have hcomp := DifferentialGeometry.Analysis.iteratedFDeriv_comp_affine
    (k := p) hs hsmooth_p (0 : E) Ls (x := u) hx
  simp only [zero_add] at hcomp
  have hsmAt : ContDiffAt ℝ ∞
      (fun w : E => framedCoordMetric (I := I) Y x (Ls w)) u :=
    (hsmooth.contDiffAt (hs.mem_nhds (hsU u hu))).comp u Ls.contDiff.contDiffAt
  have hleft := S.iteratedFDeriv_comp_left hsmAt (i := p)
    (by exact_mod_cast le_top : (p : WithTop ℕ∞) ≤ ∞)
  calc ‖iteratedFDeriv ℝ p (normalCoordMetric (I := I) Y x) u‖
      = ‖iteratedFDeriv ℝ p
          (fun w : E => pullbackForm (framedCoordMetric (I := I) Y x (Ls w), Ls)) u‖ := by
        rw [hiter]
    _ = ‖S.compContinuousMultilinearMap
          (iteratedFDeriv ℝ p
            (fun w : E => framedCoordMetric (I := I) Y x (Ls w)) u)‖ := by
        rw [hScomp, hleft]
    _ ≤ ‖S‖ * ‖iteratedFDeriv ℝ p
          (fun w : E => framedCoordMetric (I := I) Y x (Ls w)) u‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ = ‖S‖ * ‖(iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x) (Ls u)).compContinuousLinearMap
          (fun _ : Fin p => Ls)‖ := by rw [hcomp]
    _ ≤ ‖S‖ * (‖iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x) (Ls u)‖ * ‖Ls‖ ^ p) := by
        gcongr
        calc ‖(iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x) (Ls u)).compContinuousLinearMap
              (fun _ : Fin p => Ls)‖
            ≤ ‖iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x) (Ls u)‖ *
                ∏ _ : Fin p, ‖Ls‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ p (framedCoordMetric (I := I) Y x) (Ls u)‖ * ‖Ls‖ ^ p := by
              simp
    _ ≤ ‖Ls‖ ^ 2 * (C * ‖Ls‖ ^ p) := by
        gcongr
        exact hC u hu
    _ = C * ‖Ls‖ ^ (p + 2) := by ring

end CheegerGromovCompactness
end DifferentialGeometry
