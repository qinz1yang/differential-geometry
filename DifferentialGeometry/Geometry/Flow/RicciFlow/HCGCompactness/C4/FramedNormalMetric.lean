import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

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
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
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
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact NormalCoordinates.framedMetric_zero (I := I) Y.metric c

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem radialEnorm_framed
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    ∀ t : Real, ‖t • v‖ < expRadiusGp (I := I) Y.metric x →
      ‖mfderiv 𝓘(Real, Real) I
          (fun s : Real => (expMap (I := I) Y.metric x
            (show TangentSpace I x from
              s • (show E from normalFrame (I := I) Y.metric x v)) : Y.M))
          t (1 : Real)‖ₑ =
        ENNReal.ofReal
          (Real.sqrt (framedCoordMetric (I := I) Y x (t • v) v v)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
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
    change normalFrame (I := I) Y.metric x (t • v) ∈
      (expMapDiffeo (I := I) Y.metric x).source
    simpa only [a, map_smul] using hsrcRaw
  have hev : expMapDiffeo (I := I) Y.metric x =ᶠ[nhds (t • a)]
      (fun z : E => (expMap (I := I) Y.metric x
        (show TangentSpace I x from z) : Y.M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hsrcRaw) ?_
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x hz
  simp only [a] at hev
  rw [mfderiv_exp_radial (I := I) Y.metric x a t hraw]
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
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
      (Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hmap : ContMDiffOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) Y.metric x)
      (Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x)) := by
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
    simpa only [framedExpMap_apply, Function.comp_apply] using
      (hexp.comp z hframe).contMDiffWithinAt
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
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
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
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
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
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  refine ⟨expRadiusGp (I := I) Y.metric x,
    expRadiusGp_pos (I := I) Y.metric x, ?_⟩
  exact (framedCoordMetric_contDiffOn_of_smooth (I := I) Y x
    Metric.isOpen_ball (framedExp_smoothOn (I := I) Y x)).mono Set.inter_subset_left

theorem framedCoordMetric_contDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ∃ r : Real, 0 < r ∧
      ContDiffOn Real (⊤ : ℕ∞) (framedCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) r) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
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
      (Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
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
        (expRadiusGp (I := I) (X.obj k).metric (c k))) :
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
        Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rintro _ ⟨v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  have hvRaw : ‖(show E from normalFrame (I := I) Y.metric x v)‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hv
  have hchart := normalChartAt_contMDiffAt_infty (I := I) Y.metric x hvRaw
  have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (fun w : E => (normalFrame (I := I) Y.metric x).symm w)
      (normalChartAt (I := I) Y.metric x
        (framedExpMap (I := I) Y.metric x v)) :=
    (normalFrame (I := I) Y.metric x).symm.toContinuousLinearMap.contMDiff.contMDiffAt
  simpa only [framedChart_apply, framedExpMap_apply, Function.comp_apply] using
    (hframe.comp (framedExpMap (I := I) Y.metric x v) hchart).contMDiffWithinAt

theorem contDiffOn_framedTransition
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) {U : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => framedExpDiffeo (I := I) Y.metric x z) U
        (framedExpMap (I := I) Y.metric y ''
          Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric y))) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (framedTransition (I := I) Y.metric x y) U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun z => framedExpDiffeo (I := I) Y.metric x z) U :=
    (framedExp_smoothOn (I := I) Y x).mono hUx
  exact (framedChart_smooth (I := I) Y y).comp hexp hmaps

end HCGCompactness
end DifferentialGeometry
