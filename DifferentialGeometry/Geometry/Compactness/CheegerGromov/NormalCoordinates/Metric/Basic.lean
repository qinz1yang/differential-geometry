import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Basic
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.Smoothness.AwayFromZero
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.InjectivityRadiusDecay.Defs

open DifferentialGeometry.Geometry.Curvature

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

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section RawNormalCoordinates

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

private local instance : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def normalTransition
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M) : E → E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  fun z =>
    normalChartAt (I := I) X.metric y
      (expMapDiffeo (I := I) X.metric x z)

noncomputable def normalCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E -> (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  fun z =>
    let D : E →L[Real] TangentSpace I (expMapDiffeo (I := I) Y.metric x z) :=
      mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)).comp D)

omit [NeZero (Module.finrank ℝ E)] in
theorem exp_map_diffeo_cont_mdiff_on_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContMDiffOn 𝓘(Real, E) I ∞
        (fun w => expMapDiffeo (I := I) Y.metric x w)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hforward⟩ :=
    expMap_contMDiffAt_infty_of_norm_lt (I := I) Y.metric x
  refine ⟨δ, hδ, ?_⟩
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
    intro w hw
    have hwδ : ‖w‖ < δ := by
      have := hw.1; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    exact (hforward w hwδ).contMDiffWithinAt
  exact hexp.congr (fun w hw => expMapDiffeo_apply_eq (I := I) Y.metric x hw.2)

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_coord_metric_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y x z v w =
      Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [normalCoordMetric, ContinuousLinearMap.comp_apply,
    ]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_coord_metric_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y c 0 = Y.metric.inner c := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext v w
  rw [normal_coord_metric_apply (I := I), expMapDiffeo_zero (I := I)]
  exact normalChartAt_metric_pullback_at_origin (I := I) Y.metric c v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem radial_enorm_normal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    ∀ (t : Real), ‖t • v‖ < expMapC2Radius (I := I) Y.metric x →
    ‖mfderiv 𝓘(Real, Real) I
        (fun s : Real => (expMap (I := I) Y.metric x
          (show TangentSpace I x from (s • v)) : Y.M)) t (1 : Real)‖ₑ =
      ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := I) Y x (t • v) v v)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro t ht
  have hsrc : t • v ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x ht
  have hev : expMapDiffeo (I := I) Y.metric x =ᶠ[nhds (t • v)]
      (fun z : E => (expMap (I := I) Y.metric x
        (show TangentSpace I x from z) : Y.M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hsrc) ?_
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x hz
  rw [mfderiv_exp_radial (I := I) Y.metric x v t ht]
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  have hinner :
      (inner Real
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • v)
          (show TangentSpace I x from v))
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • v)
          (show TangentSpace I x from v)) : Real) =
        Y.metric.inner
          (expMap (I := I) Y.metric x (show TangentSpace I x from (t • v)))
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • v)
            (show TangentSpace I x from v))
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • v)
            (show TangentSpace I x from v)) := rfl
  rw [hinner, normal_coord_metric_apply (I := I),
    expMapDiffeo_apply_eq (I := I) Y.metric x hsrc, hev.mfderiv_eq]

omit [NeZero (Module.finrank ℝ E)] in
private theorem exp_map_diffeo_pushforward_section_cont_mdiff_on
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {U : Set E}
    (hU : IsOpen U)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) U)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E)) ∞
      (fun z => TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
        (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)) U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have htm := hf.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn
  have hσ : ContMDiff 𝓘(Real, E) (𝓘(Real, E)).tangent ∞
      (fun z : E => (TotalSpace.mk' E z v : TangentBundle 𝓘(Real, E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => v)).mpr contDiff_const
  have hcomp : ContMDiffOn 𝓘(Real, E) I.tangent ∞
      (fun z => tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
        (TotalSpace.mk' E z v)) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun z hz => hz)
  refine hcomp.congr ?_
  intro z hz
  have hmf : mfderivWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U z
      = mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z :=
    mfderivWithin_of_isOpen hU hz
  change TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
      (expMapDiffeo (I := I) Y.metric x z)
      (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
      = tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
          (TotalSpace.mk' E z v)
  dsimp only [tangentMapWithin]
  rw [hmf]

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_coord_metric_cont_diff_on_of_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {S : Set E}
    (hU : IsOpen S)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) S) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) S := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hscalar : ∀ v w : E, ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w))
      S := by
    intro v w
    have hg : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun z => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : Y.M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)))
        S :=
      Y.metric.contMDiff.comp_contMDiffOn hf
    have hv := exp_map_diffeo_pushforward_section_cont_mdiff_on (I := I) Y x hU hf v
    have hw := exp_map_diffeo_pushforward_section_cont_mdiff_on (I := I) Y x hU hf w
    have htotal : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, Real)) ∞
        (fun z => TotalSpace.mk' Real (E := Bundle.Trivial Y.M Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)))
        S :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := fun b : Y.M => TangentSpace I b) (E₂ := fun b : Y.M => TangentSpace I b)
        (E₃ := fun _ : Y.M => Real)
        (b := fun z => expMapDiffeo (I := I) Y.metric x z)
        (ψ := fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z))
        (v := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (w := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)
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
  exact (hscalar v w).congr (fun z _ => normal_coord_metric_apply (I := I) Y x z v w)

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_coord_metric_cont_diff_on
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hf⟩ := exp_map_diffeo_cont_mdiff_on_ball (I := I) Y x
  exact ⟨δ, hδ, normal_coord_metric_cont_diff_on_of_smooth (I := I) Y x
    (Metric.isOpen_ball.inter (expMapDiffeo (I := I) Y.metric x).open_source) hf⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_coord_metric_cont_diff_on_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) (Metric.ball (0 : E) r) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hsm⟩ := normal_coord_metric_cont_diff_on (I := I) Y x
  obtain ⟨r₀, hr₀, hsub⟩ :=
    Metric.isOpen_iff.mp (expMapDiffeo (I := I) Y.metric x).open_source 0
      (zero_mem_expMapDiffeo_source (I := I) Y.metric x)
  refine ⟨min δ r₀, lt_min hδ hr₀, hsm.mono fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine ⟨Metric.mem_ball.mpr ?_, hsub (Metric.mem_ball.mpr ?_)⟩
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_right _ _)

omit [NeZero (Module.finrank Real E)] in
theorem exp_map_diffeo_cont_mdiff_on_exp_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) I ∞
      (fun w => expMapDiffeo (I := I) Y.metric x w)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) Y.metric x hw).contMDiffWithinAt
  refine hexp.congr (fun w hw => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact expMapDiffeo_apply_eq (I := I) Y.metric x
    (mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hw)

omit [NeZero (Module.finrank Real E)] in
theorem normal_coord_metric_cont_diff_on_exp_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact normal_coord_metric_cont_diff_on_of_smooth (I := I) Y x Metric.isOpen_ball
    (exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x)

omit [NeZero (Module.finrank Real E)] in
theorem normal_coord_metric_cont_diff_on_of_subset_exp_ball
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (c : ∀ k : ℕ, (X.obj k).M) {U : Set E}
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric (c k))) :
    ∀ k, ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) (X.obj k) (c k)) U :=
  fun k => (normal_coord_metric_cont_diff_on_exp_ball (I := I) (X.obj k) (c k)).mono (hsub k)

end RawNormalCoordinates

end HCGCompactness
end DifferentialGeometry
