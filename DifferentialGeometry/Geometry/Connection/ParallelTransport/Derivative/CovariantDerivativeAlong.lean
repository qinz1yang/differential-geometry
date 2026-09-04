import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Chart.Transition

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace CovariantDerivativeAlong

def chartRepAt (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ → E :=
  fun s => (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (V s)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRepAt_apply (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t s : ℝ) :
    chartRepAt (I := I) γ V t s =
      (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (V s) := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem differentiableAt_chartRepAt_of_contMDiffAt_two
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ s) (V s) : TangentBundle I M)) t) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  let F : ℝ → TangentBundle I M := fun s ↦
    TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s)
  have hAt := Bundle.contMDiffAt_totalSpace.mp hV
  have hbase := hAt.1
  have hfiber := hAt.2
  have hmem :
      γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hpre :
      γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t)).baseSet ∈ 𝓝 t :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hmem)
  have heq :
      (fun s : ℝ ↦
        ((trivializationAt E (TangentSpace I) (γ t)) (F s)).2)
        =ᶠ[𝓝 t] chartRepAt (I := I) γ V t := by
    filter_upwards [hpre] with s hs
    rw [chartRepAt_apply]
    simp only [F, TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply
      (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hs]
  have hcoord : ContDiffAt ℝ 2
      (fun s : ℝ ↦
        ((trivializationAt E (TangentSpace I) (γ t)) (F s)).2) t :=
    contMDiffAt_iff_contDiffAt.mp hfiber
  exact (hcoord.differentiableAt (by norm_num)).congr_of_eventuallyEq heq.symm

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem differentiableAt_chartRepAt_of_contMDiff_two
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 2
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ s) (V s) : TangentBundle I M)))
    (t : ℝ) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t :=
  differentiableAt_chartRepAt_of_contMDiffAt_two (I := I) (hV.contMDiffAt (x := t))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma symmL_chartRepAt_self (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        (chartRepAt (I := I) γ V t t) = V t := by
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  exact (trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt
    (R := ℝ) hmem (V t)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionAlongCurve_continuousWithinAt_totalSpace
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} {x₀ : ℝ}
    (hx₀ : x₀ ∈ s)
    (hγ : ContinuousWithinAt γ s x₀)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V x₀) x₀) :
    ContinuousWithinAt
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s x₀ := by
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hγ, ?_⟩
  have hbase₀ : γ x₀ ∈ (trivializationAt E (TangentSpace I) (γ x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ x₀)
  have hopen : IsOpen (trivializationAt E (TangentSpace I) (γ x₀)).baseSet :=
    (trivializationAt E (TangentSpace I) (γ x₀)).open_baseSet
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ x₀)).baseSet ∈ 𝓝[s] x₀ :=
    hγ.preimage_mem_nhdsWithin (hopen.mem_nhds hbase₀)
  have heq :
      (fun t => ((trivializationAt E (TangentSpace I) (γ x₀))
        (TotalSpace.mk' E (γ t) (V t))).2)
        =ᶠ[𝓝[s] x₀] chartRepAt (I := I) γ V x₀ := by
    filter_upwards [hpre] with t ht
    rw [chartRepAt_apply]
    rw [(trivializationAt E (TangentSpace I) (γ x₀)).continuousLinearMapAt_apply (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ x₀)).coe_linearMapAt_of_mem ht]
  have hcont : ContinuousWithinAt (chartRepAt (I := I) γ V x₀) s x₀ :=
    hV.continuousAt.continuousWithinAt
  exact hcont.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hx₀)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionAlongCurve_continuousOn_totalSpace
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ}
    (hγ : ContinuousOn γ s)
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    ContinuousOn
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s := by
  intro x₀ hx₀
  exact sectionAlongCurve_continuousWithinAt_totalSpace (I := I) γ V hx₀
    (hγ x₀ hx₀) (hV x₀ hx₀)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    ContinuousOn
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s :=
  sectionAlongCurve_continuousOn_totalSpace (I := I) γ V hγ.continuousOn hV

def covDerivAlong (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
    (chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covDerivAlong_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ V t =
      (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        (chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_chartCoord (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlong (I := I) g γ V t) =
      chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t := by
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  rw [covDerivAlong_def]
  exact (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_symmL
    (R := ℝ) hmem _

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_eq_zero_iff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ V t = 0 ↔
      chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t = 0 := by
  constructor
  · intro h
    have := covDerivAlong_chartCoord (I := I) g γ V t
    rw [h, map_zero] at this
    exact this.symm
  · intro h
    rw [covDerivAlong_def, h, map_zero]

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_zero (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    covDerivAlong (I := I) g γ (fun s => (0 : TangentSpace I (γ s))) t = 0 := by
  have hrep : chartRepAt (I := I) γ (fun s => (0 : TangentSpace I (γ s))) t = fun _ => (0 : E) := by
    funext s
    simp [chartRepAt]
  rw [covDerivAlong_def, hrep]
  rw [chartCovDerivAlong_def]
  rw [ChartChristoffel.contraction_zero_right]
  rw [deriv_const', add_zero]
  exact map_zero _

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartRepAt_add (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => V s + W s) t =
      fun s => chartRepAt (I := I) γ V t s + chartRepAt (I := I) γ W t s := by
  funext s
  simp [chartRepAt, map_add]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartRepAt_smul (γ : ℝ → M) (c : ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => c • V s) t =
      fun s => c • chartRepAt (I := I) γ V t s := by
  funext s
  simp [chartRepAt, map_smul]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartRepAt_smulFun (γ : ℝ → M) (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => f s • V s) t =
      fun s => f s • chartRepAt (I := I) γ V t s := by
  funext s
  simp [chartRepAt, map_smul]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_add (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t) :
    covDerivAlong (I := I) g γ (fun s => V s + W s) t =
      covDerivAlong (I := I) g γ V t + covDerivAlong (I := I) g γ W t := by
  rw [covDerivAlong_def, covDerivAlong_def, covDerivAlong_def]
  rw [← map_add]
  congr 1
  rw [chartRepAt_add]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [deriv_fun_add hV hW]
  rw [ChartChristoffel.contraction_add_right]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_smul (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (c : ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ (fun s => c • V s) t =
      c • covDerivAlong (I := I) g γ V t := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  rw [chartRepAt_smul]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [deriv_fun_const_smul_field]
  rw [ChartChristoffel.contraction_smul_right]
  rw [smul_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDeriv_comp_mul (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (c t : ℝ) :
    covDerivAlong (I := I) g (fun s => γ (c * s)) (fun s => V (c * s)) t =
      c • covDerivAlong (I := I) g γ V (c * t) := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  have hrep :
      chartRepAt (I := I) (fun s => γ (c * s)) (fun s => V (c * s)) t =
        fun s => chartRepAt (I := I) γ V (c * t) (c * s) := rfl
  have hcurve :
      chartCurve (I := I) (γ (c * t)) (fun s => γ (c * s)) =
        fun s => chartCurve (I := I) (γ (c * t)) γ (c * s) := rfl
  rw [hrep, chartCovDerivAlong_def, chartCovDerivAlong_def, hcurve,
    deriv_comp_mul_left, deriv_comp_mul_left,
    ChartChristoffel.contraction_smul_left, smul_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_smulFun (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    covDerivAlong (I := I) g γ (fun s => f s • V s) t =
      (deriv f t) • V t + f t • covDerivAlong (I := I) g γ V t := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← symmL_chartRepAt_self (I := I) γ V t]
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  rw [chartRepAt_smulFun]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  have hderivSmul :
      deriv (fun s => f s • chartRepAt (I := I) γ V t s) t =
        f t • deriv (chartRepAt (I := I) γ V t) t + deriv f t • chartRepAt (I := I) γ V t t :=
    (hf.hasDerivAt.smul hV.hasDerivAt).deriv
  rw [hderivSmul]
  rw [ChartChristoffel.contraction_smul_right]
  rw [smul_add]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_comp (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (φ : ℝ → ℝ) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (φ t))
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V (φ t)) (φ t))
    (hφ : DifferentiableAt ℝ φ t) :
    covDerivAlong (I := I) g (fun s => γ (φ s)) (fun s => V (φ s)) t =
      (deriv φ t) • covDerivAlong (I := I) g γ V (φ t) := by
  have hcurve : DifferentiableAt ℝ
      (chartCurve (I := I) (γ (φ t)) γ) (φ t) := by
    change DifferentiableAt ℝ (extChartAt I (γ (φ t)) ∘ γ) (φ t)
    exact mdifferentiableAt_iff_differentiableAt.mp
      (mdifferentiableAt_iff_target.mp hγ).2
  have hrep :
      chartRepAt (I := I) (fun s => γ (φ s)) (fun s => V (φ s)) t =
        chartRepAt (I := I) γ V (φ t) ∘ φ := rfl
  have hchart :
      chartCurve (I := I) ((fun s => γ (φ s)) t) (fun s => γ (φ s)) =
        chartCurve (I := I) (γ (φ t)) γ ∘ φ := rfl
  rw [covDerivAlong_def, covDerivAlong_def, ← map_smul]
  congr 1
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrep, hchart]
  rw [deriv.scomp t hV hφ, deriv.scomp t hcurve hφ]
  simp only [Function.comp_apply]
  rw [ChartChristoffel.contraction_smul_left, smul_add]

private def chartTime (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (t : ℝ) : Set ℝ :=
  γ ⁻¹' (extChartAt I (γ t)).source

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTime_isOpen {γ : ℝ → M} (hγ : Continuous γ) (t : ℝ) :
    IsOpen (chartTime I γ t) := by
  have hsrc : IsOpen (extChartAt I (γ t)).source := isOpen_extChartAt_source (I := I) (γ t)
  exact hγ.isOpen_preimage _ hsrc

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma mem_chartTime_self (γ : ℝ → M) (t : ℝ) : t ∈ chartTime I γ t := by
  rw [chartTime, mem_preimage, extChartAt_source]
  exact mem_chart_source H (γ t)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTime_eq_chartSource (γ : ℝ → M) (t : ℝ) :
    chartTime I γ t = γ ⁻¹' (chartAt H (γ t)).source := by
  rw [chartTime, extChartAt_source]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma contDiffOn_chartCurve {n : WithTop ℕ∞} [IsManifold I n M] {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (t : ℝ) :
    ContDiffOn ℝ n (chartCurve (I := I) (γ t) γ) (chartTime I γ t) := by
  have h_comp_mdiff :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n ((extChartAt I (γ t)) ∘ γ) (chartTime I γ t) := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) n (extChartAt I (γ t)) (chartAt H (γ t)).source :=
      contMDiffOn_extChartAt (I := I) (n := n) (x := γ t)
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (chartTime I γ t) := hγ.contMDiffOn
    have hmaps : MapsTo γ (chartTime I γ t) (chartAt H (γ t)).source := by
      intro s hs
      rw [chartTime, mem_preimage, extChartAt_source] at hs
      exact hs
    exact hφ.comp hγU hmaps
  have hfun : (chartCurve (I := I) (γ t) γ) = ((extChartAt I (γ t)) ∘ γ) := rfl
  rw [hfun]
  exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma contDiffAt_chartCurve {n : WithTop ℕ∞} [IsManifold I n M] {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (t : ℝ) :
    ContDiffAt ℝ n (chartCurve (I := I) (γ t) γ) t :=
  (contDiffOn_chartCurve (I := I) hγ t).contDiffAt
    ((chartTime_isOpen (I := I) hγ.continuous t).mem_nhds (mem_chartTime_self (I := I) γ t))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma velocity_chartRep_eqOn {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    EqOn (chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t)
      (deriv (chartCurve (I := I) (γ t) γ)) (chartTime I γ t) := by
  intro s hs
  have hs' : γ s ∈ (chartAt H (γ t)).source := by
    rw [chartTime, mem_preimage, extChartAt_source] at hs
    exact hs
  rw [chartRepAt_apply]
  rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M)
    (γ := γ) hγ (γ t) (t := s) hs']
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma velocity_chartRep_eventuallyEq {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t
      =ᶠ[𝓝 t] deriv (chartCurve (I := I) (γ t) γ) :=
  (velocity_chartRep_eqOn (I := I) hγ t).eventuallyEq_of_mem
    ((chartTime_isOpen (I := I) hγ.continuous t).mem_nhds (mem_chartTime_self (I := I) γ t))

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 ↔
      HasGeodesicEquationAt (I := I) g γ t := by
  classical
  set u : ℝ → E := chartCurve (I := I) (γ t) γ with hu_def
  set rep : ℝ → E :=
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t with hrep_def
  have hu_cdiff : ContDiffAt ℝ ∞ u t := contDiffAt_chartCurve (I := I) hγ t
  have hU_open : IsOpen (chartTime I γ t) := chartTime_isOpen (I := I) hγ.continuous t
  have ht_mem : t ∈ chartTime I γ t := mem_chartTime_self (I := I) γ t
  have hU_nhds : chartTime I γ t ∈ 𝓝 t := hU_open.mem_nhds ht_mem
  have hu_cdiffOn : ContDiffOn ℝ ∞ u (chartTime I γ t) :=
    contDiffOn_chartCurve (I := I) hγ t
  have hderiv_u_cdiffOn : ContDiffOn ℝ ∞ (deriv u) (chartTime I γ t) :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
  have hu_diffAt : DifferentiableAt ℝ u t := hu_cdiff.differentiableAt (by simp)
  have hu_hasDerivAt : HasDerivAt u (deriv u t) t := hu_diffAt.hasDerivAt
  have hu_diffOn : DifferentiableOn ℝ u (chartTime I γ t) :=
    hu_cdiffOn.differentiableOn (by simp)
  have hu_eventually_hasDerivAt :
      ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s := by
    filter_upwards [hU_nhds] with s hs
    exact ((hu_diffOn s hs).differentiableAt (hU_open.mem_nhds hs)).hasDerivAt
  have hderiv_u_diffAt : DifferentiableAt ℝ (deriv u) t :=
    (hderiv_u_cdiffOn.differentiableOn (by simp) t ht_mem).differentiableAt hU_nhds
  have hderiv_u_hasDerivAt : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hderiv_u_diffAt.hasDerivAt
  have hrep_eq : rep =ᶠ[𝓝 t] deriv u := velocity_chartRep_eventuallyEq (I := I) hγ t
  have hrep_t : rep t = deriv u t := hrep_eq.eq_of_nhds
  have hderiv_rep_t : deriv rep t = deriv (deriv u) t := hrep_eq.deriv_eq
  have hchart :
      chartCovDerivAlong (I := I) g (γ t) γ rep t =
        deriv (deriv u) t +
          chartChristoffelContraction (I := I) g (γ t) (deriv u t) (deriv u t)
            (extChartAt I (γ t) (γ t)) := by
    rw [chartCovDerivAlong_def]
    rw [hderiv_rep_t, hrep_t]
    rfl
  rw [covDerivAlong_eq_zero_iff (I := I) g γ
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t]
  change chartCovDerivAlong (I := I) g (γ t) γ rep t = 0 ↔ HasGeodesicEquationAt (I := I) g γ t
  rw [hchart]
  constructor
  · intro heq
    refine ⟨deriv u t, deriv (deriv u) t, ?_, ?_, ?_, ?_⟩
    · exact hu_hasDerivAt
    · exact hu_eventually_hasDerivAt
    · exact hderiv_u_hasDerivAt
    · exact heq
  · intro hgeo
    obtain ⟨v, a, hv, _hev, ha, hid⟩ := hgeo
    have hv_eq : v = deriv u t := by
      have : HasDerivAt u v t := hv
      exact this.deriv.symm ▸ rfl
    have ha_eq : a = deriv (deriv u) t := by
      have : HasDerivAt (deriv u) a t := ha
      exact this.deriv.symm ▸ rfl
    rw [← hv_eq, ← ha_eq]
    exact hid

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : HasGeodesicEquationAt (I := I) g γ t) :
    covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 := by
  classical
  set u : ℝ → E := chartCurve (I := I) (γ t) γ with hu_def
  set rep : ℝ → E :=
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t with hrep_def
  have hev_c2 : ∀ᶠ s in 𝓝 t, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγ2
  have hev_source : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source := by
    have : (chartAt H (γ t)).source ∈ 𝓝 (γ t) :=
      (chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t))
    exact hγ2.continuousAt.preimage_mem_nhds this
  obtain ⟨U, hU_sub, hU_open, ht_U⟩ := eventually_nhds_iff.mp (hev_c2.and hev_source)
  have hUsub_c2 : ∀ s ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ s := fun s hs => (hU_sub s hs).1
  have hUsub_source : ∀ s ∈ U, γ s ∈ (chartAt H (γ t)).source := fun s hs => (hU_sub s hs).2
  have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds ht_U
  have hu_cdiffOn : ContDiffOn ℝ 2 u U := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t)) ∘ γ) U := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) 2 (extChartAt I (γ t)) (chartAt H (γ t)).source :=
        contMDiffOn_extChartAt (I := I) (n := 2) (x := γ t)
      have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ U := fun s hs => (hUsub_c2 s hs).contMDiffWithinAt
      have hmaps : MapsTo γ U (chartAt H (γ t)).source := fun s hs => hUsub_source s hs
      exact hφ.comp hγU hmaps
    have hfun : u = ((extChartAt I (γ t)) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have hderiv_u_cdiffOn : ContDiffOn ℝ 1 (deriv u) U :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by norm_num)
  have hu_diffAt : DifferentiableAt ℝ u t :=
    (hu_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hu_hasDerivAt : HasDerivAt u (deriv u t) t := hu_diffAt.hasDerivAt
  have hu_diffOn : DifferentiableOn ℝ u U := hu_cdiffOn.differentiableOn (by norm_num)
  have hu_eventually_hasDerivAt : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s := by
    filter_upwards [hU_nhds] with s hs
    exact ((hu_diffOn s hs).differentiableAt (hU_open.mem_nhds hs)).hasDerivAt
  have hderiv_u_diffAt : DifferentiableAt ℝ (deriv u) t :=
    (hderiv_u_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hderiv_u_hasDerivAt : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hderiv_u_diffAt.hasDerivAt
  have hrep_eqOn : EqOn rep (deriv u) U := by
    intro s hs
    have hs_source : γ s ∈ (chartAt H (γ t)).source := hUsub_source s hs
    have hs_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
      (hUsub_c2 s hs).mdifferentiableAt (by decide)
    rw [hrep_def, chartRepAt_apply]
    rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) hs_mdiff (γ t) (t := s) hs_source]
    rfl
  have hrep_eq : rep =ᶠ[𝓝 t] deriv u := hrep_eqOn.eventuallyEq_of_mem hU_nhds
  have hrep_t : rep t = deriv u t := hrep_eq.eq_of_nhds
  have hderiv_rep_t : deriv rep t = deriv (deriv u) t := hrep_eq.deriv_eq
  have hchart :
      chartCovDerivAlong (I := I) g (γ t) γ rep t =
        deriv (deriv u) t +
          chartChristoffelContraction (I := I) g (γ t) (deriv u t) (deriv u t)
            (extChartAt I (γ t) (γ t)) := by
    rw [chartCovDerivAlong_def]
    rw [hderiv_rep_t, hrep_t]
    rfl
  rw [covDerivAlong_eq_zero_iff (I := I) g γ
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t]
  change chartCovDerivAlong (I := I) g (γ t) γ rep t = 0
  rw [hchart]
  obtain ⟨v, a, hv, _hev, ha, hid⟩ := hgeo
  have hv_eq : v = deriv u t := by
    have : HasDerivAt u v t := hv
    exact this.deriv.symm ▸ rfl
  have ha_eq : a = deriv (deriv u) t := by
    have : HasDerivAt (deriv u) a t := ha
    exact this.deriv.symm ▸ rfl
  rw [← hv_eq, ← ha_eq]
  exact hid

def chartRepAtBase (β : M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) : ℝ → E :=
  fun s => (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s) (V s)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRepAtBase_apply (β : M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (s : ℝ) :
    chartRepAtBase (I := I) β γ V s =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s) (V s) := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartRepAtBase_foot (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAtBase (I := I) (γ t) γ V = chartRepAt (I := I) γ V t := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private theorem trivCoord_comp_symmL_eq_transition [I.Boundaryless]
    (α β : M) {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
      chartTransitionAt (I := I) α β (extChartAt I α b) v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hβ,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hα]
  have hb_self : b ∈ (chartAt H b).source := mem_chart_source H b
  have hmem : b ∈ (tangentBundleCore I M).baseSet (achart H α)
      ∩ (tangentBundleCore I M).baseSet (achart H b)
      ∩ (tangentBundleCore I M).baseSet (achart H β) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hα
    · rw [tangentBundleCore_baseSet]; exact hb_self
    · rw [tangentBundleCore_baseSet]; exact hβ
  have hcomp := (tangentBundleCore I M).coordChange_comp
    (achart H α) (achart H b) (achart H β) b hmem v
  have hcc : ((tangentBundleCore I M).coordChange (achart H α) (achart H β) b) v =
      chartTransitionAt (I := I) α β (extChartAt I α b) v := by
    change tangentCoordChange I α β b v = _
    rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
    have hrange : (Set.range I : Set E) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I)
    rw [hrange, fderivWithin_univ]
  rw [← hcc]
  exact hcomp

omit [NeZero (Module.finrank ℝ E)] in
theorem covDeriv_chartAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
        (chartCovDerivAlong (I := I) g β γ (chartRepAtBase (I := I) β γ V) t) =
      covDerivAlong (I := I) g γ V t := by
  classical
  set α : M := γ t with hα_def
  have hα : γ t ∈ (chartAt H α).source := mem_chart_source H (γ t)
  set uα : ℝ → E := chartCurve (I := I) α γ with huα_def
  set x : E := extChartAt I α (γ t) with hx_def
  have hxut : uα t = x := by rw [huα_def, chartCurve_def, hx_def]
  set xβ : E := chartTransitionMap (I := I) α β x with hxβ_def
  have hsrc : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hα hβ
  have hxβ_eq : xβ = extChartAt I β (γ t) := by
    rw [hxβ_def, hx_def, chartTransitionMap_apply_extChartAt (I := I) α β hα]
  have hxβ_curve : xβ = chartCurve (I := I) β γ t := by rw [hxβ_eq, chartCurve_def]
  set repα : ℝ → E := chartRepAt (I := I) γ V t with hrepα_def
  set repβ : ℝ → E := chartRepAtBase (I := I) β γ V with hrepβ_def
  have huα_diff : DifferentiableAt ℝ uα t := by
    have hcomp := (mdifferentiableAt_extChartAt (I := I)
      (mem_chart_source H (γ t))).comp t hγ
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    change DifferentiableAt ℝ (fun s : ℝ => extChartAt I α (γ s)) t
    exact hcomp
  have huα_hd : HasDerivAt uα (deriv uα t) t :=
    huα_diff.hasDerivAt
  have hrepα_hd : HasDerivAt repα (deriv repα t) t := hV.hasDerivAt
  set U : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) with hU_def
  have htU : t ∈ U := ⟨hα, hβ⟩
  have hU_nhds : U ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H β).open_source).mem_nhds htU)
  have hrepβ_eq : repβ =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) α β (uα s) (repα s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsα, hsβ⟩ := hs
    have hbridge :
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s)
            ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s))) =
          chartTransitionAt (I := I) α β (extChartAt I α (γ s))
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s)) :=
      trivCoord_comp_symmL_eq_transition (I := I) α β hsα hsβ _
    have hround :
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s)) =
          V s := by
      have hmem : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hsα
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hmem (V s)
    rw [hround] at hbridge
    rw [hrepβ_def, chartRepAtBase_apply]
    rw [hrepα_def, chartRepAt_apply]
    rw [huα_def, chartCurve_def]
    exact hbridge
  have hrepβ_t : repβ t = chartTransitionAt (I := I) α β x (repα t) := by
    have := hrepβ_eq.eq_of_nhds
    rw [this, hxut]
  have huβ_eq : chartCurve (I := I) β γ =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α β (uα s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsα, _⟩ := hs
    rw [chartCurve_def, huα_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α β hsα).symm
  have hTdiff : DifferentiableAt ℝ (chartTransitionMap (I := I) α β) x :=
    chartTransitionMap_differentiableAt (I := I) α β hsrc
  have huβ_hd : HasDerivAt (chartCurve (I := I) β γ)
      (chartTransitionAt (I := I) α β x (deriv uα t)) t := by
    have hcomp : HasDerivAt
        (fun s => chartTransitionMap (I := I) α β (uα s))
        (chartTransitionAt (I := I) α β x (deriv uα t)) t := by
      have hc : HasDerivAt (chartTransitionMap (I := I) α β ∘ uα)
          ((fderiv ℝ (chartTransitionMap (I := I) α β) (uα t)) (deriv uα t)) t :=
        hTdiff.hasFDerivAt.comp_hasDerivAt t huα_hd
      rw [chartTransitionAt_def]
      exact hc
    exact hcomp.congr_of_eventuallyEq huβ_eq
  have hderiv_uβ : deriv (chartCurve (I := I) β γ) t =
      chartTransitionAt (I := I) α β x (deriv uα t) := huβ_hd.deriv
  have hAdiff : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E)) x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
      chartTransitionSource_isOpen (I := I) α β
    exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
      (h_open.mem_nhds hsrc)).differentiableAt (by simp)
  have hcA : HasDerivAt
      (fun s => (chartTransitionAt (I := I) α β (uα s) : E →L[ℝ] E))
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) t :=
    hAdiff.hasFDerivAt.comp_hasDerivAt t huα_hd
  have hrepβ_hd : HasDerivAt repβ
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
        + chartTransitionAt (I := I) α β x (deriv repα t)) t := by
    have hbase : HasDerivAt (fun s => chartTransitionAt (I := I) α β (uα s) (repα s))
        (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
          + chartTransitionAt (I := I) α β x (deriv repα t)) t :=
      hcA.clm_apply hrepα_hd
    exact hbase.congr_of_eventuallyEq hrepβ_eq
  have hderiv_repβ : deriv repβ t =
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
        + chartTransitionAt (I := I) α β x (deriv repα t) := hrepβ_hd.deriv
  have hmemα : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hα
  rw [covDerivAlong_def]
  rw [← (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
    (R := ℝ) hmemα
    ((trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
      (chartCovDerivAlong (I := I) g β γ repβ t))]
  congr 1
  have hAcoord :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t)
          ((trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
            (chartCovDerivAlong (I := I) g β γ repβ t)) =
        chartTransitionAt (I := I) β α xβ
          (chartCovDerivAlong (I := I) g β γ repβ t) := by
    rw [trivCoord_comp_symmL_eq_transition (I := I) β α hβ hα
      (chartCovDerivAlong (I := I) g β γ repβ t)]
    rw [hxβ_eq]
  rw [hAcoord]
  set A : E →L[ℝ] E := chartTransitionAt (I := I) β α xβ with hA_def
  rw [chartCovDerivAlong_def]
  rw [map_add]
  have huβ_t : chartCurve (I := I) β γ t = xβ := hxβ_curve.symm
  rw [hderiv_repβ, hderiv_uβ, hrepβ_t, huβ_t]
  have hinv : (A.comp (chartTransitionAt (I := I) α β x)) = ContinuousLinearMap.id ℝ E := by
    rw [hA_def, hxβ_def]
    exact chartTransitionAt_comp_chartTransitionAt (I := I) α β hsrc
  have hcollapse : ∀ z : E, A (chartTransitionAt (I := I) α β x z) = z := by
    intro z
    have := congrArg (fun L : E →L[ℝ] E => L z) hinv
    simpa [ContinuousLinearMap.comp_apply] using this
  have hfoot :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t) =
        chartTransitionAt (I := I) α β x
          (chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x) :=
    fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α β hsrc (deriv uα t) (repα t)
  rw [map_add, hfoot, hcollapse, hcollapse]
  have htransform :
      chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x =
        chartTransitionAt (I := I) β α xβ
            (chartChristoffelContraction (I := I) g β
              (chartTransitionAt (I := I) α β x (deriv uα t))
              (chartTransitionAt (I := I) α β x (repα t)) xβ)
          + chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x := by
    have hxx : x = extChartAt I α (γ t) := hx_def
    rw [hxx]
    have h := chartChristoffelContraction_transform (I := I) g α β hα hβ
      (deriv uα t) (repα t)
    rw [← hxx, ← hxβ_def] at h
    exact h
  rw [show chartTransitionAt (I := I) β α xβ
        (chartChristoffelContraction (I := I) g β
          (chartTransitionAt (I := I) α β x (deriv uα t))
          (chartTransitionAt (I := I) α β x (repα t)) xβ)
      = chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x
          - chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x by
    rw [htransform]; abel]
  have hRHS : chartCovDerivAlong (I := I) g α γ repα t =
      deriv repα t + chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x := by
    rw [chartCovDerivAlong_def, ← huα_def, hxut]
  rw [hRHS]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_chart_foot_invariance [I.Boundaryless]
    {n : WithTop ℕ∞} (hn : n ≠ 0)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
        (chartCovDerivAlong (I := I) g β γ (chartRepAtBase (I := I) β γ V) t) =
      covDerivAlong (I := I) g γ V t :=
  covDeriv_chartAt (I := I) g γ V t β
    (hγ.contMDiffAt.mdifferentiableAt hn) hβ hV

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
theorem chartRep_base_diff [I.Boundaryless]
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    DifferentiableAt ℝ (chartRepAtBase (I := I) β γ V) t := by
  classical
  let α : M := γ t
  let uα : ℝ → E := chartCurve (I := I) α γ
  let x : E := extChartAt I α (γ t)
  let repα : ℝ → E := chartRepAt (I := I) γ V t
  let repβ : ℝ → E := chartRepAtBase (I := I) β γ V
  have hα : γ t ∈ (chartAt H α).source := mem_chart_source H (γ t)
  have hsrc : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hα hβ
  have huα_diff : DifferentiableAt ℝ uα t := by
    change DifferentiableAt ℝ (extChartAt I (γ t) ∘ γ) t
    exact mdifferentiableAt_iff_differentiableAt.mp
      (mdifferentiableAt_iff_target.mp hγ).2
  have hU_nhds :
      γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H β).open_source).mem_nhds
        ⟨hα, hβ⟩)
  have hrepβ_eq : repβ =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) α β (uα s) (repα s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsα, hsβ⟩ := hs
    have hbridge :=
      trivCoord_comp_symmL_eq_transition (I := I) α β hsα hsβ
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
          (γ s) (V s))
    have hround :
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
              (γ s) (V s)) = V s := by
      have hmem : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hsα
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hmem (V s)
    rw [hround] at hbridge
    simpa only [repα, repβ, chartRepAt_apply, chartRepAtBase_apply,
      uα, chartCurve] using hbridge
  have hAdiff : DifferentiableAt ℝ
      (fun y => (chartTransitionAt (I := I) α β y : E →L[ℝ] E)) x := by
    exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
      ((chartTransitionSource_isOpen (I := I) α β).mem_nhds hsrc)).differentiableAt
        (by simp)
  have huαt : uα t = x := by
    rfl
  have hAcomp : DifferentiableAt ℝ
      (fun s => (chartTransitionAt (I := I) α β (uα s) : E →L[ℝ] E)) t := by
    apply hAdiff.comp t
    simpa only [huαt] using huα_diff
  have hrepα : DifferentiableAt ℝ repα t := by
    simpa only [repα] using hV
  exact (hAcomp.clm_apply hrepα).congr_of_eventuallyEq hrepβ_eq

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
theorem chartRepAtBase_differentiableAt [I.Boundaryless]
    {n : WithTop ℕ∞} (hn : n ≠ 0)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    DifferentiableAt ℝ (chartRepAtBase (I := I) β γ V) t :=
  chartRep_base_diff (I := I) γ V t β
    (hγ.contMDiffAt.mdifferentiableAt hn) hβ hV

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
theorem chartRep_diff_base [I.Boundaryless]
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAtBase (I := I) β γ V) t) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  classical
  let α : M := γ t
  let uβ : ℝ → E := chartCurve (I := I) β γ
  let xβ : E := extChartAt I β (γ t)
  let repα : ℝ → E := chartRepAt (I := I) γ V t
  let repβ : ℝ → E := chartRepAtBase (I := I) β γ V
  have hα : γ t ∈ (chartAt H α).source := mem_chart_source H (γ t)
  have hsrc : xβ ∈ chartTransitionSource (I := I) β α :=
    extChartAt_mem_chartTransitionSource (I := I) β α hβ hα
  have huβ_diff : DifferentiableAt ℝ uβ t := by
    have hcomp := (mdifferentiableAt_extChartAt (I := I) hβ).comp t hγ
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    change DifferentiableAt ℝ (fun s : ℝ => extChartAt I β (γ s)) t
    exact hcomp
  have hU_nhds :
      γ ⁻¹' ((chartAt H β).source ∩ (chartAt H α).source) ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds
      (((chartAt H β).open_source.inter (chartAt H α).open_source).mem_nhds
        ⟨hβ, hα⟩)
  have hrepα_eq : repα =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) β α (uβ s) (repβ s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsβ, hsα⟩ := hs
    have hbridge :=
      trivCoord_comp_symmL_eq_transition (I := I) β α hsβ hsα
        ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ
          (γ s) (V s))
    have hround :
        (trivializationAt E (TangentSpace I) β).symmL ℝ (γ s)
            ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ
              (γ s) (V s)) = V s := by
      have hmem : γ s ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hsβ
      exact (trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
        (R := ℝ) hmem (V s)
    rw [hround] at hbridge
    simpa only [repα, repβ, chartRepAt_apply, chartRepAtBase_apply,
      uβ, chartCurve] using hbridge
  have hAdiff : DifferentiableAt ℝ
      (fun y => (chartTransitionAt (I := I) β α y : E →L[ℝ] E)) xβ := by
    exact ((chartTransitionAt_smooth (I := I) β α).contDiffAt
      ((chartTransitionSource_isOpen (I := I) β α).mem_nhds hsrc)).differentiableAt
        (by simp)
  have huβt : uβ t = xβ := by
    rfl
  have hAcomp : DifferentiableAt ℝ
      (fun s => (chartTransitionAt (I := I) β α (uβ s) : E →L[ℝ] E)) t := by
    apply hAdiff.comp t
    simpa only [huβt] using huβ_diff
  have hrepβ : DifferentiableAt ℝ repβ t := by
    simpa only [repβ] using hV
  exact (hAcomp.clm_apply hrepβ).congr_of_eventuallyEq hrepα_eq

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartRep_diff
    (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ s) (V s) : TangentBundle I M)))
    (t : ℝ) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  let S : ℝ → TangentBundle I M := fun s =>
    TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s)
  have hAt : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ S t := by
    simpa only [S] using hV.contMDiffAt
  rw [Bundle.contMDiffAt_totalSpace] at hAt
  have hbase := hAt.1
  have hfiber := hAt.2
  have hmem :
      γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hpre :
      γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t)).baseSet ∈ 𝓝 t :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hmem)
  have heq :
      (fun s : ℝ => ((trivializationAt E (TangentSpace I) (γ t)) (S s)).2)
        =ᶠ[𝓝 t]
      fun s : ℝ =>
        (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt
          ℝ (γ s) (V s) := by
    filter_upwards [hpre] with s hs
    simp only [S, TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply
      (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hs]
  have hfiber' := hfiber.congr_of_eventuallyEq heq.symm
  have hfiberDiff : ContDiffAt ℝ ∞
      (fun s : ℝ =>
        (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt
          ℝ (γ s) (V s)) t := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact hfiber'
  let hdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t :=
    hfiberDiff.differentiableAt (by simp)
  exact hdiff

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartRepAt_sum {ι : Type*} (s : Finset ι) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun u => ∑ i ∈ s, V i u) t =
      fun u => ∑ i ∈ s, chartRepAt (I := I) γ (V i) t u := by
  funext u
  simp [chartRepAt, map_sum]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_sum {ι : Type*} (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (s : Finset ι) (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hV : ∀ i ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t) :
    covDerivAlong (I := I) g γ (fun u => ∑ i ∈ s, V i u) t =
      ∑ i ∈ s, covDerivAlong (I := I) g γ (V i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun u => ∑ i ∈ (∅ : Finset ι), V i u)
          = fun u => (0 : TangentSpace I (γ u)) := by
        funext u; simp
      rw [h0, covDerivAlong_zero, Finset.sum_empty]
  | insert i s hi ih =>
      have hVi := hV i (Finset.mem_insert_self i s)
      have hVtail : ∀ j ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ (V j) t) t :=
        fun j hj => hV j (Finset.mem_insert_of_mem hj)
      have hVs : DifferentiableAt ℝ
          (chartRepAt (I := I) γ (fun u => ∑ j ∈ s, V j u) t) t := by
        rw [chartRepAt_sum]
        exact DifferentiableAt.fun_sum hVtail
      have hsplit : (fun u => ∑ j ∈ insert i s, V j u)
          = fun u => V i u + ∑ j ∈ s, V j u := by
        funext u; rw [Finset.sum_insert hi]
      rw [hsplit, covDerivAlong_add g γ _ _ t hVi hVs, ih hVtail,
        Finset.sum_insert hi]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_expand {ι : Type*} (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (s : Finset ι) (y : ι → ℝ → ℝ) (F : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hy : ∀ i ∈ s, DifferentiableAt ℝ (y i) t)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hpar : ∀ i ∈ s, covDerivAlong (I := I) g γ (F i) t = 0) :
    covDerivAlong (I := I) g γ (fun u => ∑ i ∈ s, y i u • F i u) t =
      ∑ i ∈ s, deriv (y i) t • F i t := by
  rw [covDerivAlong_sum g γ s (fun i u => y i u • F i u) t (fun i hi => by
    rw [chartRepAt_smulFun]
    exact (hy i hi).smul (hF i hi))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [covDerivAlong_smulFun g γ (y i) (F i) t (hy i hi) (hF i hi), hpar i hi,
    smul_zero, add_zero]

end CovariantDerivativeAlong

open CovariantDerivativeAlong

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartRep_congr_curve
    {γ γ' : ℝ → M}
    (V : ∀ s : ℝ, TangentSpace I (γ s))
    (V' : ∀ s : ℝ, TangentSpace I (γ' s)) {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hV : ∀ᶠ s in 𝓝 t, (V s : E) = (V' s : E)) :
    chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ' V' t := by
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hkey : ∀ (x y : M), x = y →
      ∀ (v : TangentSpace I x) (v' : TangentSpace I y),
        (v : E) = (v' : E) →
        (trivializationAt E (TangentSpace I) (γ' t)).continuousLinearMapAt ℝ x v =
          (trivializationAt E (TangentSpace I) (γ' t)).continuousLinearMapAt ℝ y v' := by
    intro x y hxy
    subst hxy
    intro v v' hvv'
    have hvv : v = v' := hvv'
    rw [hvv]
  filter_upwards [hγ, hV] with s hsγ hsV
  rw [chartRepAt_apply, chartRepAt_apply, hfoot]
  exact hkey _ _ hsγ _ _ hsV

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_congr_curve
    (g : SmoothRiemannianMetric I M) {γ γ' : ℝ → M}
    (V : ∀ s : ℝ, TangentSpace I (γ s))
    (V' : ∀ s : ℝ, TangentSpace I (γ' s)) {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hV : ∀ᶠ s in 𝓝 t, (V s : E) = (V' s : E)) :
    (covDerivAlong (I := I) g γ V t : E) =
      (covDerivAlong (I := I) g γ' V' t : E) := by
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hcurve : chartCurve (I := I) (γ' t) γ =ᶠ[𝓝 t]
      chartCurve (I := I) (γ' t) γ' := by
    filter_upwards [hγ] with s hs
    simp only [chartCurve_def]
    rw [hs]
  have hrep : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      chartRepAt (I := I) γ' V' t :=
    chartRep_congr_curve (I := I) V V' hγ hV
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [show (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t) =
        (trivializationAt E (TangentSpace I) (γ' t)).symmL ℝ (γ' t) from by
      rw [hfoot]]
  rw [show γ t = γ' t from hfoot]
  congr 1
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_const
    (g : SmoothRiemannianMetric I M) (p : M)
    (V : ℝ → TangentSpace I p) (t : ℝ)
    (hV : DifferentiableAt ℝ (fun s ↦ (V s : E)) t) :
    (covDerivAlong (I := I) g (fun _ : ℝ ↦ p) V t : E) =
      deriv (fun s ↦ (V s : E)) t := by
  classical
  let L : TangentSpace I p →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
  have hrep : chartRepAt (I := I) (fun _ : ℝ ↦ p) V t =
      fun s : ℝ ↦ L (V s) := by
    funext s
    rw [chartRepAt_apply]
  have hcurve_deriv : deriv (chartCurve (I := I) p (fun _ : ℝ ↦ p)) t = 0 := by
    have hc : chartCurve (I := I) p (fun _ : ℝ ↦ p) =
        fun _ : ℝ ↦ extChartAt I p p := by
      funext s
      rw [chartCurve_def]
    rw [hc]
    exact deriv_const t _
  have hsecderiv : HasDerivAt (fun s : ℝ ↦ L (V s))
      (L (deriv (fun s ↦ (V s : E)) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hV.hasDerivAt
  have hmem : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p
  rw [covDerivAlong_def, chartCovDerivAlong_def, hrep, hcurve_deriv,
    chartChristoffelContraction_zero_left, add_zero, hsecderiv.deriv]
  exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
    (R := ℝ) hmem (deriv (fun s ↦ (V s : E)) t)

end Riemannian
end Geometry
end DifferentialGeometry

end
