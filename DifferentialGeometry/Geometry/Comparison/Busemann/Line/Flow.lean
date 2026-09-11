import DifferentialGeometry.Analysis.ODE.Flow.Complete
import DifferentialGeometry.Geometry.Comparison.Busemann.Line.Parallel
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.ParallelField
import DifferentialGeometry.Geometry.Metric.ParallelFlow
import DifferentialGeometry.Geometry.Geodesic.Minimizing.Line.Speed

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold Topology

namespace DifferentialGeometry

open Analysis.ODE
open Geometry.Connection
open Geometry.Operator
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers (RicciBoundedBelow)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private def smoothGradient
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
  ⟨fun x : M ↦ gradFun (I := I) g b x,
    gradFun_contMDiff_total_section (I := I) g hb⟩

private theorem exists_isMIntegralCurve_gradFun_busemann
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ∀ x : M, ∃ c : ℝ → M, c 0 = x ∧
      IsMIntegralCurve c
        (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  let X : ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := smoothGradient (I := I) g hb
  have hX : ∀ y : M,
      (LeviCivita (I := I) g).toFun (fun z : M ↦ X z) y = 0 := by
    intro y
    simpa only [X, smoothGradient, ContMDiffSection.coeFn_mk, b] using
      hγ.covariantDerivative_gradFun_busemann_eq_zero (I := I) hEnorm hd hRic y
  intro x
  refine ⟨Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm x (X x), ?_, ?_⟩
  · exact Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
      (I := I) g hEnorm x (X x)
  · simpa only [X, smoothGradient, ContMDiffSection.coeFn_mk, b] using
      Geometry.Riemannian.Exponential.isMIntegralCurve_intrinsicGeodesic_of_parallel
        (I := I) g hEnorm X hX x

noncomputable def busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) (x : M) : M :=
  curveAt
    (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
    (exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic) x t

@[simp] theorem busemannFlow_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    busemannFlow (I := I) g hEnorm hγ hd hRic 0 x = x := by
  simpa only [busemannFlow] using
    curveAt_zero
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      (exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic) x

theorem isMIntegralCurve_busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    IsMIntegralCurve
      (fun t : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t x)
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) := by
  simpa only [busemannFlow] using
    curveAt_integralCurve
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      (exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic) x

theorem busemannFlow_add
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (x : M) (s t : ℝ) :
    busemannFlow (I := I) g hEnorm hγ hd hRic (s + t) x =
      busemannFlow (I := I) g hEnorm hγ hd hRic t
        (busemannFlow (I := I) g hEnorm hγ hd hRic s x) := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  have hb := hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun y : M ↦
        (⟨y, gradFun (I := I) g (busemann (I := I) γ) y⟩ :
          TangentBundle I M)) :=
    (gradFun_contMDiff_total_section (I := I) g hb).of_le (by simp)
  simpa only [busemannFlow] using
    curveAt_add
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      hv (exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic) x s t

theorem contMDiff_busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦
        busemannFlow (I := I) g hEnorm hγ hd hRic p.1 p.2) := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  have hb := hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M ↦
        (⟨y, gradFun (I := I) g (busemann (I := I) γ) y⟩ :
          TangentBundle I M)) :=
    gradFun_contMDiff_total_section (I := I) g hb
  simpa only [busemannFlow] using
    contMDiff_curveAt
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      hv (exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic)

theorem inner_mfderiv_busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (x : M) (v w : TangentSpace I x) (t : ℝ) :
    g.inner (busemannFlow (I := I) g hEnorm hγ hd hRic t x)
        (mfderiv I I
          (fun y ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t y) x v)
        (mfderiv I I
          (fun y ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t y) x w) =
      g.inner x v w := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  classical
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  let X : ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := smoothGradient (I := I) g hb
  have hcomplete : ∀ y : M, ∃ c : ℝ → M, c 0 = y ∧
      IsMIntegralCurve c (fun z : M ↦ X z) := by
    simpa only [X, smoothGradient, ContMDiffSection.coeFn_mk, b] using
      exists_isMIntegralCurve_gradFun_busemann (I := I) g hEnorm hγ hd hRic
  have hpar : ∀ y : M,
      (LeviCivita (I := I) g).toFun (fun z : M ↦ X z) y = 0 := by
    intro y
    simpa only [X, smoothGradient, ContMDiffSection.coeFn_mk, b] using
      hγ.covariantDerivative_gradFun_busemann_eq_zero (I := I) hEnorm hd hRic y
  simpa only [busemannFlow, X, smoothGradient, ContMDiffSection.coeFn_mk, b] using!
    inner_mfderiv_curveAt_eq_of_parallel (I := I) g X hcomplete hpar x v w t

theorem busemann_busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) (x : M) :
    busemann (I := I) γ
        (busemannFlow (I := I) g hEnorm hγ hd hRic t x) =
      busemann (I := I) γ x + t := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  have hunit (y : M) :
      g.inner y (gradFun (I := I) g b y) (gradFun (I := I) g b y) = 1 := by
    simpa only [b, normGradSqFun, gradient_eq_gradFun] using
      normGradSqFun_busemann_eq_one (I := I) g hEnorm hγ.positive_ray y
        (hb.contMDiffAt.mdifferentiableAt (by simp))
  have hdf : ∀ y : M,
      (NormedSpace.fromTangentSpace ((-b) y))
        ((mfderiv I 𝓘(ℝ, ℝ) (-b) y) (gradFun (I := I) g b y)) = -1 := by
    intro y
    rw [mfderiv_neg]
    change -((mfderiv I 𝓘(ℝ, ℝ) b y)
      (gradFun (I := I) g b y)) = -1
    rw [← inner_gradFun (I := I) g b y]
    exact congrArg (fun z : ℝ ↦ -z) (hunit y)
  have hcurve : IsMIntegralCurve
      (fun s : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic s x)
      (fun y : M ↦ gradFun (I := I) g b y) := by
    simpa only [b] using
      isMIntegralCurve_busemannFlow (I := I) g hEnorm hγ hd hRic x
  have htranslate := f_eq_sub_of_integralCurve (I := I)
    (-b) hb.neg (fun y : M ↦ gradFun (I := I) g b y) hdf hcurve t
  rw [busemannFlow_zero (I := I) g hEnorm hγ hd hRic x] at htranslate
  change -b (busemannFlow (I := I) g hEnorm hγ hd hRic t x) =
    -b x - t at htranslate
  change b (busemannFlow (I := I) g hEnorm hγ hd hRic t x) = b x + t
  linarith

theorem busemannFlow_neg_apply_line
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) :
    busemannFlow (I := I) g hEnorm hγ hd hRic (-t) (γ 0) = γ t := by
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  let X : (y : M) → TangentSpace I y := fun y ↦
    gradFun (I := I) g b y
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ := hγ.contMDiff
  have hbline (s : ℝ) : b (γ s) = -s := hγ.busemann_apply_line s
  have hgrad_unit (s : ℝ) :
      g.inner (γ s) (X (γ s)) (X (γ s)) = 1 := by
    simpa only [X, b, normGradSqFun, gradient_eq_gradFun] using
      normGradSqFun_busemann_eq_one (I := I) g hEnorm hγ.positive_ray (γ s)
        (hb.contMDiffAt.mdifferentiableAt (by simp))
  have hline_vel (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) = -X (γ s) := by
    let q : ℝ :=
      NormedSpace.fromTangentSpace (b (γ s))
        (mfderiv I 𝓘(ℝ, ℝ) b (γ s)
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)))
    have hcomp : HasDerivAt (fun r : ℝ ↦ b (γ r)) q s := by
      simpa only [q, Analysis.Calculus.realTangentOne] using!
        Analysis.Calculus.hasDerivAt_comp_mfderiv_along
          I b γ s (hb.contMDiffAt.mdifferentiableAt (by simp))
            (hγ_smooth.contMDiffAt.mdifferentiableAt (by simp))
    have hlinear : HasDerivAt (fun r : ℝ ↦ -r) (-1) s := by
      simpa only [Pi.neg_apply, id_eq] using! (hasDerivAt_id (x := s)).neg
    have hfun : (fun r : ℝ ↦ b (γ r)) = fun r : ℝ ↦ -r :=
      funext hbline
    rw [hfun] at hcomp
    have hq : q = -1 := hcomp.unique hlinear
    have hq_inner : q =
        g.inner (γ s) (X (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) := by
      dsimp only [q]
      change mfderiv I 𝓘(ℝ, ℝ) b (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = _
      exact (Geometry.Connection.gradFun_metricDual (I := I) g b (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))).symm
    have hgrad_vel :
        g.inner (γ s) (X (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = -1 := by
      rw [← hq_inner]
      exact hq
    have hvel_grad :
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (X (γ s)) = -1 :=
      (g.symm (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (X (γ s))).trans
        hgrad_vel
    have hvel_unit :
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = 1 :=
      hγ.inner_mfderiv_self_eq_one hEnorm s
    have hsum_inner :
        g.inner (γ s)
            (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) + X (γ s))
            (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) + X (γ s)) = 0 := by
      rw [(g.inner (γ s)).map_add, add_apply,
        (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))).map_add,
        (g.inner (γ s) (X (γ s))).map_add,
        hvel_unit, hvel_grad, hgrad_vel, hgrad_unit]
      norm_num
    have hsum : mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) + X (γ s) = 0 := by
      by_contra hne
      have hpos := g.pos (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) + X (γ s)) hne
      rw [hsum_inner] at hpos
      exact (lt_irrefl 0 hpos)
    exact eq_neg_of_add_eq_zero_left hsum
  have hγ_curve : IsMIntegralCurve γ (fun y : M ↦ -X y) := by
    intro s
    have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ s
        (mfderiv 𝓘(ℝ, ℝ) I γ s) :=
      (hγ_smooth.mdifferentiableAt (by simp)).hasMFDerivAt
    have hmfderiv : mfderiv 𝓘(ℝ, ℝ) I γ s =
        (1 : ℝ →L[ℝ] ℝ).smulRight (-X (γ s)) := by
      apply ContinuousLinearMap.ext
      intro (r : ℝ)
      calc
        mfderiv 𝓘(ℝ, ℝ) I γ s r =
            r • mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) := by
          have hmap : mfderiv 𝓘(ℝ, ℝ) I γ s (r * (1 : ℝ)) =
              r • mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) :=
            (mfderiv 𝓘(ℝ, ℝ) I γ s).map_smul r (1 : ℝ)
          simpa only [mul_one] using! hmap
        _ = r • (-X (γ s)) := by rw [hline_vel s]
        _ = ((1 : ℝ →L[ℝ] ℝ).smulRight (-X (γ s))) r := by simp
    exact hγ_at.congr_mfderiv hmfderiv
  have hrev : IsMIntegralCurve (fun s : ℝ ↦ γ (-s)) X := by
    have hc := IsMIntegralCurve.comp_mul hγ_curve (-1)
    have hcurve : (γ ∘ fun s : ℝ ↦ s * (-1)) = fun s : ℝ ↦ γ (-s) := by
      funext s
      simp
    have hfield : ((-1 : ℝ) • fun y : M ↦ -X y) = X := by
      funext y
      simp
    rw [hcurve, hfield] at hc
    exact hc
  have hflow : IsMIntegralCurve
      (fun s : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic s (γ 0)) X := by
    simpa only [X, b] using
      isMIntegralCurve_busemannFlow (I := I) g hEnorm hγ hd hRic (γ 0)
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun y : M ↦ (⟨y, X y⟩ : TangentBundle I M)) := by
    simpa only [X] using
      (gradFun_contMDiff_total_section (I := I) g hb).of_le (by simp)
  have heq := integralCurve_eq_of_agree_zero X hX hflow hrev (by
    rw [busemannFlow_zero (I := I) g hEnorm hγ hd hRic]
    simp)
  have ht := congrFun heq (-t)
  simpa only [neg_neg] using ht

end

end DifferentialGeometry
