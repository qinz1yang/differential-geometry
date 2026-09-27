import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryShift
import DifferentialGeometry.Geometry.Comparison.Nonnegative.FocalRiccati
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.IndexForm
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Metric Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



private theorem sq_le_mul_of_quadratic_nonneg {a b c : ℝ}
    (h : ∀ s : ℝ, 0 ≤ a + 2 * s * b + s ^ 2 * c) : b ^ 2 ≤ a * c := by
  have hq : ∀ s : ℝ, 0 ≤ c * (s * s) + 2 * b * s + a := by
    intro s
    have hs := h s
    nlinarith [hs]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]
    simp
  · exact (g.pos x v hv).le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_add_left (g : SmoothRiemannianMetric I M) (x : M)
    (a b w : TangentSpace I x) :
    g.inner x (a + b) w = g.inner x a w + g.inner x b w := by
  rw [ContinuousLinearMap.map_add (g.inner x) a b]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_smul_left (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (a w : TangentSpace I x) :
    g.inner x (c • a) w = c * g.inner x a w := by
  rw [ContinuousLinearMap.map_smul (g.inner x) c a]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_add_right (g : SmoothRiemannianMetric I M) (x : M)
    (v a b : TangentSpace I x) :
    g.inner x v (a + b) = g.inner x v a + g.inner x v b :=
  ContinuousLinearMap.map_add (g.inner x v) a b

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_smul_right (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (v a : TangentSpace I x) :
    g.inner x v (c • a) = c * g.inner x v a := by
  rw [ContinuousLinearMap.map_smul (g.inner x v) c a]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_neg_left (g : SmoothRiemannianMetric I M) (x : M)
    (a w : TangentSpace I x) :
    g.inner x (-a) w = -g.inner x a w := by
  rw [ContinuousLinearMap.map_neg (g.inner x) a]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_neg_right (g : SmoothRiemannianMetric I M) (x : M)
    (v a : TangentSpace I x) :
    g.inner x v (-a) = -g.inner x v a :=
  ContinuousLinearMap.map_neg (g.inner x v) a

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_add_smul_expand (g : SmoothRiemannianMetric I M) (x : M)
    (a b p q : TangentSpace I x) (s : ℝ) :
    g.inner x (a + s • b) (p + s • q)
      = g.inner x a p + s * (g.inner x a q + g.inner x b p)
        + s ^ 2 * g.inner x b q := by
  rw [inner_add_left (I := I) g x a (s • b) (p + s • q),
    inner_smul_left (I := I) g x s b (p + s • q),
    inner_add_right (I := I) g x a p (s • q),
    inner_add_right (I := I) g x b p (s • q),
    inner_smul_right (I := I) g x s a q,
    inner_smul_right (I := I) g x s b q]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem two_inner_le_of_pos (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) {c : ℝ} (hc : 0 < c) :
    2 * g.inner x v w ≤ c * g.inner x v v + g.inner x w w / c := by
  have hexp := inner_add_smul_expand (I := I) g x v w v w (-(1 / c))
  have hnn : 0 ≤ g.inner x (v + (-(1 / c)) • w) (v + (-(1 / c)) • w) :=
    inner_self_nonneg (I := I) g x _
  rw [hexp, g.symm x w v] at hnn
  have hcne : c ≠ 0 := ne_of_gt hc
  have hkey : 0 ≤ c * (g.inner x v v + -(1 / c) * (g.inner x v w + g.inner x v w)
      + (-(1 / c)) ^ 2 * g.inner x w w) := mul_nonneg hc.le hnn
  have hrw : c * (g.inner x v v + -(1 / c) * (g.inner x v w + g.inner x v w)
      + (-(1 / c)) ^ 2 * g.inner x w w)
      = c * g.inner x v v + g.inner x w w / c - 2 * g.inner x v w := by
    field_simp
    ring
  rw [hrw] at hkey
  linarith



def jacobiCurvOp (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (v : TangentSpace I (γ t)) : TangentSpace I (γ t) :=
  riemannOp (LeviCivita (I := I) g) (γ t) v
    (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
@[simp]
theorem jacobiCurvOp_apply (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (v : TangentSpace I (γ t)) :
    jacobiCurvOp (I := I) g γ t v =
      riemannOp (LeviCivita (I := I) g) (γ t) v
        (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_jacobiCurvOp_symm (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) (v w : TangentSpace I (γ t)) :
    g.inner (γ t) (jacobiCurvOp (I := I) g γ t v) w =
      g.inner (γ t) v (jacobiCurvOp (I := I) g γ t w) :=
  riemannOp_diag_symm (I := I) g (γ t) (curveVelocity (I := I) γ t) v w

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem jacobiCurvOp_add (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (v w : TangentSpace I (γ t)) :
    jacobiCurvOp (I := I) g γ t (v + w) =
      jacobiCurvOp (I := I) g γ t v + jacobiCurvOp (I := I) g γ t w := by
  simp only [jacobiCurvOp_apply]
  rw [ContinuousLinearMap.map_add (riemannOp (LeviCivita (I := I) g) (γ t)) v w]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem jacobiCurvOp_smul (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (c : ℝ) (v : TangentSpace I (γ t)) :
    jacobiCurvOp (I := I) g γ t (c • v) = c • jacobiCurvOp (I := I) g γ t v := by
  simp only [jacobiCurvOp_apply]
  rw [ContinuousLinearMap.map_smul (riemannOp (LeviCivita (I := I) g) (γ t)) c v]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_jacobiCurvOp_self_le (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hpos : ∀ v : TangentSpace I (γ t), 0 ≤ g.inner (γ t) (jacobiCurvOp (I := I) g γ t v) v)
    (hub : ∀ v : TangentSpace I (γ t),
      g.inner (γ t) (jacobiCurvOp (I := I) g γ t v) v ≤ K * g.inner (γ t) v v)
    (v : TangentSpace I (γ t)) :
    g.inner (γ t) (jacobiCurvOp (I := I) g γ t v) (jacobiCurvOp (I := I) g γ t v)
      ≤ K * g.inner (γ t) (jacobiCurvOp (I := I) g γ t v) v := by
  classical
  set S : TangentSpace I (γ t) → TangentSpace I (γ t) := jacobiCurvOp (I := I) g γ t with hS
  have hSadd : ∀ a b, S (a + b) = S a + S b := jacobiCurvOp_add (I := I) g γ t
  have hSsmul : ∀ (c : ℝ) a, S (c • a) = c • S a := jacobiCurvOp_smul (I := I) g γ t
  have hSsymm : ∀ a b, g.inner (γ t) (S a) b = g.inner (γ t) a (S b) :=
    inner_jacobiCurvOp_symm (I := I) g γ t
  have hSSvv : g.inner (γ t) (S (S v)) v = g.inner (γ t) (S v) (S v) := by
    rw [hSsymm (S v) v, g.symm (γ t) (S v) (S v)]
  have hquad : ∀ s : ℝ, 0 ≤ g.inner (γ t) (S v) v
      + 2 * s * g.inner (γ t) (S v) (S v)
      + s ^ 2 * g.inner (γ t) (S (S v)) (S v) := by
    intro s
    have hexp := inner_add_smul_expand (I := I) g (γ t) (S v) (S (S v)) v (S v) s
    have hSv : S (v + s • S v) = S v + s • S (S v) := by
      rw [hSadd v (s • S v), hSsmul s (S v)]
    have hnn : 0 ≤ g.inner (γ t) (S (v + s • S v)) (v + s • S v) := hpos _
    rw [hSv, hexp, hSSvv] at hnn
    have heq : g.inner (γ t) (S v) v
          + s * (g.inner (γ t) (S v) (S v) + g.inner (γ t) (S v) (S v))
          + s ^ 2 * g.inner (γ t) (S (S v)) (S v)
        = g.inner (γ t) (S v) v + 2 * s * g.inner (γ t) (S v) (S v)
          + s ^ 2 * g.inner (γ t) (S (S v)) (S v) := by ring
    rw [heq] at hnn
    exact hnn
  have hCS : (g.inner (γ t) (S v) (S v)) ^ 2
      ≤ g.inner (γ t) (S v) v * g.inner (γ t) (S (S v)) (S v) :=
    sq_le_mul_of_quadratic_nonneg hquad
  have hBSvSv : g.inner (γ t) (S (S v)) (S v) ≤ K * g.inner (γ t) (S v) (S v) := hub (S v)
  have hnn : 0 ≤ g.inner (γ t) (S v) (S v) := inner_self_nonneg (I := I) g (γ t) _
  have hBvvnn : 0 ≤ g.inner (γ t) (S v) v := hpos v
  rcases eq_or_lt_of_le hnn with hzero | hposn
  · rw [← hzero]
    exact mul_nonneg hK hBvvnn
  · nlinarith [hCS, hBSvSv, hposn, hBvvnn]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem contMDiff_velocity_section (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun t : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) t (1 : ℝ)) := by
    intro t
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I γ ∘ fun t : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) t (1 : ℝ))
  exact (hγ.contMDiff_tangentMap (le_refl _)).comp hunit

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem contMDiff_jacobiCurvOp_section (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (X : ∀ t : ℝ, TangentSpace I (γ t))
    (hX : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (X t))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t)
        (jacobiCurvOp (I := I) g γ t (X t))) := by
  classical
  have hvel := contMDiff_velocity_section (I := I) γ hγ
  let _i1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let _i2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let _i3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _i4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let _i5 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _i6 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let _i7 : NormedAddCommGroup (E × (E →L[ℝ] E)) := Prod.normedAddCommGroup
  let _i8 : NormedSpace ℝ (E × (E →L[ℝ] E)) := Prod.normedSpace
  let _i9 : NormedAddCommGroup (E × (E →L[ℝ] E →L[ℝ] E)) := Prod.normedAddCommGroup
  let _i10 : NormedSpace ℝ (E × (E →L[ℝ] E →L[ℝ] E)) := Prod.normedSpace
  let _i11 : NormedAddCommGroup (E × (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) :=
    Prod.normedAddCommGroup
  let _i12 : NormedSpace ℝ (E × (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) := Prod.normedSpace
  have hR0 := (riemannOp_section_contMDiff (I := I) (M := M) g).comp hγ
  have hR1 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
      (b := γ)
      (ϕ := fun t => riemannOp (LeviCivita (I := I) g) (γ t))
      (v := fun t => X t) hR0 hX
  have hR2 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      (b := γ)
      (ϕ := fun t => (riemannOp (LeviCivita (I := I) g) (γ t)) (X t))
      (v := fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      hR1 hvel
  have hR3 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := γ)
      (ϕ := fun t => (riemannOp (LeviCivita (I := I) g) (γ t)) (X t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (v := fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      hR2 hvel
  exact hR3

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem differentiableAt_chartRepAt_covDerivAlong (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (V : ∀ t : ℝ, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))
    (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s : ℝ => covDerivAlong (I := I) g γ V s) t) t := by
  classical
  have hVdiff : ∀ s : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ V s) s :=
    fun s => differentiableAt_chartRepAt_of_contMDiff (I := I) γ V hV s
  have hY0_C2 : ContDiffAt ℝ 2 (chartRepAtBase (I := I) (γ t) γ V) t := by
    have hsplit := Bundle.contMDiffAt_totalSpace.mp (hV t)
    have hnbd : ∀ᶠ s in 𝓝 t,
        γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      hsplit.1.continuousAt.preimage_mem_nhds
        ((Trivialization.open_baseSet _).mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    have heq : chartRepAtBase (I := I) (γ t) γ V =ᶠ[𝓝 t]
        (fun s : ℝ => (trivializationAt E (TangentSpace I) (γ t)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s))).2) := by
      filter_upwards [hnbd] with s hs
      rw [chartRepAtBase_apply]
      change (trivializationAt E (TangentSpace I) (γ t)).linearMapAt ℝ (γ s) (V s) = _
      rw [Trivialization.coe_linearMapAt_of_mem _ hs]
    exact ((contMDiffAt_iff_contDiffAt.mp hsplit.2).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).congr_of_eventuallyEq heq
  have hY0_diff : DifferentiableAt ℝ (chartRepAtBase (I := I) (γ t) γ V) t :=
    (hY0_C2.of_le one_le_two).differentiableAt (by norm_cast)
  have hderivY0_diff : DifferentiableAt ℝ (deriv (chartRepAtBase (I := I) (γ t) γ V)) t :=
    (hY0_C2.derivWithin (m := 1) (by norm_cast)).differentiableAt (by norm_cast)
  have huC_cdiff : ContDiffAt ℝ 2 (chartCurve (I := I) (γ t) γ) t :=
    (contDiffAt_chartCurve (I := I) hγ t).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have huC_diff : DifferentiableAt ℝ (chartCurve (I := I) (γ t) γ) t :=
    (huC_cdiff.of_le one_le_two).differentiableAt (by norm_cast)
  have hderivuC_diff : DifferentiableAt ℝ (deriv (chartCurve (I := I) (γ t) γ)) t :=
    (huC_cdiff.derivWithin (m := 1) (by norm_cast)).differentiableAt (by norm_cast)
  have huC0 : chartCurve (I := I) (γ t) γ t = extChartAt I (γ t) (γ t) := rfl
  have hΓ_diff : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (DifferentialGeometry.Geometry.Operator.chartChristoffel (I := I) g (γ t) i j k)
        (chartCurve (I := I) (γ t) γ t) := by
    intro i j k
    rw [huC0]
    exact ChristoffelRegularity.chartChristoffel_differentiableAt_self
      (I := I) g (γ t) i j k
  have hbridge : chartRepAt (I := I) γ (fun s : ℝ => covDerivAlong (I := I) g γ V s) t
      =ᶠ[𝓝 t] (fun s : ℝ => chartCovDerivAlong (I := I) g (γ t) γ
        (chartRepAtBase (I := I) (γ t) γ V) s) := by
    have hopen : IsOpen {s : ℝ | γ s ∈ (chartAt H (γ t)).source} :=
      hγ.continuous.isOpen_preimage _ (chartAt H (γ t)).open_source
    have hmemt : t ∈ {s : ℝ | γ s ∈ (chartAt H (γ t)).source} :=
      mem_chart_source H (γ t)
    filter_upwards [hopen.mem_nhds hmemt] with s hs
    rw [chartRepAt_apply]
    have hinv := covDerivAlong_chart_foot_invariance (I := I) (E := E) (n := ∞)
      (by simp) g γ V s (γ t) hγ hs (hVdiff s)
    rw [← hinv]
    have hmemb : γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hs
    exact (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_symmL
      (R := ℝ) hmemb _
  have hccd_diff : DifferentiableAt ℝ
      (fun s : ℝ => chartCovDerivAlong (I := I) g (γ t) γ
        (chartRepAtBase (I := I) (γ t) γ V) s) t := by
    have hfun : (fun s : ℝ => chartCovDerivAlong (I := I) g (γ t) γ
          (chartRepAtBase (I := I) (γ t) γ V) s)
        = (fun s : ℝ => deriv (chartRepAtBase (I := I) (γ t) γ V) s
            + DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I) g (γ t)
              (deriv (chartCurve (I := I) (γ t) γ) s)
              (chartRepAtBase (I := I) (γ t) γ V s)
              (chartCurve (I := I) (γ t) γ s)) := by
      funext s
      rw [chartCovDerivAlong_def]
    rw [hfun]
    refine DifferentiableAt.add hderivY0_diff ?_
    have hΓhd := hasDerivAt_chartChristoffelContraction (I := I) g (γ t)
      (P := deriv (chartCurve (I := I) (γ t) γ))
      (Q := chartRepAtBase (I := I) (γ t) γ V)
      (R := chartCurve (I := I) (γ t) γ)
      (P' := deriv (deriv (chartCurve (I := I) (γ t) γ)) t)
      (Q' := deriv (chartRepAtBase (I := I) (γ t) γ V) t)
      (R' := deriv (chartCurve (I := I) (γ t) γ) t)
      hderivuC_diff.hasDerivAt hY0_diff.hasDerivAt huC_diff.hasDerivAt hΓ_diff
    exact hΓhd.differentiableAt
  exact (hbridge.differentiableAt_iff).mpr hccd_diff



private theorem scalar_focal_comparison
    {f phi psi Phi psider : ℝ → ℝ} {K ρ : ℝ}
    (hK : 0 ≤ K) (hKρ : 4 * K * ρ ^ 2 ≤ 1)
    (hPhicont : ContinuousOn Phi (Icc 0 ρ))
    (hpsicont : ContinuousOn psi (Icc 0 ρ))
    (hphicont : ContinuousOn phi (Icc 0 ρ))
    (hpsidercont : ContinuousOn psider (Icc 0 ρ))
    (hPhinn : ∀ s ∈ Icc (0 : ℝ) ρ, 0 ≤ Phi s)
    (hpsinn : ∀ s ∈ Icc (0 : ℝ) ρ, 0 ≤ psi s)
    (hpsi0 : psi 0 = 0) (hphi0 : phi 0 = 0)
    (hfd : ∀ s ∈ Icc (0 : ℝ) ρ, HasDerivAt f (2 * phi s) s)
    (hphid : ∀ s ∈ Icc (0 : ℝ) ρ, HasDerivAt phi (psi s - Phi s) s)
    (hpsid : ∀ s ∈ Icc (0 : ℝ) ρ, HasDerivAt psi (psider s) s)
    (hpsibd : ∀ s ∈ Icc (0 : ℝ) ρ, ∀ c : ℝ, 0 < c →
      psider s ≤ c * K * Phi s + psi s / c)
    {h : ℝ} (hh0 : 0 ≤ h) (hhρ : h ≤ ρ) :
    f h ≤ f 0 := by
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans hh0 hhρ
  have hsubset : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ ρ → uIcc a b ⊆ Icc (0 : ℝ) ρ := by
    intro a b ha hab hb
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hint : ∀ (u : ℝ → ℝ), ContinuousOn u (Icc 0 ρ) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ ρ →
      IntervalIntegrable u MeasureTheory.volume a b := by
    intro u hu a b ha hab hb
    exact (hu.mono (hsubset a b ha hab hb)).intervalIntegrable
  have hphile : ∀ s ∈ Icc (0 : ℝ) ρ, phi s ≤ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [← hs0, hphi0]
    · have hsρ : s ≤ ρ := hs.2
      have hAnn : 0 ≤ ∫ u in (0 : ℝ)..s, Phi u :=
        intervalIntegral.integral_nonneg hs.1
          (fun u hu => hPhinn u ⟨hu.1, le_trans hu.2 hsρ⟩)
      have hBnn : 0 ≤ ∫ u in (0 : ℝ)..s, psi u :=
        intervalIntegral.integral_nonneg hs.1
          (fun u hu => hpsinn u ⟨hu.1, le_trans hu.2 hsρ⟩)
      set c : ℝ := 2 * s with hc_def
      have hc : 0 < c := by rw [hc_def]; linarith
      have hkey : ∀ r ∈ Icc (0 : ℝ) s,
          psi r ≤ c * K * (∫ u in (0 : ℝ)..s, Phi u)
            + (∫ u in (0 : ℝ)..s, psi u) / c := by
        intro r hr
        have hrρ : r ≤ ρ := le_trans hr.2 hsρ
        have hFTC : ∫ u in (0 : ℝ)..r, psider u = psi r - psi 0 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun u hu => hpsid u (hsubset 0 r le_rfl hr.1 hrρ hu))
            (hint psider hpsidercont 0 r le_rfl hr.1 hrρ)
        have hbdint : IntervalIntegrable (fun u => c * K * Phi u + psi u / c)
            MeasureTheory.volume 0 r :=
          hint (fun u => c * K * Phi u + psi u / c)
            (((continuousOn_const.mul hPhicont).add (hpsicont.div_const c))) 0 r le_rfl hr.1 hrρ
        have hmono : ∫ u in (0 : ℝ)..r, psider u
            ≤ ∫ u in (0 : ℝ)..r, (c * K * Phi u + psi u / c) :=
          intervalIntegral.integral_mono_on hr.1
            (hint psider hpsidercont 0 r le_rfl hr.1 hrρ) hbdint
            (fun u hu => hpsibd u ⟨hu.1, le_trans hu.2 hrρ⟩ c hc)
        have hsplit : ∫ u in (0 : ℝ)..r, (c * K * Phi u + psi u / c)
            = c * K * (∫ u in (0 : ℝ)..r, Phi u) + (∫ u in (0 : ℝ)..r, psi u) / c := by
          rw [intervalIntegral.integral_add
            (hint (fun u => c * K * Phi u) (continuousOn_const.mul hPhicont) 0 r le_rfl hr.1 hrρ)
            (hint (fun u => psi u / c) (hpsicont.div_const c) 0 r le_rfl hr.1 hrρ),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
        have hPhimono : (∫ u in (0 : ℝ)..r, Phi u) ≤ ∫ u in (0 : ℝ)..s, Phi u := by
          have hadd := intervalIntegral.integral_add_adjacent_intervals
            (hint Phi hPhicont 0 r le_rfl hr.1 hrρ) (hint Phi hPhicont r s hr.1 hr.2 hsρ)
          have hnn : 0 ≤ ∫ u in r..s, Phi u :=
            intervalIntegral.integral_nonneg hr.2
              (fun u hu => hPhinn u ⟨le_trans hr.1 hu.1, le_trans hu.2 hsρ⟩)
          linarith [hadd]
        have hpsimono : (∫ u in (0 : ℝ)..r, psi u) ≤ ∫ u in (0 : ℝ)..s, psi u := by
          have hadd := intervalIntegral.integral_add_adjacent_intervals
            (hint psi hpsicont 0 r le_rfl hr.1 hrρ) (hint psi hpsicont r s hr.1 hr.2 hsρ)
          have hnn : 0 ≤ ∫ u in r..s, psi u :=
            intervalIntegral.integral_nonneg hr.2
              (fun u hu => hpsinn u ⟨le_trans hr.1 hu.1, le_trans hu.2 hsρ⟩)
          linarith [hadd]
        rw [hsplit] at hmono
        rw [hFTC, hpsi0] at hmono
        have hcK : 0 ≤ c * K := mul_nonneg hc.le hK
        have h1 : c * K * (∫ u in (0 : ℝ)..r, Phi u) ≤ c * K * (∫ u in (0 : ℝ)..s, Phi u) :=
          mul_le_mul_of_nonneg_left hPhimono hcK
        have h2 : (∫ u in (0 : ℝ)..r, psi u) / c ≤ (∫ u in (0 : ℝ)..s, psi u) / c := by
          have hd : 0 ≤ ((∫ u in (0 : ℝ)..s, psi u) - ∫ u in (0 : ℝ)..r, psi u) / c :=
            div_nonneg (sub_nonneg.mpr hpsimono) hc.le
          rw [sub_div] at hd
          linarith
        linarith
      have hBbd : (∫ u in (0 : ℝ)..s, psi u)
          ≤ s * (c * K * (∫ u in (0 : ℝ)..s, Phi u)
            + (∫ u in (0 : ℝ)..s, psi u) / c) := by
        have hmono := intervalIntegral.integral_mono_on hs.1
          (hint psi hpsicont 0 s le_rfl hs.1 hsρ)
          (intervalIntegrable_const
            (c := c * K * (∫ u in (0 : ℝ)..s, Phi u) + (∫ u in (0 : ℝ)..s, psi u) / c))
          (fun u hu => hkey u hu)
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
        exact hmono
      have hB2 : (∫ u in (0 : ℝ)..s, psi u)
          ≤ 4 * K * s ^ 2 * (∫ u in (0 : ℝ)..s, Phi u) := by
        rw [hc_def] at hBbd
        have hsne : s ≠ 0 := ne_of_gt hs0
        have hrw : s * (2 * s * K * (∫ u in (0 : ℝ)..s, Phi u)
              + (∫ u in (0 : ℝ)..s, psi u) / (2 * s))
            = 2 * K * s ^ 2 * (∫ u in (0 : ℝ)..s, Phi u)
              + (∫ u in (0 : ℝ)..s, psi u) / 2 := by
          field_simp
        rw [hrw] at hBbd
        linarith
      have hphis : phi s = (∫ u in (0 : ℝ)..s, psi u) - ∫ u in (0 : ℝ)..s, Phi u := by
        have hFTC : ∫ u in (0 : ℝ)..s, (psi u - Phi u) = phi s - phi 0 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun u hu => hphid u (hsubset 0 s le_rfl hs.1 hsρ hu))
            (hint (fun u => psi u - Phi u) (hpsicont.sub hPhicont) 0 s le_rfl hs.1 hsρ)
        rw [intervalIntegral.integral_sub (hint psi hpsicont 0 s le_rfl hs.1 hsρ)
          (hint Phi hPhicont 0 s le_rfl hs.1 hsρ), hphi0, sub_zero] at hFTC
        exact hFTC.symm
      have hsq : 4 * K * s ^ 2 ≤ 1 := by
        have hss : s ^ 2 ≤ ρ ^ 2 := by nlinarith [hs.1, hsρ]
        nlinarith [hK, hss, hKρ]
      rw [hphis]
      nlinarith [hB2, hAnn, hsq]
  have hFTCf : ∫ u in (0 : ℝ)..h, 2 * phi u = f h - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hfd u (hsubset 0 h le_rfl hh0 hhρ hu))
      (hint (fun u => 2 * phi u) (continuousOn_const.mul hphicont) 0 h le_rfl hh0 hhρ)
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..h, -(2 * phi u) :=
    intervalIntegral.integral_nonneg hh0 (fun u hu => by
      have := hphile u ⟨hu.1, le_trans hu.2 hhρ⟩
      linarith)
  rw [intervalIntegral.integral_neg] at hnn
  linarith [hFTCf]



omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem inner_le_of_covDerivAlong_zero (g : SmoothRiemannianMetric I M)
    (σ : ℝ → M) (hσ : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ)
    (J : ∀ s : ℝ, TangentSpace I (σ s))
    (hJsm : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (σ s) (J s)))
    (hjac : IsJacobiAlong (I := I) g σ J)
    (hD0 : covDerivAlong (I := I) g σ J 0 = 0)
    {K ρ : ℝ} (hK : 0 ≤ K) (hKρ : 4 * K * ρ ^ 2 ≤ 1)
    (hpos : ∀ s ∈ Icc (0 : ℝ) ρ, ∀ v : TangentSpace I (σ s),
      0 ≤ g.inner (σ s) (jacobiCurvOp (I := I) g σ s v) v)
    (hub : ∀ s ∈ Icc (0 : ℝ) ρ, ∀ v : TangentSpace I (σ s),
      g.inner (σ s) (jacobiCurvOp (I := I) g σ s v) v ≤ K * g.inner (σ s) v v)
    {h : ℝ} (hh0 : 0 ≤ h) (hhρ : h ≤ ρ) :
    g.inner (σ h) (J h) (J h) ≤ g.inner (σ 0) (J 0) (J 0) := by
  classical
  have hone : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
  have hJdiff : ∀ s : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) σ J s) s :=
    fun s => differentiableAt_chartRepAt_of_contMDiff (I := I) σ J hJsm s
  have hSJsm := contMDiff_jacobiCurvOp_section (I := I) g σ hσ J hJsm
  have hSJdiff : ∀ s : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) σ (fun u : ℝ => jacobiCurvOp (I := I) g σ u (J u)) s) s :=
    fun s => differentiableAt_chartRepAt_of_contMDiff (I := I) σ
      (fun u : ℝ => jacobiCurvOp (I := I) g σ u (J u)) hSJsm s
  have hDJdiff : ∀ s : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) σ (fun u : ℝ => covDerivAlong (I := I) g σ J u) s) s :=
    fun s => differentiableAt_chartRepAt_covDerivAlong (I := I) g σ hσ J hJsm s
  have hd2 : ∀ s : ℝ, covDerivAlong (I := I) g σ
      (fun u : ℝ => covDerivAlong (I := I) g σ J u) s
        = -(jacobiCurvOp (I := I) g σ s (J s)) :=
    fun s => jacobi_d2_eq (I := I) g σ J (hjac s)
  have hfd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => g.inner (σ u) (J u) (J u))
      (2 * g.inner (σ s) (covDerivAlong (I := I) g σ J s) (J s)) s := by
    intro s
    have hderiv := inner_deriv_at (I := I) hone g σ J J s hσ.contMDiffAt
      (hJdiff s) (hJdiff s)
    have heq : g.inner (σ s) (covDerivAlong (I := I) g σ J s) (J s)
        + g.inner (σ s) (J s) (covDerivAlong (I := I) g σ J s)
        = 2 * g.inner (σ s) (covDerivAlong (I := I) g σ J s) (J s) := by
      rw [g.symm (σ s) (J s) (covDerivAlong (I := I) g σ J s)]
      ring
    rw [heq] at hderiv
    exact hderiv
  have hphid : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => g.inner (σ u) (covDerivAlong (I := I) g σ J u) (J u))
        (g.inner (σ s) (covDerivAlong (I := I) g σ J s) (covDerivAlong (I := I) g σ J s)
          - g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s)) (J s)) s := by
    intro s
    have hderiv := inner_deriv_at (I := I) hone g σ
      (fun u : ℝ => covDerivAlong (I := I) g σ J u) J s hσ.contMDiffAt
      (hDJdiff s) (hJdiff s)
    rw [hd2 s, inner_neg_left (I := I) g (σ s)] at hderiv
    have heq : -g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s)) (J s)
        + g.inner (σ s) (covDerivAlong (I := I) g σ J s) (covDerivAlong (I := I) g σ J s)
        = g.inner (σ s) (covDerivAlong (I := I) g σ J s) (covDerivAlong (I := I) g σ J s)
          - g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s)) (J s) := by ring
    rw [heq] at hderiv
    exact hderiv
  have hpsid : ∀ s : ℝ, HasDerivAt
      (fun u : ℝ => g.inner (σ u) (covDerivAlong (I := I) g σ J u)
        (covDerivAlong (I := I) g σ J u))
      (-2 * g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
        (covDerivAlong (I := I) g σ J s)) s := by
    intro s
    have hderiv := inner_deriv_at (I := I) hone g σ
      (fun u : ℝ => covDerivAlong (I := I) g σ J u)
      (fun u : ℝ => covDerivAlong (I := I) g σ J u) s hσ.contMDiffAt
      (hDJdiff s) (hDJdiff s)
    rw [hd2 s, inner_neg_left (I := I) g (σ s), inner_neg_right (I := I) g (σ s)] at hderiv
    have heq : -g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
          (covDerivAlong (I := I) g σ J s)
        + -g.inner (σ s) (covDerivAlong (I := I) g σ J s)
          (jacobiCurvOp (I := I) g σ s (J s))
        = -2 * g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
          (covDerivAlong (I := I) g σ J s) := by
      rw [g.symm (σ s) (covDerivAlong (I := I) g σ J s)
        (jacobiCurvOp (I := I) g σ s (J s))]
      ring
    rw [heq] at hderiv
    exact hderiv
  have hPhid : ∀ s : ℝ,
      DifferentiableAt ℝ
        (fun u : ℝ => g.inner (σ u) (jacobiCurvOp (I := I) g σ u (J u)) (J u)) s :=
    fun s => (inner_deriv_at (I := I) hone g σ
      (fun u : ℝ => jacobiCurvOp (I := I) g σ u (J u)) J s hσ.contMDiffAt
      (hSJdiff s) (hJdiff s)).differentiableAt
  have hpsiderd : ∀ s : ℝ,
      DifferentiableAt ℝ
        (fun u : ℝ => g.inner (σ u) (jacobiCurvOp (I := I) g σ u (J u))
          (covDerivAlong (I := I) g σ J u)) s :=
    fun s => (inner_deriv_at (I := I) hone g σ
      (fun u : ℝ => jacobiCurvOp (I := I) g σ u (J u))
      (fun u : ℝ => covDerivAlong (I := I) g σ J u) s hσ.contMDiffAt
      (hSJdiff s) (hDJdiff s)).differentiableAt
  refine scalar_focal_comparison (f := fun s : ℝ => g.inner (σ s) (J s) (J s))
    (phi := fun s : ℝ => g.inner (σ s) (covDerivAlong (I := I) g σ J s) (J s))
    (psi := fun s : ℝ => g.inner (σ s) (covDerivAlong (I := I) g σ J s)
      (covDerivAlong (I := I) g σ J s))
    (Phi := fun s : ℝ => g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s)) (J s))
    (psider := fun s : ℝ => -2 * g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
      (covDerivAlong (I := I) g σ J s))
    hK hKρ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun s _ => hfd s) (fun s _ => hphid s)
    (fun s _ => hpsid s) ?_ hh0 hhρ
  · exact fun s _ => ((hPhid s).continuousAt).continuousWithinAt
  · exact fun s _ => (((hpsid s).differentiableAt).continuousAt).continuousWithinAt
  · exact fun s _ => (((hphid s).differentiableAt).continuousAt).continuousWithinAt
  · exact fun s _ =>
      ((continuousAt_const.mul ((hpsiderd s).continuousAt))).continuousWithinAt
  · exact fun s hs => hpos s hs (J s)
  · exact fun s _ => inner_self_nonneg (I := I) g (σ s) _
  · rw [hD0]
    simp
  · rw [hD0]
    simp
  · intro s hs c hc
    have hyoung := two_inner_le_of_pos (I := I) g (σ s)
      (-(jacobiCurvOp (I := I) g σ s (J s))) (covDerivAlong (I := I) g σ J s) hc
    have hnegneg : g.inner (σ s) (-(jacobiCurvOp (I := I) g σ s (J s)))
        (-(jacobiCurvOp (I := I) g σ s (J s)))
        = g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
          (jacobiCurvOp (I := I) g σ s (J s)) := by
      rw [inner_neg_left (I := I) g (σ s), inner_neg_right (I := I) g (σ s)]
      ring
    have hnegleft : g.inner (σ s) (-(jacobiCurvOp (I := I) g σ s (J s)))
        (covDerivAlong (I := I) g σ J s)
        = -g.inner (σ s) (jacobiCurvOp (I := I) g σ s (J s))
          (covDerivAlong (I := I) g σ J s) := inner_neg_left (I := I) g (σ s) _ _
    rw [hnegneg, hnegleft] at hyoung
    have hcs := inner_jacobiCurvOp_self_le (I := I) g σ s hK (hpos s hs) (hub s hs) (J s)
    have hcnn : 0 ≤ c := hc.le
    nlinarith [hyoung, hcs, hcnn]



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem abs_metricRm04StandardAt_diag_le (g : SmoothRiemannianMetric I M) (y : M)
    (v u : TangentSpace I y) :
    |metricRm04StandardAt (I := I) (M := M) g y v u u v|
      ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04At (I := I) (M := M) g y))
        * (g.inner y v v * g.inner y u u) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g y
  have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g y 4 basis hON
    (metricRm04At (I := I) (M := M) g y) (vec4 (I := I) v u u v)
  have e0 : vec4 (I := I) v u u v 0 = v := rfl
  have e1 : vec4 (I := I) v u u v 1 = u := rfl
  have e2 : vec4 (I := I) v u u v 2 = u := rfl
  have e3 : vec4 (I := I) v u u v 3 = v := rfl
  have hprod : (∏ a : Fin 4, Real.sqrt (g.inner y (vec4 (I := I) v u u v a)
        (vec4 (I := I) v u u v a))) = g.inner y v v * g.inner y u u := by
    have hv : 0 ≤ g.inner y v v := inner_self_nonneg (I := I) g y v
    have hu : 0 ≤ g.inner y u u := inner_self_nonneg (I := I) g y u
    rw [Fin.prod_univ_four, e0, e1, e2, e3,
      show Real.sqrt (g.inner y v v) * Real.sqrt (g.inner y u u)
          * Real.sqrt (g.inner y u u) * Real.sqrt (g.inner y v v)
        = (Real.sqrt (g.inner y v v) * Real.sqrt (g.inner y v v))
          * (Real.sqrt (g.inner y u u) * Real.sqrt (g.inner y u u)) from by ring,
      Real.mul_self_sqrt hv, Real.mul_self_sqrt hu]
  rw [metricRm04StandardAt_apply]
  rw [hprod] at h
  exact h

omit [ConnectedSpace M] in
theorem exists_curvature_bound_closedBall (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : M, dist x y ≤ R → ∀ v u : TangentSpace I y,
      |metricRm04StandardAt (I := I) (M := M) g y v u u v|
        ≤ K * (g.inner y v v * g.inner y u u) := by
  classical
  by_cases hR : 0 ≤ R
  · have hcont : Continuous (fun y : M => Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04 (I := I) (M := M) g y))) :=
      Real.continuous_sqrt.comp
        (Tensor0SBundle.normSq0S_cont (I := I) g (metricRm04 (I := I) (M := M) g))
    have hcpt : IsCompact (Metric.closedBall x R) :=
      soul_isCompact_closedBall (I := I) g hEnorm x R
    have hne : (Metric.closedBall x R).Nonempty := ⟨x, by simpa using hR⟩
    obtain ⟨y₀, _hy₀, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
    refine ⟨Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y₀ 4
      (metricRm04 (I := I) (M := M) g y₀)), Real.sqrt_nonneg _, fun y hy v u => ?_⟩
    have hymem : y ∈ Metric.closedBall x R := by
      simpa [Metric.mem_closedBall, dist_comm] using hy
    have hle : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04 (I := I) (M := M) g y))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y₀ 4
          (metricRm04 (I := I) (M := M) g y₀)) := hmax hymem
    have hnn : 0 ≤ g.inner y v v * g.inner y u u :=
      mul_nonneg (inner_self_nonneg (I := I) g y v) (inner_self_nonneg (I := I) g y u)
    have hrw : ∀ z : M, Tensor0SBundle.normSq0S (I := I) g z 4
        (metricRm04 (I := I) (M := M) g z)
        = Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) (M := M) g z) := by
      intro z
      rw [metricRm04_apply]
    rw [hrw y, hrw y₀] at hle
    exact le_trans (abs_metricRm04StandardAt_diag_le (I := I) g y v u)
      (mul_le_mul_of_nonneg_right hle hnn)
  · refine ⟨0, le_rfl, fun y hy _v _u => ?_⟩
    exact absurd (le_trans dist_nonneg hy) hR



variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [ConnectedSpace M] in
theorem hasFocalJacobiBound_of_sec_nonneg (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    HasFocalJacobiBound (I := I) g hEnorm := by
  classical
  intro x r
  obtain ⟨K, hK0, hKbd⟩ := exists_curvature_bound_closedBall (I := I) g hEnorm x (r + 1)
  have hKpos : (0 : ℝ) < K + 1 := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (K + 1) := Real.sqrt_pos.mpr hKpos
  have hρpos : (0 : ℝ) < min 1 (1 / (2 * Real.sqrt (K + 1))) :=
    lt_min one_pos (by positivity)
  refine ⟨min 1 (1 / (2 * Real.sqrt (K + 1))), hρpos, ?_⟩
  intro z w hz hw σ hσeq J hJsm hjac hD0 _hperp h hh0 hhρ
  subst hσeq
  have hρ1 : min 1 (1 / (2 * Real.sqrt (K + 1))) ≤ 1 := min_le_left _ _
  have hρK : 4 * K * min 1 (1 / (2 * Real.sqrt (K + 1))) ^ 2 ≤ 1 := by
    have hb : min 1 (1 / (2 * Real.sqrt (K + 1))) ≤ 1 / (2 * Real.sqrt (K + 1)) :=
      min_le_right _ _
    have hden : (0 : ℝ) < 2 * Real.sqrt (K + 1) := by positivity
    have hmul : min 1 (1 / (2 * Real.sqrt (K + 1))) * (2 * Real.sqrt (K + 1)) ≤ 1 := by
      rw [le_div_iff₀ hden] at hb
      exact hb
    have hnn : 0 ≤ min 1 (1 / (2 * Real.sqrt (K + 1))) * (2 * Real.sqrt (K + 1)) := by
      positivity
    have hsq : (min 1 (1 / (2 * Real.sqrt (K + 1))) * (2 * Real.sqrt (K + 1))) ^ 2 ≤ 1 := by
      nlinarith [hmul, hnn]
    have hS2 : Real.sqrt (K + 1) ^ 2 = K + 1 := Real.sq_sqrt hKpos.le
    have hexp : (min 1 (1 / (2 * Real.sqrt (K + 1))) * (2 * Real.sqrt (K + 1))) ^ 2
        = 4 * min 1 (1 / (2 * Real.sqrt (K + 1))) ^ 2 * (K + 1) := by
      rw [mul_pow, mul_pow, hS2]
      ring
    rw [hexp] at hsq
    nlinarith [hsq, sq_nonneg (min 1 (1 / (2 * Real.sqrt (K + 1)))), hK0]
  have hσsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm z w) :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm z w
  have hunit : ∀ s : ℝ,
      g.inner (intrinsicGeodesic (I := I) g hEnorm z w s)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s) = 1 :=
    fun s => inner_velocity_intrinsicGeodesic (I := I) g hEnorm z w hw s
  have hball : ∀ s ∈ Icc (0 : ℝ) (min 1 (1 / (2 * Real.sqrt (K + 1)))),
      dist x (intrinsicGeodesic (I := I) g hEnorm z w s) ≤ r + 1 := by
    intro s hs
    have h1 := dist_intrinsicGeodesic_le (I := I) g hEnorm z w hw hs.1
    have h2 := dist_triangle x z (intrinsicGeodesic (I := I) g hEnorm z w s)
    have h3 : s ≤ 1 := le_trans hs.2 hρ1
    linarith
  have hbridge : ∀ (s : ℝ) (v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm z w s)),
      g.inner (intrinsicGeodesic (I := I) g hEnorm z w s)
          (jacobiCurvOp (I := I) g (intrinsicGeodesic (I := I) g hEnorm z w) s v) v
        = metricRm04StandardAt (I := I) (M := M) g
          (intrinsicGeodesic (I := I) g hEnorm z w s) v
          (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s)
          (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s) v := by
    intro s v
    rw [rm04_eq_inner_riem (I := I) (M := M) g
      (intrinsicGeodesic (I := I) g hEnorm z w s) v
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s) v]
    rw [g.symm (intrinsicGeodesic (I := I) g hEnorm z w s)
      (jacobiCurvOp (I := I) g (intrinsicGeodesic (I := I) g hEnorm z w) s v) v]
    rfl
  have hpos : ∀ s ∈ Icc (0 : ℝ) (min 1 (1 / (2 * Real.sqrt (K + 1)))),
      ∀ v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm z w s),
        0 ≤ g.inner (intrinsicGeodesic (I := I) g hEnorm z w s)
          (jacobiCurvOp (I := I) g (intrinsicGeodesic (I := I) g hEnorm z w) s v) v := by
    intro s _ v
    rw [hbridge s v]
    exact (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm z w s)).mp
      (hsec (intrinsicGeodesic (I := I) g hEnorm z w s)) v
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s)
  have hub : ∀ s ∈ Icc (0 : ℝ) (min 1 (1 / (2 * Real.sqrt (K + 1)))),
      ∀ v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm z w s),
        g.inner (intrinsicGeodesic (I := I) g hEnorm z w s)
            (jacobiCurvOp (I := I) g (intrinsicGeodesic (I := I) g hEnorm z w) s v) v
          ≤ K * g.inner (intrinsicGeodesic (I := I) g hEnorm z w s) v v := by
    intro s hs v
    rw [hbridge s v]
    have habs := hKbd (intrinsicGeodesic (I := I) g hEnorm z w s) (hball s hs) v
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm z w) s)
    rw [hunit s, mul_one] at habs
    exact le_trans (le_abs_self _) habs
  exact inner_le_of_covDerivAlong_zero (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm z w) hσsm J hJsm hjac hD0 hK0 hρK hpos hub
    hh0 hhρ.le

omit [ConnectedSpace M] in
theorem hasParallelShiftBound_of_sec_nonneg (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    HasParallelShiftBound (I := I) g hEnorm :=
  hasParallelShiftBound_of_focalJacobiBound (I := I) g hEnorm
    (hasFocalJacobiBound_of_sec_nonneg (I := I) g hEnorm hsec)



theorem hasOrthogonalBoundaryShift_relBoundary_of_sec_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C)) :
    HasOrthogonalBoundaryShift (I := I) g hEnorm C (relBoundary I C) :=
  hasOrthogonalBoundaryShift_relBoundary (I := I) g hEnorm hC hCclosed hdim hBne hsupp
    (hasParallelShiftBound_of_sec_nonneg (I := I) g hEnorm hsec)

theorem concaveOn_infDist_relBoundary_of_sec_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hmaps : MapsTo γ (Icc a b) C) :
    ConcaveOn ℝ (Icc a b) (fun s => Metric.infDist (γ s) (relBoundary I C)) :=
  concaveOn_infDist_relBoundary (I := I) g hEnorm hsec hC hCclosed hdim hBne hsupp
    (hasParallelShiftBound_of_sec_nonneg (I := I) g hEnorm hsec) hab hgeo hcont hmaps

theorem isTotallyConvex_superlevel_infDist_relBoundary_of_sec_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C)) (t : ℝ) :
    IsTotallyConvex (I := I) g
      {z ∈ C | t ≤ Metric.infDist z (relBoundary I C)} :=
  isTotallyConvex_superlevel_infDist_relBoundary (I := I) g hEnorm hsec hC hCclosed
    hdim hBne hsupp (hasParallelShiftBound_of_sec_nonneg (I := I) g hEnorm hsec) t

end DifferentialGeometry.Geometry.Topology

end
