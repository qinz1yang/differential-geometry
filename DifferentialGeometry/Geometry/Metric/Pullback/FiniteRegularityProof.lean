import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.PointwiseSmoothness

/-!
# Pullback of a finite-regularity Riemannian metric by a finite-regularity diffeomorphism

Blueprint LFR01, last assertion: if `g` is a `C^n` Riemannian metric on `N` and `f : M → N` is a
`C^s` diffeomorphism with `m ≤ n` and `m + 1 ≤ s`, then
`h_x(v, w) = g_{f x}(df_x v, df_x w)` is a `C^m` Riemannian metric on `M`.

The smooth version `Diffeomorph.pullbackMetricCross` (in `Cross.lean`) tests the bilinear-form
section against global smooth vector fields, which needs `[T2Space M]` (bump functions). Here the
regularity is checked at each point `x₀` against the *local* frame
`x ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ x v`, so no separation axiom is used.

Main results:
* `DifferentialGeometry.Geometry.finitePullbackMetric`: the pulled-back metric, general orders
  `m ≤ n`, `m + 1 ≤ s` in `WithTop ℕ∞`;
* `DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph_proved`: the exact
  statement of `exists_pullback_metric_of_finite_diffeomorph` (`FiniteRegularity.lean`);
* `finitePullbackMetric_refl_inner`, `finitePullbackMetric_refl`: pullback by the identity;
* `finitePullbackMetric_eq_pullbackMetricCross`: agreement with the smooth pullback.
-/

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

section LocalFrame

omit [FiniteDimensional ℝ E] in
/-- The local frame vector field `x ↦ e.symmL ℝ x v` of the tangent trivialization `e` at `x₀`
is `C^n` at `x₀`, for every order `n`. -/
theorem contMDiffAt_tangent_symmL_frame {n : WithTop ℕ∞} (x₀ : M) (v : E) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun x => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) x
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v)) x₀ := by
  rw [contMDiffAt_section]
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ x₀)] with x hx
  rw [e.symmL_apply hx, e.apply_mk_symm hx]

/-- A section `φ` of the bundle `TM →L V₂` is `C^n` at `x₀` as soon as its values on the local
frame `x ↦ e.symmL ℝ x v` (`e` the tangent trivialization at `x₀`) are `C^n` at `x₀`.
No separation axiom is needed: only the local frame at `x₀` is used. -/
theorem contMDiffAt_tangent_clm_section_of_symmL_apply {n : WithTop ℕ∞}
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x) (x₀ : M)
    (h : ∀ v : E, ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) n
      (fun x => TotalSpace.mk' F₂ (E := V₂) x
        (φ x ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v))) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) n
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro v
  let e₂ := trivializationAt F₂ V₂ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hv := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp (h v)
  refine hv.congr_of_eventuallyEq ?_
  filter_upwards [e₂.open_baseSet.mem_nhds he₂] with x hx
  change (e₂.continuousLinearMapAt ℝ x)
      ((φ x) ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v)) = _
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx]

end LocalFrame

section Pullback

variable {n s m : WithTop ℕ∞}

/-- The pulled-back bilinear form `h_x(v, w) = g_{f x}(df_x v, df_x w)`. -/
def finitePullbackInner
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N s) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x) :
      (TangentSpace J (f x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
@[simp]
theorem finitePullbackInner_apply
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N s) (x : M) (v w : TangentSpace I x) :
    finitePullbackInner g f x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem withTop_ne_zero_of_add_one_le (hms : m + 1 ≤ s) : s ≠ 0 := by
  rintro rfl
  rw [nonpos_iff_eq_zero, add_eq_zero] at hms
  exact one_ne_zero hms.2

omit [FiniteDimensional ℝ F] in
/-- The regularity of the pulled-back form: `C^m` at every point when `m ≤ n` and `m + 1 ≤ s`. -/
theorem contMDiffAt_finitePullbackInner
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N s) (hmn : m ≤ n) (hms : m + 1 ≤ s) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (finitePullbackInner g f x)) x₀ := by
  have hfm : ContMDiff I J m f := f.contMDiff.of_le (le_self_add.trans hms)
  have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) m
      (fun x : M => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun b : N => TangentSpace J b →L[ℝ] TangentSpace J b →L[ℝ] ℝ)
        (f x) (g.inner (f x))) :=
    (g.contMDiff.of_le hmn).comp hfm
  have hT : ContMDiff I.tangent J.tangent m (tangentMap I J f) :=
    f.contMDiff.contMDiff_tangentMap hms
  have hY : ∀ v : E, ContMDiffAt I (J.prod 𝓘(ℝ, F)) m
      (fun x : M => TotalSpace.mk' F (E := (TangentSpace J : N → Type _)) (f x)
        (mfderiv I J f x
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v))) x₀ :=
    fun v => (hT _).comp x₀ (contMDiffAt_tangent_symmL_frame x₀ v)
  apply contMDiffAt_tangent_clm_section_of_symmL_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => finitePullbackInner g f x)
  intro v
  apply contMDiffAt_tangent_clm_section_of_symmL_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => finitePullbackInner g f x
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v))
  intro w
  have h_total := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : N => TangentSpace J b)
    (E₂ := fun b : N => TangentSpace J b)
    (E₃ := fun _ : N => ℝ)
    (b := fun x : M => f x)
    (ψ := fun x : M => g.inner (f x))
    (hg x₀) (hY v) (hY w)
  rw [contMDiffAt_totalSpace] at h_total
  rw [contMDiffAt_section]
  exact h_total.2

/-- **Pullback of a `C^n` metric by a `C^s` diffeomorphism** (blueprint LFR01): for `m ≤ n` and
`m + 1 ≤ s`, the form `h_x(v, w) = g_{f x}(df_x v, df_x w)` is a `C^m` Riemannian metric. -/
def finitePullbackMetric
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N s) (hmn : m ≤ n) (hms : m + 1 ≤ s) :
    ContMDiffRiemannianMetric I m E (TangentSpace I : M → Type _) where
  inner x := finitePullbackInner g f x
  symm x v w := by
    simp only [finitePullbackInner_apply]
    exact g.symm _ _ _
  pos x v hv := by
    have hs : s ≠ 0 := withTop_ne_zero_of_add_one_le hms
    have hne : f.mfderivToContinuousLinearEquiv hs x v ≠ 0 :=
      (f.mfderivToContinuousLinearEquiv hs x).map_ne_zero_iff.mpr hv
    exact g.pos (f x) _ hne
  isVonNBounded x := by
    have hs : s ≠ 0 := withTop_ne_zero_of_add_one_le hms
    let e := f.mfderivToContinuousLinearEquiv hs x
    have hb := (g.isVonNBounded (f x)).image
      (e.symm : TangentSpace J (f x) →L[ℝ] TangentSpace I x)
    have hset : {v : TangentSpace I x | finitePullbackInner g f x v v < 1} =
        ((e.symm : TangentSpace J (f x) →L[ℝ] TangentSpace I x) : _ → _) ''
          {w : TangentSpace J (f x) | g.inner (f x) w w < 1} := by
      rw [ContinuousLinearEquiv.coe_coe, e.image_symm_eq_preimage]
      rfl
    rw [hset]
    exact hb
  contMDiff x₀ := contMDiffAt_finitePullbackInner g f hmn hms x₀

omit [FiniteDimensional ℝ F] in
@[simp]
theorem finitePullbackMetric_inner
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N s) (hmn : m ≤ n) (hms : m + 1 ≤ s)
    (x : M) (v w : TangentSpace I x) :
    (finitePullbackMetric g f hmn hms).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- Two `C^n` Riemannian metrics with the same scalar products are equal. -/
theorem contMDiffRiemannianMetric_ext_inner
    {g h : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
    (hinner : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = h.inner x v w) :
    g = h := by
  obtain ⟨gi, gs, gp, gb, gc⟩ := g
  obtain ⟨hi, hs, hp, hb, hc⟩ := h
  have hfield : gi = hi :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => hinner x v w
  subst hfield
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The differential of the identity diffeomorphism is the identity. -/
theorem mfderiv_diffeomorph_refl (x : M) (v : TangentSpace I x) :
    mfderiv I I (Diffeomorph.refl I M s) x v = v := by
  have h : mfderiv I I (fun y : M => (Diffeomorph.refl I M s : M ≃ₘ^s⟮I, I⟯ M) y) x =
      mfderiv I I (id : M → M) x := rfl
  rw [h, mfderiv_id]
  rfl

/-- Pullback by the identity does not change the scalar products. -/
theorem finitePullbackMetric_refl_inner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) (x : M) (v w : TangentSpace I x) :
    (finitePullbackMetric g (Diffeomorph.refl I M s) hmn hms).inner x v w = g.inner x v w := by
  rw [finitePullbackMetric_inner, mfderiv_diffeomorph_refl, mfderiv_diffeomorph_refl]
  rfl

/-- Pullback by the identity, at the same order, is the same metric. -/
theorem finitePullbackMetric_refl
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hns : n + 1 ≤ s) :
    finitePullbackMetric g (Diffeomorph.refl I M s) le_rfl hns = g :=
  contMDiffRiemannianMetric_ext_inner fun x v w => finitePullbackMetric_refl_inner g le_rfl hns x v w

/-- Naturality: pulling back twice is pulling back by the composite (scalar products). -/
theorem finitePullbackMetric_trans_inner
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {L : Type*} [TopologicalSpace L] {K : ModelWithCorners ℝ W L}
    {P : Type*} [TopologicalSpace P] [ChartedSpace L P] [IsManifold K ∞ P]
    {m' : WithTop ℕ∞}
    (g : ContMDiffRiemannianMetric K n W (TangentSpace K : P → Type _))
    (Φ : Diffeomorph I J M N s) (Ψ : Diffeomorph J K N P s)
    (hm'n : m' ≤ n) (hm's : m' + 1 ≤ s) (hmm' : m ≤ m') (hms : m + 1 ≤ s) (hmn : m ≤ n)
    (x : M) (v w : TangentSpace I x) :
    (finitePullbackMetric (finitePullbackMetric g Ψ hm'n hm's) Φ hmm' hms).inner x v w =
      (finitePullbackMetric g (Φ.trans Ψ) hmn hms).inner x v w := by
  have hs : s ≠ 0 := withTop_ne_zero_of_add_one_le hms
  rw [finitePullbackMetric_inner, finitePullbackMetric_inner, finitePullbackMetric_inner]
  have hcomp : mfderiv I K (Φ.trans Ψ : M → P) x =
      (mfderiv J K (Ψ : N → P) (Φ x)).comp (mfderiv I J (Φ : M → N) x) :=
    mfderiv_comp x (Ψ.contMDiff.mdifferentiableAt hs) (Φ.contMDiff.mdifferentiableAt hs)
  rw [hcomp]
  rfl

end Pullback

section Smooth

omit [FiniteDimensional ℝ F] in
/-- The finite-order pullback of a smooth metric by a smooth diffeomorphism has the same scalar
products as the smooth pullback `Diffeomorph.pullbackMetricCross`. -/
theorem finitePullbackMetric_inner_eq_pullbackMetricCross_inner [T2Space M]
    {m : WithTop ℕ∞} (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (hmn : m ≤ ∞) (hms : m + 1 ≤ ∞) (x : M) (v w : TangentSpace I x) :
    (finitePullbackMetric g Φ hmn hms).inner x v w =
      (Diffeomorph.pullbackMetricCross g Φ).inner x v w := by
  rw [finitePullbackMetric_inner, Diffeomorph.pullbackMetricCross_inner]

omit [FiniteDimensional ℝ F] in
/-- At order `∞` the finite-order pullback is the smooth pullback. -/
theorem finitePullbackMetric_eq_pullbackMetricCross [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (hms : (∞ : WithTop ℕ∞) + 1 ≤ ∞) :
    finitePullbackMetric g Φ le_rfl hms = Diffeomorph.pullbackMetricCross g Φ :=
  SmoothRiemannianMetric.ext_inner fun x v w =>
    finitePullbackMetric_inner_eq_pullbackMetricCross_inner g Φ le_rfl hms x v w

end Smooth

-- The binder `[FiniteDimensional ℝ F]` is unused but kept (hence the `nolint`), so that the
-- binder list is identical to the target `exists_pullback_metric_of_finite_diffeomorph`.
set_option linter.unusedSectionVars false in
/-- The exact statement of `exists_pullback_metric_of_finite_diffeomorph`
(`FiniteRegularity.lean`), proved: a `C^K` metric pulled back by a `C^s` diffeomorphism is
`C^r` whenever `r ≤ K` and `r + 1 ≤ s`. -/
@[nolint unusedArguments]
theorem exists_pullback_metric_of_finite_diffeomorph_proved
    (K s r : ℕ) (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N (s : WithTop ℕ∞)) :
    ∃ h : ContMDiffRiemannianMetric I (r : WithTop ℕ∞)
        E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  ⟨finitePullbackMetric g f (by exact_mod_cast hrK) (by exact_mod_cast hrs),
    fun _ _ _ => rfl⟩

end DifferentialGeometry.Geometry
