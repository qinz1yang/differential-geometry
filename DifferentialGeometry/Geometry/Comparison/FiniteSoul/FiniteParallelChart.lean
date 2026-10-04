import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelDefs
import DifferentialGeometry.Bundle.TangentChart
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients

/-!
# Finite-order parallel transport: the chart toolkit (lane CMS3-PT, group G1)

* `extChartAt_tangent_zero_snd_eq_mfderiv`: the fibre coordinate of the tangent chart at `⟨q, 0⟩` is
  `dφ_q`.
* `chartCoeffFinite_transition`, `contDiffOn_chartCoeffFinite`, `isCoercive_chartCoeffFinite`: the chart
  coefficients pull back along chart transitions, are `C^{r+1}` and coercive (public versions of private
  lemmas of `Curvature/Riemann/FiniteMetric.lean`).
* `fderiv_fderiv_chartTransition`: the polarized chart naturality of `raisedKoszulOp`
  (the chart instance of `Analysis.fderiv_fderiv_eq_raisedKoszulOp_of_pullback`).
* `hasDerivWithinAt_fderiv_apply_of_pullback`: Euclidean transfer of the parallel ODE along a `C²`
  change of coordinates.
* `raisedKoszulOp_add_raisedKoszulOp_flip`: metric compatibility of the Koszul operator.
* `eqOn_Icc_of_hasDerivWithinAt_linear`: uniqueness for linear ODEs on `Icc` (Grönwall).
* geodesic chart equations and the transfer of the parallel ODE to every chart.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness for a linear ODE on `Icc`** (derivatives within `Icc`): two solutions of
`Y' = A t Y` that agree at one time agree everywhere. Grönwall, through Mathlib's
`ODE_solution_unique_of_mem_Icc_right/_left`. -/
theorem eqOn_Icc_of_hasDerivWithinAt_linear {A : ℝ → E →L[ℝ] E} {K : ℝ≥0} {α β t₀ : ℝ}
    (hA : ∀ t ∈ Icc α β, ‖A t‖ ≤ K) {Y₁ Y₂ : ℝ → E}
    (hY₁c : ContinuousOn Y₁ (Icc α β)) (hY₂c : ContinuousOn Y₂ (Icc α β))
    (hY₁ : ∀ t ∈ Icc α β, HasDerivWithinAt Y₁ (A t (Y₁ t)) (Icc α β) t)
    (hY₂ : ∀ t ∈ Icc α β, HasDerivWithinAt Y₂ (A t (Y₂ t)) (Icc α β) t)
    (ht₀ : t₀ ∈ Icc α β) (heq : Y₁ t₀ = Y₂ t₀) : EqOn Y₁ Y₂ (Icc α β) := by
  have hlip : ∀ t ∈ Icc α β, LipschitzOnWith K (fun y => A t y) (univ : Set E) := fun t ht =>
    ((A t).lipschitzWith_of_opNorm_le (hA t ht)).lipschitzOnWith
  have hright : EqOn Y₁ Y₂ (Icc t₀ β) := by
    have hsub : Icc t₀ β ⊆ Icc α β := Icc_subset_Icc_left ht₀.1
    have hder : ∀ Y : ℝ → E, (∀ t ∈ Icc α β, HasDerivWithinAt Y (A t (Y t)) (Icc α β) t) →
        ∀ t ∈ Ico t₀ β, HasDerivWithinAt Y (A t (Y t)) (Ici t) t := by
      intro Y hY t ht
      have htm : t ∈ Icc α β := hsub (Ico_subset_Icc_self ht)
      refine (hY t htm).mono_of_mem_nhdsWithin ?_
      exact mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left htm.1)
    exact ODE_solution_unique_of_mem_Icc_right (fun t ht => hlip t (hsub (Ico_subset_Icc_self ht)))
      (hY₁c.mono hsub) (hder Y₁ hY₁) (fun _ _ => mem_univ _)
      (hY₂c.mono hsub) (hder Y₂ hY₂) (fun _ _ => mem_univ _) heq
  have hleft : EqOn Y₁ Y₂ (Icc α t₀) := by
    have hsub : Icc α t₀ ⊆ Icc α β := Icc_subset_Icc_right ht₀.2
    have hder : ∀ Y : ℝ → E, (∀ t ∈ Icc α β, HasDerivWithinAt Y (A t (Y t)) (Icc α β) t) →
        ∀ t ∈ Ioc α t₀, HasDerivWithinAt Y (A t (Y t)) (Iic t) t := by
      intro Y hY t ht
      have htm : t ∈ Icc α β := hsub (Ioc_subset_Icc_self ht)
      refine (hY t htm).mono_of_mem_nhdsWithin ?_
      exact mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right htm.2)
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht => hlip t (hsub (Ioc_subset_Icc_self ht)))
      (hY₁c.mono hsub) (hder Y₁ hY₁) (fun _ _ => mem_univ _)
      (hY₂c.mono hsub) (hder Y₂ hY₂) (fun _ _ => mem_univ _) heq
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1, h⟩
  · exact hright ⟨h, ht.2⟩

/-- The derivative of a field of symmetric bilinear forms is symmetric in the last two slots. -/
theorem fderiv_apply_symm_of_eventually {b : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hb : DifferentiableAt ℝ b y) (hsymm : ∀ᶠ z in 𝓝 y, ∀ u v : E, b z u v = b z v u)
    (a u v : E) : fderiv ℝ b y a u v = fderiv ℝ b y a v u := by
  have hu : HasFDerivAt (fun z => b z u v) ((ContinuousLinearMap.apply ℝ ℝ v).comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u).comp (fderiv ℝ b y))) y :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u).hasFDerivAt.comp y hb.hasFDerivAt)
  have hv : HasFDerivAt (fun z => b z v u) ((ContinuousLinearMap.apply ℝ ℝ u).comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).comp (fderiv ℝ b y))) y :=
    (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).hasFDerivAt.comp y hb.hasFDerivAt)
  have heq : (fun z => b z u v) =ᶠ[𝓝 y] (fun z => b z v u) := by
    filter_upwards [hsymm] with z hz
    exact hz u v
  have h := (hu.congr_of_eventuallyEq heq.symm).unique hv
  exact congrArg (fun L : E →L[ℝ] ℝ => L a) h

variable [FiniteDimensional ℝ E]

local instance continuousDualEquivPTe : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPT : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePT : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Metric compatibility of the Koszul operator.** For a symmetric coercive `B` and a `D` symmetric in
its last two slots, `B (Γ u v) w + B v (Γ u w) = D u v w`, `Γ = raisedKoszulOp B D`. -/
theorem raisedKoszulOp_add_raisedKoszulOp_flip {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    (hBsymm : ∀ u v : E, B u v = B v u) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hDsymm : ∀ a u v : E, D a u v = D a v u) (u v w : E) :
    B (raisedKoszulOp B D u v) w + B v (raisedKoszulOp B D u w) = D u v w := by
  rw [hBsymm v, MetricKoszul.raisedKoszulOp_eq hB, MetricKoszul.raisedKoszulOp_eq hB,
    MetricKoszul.apply_koszul_vec, MetricKoszul.apply_koszul_vec, MetricKoszul.koszul_cov_apply,
    MetricKoszul.koszul_cov_apply, hDsymm u w v]
  ring

/-- **Euclidean transfer of the parallel ODE** along a `C²` change of coordinates `Φ` with `b = Φ^* c`:
if `W' = −Γ_b(x', W)` at `t` (within `s`), then `(dΦ_x W)' = −Γ_c((Φ x)', dΦ_x W)`. -/
theorem hasDerivWithinAt_fderiv_apply_of_pullback {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 1 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {x W : ℝ → E} {s : Set ℝ} {t : ℝ} {u : E} (hxU : x t ∈ U) (hx : HasDerivAt x u t)
    (hW : HasDerivWithinAt W (-(raisedKoszulOp (b (x t)) (fderiv ℝ b (x t)) u (W t))) s t) :
    HasDerivWithinAt (fun τ => fderiv ℝ Φ (x τ) (W τ))
      (-(raisedKoszulOp (c (Φ (x t))) (fderiv ℝ c (Φ (x t))) (fderiv ℝ Φ (x t) u)
        (fderiv ℝ Φ (x t) (W t)))) s t := by
  have hΦ2 : ContDiffAt ℝ 2 Φ (x t) := hΦ.contDiffAt (hU.mem_nhds hxU)
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (x t)) (x t) :=
    ((hΦ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDx : HasDerivAt (fun τ => fderiv ℝ Φ (x τ)) (fderiv ℝ (fderiv ℝ Φ) (x t) u) t :=
    hD.comp_hasDerivAt t hx
  have h := hDx.hasDerivWithinAt.clm_apply hW
  have hkey := DifferentialGeometry.Analysis.fderiv_fderiv_eq_raisedKoszulOp_of_pullback hU hV hc
    hcsymm hcco hΦ hΦUV hΦinv hpull hxU u (W t)
  convert h using 1
  rw [hkey, map_neg]
  abel

end Euclidean


section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The fibre coordinate of the tangent chart at `⟨q, 0⟩` is the derivative of the chart at `q`. -/
theorem extChartAt_tangent_zero_snd_eq_mfderiv (q : M) {x : M} (hx : x ∈ (chartAt H q).source)
    (v : E) :
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (⟨x, v⟩ : TangentBundle I M)).2 =
      mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v := by
  rw [TangentBundle.extChartAt_tangent_apply_snd (⟨q, 0⟩ : TangentBundle I M) (p := ⟨x, v⟩) hx,
    TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

omit [FiniteDimensional ℝ E] in
/-- `d(φ_q⁻¹) ∘ dφ_q = id` at a point of the chart source. -/
theorem mfderiv_extChartAt_symm_apply_mfderiv {q x : M} (hx : x ∈ (chartAt H q).source) (v : E) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) : E) = v := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := q)
    (y := x) (by rwa [extChartAt_source])
  rw [I.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h

omit [FiniteDimensional ℝ E] in
/-- `dφ_q ∘ d(φ_q⁻¹) = id` at a point of the chart target. -/
theorem mfderiv_extChartAt_apply_mfderiv_symm {q : M} {y : E} (hy : y ∈ (extChartAt I q).target)
    (w : E) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I q) ((extChartAt I q).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y w) : E) = w := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := q) hy
  rw [I.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L : E →L[ℝ] E => L w) h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The source of a chart transition is open. -/
theorem isOpen_transition_source (q₁ q₂ : M) :
    IsOpen ((extChartAt I q₁).symm ≫ extChartAt I q₂).source := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  exact (continuousOn_extChartAt_symm q₁).isOpen_inter_preimage (isOpen_extChartAt_target q₁)
    (isOpen_extChartAt_source q₂)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem mem_transition_source {q₁ q₂ x : M} (h₁ : x ∈ (chartAt H q₁).source)
    (h₂ : x ∈ (chartAt H q₂).source) :
    extChartAt I q₁ x ∈ ((extChartAt I q₁).symm ≫ extChartAt I q₂).source := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  refine ⟨(extChartAt I q₁).map_source (by rwa [extChartAt_source]), ?_⟩
  change (extChartAt I q₁).symm (extChartAt I q₁ x) ∈ (extChartAt I q₂).source
  rw [(extChartAt I q₁).left_inv (by rwa [extChartAt_source]), extChartAt_source]
  exact h₂

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The chart transition is smooth on its source. -/
theorem contDiffOn_transition (q₁ q₂ : M) {m : ℕ∞} :
    ContDiffOn ℝ m (extChartAt I q₂ ∘ (extChartAt I q₁).symm)
      ((extChartAt I q₁).symm ≫ extChartAt I q₂).source :=
  (contDiffOn_ext_coord_change (I := I) (n := ∞) q₂ q₁).of_le (by exact_mod_cast le_top)

omit [FiniteDimensional ℝ E] in
/-- **Chart transition of the tangent chart:** `dφ_{q₂} = dT ∘ dφ_{q₁}`, `T = φ_{q₂} ∘ φ_{q₁}⁻¹`. -/
theorem mfderiv_extChartAt_eq_fderiv_transition {q₁ q₂ x : M} (h₁ : x ∈ (chartAt H q₁).source)
    (h₂ : x ∈ (chartAt H q₂).source) (v : E) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I q₂) x v : E) =
      fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) (extChartAt I q₁ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q₁) x v) := by
  set T := extChartAt I q₂ ∘ (extChartAt I q₁).symm
  have hT : DifferentiableAt ℝ T (extChartAt I q₁ x) :=
    ((contDiffOn_transition (I := I) q₁ q₂ (m := 1)).contDiffAt
      ((isOpen_transition_source q₁ q₂).mem_nhds (mem_transition_source h₁ h₂))).differentiableAt
      (by norm_num)
  have heq : (T ∘ extChartAt I q₁) =ᶠ[𝓝 x] extChartAt I q₂ := by
    filter_upwards [(isOpen_extChartAt_source (I := I) q₁).mem_nhds
      (by rwa [extChartAt_source])] with y hy
    exact congrArg (extChartAt I q₂) ((extChartAt I q₁).left_inv hy)
  have hcomp := mfderiv_comp x hT.mdifferentiableAt
    (mdifferentiableAt_extChartAt (I := I) h₁)
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] E => L v) hcomp

omit [FiniteDimensional ℝ E] in
/-- The derivative of a chart transition is `dφ_{q₂} ∘ d(φ_{q₁}⁻¹)`. -/
theorem fderiv_transition_apply {q₁ q₂ : M} {y : E}
    (hy : y ∈ ((extChartAt I q₁).symm ≫ extChartAt I q₂).source) (w : E) :
    fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) y w =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q₂) ((extChartAt I q₁).symm y)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I q₁).symm y w) : E) := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source] at hy
  have h₁ : (extChartAt I q₁).symm y ∈ (chartAt H q₁).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I q₁).map_target hy.1
  have h₂ : (extChartAt I q₁).symm y ∈ (chartAt H q₂).source := by
    rw [← extChartAt_source (I := I)]; exact hy.2
  have hy' : extChartAt I q₁ ((extChartAt I q₁).symm y) = y := (extChartAt I q₁).right_inv hy.1
  rw [mfderiv_extChartAt_eq_fderiv_transition (I := I) h₁ h₂
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q₁).symm y w),
    mfderiv_extChartAt_apply_mfderiv_symm hy.1, hy']

omit [FiniteDimensional ℝ E] in
/-- The derivative of a chart transition is invertible on its source. -/
theorem isInvertible_fderiv_transition {q₁ q₂ : M} {y : E}
    (hy : y ∈ ((extChartAt I q₁).symm ≫ extChartAt I q₂).source) :
    (fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) y).IsInvertible := by
  have hy' := hy
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source] at hy'
  let A : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I q₂) ((extChartAt I q₁).symm y)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (extChartAt I q₁).symm y
  have hA : A.IsInvertible := isInvertible_mfderiv_extChartAt (I := I) hy'.2
  have hB : B.IsInvertible := by
    have h1 := isInvertible_mfderivWithin_extChartAt_symm (I := I) hy'.1
    rw [I.range_eq_univ, mfderivWithin_univ] at h1
    exact h1
  have heq : fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) y = A.comp B :=
    ContinuousLinearMap.ext fun w => fderiv_transition_apply hy w
  rw [heq]
  exact hA.comp hB

omit [FiniteDimensional ℝ E] in
/-- The metric read in the chart at `q`. -/
theorem inner_eq_chartCoeffFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {q x : M}
    (hx : x ∈ (chartAt H q).source) (v w : E) :
    g.inner x v w = chartCoeffFinite g q (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w) := by
  have hl : (extChartAt I q).symm (extChartAt I q x) = x :=
    (extChartAt I q).left_inv (by rwa [extChartAt_source])
  change g.inner x v w = g.inner ((extChartAt I q).symm (extChartAt I q x))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x w))
  rw [mfderiv_extChartAt_symm_apply_mfderiv hx, mfderiv_extChartAt_symm_apply_mfderiv hx, hl]

omit [FiniteDimensional ℝ E] in
/-- **Chart transition of the coefficients:** `b_{q₁} = T^* b_{q₂}`. -/
theorem chartCoeffFinite_transition {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {q₁ q₂ : M} {y : E}
    (hy : y ∈ ((extChartAt I q₁).symm ≫ extChartAt I q₂).source) (u v : E) :
    chartCoeffFinite g q₁ y u v =
      chartCoeffFinite g q₂ ((extChartAt I q₂ ∘ (extChartAt I q₁).symm) y)
        (fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) y u)
        (fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm) y v) := by
  have hy' := hy
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source] at hy'
  have h₂ : (extChartAt I q₁).symm y ∈ (chartAt H q₂).source := by
    rw [← extChartAt_source (I := I)]; exact hy'.2
  rw [fderiv_transition_apply hy, fderiv_transition_apply hy]
  calc chartCoeffFinite g q₁ y u v
      = g.inner ((extChartAt I q₁).symm y) (mfderiv 𝓘(ℝ, E) I (extChartAt I q₁).symm y u)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I q₁).symm y v) := rfl
    _ = _ := inner_eq_chartCoeffFinite g h₂ _ _

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The chart coefficients are symmetric. -/
theorem chartCoeffFinite_symm {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (q : M) (y u v : E) :
    chartCoeffFinite g q y u v = chartCoeffFinite g q y v u := by
  change g.inner ((extChartAt I q).symm y) (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y u)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y v) =
    g.inner ((extChartAt I q).symm y) (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y v)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y u)
  exact g.symm _ _ _

/-- The chart coefficients are coercive on the chart target. -/
theorem isCoercive_chartCoeffFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {q : M} {y : E}
    (hy : y ∈ (extChartAt I q).target) : IsCoercive (chartCoeffFinite g q y) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  change 0 < g.inner ((extChartAt I q).symm y) (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y v)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y v)
  apply g.pos
  intro hzero
  apply hv
  have h := mfderiv_extChartAt_apply_mfderiv_symm (I := I) hy v
  rw [← h]
  exact (congrArg (mfderiv I 𝓘(ℝ, E) (extChartAt I q) ((extChartAt I q).symm y)) hzero).trans
    (map_zero _)

omit [FiniteDimensional ℝ E] in
/-- The chart coefficients of a `C^n` metric are `C^m` on the chart target (`m ≤ n`). -/
theorem contDiffOn_chartCoeffFinite {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    (hm : m + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω)) (q : M) :
    ContDiffOn ℝ m (chartCoeffFinite g q) (extChartAt I q).target :=
  g.contDiffOn_pullback_inner hmn hm (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm q)

local instance continuousDualEquivPTc : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTc : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTc : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] in
/-- The Christoffel operator of `g` in the extended chart at `q`: `Γ_q y = raisedKoszulOp (b y) (db y)`,
`b = chartCoeffFinite g q` (first slot = velocity, `IsParallelAlongFinite` reads `V' = −Γ_q(c', V)`). -/
def chartChristoffelFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (q : M) (y : E) :
    E →L[ℝ] E →L[ℝ] E :=
  raisedKoszulOp (chartCoeffFinite g q y) (fderiv ℝ (chartCoeffFinite g q) y)

end Chart

section Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

local instance continuousDualEquivPTg : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTg : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTg : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- A geodesic defined for all times is continuous in `TM`. -/
theorem continuous_geodesicFlow_of_forall_mem (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) :
    Continuous fun t => g.geodesicFlow p t := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hin : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
    contMDiff_const.prodMk contMDiff_id
  exact (((g.contMDiffOn_geodesicFlow hr).contMDiffAt
    ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hdom t))).comp t
    ((hin t).of_le (by exact_mod_cast le_top))).continuousAt

omit [I.Boundaryless] [T2Space M] in
/-- The chart velocity of a geodesic is the chart image of its velocity. -/
theorem extChartAt_tangent_geodesicFlow_snd_eq
    {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) (t : ℝ) {q : M}
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q).source) :
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 =
      mfderiv I 𝓘(ℝ, E) (extChartAt I q) (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd :=
  extChartAt_tangent_zero_snd_eq_mfderiv q hq _

/-- **Geodesic chart equation, first order:** the chart curve has derivative the chart velocity. -/
theorem hasDerivAt_extChartAt_geodesicFlow (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} {t : ℝ} (ht : (p, t) ∈ g.geodesicFlowDomain) {q : M}
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q).source) :
    HasDerivAt (fun τ => extChartAt I q (g.geodesicFlow p τ).proj)
      (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 t := by
  have h := g.hasDerivAt_geodesicFlow_chart hr ht (⟨q, 0⟩ : TangentBundle I M) hq
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E)
    (p := extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t))).comp_hasDerivAt t h
  have hfun : (Prod.fst ∘ fun τ => extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
      (g.geodesicFlow p τ)) = fun τ => extChartAt I q (g.geodesicFlow p τ).proj :=
    funext fun τ => TangentBundle.extChartAt_tangent_apply_fst (⟨q, 0⟩ : TangentBundle I M)
  rw [hfun] at h1
  exact h1

/-- **Geodesic chart equation, second order:** `u' = −Γ_q(x)(u, u)` for the chart velocity `u`. -/
theorem hasDerivAt_extChartAt_tangent_geodesicFlow (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} {t : ℝ} (ht : (p, t) ∈ g.geodesicFlowDomain) {q : M}
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q).source) :
    HasDerivAt (fun τ => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p τ)).2)
      (-(chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t).proj)
        (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
        (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2)) t := by
  have h := g.hasDerivAt_geodesicFlow_chart hr ht (⟨q, 0⟩ : TangentBundle I M) hq
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E)
    (p := extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t))).comp_hasDerivAt t h
  have hz : (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).1 =
      extChartAt I q (g.geodesicFlow p t).proj :=
    TangentBundle.extChartAt_tangent_apply_fst (⟨q, 0⟩ : TangentBundle I M)
  change HasDerivAt _ (-(chartChristoffelFinite g q
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).1
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2)) t at h2
  rw [hz] at h2
  exact h2

omit [I.Boundaryless] [T2Space M] in
/-- On a subsingleton every field is parallel. -/
theorem isParallelAlongFinite_of_subsingleton {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (c : ℝ → M) (V : ℝ → E)
    {s : Set ℝ} (hs : s.Subsingleton) : IsParallelAlongFinite g c V s :=
  fun _ _ _ _ => HasFDerivWithinAt.of_subsingleton hs

/-- **Frozen form = velocity form** along a geodesic, on a set with unique derivatives: the
`derivWithin` of the chart curve is the chart velocity. -/
theorem isParallelAlongFinite_geodesicFlow_iff (hr : 1 ≤ r)
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} {s : Set ℝ} (hdom : ∀ t ∈ s, (p, t) ∈ g.geodesicFlowDomain)
    (hs : ∀ t ∈ s, UniqueDiffWithinAt ℝ s t) {V : ℝ → E} :
    IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) V s ↔
      ∀ t ∈ s, ∀ q : M, (g.geodesicFlow p t).proj ∈ (chartAt H q).source →
        HasDerivWithinAt (fun τ => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
            (⟨(g.geodesicFlow p τ).proj, V τ⟩ : TangentBundle I M)).2)
          (-(chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t).proj)
            (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
            (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
              (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)).2)) s t := by
  refine forall₂_congr fun t ht => forall₂_congr fun q hq => ?_
  rw [((hasDerivAt_extChartAt_geodesicFlow hr g (hdom t ht) hq).hasDerivWithinAt).derivWithin
    (hs t ht)]
  rfl

/-- **Transfer of the parallel ODE between charts** along a geodesic defined for all times. -/
theorem hasDerivWithinAt_chart_of_chart (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V : ℝ → E}
    {s : Set ℝ} {t : ℝ} {q₁ q₂ : M} (h₁ : (g.geodesicFlow p t).proj ∈ (chartAt H q₁).source)
    (h₂ : (g.geodesicFlow p t).proj ∈ (chartAt H q₂).source)
    (h : HasDerivWithinAt (fun τ => (extChartAt I.tangent (⟨q₁, 0⟩ : TangentBundle I M)
            (⟨(g.geodesicFlow p τ).proj, V τ⟩ : TangentBundle I M)).2)
          (-(chartChristoffelFinite g q₁ (extChartAt I q₁ (g.geodesicFlow p t).proj)
            (extChartAt I.tangent (⟨q₁, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
            (extChartAt I.tangent (⟨q₁, 0⟩ : TangentBundle I M)
              (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)).2)) s t) :
    HasDerivWithinAt (fun τ => (extChartAt I.tangent (⟨q₂, 0⟩ : TangentBundle I M)
            (⟨(g.geodesicFlow p τ).proj, V τ⟩ : TangentBundle I M)).2)
          (-(chartChristoffelFinite g q₂ (extChartAt I q₂ (g.geodesicFlow p t).proj)
            (extChartAt I.tangent (⟨q₂, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
            (extChartAt I.tangent (⟨q₂, 0⟩ : TangentBundle I M)
              (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)).2)) s t := by
  set c : ℝ → M := fun τ => (g.geodesicFlow p τ).proj with hc
  have hcont : Continuous c :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  set T : E → E := extChartAt I q₂ ∘ (extChartAt I q₁).symm with hT
  have hev : ∀ᶠ τ in 𝓝 t, c τ ∈ (chartAt H q₁).source ∧ c τ ∈ (chartAt H q₂).source :=
    (hcont.continuousAt.eventually ((chartAt H q₁).open_source.mem_nhds h₁)).and
      (hcont.continuousAt.eventually ((chartAt H q₂).open_source.mem_nhds h₂))
  have hW : ∀ τ, c τ ∈ (chartAt H q₁).source → c τ ∈ (chartAt H q₂).source →
      (extChartAt I.tangent (⟨q₂, 0⟩ : TangentBundle I M) (⟨c τ, V τ⟩ : TangentBundle I M)).2 =
        fderiv ℝ T (extChartAt I q₁ (c τ))
          (extChartAt I.tangent (⟨q₁, 0⟩ : TangentBundle I M) (⟨c τ, V τ⟩ : TangentBundle I M)).2 := by
    intro τ hτ₁ hτ₂
    rw [extChartAt_tangent_zero_snd_eq_mfderiv q₂ hτ₂, extChartAt_tangent_zero_snd_eq_mfderiv q₁ hτ₁]
    exact mfderiv_extChartAt_eq_fderiv_transition hτ₁ hτ₂ (V τ)
  have hmem : extChartAt I q₁ (c t) ∈ ((extChartAt I q₁).symm ≫ extChartAt I q₂).source :=
    mem_transition_source h₁ h₂
  have hmaps : MapsTo T ((extChartAt I q₁).symm ≫ extChartAt I q₂).source
      (extChartAt I q₂).target := by
    intro y hy
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source] at hy
    exact (extChartAt I q₂).map_source hy.2
  have key := hasDerivWithinAt_fderiv_apply_of_pullback (isOpen_transition_source q₁ q₂)
    (isOpen_extChartAt_target q₂) (b := chartCoeffFinite g q₁) (c := chartCoeffFinite g q₂)
    (Φ := T)
    (contDiffOn_chartCoeffFinite g (m := 1) (by exact_mod_cast le_add_self) (by norm_num) q₂)
    (fun z _ u v => chartCoeffFinite_symm g q₂ z u v)
    (fun z hz => isCoercive_chartCoeffFinite g hz) (contDiffOn_transition q₁ q₂) hmaps
    (fun y hy => isInvertible_fderiv_transition hy)
    (fun y hy u v => chartCoeffFinite_transition g hy u v)
    (x := fun τ => extChartAt I q₁ (c τ)) hmem
    (hasDerivAt_extChartAt_geodesicFlow hr g (hdom t) h₁) h
  have e1 : T (extChartAt I q₁ (c t)) = extChartAt I q₂ (c t) :=
    congrArg (extChartAt I q₂) ((extChartAt I q₁).left_inv (by rwa [extChartAt_source]))
  have e2 : fderiv ℝ T (extChartAt I q₁ (c t))
      (extChartAt I.tangent (⟨q₁, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 =
      (extChartAt I.tangent (⟨q₂, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 := by
    rw [extChartAt_tangent_geodesicFlow_snd_eq g p t h₁,
      extChartAt_tangent_geodesicFlow_snd_eq g p t h₂]
    exact (mfderiv_extChartAt_eq_fderiv_transition h₁ h₂ _).symm
  have e3 := (hW t h₁ h₂).symm
  rw [e2, e3, e1] at key
  refine key.congr_of_eventuallyEq ?_ (hW t h₁ h₂)
  filter_upwards [nhdsWithin_le_nhds hev] with τ hτ
  exact hW τ hτ.1 hτ.2

/-- **One chart per time suffices:** if at every time of `s` the parallel ODE holds in SOME chart, it
holds in every chart, i.e. the field is parallel (sets with unique derivatives). -/
theorem isParallelAlongFinite_of_forall_exists_chart (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V : ℝ → E}
    {s : Set ℝ} (hs : ∀ t ∈ s, UniqueDiffWithinAt ℝ s t)
    (h : ∀ t ∈ s, ∃ q : M, (g.geodesicFlow p t).proj ∈ (chartAt H q).source ∧
      HasDerivWithinAt (fun τ => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
            (⟨(g.geodesicFlow p τ).proj, V τ⟩ : TangentBundle I M)).2)
          (-(chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t).proj)
            (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2
            (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
              (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)).2)) s t) :
    IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) V s := by
  rw [isParallelAlongFinite_geodesicFlow_iff hr (fun t _ => hdom t) hs]
  intro t ht q₂ h₂
  obtain ⟨q₁, h₁, hq₁⟩ := h t ht
  exact hasDerivWithinAt_chart_of_chart hr g hdom h₁ h₂ hq₁

end Geodesic

end DifferentialGeometry.Geometry.FiniteSoul
