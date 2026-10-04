import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.GlobalExistence

/-!
# Finite-order parallel transport along geodesics: S3-PT.a (lane CMS3-PT, group G2)

Along a geodesic `c t = π φ_t p` defined for all times, the chart representative
`chartRepFinite g p q V` of a field `V` solves the linear ODE `W' = parallelCoeffFinite g p q t W`
(`= −Γ_q(c', W)`). We prove
* chart-local existence (tree linear-ODE theory, `hasLinearODESolution_of_continuousOn`),
* uniqueness on every `Icc` (Grönwall in charts + connectedness),
* existence on every `Icc (-R) R` (Lebesgue number + chart extension),
* the transport `P t`, its linearity, isometry (metric compatibility of the Koszul operator) and
  `P t γ'(0) = γ'(t)`,
and the frozen statement `exists_parallelTransport_geodesicFlow` (S3-PT.a).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)

section TransportDefs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

local instance continuousDualEquivPTt : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTt : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTt : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] [T2Space M] in
/-- The chart representative (chart at `q`) of a field `V` along `t ↦ π φ_t p`. -/
def chartRepFinite {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) (q : M) (V : ℝ → E) (τ : ℝ) : E :=
  (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
    (⟨(g.geodesicFlow p τ).proj, V τ⟩ : TangentBundle I M)).2

omit [I.Boundaryless] [T2Space M] in
/-- The coefficient `−Γ_q(c', ·)` of the parallel ODE along `t ↦ π φ_t p` in the chart at `q`. -/
def parallelCoeffFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) (q : M) (τ : ℝ) : E →L[ℝ] E :=
  -(chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p τ).proj)
    (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p τ)).2)

end TransportDefs

/-- The parallel ODE in every chart, on a set `s` of times (velocity form); `H` is the model space. -/
local macro "PVF[" H:term ", " g:term ", " p:term ", " V:term ", " s:term "]" : term =>
  `(∀ t ∈ $s, ∀ q, (Bundle.ContMDiffRiemannianMetric.geodesicFlow $g $p t).proj ∈
    (chartAt $H q).source →
    HasDerivWithinAt (DifferentialGeometry.Geometry.FiniteSoul.chartRepFinite $g $p q $V)
      (DifferentialGeometry.Geometry.FiniteSoul.parallelCoeffFinite $g $p q t
        (DifferentialGeometry.Geometry.FiniteSoul.chartRepFinite $g $p q $V t)) $s t)

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

local instance continuousDualEquivPTt2 : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTt2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTt2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] [T2Space M] in
theorem chartRepFinite_eq_mfderiv {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    {q : M} (V : ℝ → E) {τ : ℝ} (hq : (g.geodesicFlow p τ).proj ∈ (chartAt H q).source) :
    chartRepFinite g p q V τ =
      mfderiv I 𝓘(ℝ, E) (extChartAt I q) (g.geodesicFlow p τ).proj (V τ) :=
  extChartAt_tangent_zero_snd_eq_mfderiv q hq (V τ)

omit [T2Space M] in
/-- The chart representative determines the field. -/
theorem eq_of_chartRepFinite_eq {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    {q : M} {V₁ V₂ : ℝ → E} {τ : ℝ} (hq : (g.geodesicFlow p τ).proj ∈ (chartAt H q).source)
    (h : chartRepFinite g p q V₁ τ = chartRepFinite g p q V₂ τ) : V₁ τ = V₂ τ := by
  rw [chartRepFinite_eq_mfderiv g p V₁ hq, chartRepFinite_eq_mfderiv g p V₂ hq] at h
  have e1 := mfderiv_extChartAt_symm_apply_mfderiv (I := I) hq (V₁ τ)
  have e2 := mfderiv_extChartAt_symm_apply_mfderiv (I := I) hq (V₂ τ)
  rw [h] at e1
  exact e1.symm.trans e2

omit [I.Boundaryless] [T2Space M] in
theorem chartRepFinite_congr {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (q : M) {V₁ V₂ : ℝ → E} {τ : ℝ} (h : V₁ τ = V₂ τ) :
    chartRepFinite g p q V₁ τ = chartRepFinite g p q V₂ τ := by
  unfold chartRepFinite
  rw [h]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- `dφ_q ∘ d(φ_q⁻¹) = id`, base point in the chart source. -/
theorem mfderiv_extChartAt_apply_mfderiv_symm_of_mem {q x : M} (hx : x ∈ (chartAt H q).source)
    (w : E) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q x) w) : E) = w := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) (x := q) (y := x)
    (by rwa [extChartAt_source])
  rw [I.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L : E →L[ℝ] E => L w) h

omit [T2Space M] in
/-- Chart transition of chart representatives along the geodesic. -/
theorem chartRepFinite_transition {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    {q₁ q₂ : M} (V : ℝ → E) {τ : ℝ} (h₁ : (g.geodesicFlow p τ).proj ∈ (chartAt H q₁).source)
    (h₂ : (g.geodesicFlow p τ).proj ∈ (chartAt H q₂).source) :
    chartRepFinite g p q₂ V τ = fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm)
      (extChartAt I q₁ (g.geodesicFlow p τ).proj) (chartRepFinite g p q₁ V τ) := by
  rw [chartRepFinite_eq_mfderiv g p V h₂, chartRepFinite_eq_mfderiv g p V h₁]
  exact mfderiv_extChartAt_eq_fderiv_transition h₁ h₂ (V τ)

/-- Continuity of chart representatives does not depend on the chart. -/
theorem continuousWithinAt_chartRepFinite_of_chart (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V : ℝ → E}
    {s : Set ℝ} {τ : ℝ} {q₁ q₂ : M} (h₁ : (g.geodesicFlow p τ).proj ∈ (chartAt H q₁).source)
    (h₂ : (g.geodesicFlow p τ).proj ∈ (chartAt H q₂).source)
    (h : ContinuousWithinAt (chartRepFinite g p q₁ V) s τ) :
    ContinuousWithinAt (chartRepFinite g p q₂ V) s τ := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  have hev : ∀ᶠ σ in 𝓝 τ, (g.geodesicFlow p σ).proj ∈ (chartAt H q₁).source ∧
      (g.geodesicFlow p σ).proj ∈ (chartAt H q₂).source :=
    (hcont.continuousAt.eventually ((chartAt H q₁).open_source.mem_nhds h₁)).and
      (hcont.continuousAt.eventually ((chartAt H q₂).open_source.mem_nhds h₂))
  have hx : ContinuousAt (fun σ => extChartAt I q₁ (g.geodesicFlow p σ).proj) τ :=
    (continuousAt_extChartAt' (I := I) (by rwa [extChartAt_source])).comp hcont.continuousAt
  have hD : ContinuousOn (fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm))
      ((extChartAt I q₁).symm ≫ extChartAt I q₂).source :=
    (contDiffOn_transition (I := I) q₁ q₂ (m := 1)).continuousOn_fderiv_of_isOpen
      (isOpen_transition_source q₁ q₂) le_rfl
  have hDx : ContinuousAt (fun σ => fderiv ℝ (extChartAt I q₂ ∘ (extChartAt I q₁).symm)
      (extChartAt I q₁ (g.geodesicFlow p σ).proj)) τ :=
    ContinuousAt.comp (f := fun σ => extChartAt I q₁ (g.geodesicFlow p σ).proj)
      (hD.continuousAt ((isOpen_transition_source q₁ q₂).mem_nhds
        (mem_transition_source h₁ h₂))) hx
  refine (hDx.continuousWithinAt.clm_apply h).congr_of_eventuallyEq ?_
    (chartRepFinite_transition g p V h₁ h₂)
  filter_upwards [nhdsWithin_le_nhds hev] with σ hσ
  exact chartRepFinite_transition g p V hσ.1 hσ.2

/-- **Continuity in `TM` = continuity of a chart representative.** -/
theorem continuousWithinAt_iff_chartRepFinite (hr : 1 ≤ r)
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V : ℝ → E}
    {s : Set ℝ} {τ : ℝ} {q : M} (hq : (g.geodesicFlow p τ).proj ∈ (chartAt H q).source) :
    ContinuousWithinAt (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) s τ ↔
      ContinuousWithinAt (chartRepFinite g p q V) s τ := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  set x₀ := (g.geodesicFlow p τ).proj with hx₀
  have hself : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hfib : ∀ σ, (g.geodesicFlow p σ).proj ∈ (chartAt H x₀).source →
      (trivializationAt E (TangentSpace I) x₀
        (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)).2 = chartRepFinite g p x₀ V σ := by
    intro σ hσ
    have h := TangentBundle.extChartAt_tangent_zero_apply_chartFiber (I := I) x₀
      (p := (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) hσ
    exact (congrArg Prod.snd h).symm
  have hev : ∀ᶠ σ in 𝓝[s] τ, (trivializationAt E (TangentSpace I) x₀
      (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)).2 = chartRepFinite g p x₀ V σ := by
    filter_upwards [nhdsWithin_le_nhds
      (hcont.continuousAt.eventually ((chartAt H x₀).open_source.mem_nhds hself))] with σ hσ
    exact hfib σ hσ
  have h0 := hfib τ hself
  rw [FiberBundle.continuousWithinAt_totalSpace]
  constructor
  · rintro ⟨-, h⟩
    exact continuousWithinAt_chartRepFinite_of_chart hr g hdom hself hq
      (h.congr_of_eventuallyEq (hev.mono fun σ hσ => hσ.symm) h0.symm)
  · intro h
    refine ⟨hcont.continuousWithinAt, ?_⟩
    exact (continuousWithinAt_chartRepFinite_of_chart hr g hdom hq hself h).congr_of_eventuallyEq
      hev h0

omit [I.Boundaryless] [T2Space M] in
theorem pvf_mono {n : ℕ∞ω} {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} {V : ℝ → E} {s s' : Set ℝ} (h : PVF[H, g, p, V, s]) (hs : s' ⊆ s) :
    PVF[H, g, p, V, s'] :=
  fun t ht q hq => (h t (hs ht) q hq).mono hs

omit [I.Boundaryless] [T2Space M] in
theorem pvf_congr {n : ℕ∞ω} {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} {V V' : ℝ → E} {s : Set ℝ} (h : PVF[H, g, p, V, s])
    (heq : EqOn V' V s) : PVF[H, g, p, V', s] := by
  intro t ht q hq
  have h0 : chartRepFinite g p q V' t = chartRepFinite g p q V t := chartRepFinite_congr g p q (heq ht)
  rw [h0]
  exact (h t ht q hq).congr_of_eventuallyEq
    (eventuallyEq_nhdsWithin_of_eqOn fun σ hσ => chartRepFinite_congr g p q (heq hσ)) h0

omit [I.Boundaryless] [T2Space M] in
theorem pvf_union {n : ℕ∞ω} {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} {V : ℝ → E} {s₁ s₂ : Set ℝ} (h₁ : PVF[H, g, p, V, s₁])
    (h₂ : PVF[H, g, p, V, s₂]) (hs₁ : IsClosed s₁) (hs₂ : IsClosed s₂) :
    PVF[H, g, p, V, s₁ ∪ s₂] := by
  intro t ht q hq
  have k₁ : HasDerivWithinAt (chartRepFinite g p q V)
      (parallelCoeffFinite g p q t (chartRepFinite g p q V t)) s₁ t := by
    by_cases hts : t ∈ s₁
    · exact h₁ t hts q hq
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hs₁.closure_eq])
  have k₂ : HasDerivWithinAt (chartRepFinite g p q V)
      (parallelCoeffFinite g p q t (chartRepFinite g p q V t)) s₂ t := by
    by_cases hts : t ∈ s₂
    · exact h₂ t hts q hq
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hs₂.closure_eq])
  exact k₁.union k₂

omit [I.Boundaryless] [T2Space M] in
/-- On a degenerate set every field satisfies the velocity form. -/
theorem pvf_of_subsingleton {n : ℕ∞ω}
    {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} {V : ℝ → E} {s : Set ℝ} (hs : s.Subsingleton) : PVF[H, g, p, V, s] :=
  fun _ _ _ _ => HasFDerivWithinAt.of_subsingleton hs

/-- Linear combinations of solutions are solutions. -/
theorem pvf_linear (hr : 1 ≤ r)
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V₁ V₂ : ℝ → E}
    {s : Set ℝ} (h₁ : PVF[H, g, p, V₁, s]) (h₂ : PVF[H, g, p, V₂, s]) (a : ℝ) :
    PVF[H, g, p, fun σ => a • V₁ σ + V₂ σ, s] := by
  intro t ht q hq
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  have hlin : ∀ σ, (g.geodesicFlow p σ).proj ∈ (chartAt H q).source →
      chartRepFinite g p q (fun σ => a • V₁ σ + V₂ σ) σ =
        a • chartRepFinite g p q V₁ σ + chartRepFinite g p q V₂ σ := by
    intro σ hσ
    rw [chartRepFinite_eq_mfderiv g p _ hσ, chartRepFinite_eq_mfderiv g p V₁ hσ,
      chartRepFinite_eq_mfderiv g p V₂ hσ]
    exact ((mfderiv I 𝓘(ℝ, E) (extChartAt I q) (g.geodesicFlow p σ).proj).map_add _ _).trans
      (congrArg (· + _) ((mfderiv I 𝓘(ℝ, E) (extChartAt I q) (g.geodesicFlow p σ).proj).map_smul
        a (V₁ σ)))
  have hev : ∀ᶠ σ in 𝓝[s] t, chartRepFinite g p q (fun σ => a • V₁ σ + V₂ σ) σ =
      a • chartRepFinite g p q V₁ σ + chartRepFinite g p q V₂ σ := by
    filter_upwards [nhdsWithin_le_nhds
      (hcont.continuousAt.eventually ((chartAt H q).open_source.mem_nhds hq))] with σ hσ
    exact hlin σ hσ
  rw [hlin t hq, map_add, map_smul]
  exact (((h₁ t ht q hq).const_smul a).add (h₂ t ht q hq)).congr_of_eventuallyEq hev (hlin t hq)

/-- Continuity of linear combinations of fields along the geodesic. -/
theorem continuousOn_linear (hr : 1 ≤ r)
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V₁ V₂ : ℝ → E}
    {s : Set ℝ}
    (h₁ : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V₁ σ⟩ : TangentBundle I M)) s)
    (h₂ : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V₂ σ⟩ : TangentBundle I M)) s)
    (a : ℝ) :
    ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, a • V₁ σ + V₂ σ⟩ : TangentBundle I M)) s := by
  intro t ht
  set x₀ := (g.geodesicFlow p t).proj
  have hself : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  have k₁ := (continuousWithinAt_iff_chartRepFinite hr hdom (V := V₁) (s := s) hself).1 (h₁ t ht)
  have k₂ := (continuousWithinAt_iff_chartRepFinite hr hdom (V := V₂) (s := s) hself).1 (h₂ t ht)
  refine (continuousWithinAt_iff_chartRepFinite hr hdom (V := fun σ => a • V₁ σ + V₂ σ)
    (s := s) hself).2 ?_
  have hlin : ∀ σ, (g.geodesicFlow p σ).proj ∈ (chartAt H x₀).source →
      chartRepFinite g p x₀ (fun σ => a • V₁ σ + V₂ σ) σ =
        a • chartRepFinite g p x₀ V₁ σ + chartRepFinite g p x₀ V₂ σ := by
    intro σ hσ
    rw [chartRepFinite_eq_mfderiv g p _ hσ, chartRepFinite_eq_mfderiv g p V₁ hσ,
      chartRepFinite_eq_mfderiv g p V₂ hσ]
    exact ((mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p σ).proj).map_add _ _).trans
      (congrArg (· + _) ((mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p σ).proj).map_smul
        a (V₁ σ)))
  refine ((k₁.const_smul a).add k₂).congr_of_eventuallyEq ?_ (hlin t hself)
  filter_upwards [nhdsWithin_le_nhds
    (hcont.continuousAt.eventually ((chartAt H x₀).open_source.mem_nhds hself))] with σ hσ
  exact hlin σ hσ

/-- The coefficient of the parallel ODE is continuous where the geodesic lies in the chart. -/
theorem continuousAt_parallelCoeffFinite (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {q : M} {τ : ℝ}
    (hq : (g.geodesicFlow p τ).proj ∈ (chartAt H q).source) :
    ContinuousAt (parallelCoeffFinite g p q) τ := by
  have hflow := continuous_geodesicFlow_of_forall_mem hr g hdom
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp hflow
  have hΓ : ContinuousOn (chartChristoffelFinite g q) (extChartAt I q).target :=
    (MetricKoszul.raisedOp_contDiffOn_succ (n := 0) (isOpen_extChartAt_target q)
      (contDiffOn_chartCoeffFinite g (m := 0 + 1) (by exact_mod_cast le_add_self) (by norm_num) q)
      (fun y hy => isCoercive_chartCoeffFinite g hy)).continuousOn
  have hxsrc : (g.geodesicFlow p τ).proj ∈ (extChartAt I q).source := by
    rwa [extChartAt_source]
  have hx : ContinuousAt (fun σ => extChartAt I q (g.geodesicFlow p σ).proj) τ :=
    ContinuousAt.comp (f := fun σ => (g.geodesicFlow p σ).proj)
      (continuousAt_extChartAt' (I := I) hxsrc) hcont.continuousAt
  have hΓx : ContinuousAt (fun σ => chartChristoffelFinite g q
      (extChartAt I q (g.geodesicFlow p σ).proj)) τ :=
    ContinuousAt.comp (f := fun σ => extChartAt I q (g.geodesicFlow p σ).proj)
      (hΓ.continuousAt ((isOpen_extChartAt_target q).mem_nhds
        ((extChartAt I q).map_source hxsrc))) hx
  have hTsrc : g.geodesicFlow p τ ∈ (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact hq
  have hu : ContinuousAt (fun σ =>
      (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p σ)).2) τ :=
    continuous_snd.continuousAt.comp
      ((continuousAt_extChartAt' (I := I.tangent) hTsrc).comp hflow.continuousAt)
  exact (hΓx.clm_apply hu).neg

/-- **Chart-local existence** for the parallel ODE along the geodesic. -/
theorem exists_chart_parallel (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {q : M}
    {α β t₁ : ℝ} (hsrc : ∀ τ ∈ Ioo α β, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source)
    (ht₁ : t₁ ∈ Ioo α β) (w : E) :
    ∃ V : ℝ → E, V t₁ = w ∧ ∀ τ ∈ Ioo α β, HasDerivAt (chartRepFinite g p q V)
      (parallelCoeffFinite g p q τ (chartRepFinite g p q V τ)) τ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA : ContinuousOn (Function.uncurry fun (_ : ℝ) => parallelCoeffFinite g p q)
      ((univ : Set ℝ) ×ˢ Ioo α β) := by
    intro z hz
    exact ((continuousAt_parallelCoeffFinite hr g hdom (hsrc z.2 hz.2)).comp
      continuous_snd.continuousAt).continuousWithinAt
  obtain ⟨Z, hZ0, hZ⟩ := DifferentialGeometry.Analysis.ODE.Flow.hasLinearODESolution_of_continuousOn
    (A := fun (_ : ℝ) => parallelCoeffFinite g p q)
    (Z₀ := fun _ => chartRepFinite g p q (fun _ => w) t₁) ht₁ hA (mem_univ (0 : ℝ))
  set V : ℝ → E := fun τ =>
    mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q (g.geodesicFlow p τ).proj) (Z τ)
    with hV
  have hrep : ∀ τ ∈ Ioo α β, chartRepFinite g p q V τ = Z τ := by
    intro τ hτ
    rw [chartRepFinite_eq_mfderiv g p V (hsrc τ hτ)]
    exact mfderiv_extChartAt_apply_mfderiv_symm_of_mem (hsrc τ hτ) (Z τ)
  refine ⟨V, ?_, fun τ hτ => ?_⟩
  · have h1 : Z t₁ = mfderiv I 𝓘(ℝ, E) (extChartAt I q) (g.geodesicFlow p t₁).proj w := by
      rw [hZ0]
      exact chartRepFinite_eq_mfderiv g p (fun _ => w) (hsrc t₁ ht₁)
    change (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm
      (extChartAt I q (g.geodesicFlow p t₁).proj) (Z t₁) : E) = w
    rw [h1]
    exact mfderiv_extChartAt_symm_apply_mfderiv (hsrc t₁ ht₁) w
  · rw [hrep τ hτ]
    refine (hZ τ hτ).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with σ hσ
    exact hrep σ hσ

/-- **Uniqueness on `Icc`:** two continuous solutions of the parallel ODE on `Icc a b` that agree at
one time agree on `Icc a b` (Grönwall in charts, `eqOn_Icc_of_hasDerivWithinAt_linear`, and
connectedness). -/
theorem eqOn_Icc_of_pvf (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {a b t₀ : ℝ}
    {V₁ V₂ : ℝ → E}
    (hc₁ : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V₁ σ⟩ : TangentBundle I M)) (Icc a b))
    (hc₂ : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V₂ σ⟩ : TangentBundle I M)) (Icc a b))
    (h₁ : PVF[H, g, p, V₁, Icc a b]) (h₂ : PVF[H, g, p, V₂, Icc a b]) (ht₀ : t₀ ∈ Icc a b)
    (heq : V₁ t₀ = V₂ t₀) : EqOn V₁ V₂ (Icc a b) := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  have hloc : ∀ x ∈ Icc a b, ∃ J ∈ 𝓝[Icc a b] x, ∀ y ∈ J, ∀ z ∈ J, V₁ y = V₂ y → V₁ z = V₂ z := by
    intro x hx
    set q := (g.geodesicFlow p x).proj with hqdef
    have hq : q ∈ (chartAt H q).source := mem_chart_source H q
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ((chartAt H q).open_source.preimage hcont) x hq
    have hsub : ∀ σ ∈ Icc (x - ε / 2) (x + ε / 2), (g.geodesicFlow p σ).proj ∈ (chartAt H q).source :=
      fun σ hσ => hball (by rw [Real.ball_eq_Ioo]; constructor <;> linarith [hσ.1, hσ.2])
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := x - ε / 2) (b := x + ε / 2)).exists_bound_of_continuousOn
      (f := parallelCoeffFinite g p q)
      (fun σ hσ => (continuousAt_parallelCoeffFinite hr g hdom (hsub σ hσ)).continuousWithinAt)
    set J := Icc (a ⊔ (x - ε / 2)) (b ⊓ (x + ε / 2)) with hJdef
    have hJ : Icc a b ∩ Icc (x - ε / 2) (x + ε / 2) = J := Icc_inter_Icc
    have hJ₁ : J ⊆ Icc a b := hJ ▸ inter_subset_left
    have hJ₂ : J ⊆ Icc (x - ε / 2) (x + ε / 2) := hJ ▸ inter_subset_right
    refine ⟨J, ?_, fun y hy z hz hyz => ?_⟩
    · rw [← hJ]
      exact inter_mem_nhdsWithin _ (Icc_mem_nhds (by linarith) (by linarith))
    · have hcJ : ∀ V : ℝ → E, ContinuousOn
          (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) (Icc a b) →
          ContinuousOn (chartRepFinite g p q V) J := fun V hV σ hσ =>
        ((continuousWithinAt_iff_chartRepFinite hr hdom (hsub σ (hJ₂ hσ))).1
          (hV σ (hJ₁ hσ))).mono hJ₁
      have hdJ : ∀ V : ℝ → E, PVF[H, g, p, V, Icc a b] → ∀ σ ∈ J,
          HasDerivWithinAt (chartRepFinite g p q V)
            (parallelCoeffFinite g p q σ (chartRepFinite g p q V σ)) J σ := fun V hV σ hσ =>
        (hV σ (hJ₁ hσ) q (hsub σ (hJ₂ hσ))).mono hJ₁
      have key := eqOn_Icc_of_hasDerivWithinAt_linear (K := C.toNNReal)
        (fun σ hσ => (hC σ (hJ₂ hσ)).trans (Real.le_coe_toNNReal C)) (hcJ V₁ hc₁) (hcJ V₂ hc₂)
        (hdJ V₁ h₁) (hdJ V₂ h₂) hy (chartRepFinite_congr g p q hyz)
      exact eq_of_chartRepFinite_eq g p (hsub z (hJ₂ hz)) (key hz)
  intro t ht
  refine isPreconnected_Icc.induction₂' (fun x y => V₁ x = V₂ x → V₁ y = V₂ y) ?_ ?_ ht₀ ht heq
  · intro x hx
    obtain ⟨J, hJ, hJprop⟩ := hloc x hx
    have hxJ : x ∈ J := mem_of_mem_nhdsWithin hx hJ
    filter_upwards [hJ] with y hy
    exact ⟨fun h => hJprop x hxJ y hy h, fun h => hJprop y hy x hxJ h⟩
  · intro x y z _ _ _ hxy hyz h
    exact hyz (hxy h)

/-- **Extension by a chart solution:** a solution on `Icc a b` extends to `Icc a b ∪ Icc a' b'` when
`Icc a' b'` meets `Icc a b` and lies, with room, in a chart interval of the geodesic. -/
theorem exists_pvf_extend (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {q : M} {α β : ℝ}
    (hsrc : ∀ τ ∈ Ioo α β, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source)
    {a b a' b' : ℝ} (ha' : α < a') (hb' : b' < β) (hov₁ : a ≤ b') (hov₂ : a' ≤ b) (hab : a ≤ b)
    (ha'b' : a' ≤ b') {V : ℝ → E}
    (hVc : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) (Icc a b))
    (hV : PVF[H, g, p, V, Icc a b]) :
    ∃ V' : ℝ → E, EqOn V' V (Icc a b) ∧
      ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V' σ⟩ : TangentBundle I M))
        (Icc a b ∪ Icc a' b') ∧ PVF[H, g, p, V', Icc a b ∪ Icc a' b'] := by
  classical
  have ht₁ab : a ⊔ a' ∈ Icc a b := ⟨le_sup_left, sup_le hab hov₂⟩
  have ht₁' : a ⊔ a' ∈ Icc a' b' := ⟨le_sup_right, sup_le hov₁ ha'b'⟩
  have hsub' : Icc a' b' ⊆ Ioo α β := Icc_subset_Ioo ha' hb'
  obtain ⟨Vc, hVc1, hVcD⟩ := exists_chart_parallel hr g hdom hsrc (hsub' ht₁') (V (a ⊔ a'))
  have hVcP : PVF[H, g, p, Vc, Icc a' b'] := fun τ hτ q₂ h₂ =>
    hasDerivWithinAt_chart_of_chart hr g hdom (hsrc τ (hsub' hτ)) h₂
      ((hVcD τ (hsub' hτ)).hasDerivWithinAt)
  have hVcC : ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, Vc σ⟩ : TangentBundle I M))
      (Icc a' b') := fun τ hτ =>
    (continuousWithinAt_iff_chartRepFinite hr hdom (hsrc τ (hsub' hτ))).2
      (hVcD τ (hsub' hτ)).continuousAt.continuousWithinAt
  have hJ : Icc a b ∩ Icc a' b' = Icc (a ⊔ a') (b ⊓ b') := Icc_inter_Icc
  have hJ₁ : Icc (a ⊔ a') (b ⊓ b') ⊆ Icc a b := hJ ▸ inter_subset_left
  have hJ₂ : Icc (a ⊔ a') (b ⊓ b') ⊆ Icc a' b' := hJ ▸ inter_subset_right
  have ht₁J : a ⊔ a' ∈ Icc (a ⊔ a') (b ⊓ b') := hJ ▸ ⟨ht₁ab, ht₁'⟩
  have hov : EqOn V Vc (Icc a b ∩ Icc a' b') := by
    rw [hJ]
    exact eqOn_Icc_of_pvf hr g hdom (hVc.mono hJ₁) (hVcC.mono hJ₂) (pvf_mono hV hJ₁)
      (pvf_mono hVcP hJ₂) ht₁J hVc1.symm
  set V' : ℝ → E := fun τ => if τ ∈ Icc a b then V τ else Vc τ with hV'
  have hE₁ : EqOn V' V (Icc a b) := fun τ hτ => ite_eq_left hτ
  have hE₂ : EqOn V' Vc (Icc a' b') := by
    intro τ hτ
    by_cases h : τ ∈ Icc a b
    · exact (ite_eq_left h).trans (hov ⟨h, hτ⟩)
    · exact ite_eq_right h
  refine ⟨V', hE₁, ?_, pvf_union (pvf_congr hV hE₁) (pvf_congr hVcP hE₂) isClosed_Icc isClosed_Icc⟩
  refine ContinuousOn.union_of_isClosed (hVc.congr fun τ hτ => ?_) (hVcC.congr fun τ hτ => ?_)
    isClosed_Icc isClosed_Icc
  · exact congrArg (fun w : E => (⟨(g.geodesicFlow p τ).proj, w⟩ : TangentBundle I M)) (hE₁ hτ)
  · exact congrArg (fun w : E => (⟨(g.geodesicFlow p τ).proj, w⟩ : TangentBundle I M)) (hE₂ hτ)

/-- **Existence on `Icc (-R) R`** (Lebesgue number of the chart cover + repeated chart extension). -/
theorem exists_pvf_Icc (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {R : ℝ} (hR : 0 ≤ R)
    (v : E) :
    ∃ V : ℝ → E, V 0 = v ∧
      ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) (Icc (-R) R) ∧
      PVF[H, g, p, V, Icc (-R) R] := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := -R) (b := R))
    (c := fun q : M => (fun σ => (g.geodesicFlow p σ).proj) ⁻¹' (chartAt H q).source)
    (fun q => (chartAt H q).open_source.preimage hcont)
    (fun τ _ => mem_iUnion.2 ⟨(g.geodesicFlow p τ).proj, mem_chart_source H _⟩)
  set T : ℕ → ℝ := fun n => min R (n * (δ / 2)) with hTdef
  have hT0 : T 0 = 0 := by simp [T, hR]
  have hTnn : ∀ n, 0 ≤ T n := fun n => le_min hR (by positivity)
  have hTle : ∀ n, T n ≤ R := fun n => min_le_left _ _
  have hTmono : ∀ n, T n ≤ T (n + 1) := fun n =>
    min_le_min_left _ (by push_cast; nlinarith)
  have hTstep : ∀ n, T (n + 1) ≤ T n + δ / 2 := by
    intro n
    calc T (n + 1) ≤ min (R + δ / 2) (n * (δ / 2) + δ / 2) :=
          min_le_min (by linarith) (le_of_eq (by push_cast; ring))
      _ = T n + δ / 2 := min_add_add_right _ _ _
  have hind : ∀ n : ℕ, ∃ V : ℝ → E, V 0 = v ∧
      ContinuousOn (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M))
        (Icc (-T n) (T n)) ∧ PVF[H, g, p, V, Icc (-T n) (T n)] := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => v, rfl, ?_, ?_⟩
      · rw [hT0, neg_zero, Icc_self]
        exact continuousOn_singleton _ _
      · rw [hT0, neg_zero, Icc_self]
        exact pvf_of_subsingleton subsingleton_singleton
    | succ n ih =>
      obtain ⟨V, hV0, hVc, hVP⟩ := ih
      obtain ⟨q, hq⟩ := hleb (T n) ⟨by linarith [hTnn n], hTle n⟩
      have hsrc : ∀ τ ∈ Ioo (T n - δ) (T n + δ),
          (g.geodesicFlow p τ).proj ∈ (chartAt H q).source := fun τ hτ =>
        hq (by rw [Real.ball_eq_Ioo]; exact hτ)
      obtain ⟨V₁, hV₁eq, hV₁c, hV₁P⟩ := exists_pvf_extend hr g hdom hsrc (a := -T n) (b := T n)
        (a' := T n) (b' := T (n + 1)) (by linarith) (by linarith [hTstep n])
        (by linarith [hTnn n, hTnn (n + 1)]) le_rfl (by linarith [hTnn n]) (hTmono n) hVc hVP
      have hU₁ : Icc (-T n) (T n) ∪ Icc (T n) (T (n + 1)) = Icc (-T n) (T (n + 1)) :=
        Icc_union_Icc_eq_Icc (by linarith [hTnn n]) (hTmono n)
      rw [hU₁] at hV₁c hV₁P
      have hV₁0 : V₁ 0 = v := (hV₁eq ⟨by linarith [hTnn n], hTnn n⟩).trans hV0
      obtain ⟨q', hq'⟩ := hleb (-T n) ⟨by linarith [hTle n], by linarith [hTnn n]⟩
      have hsrc' : ∀ τ ∈ Ioo (-T n - δ) (-T n + δ),
          (g.geodesicFlow p τ).proj ∈ (chartAt H q').source := fun τ hτ =>
        hq' (by rw [Real.ball_eq_Ioo]; exact hτ)
      obtain ⟨V₂, hV₂eq, hV₂c, hV₂P⟩ := exists_pvf_extend hr g hdom hsrc' (a := -T n)
        (b := T (n + 1)) (a' := -T (n + 1)) (b' := -T n) (by linarith [hTstep n]) (by linarith)
        le_rfl (by linarith [hTnn (n + 1)]) (by linarith [hTnn n, hTnn (n + 1)])
        (by linarith [hTmono n]) hV₁c hV₁P
      have hU₂ : Icc (-T n) (T (n + 1)) ∪ Icc (-T (n + 1)) (-T n) =
          Icc (-T (n + 1)) (T (n + 1)) := by
        rw [union_comm]
        exact Icc_union_Icc_eq_Icc (by linarith [hTmono n]) (by linarith [hTnn n, hTnn (n + 1)])
      rw [hU₂] at hV₂c hV₂P
      exact ⟨V₂, (hV₂eq ⟨by linarith [hTnn n], hTnn (n + 1)⟩).trans hV₁0, hV₂c, hV₂P⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (R / (δ / 2))
  have hTn : T n = R := min_eq_left (by rw [div_le_iff₀ (by positivity)] at hn; linarith)
  obtain ⟨V, hV0, hVc, hVP⟩ := hind n
  rw [hTn] at hVc hVP
  exact ⟨V, hV0, hVc, hVP⟩

/-- **Parallel fields have constant inner products** (metric compatibility of the Koszul operator). -/
theorem inner_eq_of_pvf_univ (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {V W : ℝ → E}
    (hV : PVF[H, g, p, V, univ]) (hW : PVF[H, g, p, W, univ]) (t : ℝ) :
    g.inner (g.geodesicFlow p t).proj (V t) (W t) =
      g.inner (g.geodesicFlow p 0).proj (V 0) (W 0) := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  set f : ℝ → ℝ := fun σ => g.inner (g.geodesicFlow p σ).proj (V σ) (W σ) with hf
  have hderiv : ∀ σ, HasDerivAt f 0 σ := by
    intro σ
    obtain ⟨q, hq⟩ : ∃ q : M, (g.geodesicFlow p σ).proj ∈ (chartAt H q).source :=
      ⟨_, mem_chart_source H _⟩
    have hxsrc : (g.geodesicFlow p σ).proj ∈ (extChartAt I q).source := by rwa [extChartAt_source]
    have hxσ : extChartAt I q (g.geodesicFlow p σ).proj ∈ (extChartAt I q).target :=
      (extChartAt I q).map_source hxsrc
    have hbC1 : ContDiffOn ℝ 1 (chartCoeffFinite g q) (extChartAt I q).target :=
      contDiffOn_chartCoeffFinite g (m := 1) (by exact_mod_cast le_add_self) (by norm_num) q
    have hbd : DifferentiableAt ℝ (chartCoeffFinite g q) (extChartAt I q (g.geodesicFlow p σ).proj) :=
      (hbC1.contDiffAt ((isOpen_extChartAt_target q).mem_nhds hxσ)).differentiableAt
        (by norm_num)
    have hx := hasDerivAt_extChartAt_geodesicFlow hr g (hdom σ) hq
    have hB : HasDerivAt (fun τ => chartCoeffFinite g q (extChartAt I q (g.geodesicFlow p τ).proj))
        (fderiv ℝ (chartCoeffFinite g q) (extChartAt I q (g.geodesicFlow p σ).proj)
          (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p σ)).2) σ :=
      HasFDerivAt.comp_hasDerivAt (l := chartCoeffFinite g q) σ hbd.hasFDerivAt hx
    have hV' := hasDerivWithinAt_univ.mp (hV σ (mem_univ σ) q hq)
    have hW' := hasDerivWithinAt_univ.mp (hW σ (mem_univ σ) q hq)
    have hprod := (hB.clm_apply hV').clm_apply hW'
    have hev : f =ᶠ[𝓝 σ] fun τ => chartCoeffFinite g q (extChartAt I q (g.geodesicFlow p τ).proj)
        (chartRepFinite g p q V τ) (chartRepFinite g p q W τ) := by
      filter_upwards [hcont.continuousAt.eventually ((chartAt H q).open_source.mem_nhds hq)]
        with τ hτ
      rw [chartRepFinite_eq_mfderiv g p V hτ, chartRepFinite_eq_mfderiv g p W hτ]
      exact inner_eq_chartCoeffFinite g hτ (V τ) (W τ)
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    have hco : IsCoercive (chartCoeffFinite g q (extChartAt I q (g.geodesicFlow p σ).proj)) :=
      isCoercive_chartCoeffFinite g hxσ
    have hDsymm := fderiv_apply_symm_of_eventually hbd
      (Filter.Eventually.of_forall fun z u v => chartCoeffFinite_symm g q z u v)
    have hcompat := raisedKoszulOp_add_raisedKoszulOp_flip hco
      (fun u v => chartCoeffFinite_symm g q _ u v) _ hDsymm
      (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p σ)).2
      (chartRepFinite g p q V σ) (chartRepFinite g p q W σ)
    simp only [parallelCoeffFinite, chartChristoffelFinite, neg_apply, map_neg, add_apply]
    linarith [hcompat]
  have hdiff : Differentiable ℝ f := fun σ => (hderiv σ).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun σ => (hderiv σ).deriv) t 0

end Transport


section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **S3-PT.a** (`1 ≤ r`, i.e. `m ≥ 2`). Parallel transport along the complete geodesic `t ↦ π φ_t p`:
a linear isometry family `P t : T_{γ 0} → T_{γ t}` (both are `E` as types), parallel, continuous along `γ`
in `TM`, carrying `γ'(0)` to `γ'(t)`, and unique among continuous parallel fields on any `[a, b] ∋ 0`. -/
theorem exists_parallelTransport_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) :
    ∃ P : ℝ → E →L[ℝ] E, P 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ v : E, IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) (fun t => P t v) univ) ∧
      (∀ v : E, Continuous (fun t => (⟨(g.geodesicFlow p t).proj, P t v⟩ : TangentBundle I M))) ∧
      (∀ (t : ℝ) (v w : E), g.inner (g.geodesicFlow p t).proj (P t v) (P t w) = g.inner p.proj v w) ∧
      (∀ t : ℝ, P t p.snd = (g.geodesicFlow p t).snd) ∧
      ∀ (a b : ℝ) (V : ℝ → E), a ≤ 0 → 0 ≤ b →
        ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)) (Icc a b) →
        IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) V (Icc a b) →
          ∀ t ∈ Icc a b, V t = P t (V 0) := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ_of_one_le g hr hnorm
  have hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain := fun t => by rw [hD]; exact mem_univ _
  choose Vsol hVsol0 hVsolc hVsolP using
    fun (R : ℝ) (v : E) => exists_pvf_Icc hr g hdom (abs_nonneg R) v
  set Pf : ℝ → E → E := fun t v => Vsol (|t| + 1) v t with hPfdef
  have hpos : ∀ t : ℝ, |(|t| + 1)| = |t| + 1 := fun t => abs_of_pos (by positivity)
  have hagree : ∀ (R : ℝ) (v : E), ∀ σ ∈ Icc (-|R|) |R|, Pf σ v = Vsol R v σ := by
    intro R v σ hσ
    have hσR : |σ| ≤ |R| := abs_le.2 ⟨by linarith [hσ.1], hσ.2⟩
    set m := min |R| (|σ| + 1) with hm
    have hm0 : 0 ≤ m := le_min (abs_nonneg _) (by positivity)
    have hσm : σ ∈ Icc (-m) m := by
      have h1 : |σ| ≤ m := le_min hσR (by linarith)
      exact ⟨by linarith [neg_abs_le σ], le_trans (le_abs_self σ) h1⟩
    have hsub₁ : Icc (-m) m ⊆ Icc (-|R|) |R| :=
      Icc_subset_Icc (by linarith [min_le_left |R| (|σ| + 1)]) (min_le_left _ _)
    have hsub₂ : Icc (-m) m ⊆ Icc (-|(|σ| + 1)|) |(|σ| + 1)| := by
      rw [hpos σ]
      exact Icc_subset_Icc (by linarith [min_le_right |R| (|σ| + 1)]) (min_le_right _ _)
    exact eqOn_Icc_of_pvf hr g hdom ((hVsolc _ v).mono hsub₂) ((hVsolc R v).mono hsub₁)
      (pvf_mono (hVsolP _ v) hsub₂) (pvf_mono (hVsolP R v) hsub₁) ⟨by linarith, hm0⟩
      ((hVsol0 _ v).trans (hVsol0 R v).symm) hσm
  have hnhds : ∀ t : ℝ, Icc (-|(|t| + 1)|) |(|t| + 1)| ∈ 𝓝 t := fun t => by
    rw [hpos t]
    exact Icc_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
  have hevP : ∀ (t : ℝ) (v : E), (fun σ => Pf σ v) =ᶠ[𝓝 t] Vsol (|t| + 1) v :=
    fun t v => Filter.eventually_of_mem (hnhds t) fun σ hσ => hagree _ v σ hσ
  have hPfP : ∀ v : E, PVF[H, g, p, fun σ => Pf σ v, univ] := by
    intro v t _ q hq
    have ht : t ∈ Icc (-|(|t| + 1)|) |(|t| + 1)| := mem_of_mem_nhds (hnhds t)
    have h1 := (hVsolP (|t| + 1) v t ht q hq).hasDerivAt (hnhds t)
    have hev' : chartRepFinite g p q (fun σ => Pf σ v) =ᶠ[𝓝 t]
        chartRepFinite g p q (Vsol (|t| + 1) v) :=
      (hevP t v).mono fun σ hσ => chartRepFinite_congr g p q hσ
    rw [hev'.eq_of_nhds]
    exact (h1.congr_of_eventuallyEq hev').hasDerivWithinAt
  have hPfc : ∀ v : E, Continuous fun σ =>
      (⟨(g.geodesicFlow p σ).proj, Pf σ v⟩ : TangentBundle I M) := by
    intro v
    refine continuous_iff_continuousAt.2 fun t => ?_
    have h1 := (hVsolc (|t| + 1) v).continuousAt (hnhds t)
    refine h1.congr ?_
    filter_upwards [hevP t v] with σ hσ
    exact congrArg (fun w : E => (⟨(g.geodesicFlow p σ).proj, w⟩ : TangentBundle I M)) hσ.symm
  have hPf0 : ∀ v : E, Pf 0 v = v := fun v => hVsol0 _ v
  have h0mem : ∀ t : ℝ, (0 : ℝ) ∈ Icc (-|(|t| + 1)|) |(|t| + 1)| := fun t => by
    rw [hpos t]; constructor <;> linarith [abs_nonneg t]
  have hPflin : ∀ (t a : ℝ) (v w : E), Pf t (a • v + w) = a • Pf t v + Pf t w := by
    intro t a v w
    have ht : t ∈ Icc (-|(|t| + 1)|) |(|t| + 1)| := mem_of_mem_nhds (hnhds t)
    exact eqOn_Icc_of_pvf hr g hdom (hPfc (a • v + w)).continuousOn
      (continuousOn_linear hr hdom (hPfc v).continuousOn (hPfc w).continuousOn a)
      (pvf_mono (hPfP (a • v + w)) (subset_univ _))
      (pvf_mono (pvf_linear hr hdom (hPfP v) (hPfP w) a) (subset_univ _)) (h0mem t)
      (by simp only [hPf0]) ht
  have hPfzero : ∀ t : ℝ, Pf t 0 = 0 := by
    intro t
    have h := hPflin t (-1) 0 0
    simp only [smul_zero, add_zero, neg_smul, one_smul, neg_add_cancel] at h
    exact h
  let P : ℝ → E →L[ℝ] E := fun t => LinearMap.toContinuousLinearMap
    { toFun := Pf t
      map_add' := fun v w => by simpa only [one_smul] using hPflin t 1 v w
      map_smul' := fun a v => by
        simpa only [add_zero, hPfzero, RingHom.id_apply] using hPflin t a v 0 }
  have hP : ∀ t v, P t v = Pf t v := fun t v => rfl
  have hvel : PVF[H, g, p, fun σ => ((g.geodesicFlow p σ).snd : E), univ] := fun t _ q hq =>
    (hasDerivAt_extChartAt_tangent_geodesicFlow hr g (hdom t) hq).hasDerivWithinAt
  refine ⟨P, ?_, fun v => ?_, fun v => hPfc v, fun t v w => ?_, fun t => ?_, ?_⟩
  · ext v
    exact hPf0 v
  · exact (isParallelAlongFinite_geodesicFlow_iff hr (fun t _ => hdom t)
      (fun t _ => uniqueDiffWithinAt_univ)).2 (hPfP v)
  · rw [hP, hP, inner_eq_of_pvf_univ hr g hdom (hPfP v) (hPfP w) t, hPf0, hPf0,
      g.geodesicFlow_zero hr p]
  · have ht : t ∈ Icc (-|(|t| + 1)|) |(|t| + 1)| := mem_of_mem_nhds (hnhds t)
    have h0 : Pf 0 p.snd = ((g.geodesicFlow p 0).snd : E) :=
      (hPf0 p.snd).trans (by rw [g.geodesicFlow_zero hr p])
    exact eqOn_Icc_of_pvf (V₂ := fun σ => ((g.geodesicFlow p σ).snd : E)) hr g hdom
      (hPfc p.snd).continuousOn (continuous_geodesicFlow_of_forall_mem hr g hdom).continuousOn
      (pvf_mono (hPfP p.snd) (subset_univ _)) (pvf_mono hvel (subset_univ _)) (h0mem t) h0 ht
  · intro a b V ha hb hVc hV t ht
    rcases lt_or_ge a b with hab | hab
    · have hVP : PVF[H, g, p, V, Icc a b] :=
        (isParallelAlongFinite_geodesicFlow_iff hr (fun t _ => hdom t)
          (fun t ht => uniqueDiffOn_Icc hab t ht)).1 hV
      exact eqOn_Icc_of_pvf hr g hdom hVc (hPfc (V 0)).continuousOn hVP
        (pvf_mono (hPfP (V 0)) (subset_univ _)) ⟨ha, hb⟩ (hPf0 (V 0)).symm ht
    · have ht0 : t = 0 := by linarith [ht.1, ht.2]
      rw [ht0]
      exact (hPf0 (V 0)).symm

end Frozen

end DifferentialGeometry.Geometry.FiniteSoul
