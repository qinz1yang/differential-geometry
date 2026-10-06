import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyField
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Global.InteriorInterval

/-!
# CP1-D5: isotopy extension, step 3: time reparametrisation and the flow
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Filter Bundle DifferentialGeometry.Analysis.ODE
noncomputable section
namespace GC.LongTime.CuspP1

/-- a smooth time reparametrisation `θ : ℝ → [a - 2δ, b + 2δ]` equal to the identity on `[a,b]` -/
def timeReparam_CPD5 (a b δ : ℝ) (t : ℝ) : ℝ := a + timeWindowBump a b δ t * (t - a)

theorem contDiff_timeReparam_CPD5 (a b δ : ℝ) : ContDiff ℝ ∞ (timeReparam_CPD5 a b δ) :=
  contDiff_const.add ((timeWindowBump_contDiff a b δ).mul (contDiff_id.sub contDiff_const))

theorem timeReparam_eq_self_CPD5 {a b δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc a b) :
    timeReparam_CPD5 a b δ t = t := by
  have : timeWindowBump a b δ t = 1 :=
    timeWindowBump_eq_one a b δ t hδ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp [timeReparam_CPD5, this]

theorem timeReparam_mem_CPD5 {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (t : ℝ) :
    timeReparam_CPD5 a b δ t ∈ Icc (a - 2 * δ) (b + 2 * δ) := by
  by_cases h0 : timeWindowBump a b δ t = 0
  · simp only [timeReparam_CPD5, h0, zero_mul, add_zero]
    exact ⟨by linarith, by linarith⟩
  · have ht := timeWindowBump_mem_Icc_of_ne_zero a b δ t hδ h0
    have h1 : 0 ≤ timeWindowBump a b δ t := by
      unfold timeWindowBump
      exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have h2 : timeWindowBump a b δ t ≤ 1 := by
      unfold timeWindowBump
      exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)
    simp only [timeReparam_CPD5]
    constructor <;> nlinarith [ht.1, ht.2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
theorem contMDiff_reparamField_CPD5 (W : ℝ → ∀ y : M, TangentSpace I y)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, W q.1 q.2⟩ : TangentBundle I M)))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, deriv θ q.1 • W (θ q.1) q.2⟩ : TangentBundle I M)) := by
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (θ q.1, q.2)) :=
    (hθ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, W (θ q.1) q.2⟩ : TangentBundle I M)) := hW.comp hg
  have hθ' : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.mp hθ).2
  have hρ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => deriv θ q.1) :=
    hθ'.contMDiff.comp contMDiff_fst
  intro q
  have h := smul_section_contMDiffWithinAt_CPD5 (I := I) (fun t y => W (θ t) y)
    (fun q : ℝ × M => deriv θ q.1) (u := univ) (q₀ := q)
    (hρ q).contMDiffWithinAt (hcomp q).contMDiffWithinAt
  exact (contMDiffWithinAt_univ).mp h

/-- The flow of the reparametrised field `θ'(t) • W (θ t) y`: compactly supported, every global
solution of its equation is a flow line. -/
theorem exists_flow_of_reparamField_CPD5 [T2Space M]
    (W : ℝ → ∀ y : M, TangentSpace I y) {C : Set M} (hCc : IsCompact C)
    (hWsm : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, W q.1 q.2⟩ : TangentBundle I M)))
    (hWsupp : ∀ s y, y ∉ C → W s y = 0) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ γ : ℝ → M, (∀ τ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv θ τ • W (θ τ) (γ τ)))) → ∀ s t, γ t = Φ s t (γ s) := by
  let V : ℝ → ∀ y : M, TangentSpace I y := fun t y => deriv θ t • W (θ t) y
  have hVsm : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)) :=
    contMDiff_reparamField_CPD5 W hWsm hθ
  have hVsupp : ∀ t y, y ∉ C → V t y = 0 := fun t y hy => by simp [V, hWsupp _ y hy]
  have hW1 := contMDiff_one_autonomizedFlowVF_section (n := ∞) (by simp) V hVsm
  refine ⟨finiteOrderFlow V, ?_, finiteOrderFlow_self V hW1 hCc hVsupp,
    finiteOrderFlow_trans V hW1 hCc hVsupp, fun s t y hy => ?_,
    fun γ hγ s t => eq_finiteOrderFlow_of_hasMFDerivAt V hW1 hγ s t⟩
  · exact contMDiff_finiteOrderFlow (n := ⊤) (by simp) V hVsm hCc hVsupp
  · exact finiteOrderFlow_eq_self_of_forall_eq_zero V hW1 (fun t => hVsupp t y hy) s t

/-- the reparametrised curve `τ ↦ F (θ τ, x)` solves the reparametrised equation -/
theorem hasMFDerivAt_reparamCurve_CPD5
    {F : ℝ × N → M} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (hJ2 : Icc (a - 2 * δ) (b + 2 * δ) ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U)) {x : N} (hxU : x ∈ U)
    (W : ℝ → ∀ y : M, TangentSpace I y)
    (hWF : ∀ s ∈ Icc (a - 2 * δ) (b + 2 * δ),
      W s (F (s, x)) = mfderiv (𝓘(ℝ, ℝ).prod I) I F (s, x) ((1 : ℝ), (0 : E))) (τ : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ => F (timeReparam_CPD5 a b δ τ, x)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (deriv (timeReparam_CPD5 a b δ) τ •
          W (timeReparam_CPD5 a b δ τ) (F (timeReparam_CPD5 a b δ τ, x)))) := by
  set θ := timeReparam_CPD5 a b δ with hθdef
  have hθ : ContDiff ℝ ∞ θ := contDiff_timeReparam_CPD5 a b δ
  have hopen : IsOpen (J ×ˢ U) := hJ.prod hU
  have hθmem : θ τ ∈ Icc (a - 2 * δ) (b + 2 * δ) := timeReparam_mem_CPD5 hδ hab τ
  have hFd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I F (θ τ, x) :=
    (hF.contMDiffAt (hopen.mem_nhds ⟨hJ2 hθmem, hxU⟩)).mdifferentiableAt (by simp)
  have hθd : HasDerivAt θ (deriv θ τ) τ :=
    ((hθ.differentiable (by simp)) τ).hasDerivAt
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun τ => (θ τ, x)) τ
      (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv θ τ)).prod (0 : ℝ →L[ℝ] E)) :=
    hθd.hasFDerivAt.hasMFDerivAt.prodMk (hasMFDerivAt_const x τ)
  refine (hFd.hasMFDerivAt.comp τ hc).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  have h1 := hWF (θ τ) hθmem
  have e1 : (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv θ τ)).prod (0 : ℝ →L[ℝ] E)) 1 =
      deriv θ τ • (((1 : ℝ), (0 : E)) : ℝ × E) := by ext <;> simp
  change mfderiv (𝓘(ℝ, ℝ).prod I) I F (θ τ, x)
    ((((1 : ℝ →L[ℝ] ℝ).smulRight (deriv θ τ)).prod (0 : ℝ →L[ℝ] E)) 1) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv θ τ • W (θ τ) (F (θ τ, x)))) 1
  rw [e1]
  refine (map_smul (mfderiv (𝓘(ℝ, ℝ).prod I) I F (θ τ, x)) (deriv θ τ)
    (((1 : ℝ), (0 : E)) : TangentSpace (𝓘(ℝ, ℝ).prod I) (θ τ, x))).trans ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, h1]
  rfl

theorem exists_ambient_isotopy_of_field_CPD5 [T2Space M]
    {F : ℝ × N → M} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set N} (hKU : K ⊆ U) {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hJ2 : Icc (a - 2 * δ) (b + 2 * δ) ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (W : ℝ → ∀ y : M, TangentSpace I y) {C : Set M} (hCc : IsCompact C)
    (hWsm : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, W q.1 q.2⟩ : TangentBundle I M)))
    (hWsupp : ∀ s y, y ∉ C → W s y = 0)
    (hWF : ∀ s ∈ Icc (a - 2 * δ) (b + 2 * δ), ∀ x ∈ K,
      W s (F (s, x)) = mfderiv (𝓘(ℝ, ℝ).prod I) I F (s, x) ((1 : ℝ), (0 : E))) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K, Φ s t (F (s, x)) = F (t, x) := by
  obtain ⟨Φ, h1, h2, h3, h4, h5⟩ := exists_flow_of_reparamField_CPD5 W hCc hWsm hWsupp
    (contDiff_timeReparam_CPD5 a b δ)
  refine ⟨Φ, h1, h2, h3, h4, ?_⟩
  intro s hs t ht x hx
  have := h5 (fun τ => F (timeReparam_CPD5 a b δ τ, x))
    (fun τ => hasMFDerivAt_reparamCurve_CPD5 hJ hU hδ hab hJ2 hF (hKU hx) W (fun s hs => hWF s hs x hx) τ) s t
  simpa [timeReparam_eq_self_CPD5 hδ hs, timeReparam_eq_self_CPD5 hδ ht] using this.symm

end GC.LongTime.CuspP1
