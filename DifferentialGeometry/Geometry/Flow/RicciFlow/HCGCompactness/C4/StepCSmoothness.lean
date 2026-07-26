import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCCenterOfMass
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.DiagInvReadout
import Mathlib.Analysis.Calculus.Implicit

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C: C2 = `lbl430`, smooth dependence of the center of mass

MSM135 Proposition `lbl430`(i): the center of mass is a smooth function of the weights
`μ₁,…,μₖ` and the points `q₁,…,qₖ`.  The book's proof (chapter4.tex L2709+, transferring to
normal-chart coordinates at the center exactly as at L1699–1703) is the **Banach implicit
function theorem** applied to the defining equation
`G(μ, q⃗, y) := Σ μᵢ exp_y⁻¹ qᵢ = 0`, solving for `y = cm` as a function of `(μ, q⃗)`, using
that the partial derivative `∂_y G` is invertible (`≈ -(Σμᵢ)·id` near the diagonal).

This file provides the **IFT-core** of that argument — `cmSolution_hasStrictFDerivAt` — which
turns the IFT data for the (E-valued, chart-level) equation into `C¹` (strict-derivative)
smoothness of the extracted center `y = cm` in the parameters.  This is exactly the
`ImplicitFunctionData` "solve for `y`" pattern (`leftFun := G`, `rightFun :=` the parameter
projection); the `y`-component of `ImplicitFunctionData.implicitFunction` is the center of mass,
and it is strictly differentiable.

## Remaining producer (the two frontiers this core consumes)

The concrete `ImplicitFunctionData` for the cm equation is produced from:
- **joint smoothness of `G`** — AVAILABLE: `(y, q) ↦ exp_y⁻¹ q` is jointly `C¹` at the diagonal
  via `Exponential.diagExpInv` / `diagExpInv_contMDiffAt` (`DiagExpDerivative.lean`); assembling
  the chart-level `HasStrictFDerivAt` of `G = Σ μᵢ (chart of exp_y⁻¹ qᵢ)` from it (plus linearity
  in `μ`) is the geometric assembly step;
- **`∂_y G` invertibility** — the FRONTIER: the quantitative Hessian nondegeneracy of the center
  energy (`∂_y G ≈ -(Σμᵢ)·id`, invertible for `Σμᵢ>0`).  `StepCInputs.StrictDistInput` carries
  only qualitative strict convexity; the invertibility is the `lbl413`-family Hessian input, to
  be added as the honest scale/curvature-comparison field (pre-approved).

`cmSolution_hasStrictFDerivAt` is the `𝕜`-general Banach-IFT bridge (the task's "parametric
Banach IFT" smallest-bridge lemma): its `ImplicitFunctionData` argument is precisely the bundled
output of those two producers, and it delivers the `C¹` center-of-mass dependence B1 consumes.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology

/-- **C2 (`lbl430`) IFT core — the center of mass is `C¹` in the parameters.**

For the "solve `G(y, params) = 0` for `y`" implicit-function datum `φ` on the ambient space
`Eamb = Ey × P` — where `φ.leftFun` is the (E-valued, normal-chart-coordinate) center-of-mass
equation `Σ μᵢ exp_y⁻¹ qᵢ` and `φ.rightFun := Prod.snd` projects to the parameters
`params = (μ, q⃗-in-chart)` — the parameter-to-center map
`params ↦ (φ.implicitFunction (φ.leftFun φ.pt) params).1` (the `y`-component of the implicit
solution, i.e. the center of mass) is strictly differentiable, hence `C¹`, at the base
parameters.

This is the Banach-IFT half of MSM135 `lbl430`(i): `ImplicitFunctionData.implicitFunction` is
strictly differentiable (`hasStrictFDerivAt_implicitFunction_fderiv`), and the center is its
first coordinate, extracted by the continuous-linear projection `ContinuousLinearMap.fst`.  The
concrete `φ` for the cm equation is produced from `diagExpInv` (joint smoothness) and the
`lbl413` Hessian nondegeneracy (`∂_y G` invertibility) — see the module docstring. -/
theorem cmSolution_hasStrictFDerivAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Ey : Type*} [NormedAddCommGroup Ey] [NormedSpace 𝕜 Ey] [CompleteSpace Ey]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    (φ : ImplicitFunctionData 𝕜 (Ey × P) F P) :
    HasStrictFDerivAt
      (fun params : P => (φ.implicitFunction (φ.leftFun φ.pt) params).1)
      ((ContinuousLinearMap.fst 𝕜 Ey P).comp
        (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)))
      (φ.rightFun φ.pt) :=
  (ContinuousLinearMap.fst 𝕜 Ey P).hasStrictFDerivAt.comp (φ.rightFun φ.pt)
    φ.hasStrictFDerivAt_implicitFunction_fderiv

section ChartEquation

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

/-- **The chart-level center-of-mass equation `G`** in the normal chart at the base point `p`.
`chartCmEqn g p z (μ, ξ) = Σᵢ μᵢ • exp_y⁻¹ qᵢ`, where the base `y := (normalChartAt g p).symm z`
and targets `qᵢ := (normalChartAt g p).symm ξᵢ` are recovered from their `p`-chart coordinates
`z, ξ ∈ E`, and `exp_y⁻¹ qᵢ := normalChartAt g y qᵢ ∈ E`.  This is the `E`-valued MSM135 `lbl430`
equation `Σ μᵢ exp_y⁻¹ qᵢ = 0` that the Banach IFT solves for `z` (hence for the center `y = cm`)
as a function of the parameters `(μ, ξ)`. -/
noncomputable def chartCmEqn (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    (NormalCoordinates.normalChartAt (I := I) g
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) : E)

/-- **Correctness anchor (step 1).**  Evaluated at the `p`-chart coordinates of the center and
the points, `chartCmEqn` reduces to the book's inverse-exponential sum
`Σᵢ μᵢ • normalChartAt g y qᵢ` (`y = centerOfMass`).  Hence `chartCmEqn … = 0` is *equivalent*
to the defining equation `Σ μᵢ exp_y⁻¹ qᵢ = 0` (`centerOfMass.expInv_eqn`); the reduction is the
`normalChartAt` left-inverse on the base and each point.  This pins the IFT statement to the
actual center-of-mass equation before any analysis. -/
theorem chartCmEqn_center (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r)
    (hcm : (centerOfMass (I := I) g μ pts join p r h) ∈
      (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hpts : ∀ i : ι, pts i ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    chartCmEqn (I := I) g p
        (NormalCoordinates.normalChartAt (I := I) g p (centerOfMass (I := I) g μ pts join p r h))
        (μ, fun i => NormalCoordinates.normalChartAt (I := I) g p (pts i))
      = ∑ i : ι, μ i •
          (NormalCoordinates.normalChartAt (I := I) g
            (centerOfMass (I := I) g μ pts join p r h) (pts i) : E) := by
  unfold chartCmEqn
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [NormalCoordinates.normalChartAt_left_inv (I := I) g p hcm,
    NormalCoordinates.normalChartAt_left_inv (I := I) g p (hpts i)]

/-- **Honest input (step 3) — `lbl430`/`lbl413` Hessian nondegeneracy.**  At the configuration
`(z₀, params₀)` the `z`-partial Fréchet derivative of the chart cm-equation `chartCmEqn` is a
continuous linear *equivalence* `L : E ≃L[ℝ] E`.  This is the book's `∂_y G ≈ -(Σμᵢ)·id`
invertibility (nondegeneracy of the center energy Hessian, valid for `Σμᵢ>0`); its native
provenance is the per-summand near-`-id` bound `‖∂_z(exp_y⁻¹ qᵢ)+id‖<1` together with the Neumann
series (`Σμᵢ(-id+Eᵢ)` invertible for `‖ΣμᵢEᵢ‖<Σμᵢ`).  It is the *only* geometric datum the `lbl430`
implicit-function theorem consumes beyond joint `C¹`-ness of `G`, and it enters exactly as the
`ImplicitFunctionData` surjectivity/kernel-complement conditions. -/
def CmHessianInput (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z₀ : E) (params : (ι → ℝ) × (ι → E)) : Prop :=
  ∃ L : E ≃L[ℝ] E,
    HasFDerivAt (fun z : E => chartCmEqn (I := I) g p z params) (L : E →L[ℝ] E) z₀

/-- **Endpoint (step 4) — MSM135 `lbl430`(i): the chart center of mass is `C¹` in the
parameters.**  From joint strict differentiability of `G = chartCmEqn` (the moving-base `C¹`
assembly out of `Exponential.diagExpInv` / `diagExpInv_contMDiffAt`, carried here as the
hypothesis `hjoint`) and the Hessian-nondegeneracy input `hinv` (`CmHessianInput`, the invertible
`z`-block), the Banach implicit function theorem solves `G = 0` for the base chart coordinate `z`
as a strictly differentiable function `f` of the parameters `(μ, ξ)`, with `f params₀ = z₀` and
`G(f params, params) = 0` near `params₀`.  Composing `f` with `(normalChartAt g p).symm` and the
correctness anchor `chartCmEqn_center` identifies `(normalChartAt g p).symm (f params)` with the
center of mass, giving its `C¹` dependence on the weights and points.

Proof: assemble the `ImplicitFunctionData` `⟨leftFun := G, rightFun := Prod.snd, leftDeriv := D,
…⟩` from `hjoint` and `hinv`.  The `z`-block of `D` is the invertible `L` (chain rule +
`HasFDerivAt.unique`), whence `D` is surjective (`range D = ⊤`) and `IsCompl (ker D) (ker snd)`;
the conclusion is read off via `cmSolution_hasStrictFDerivAt` and the implicit-function
right-inverse germ.  Sorry-free: the only remaining inputs are the honest hypotheses `hjoint` (the
moving-base `C¹` assembly) and `hinv` (the Hessian nondegeneracy). -/
theorem implicitSol_hasStrictFDerivAt
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (D : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) D (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E, HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀ : G z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, G (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          G zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  classical
  obtain ⟨L, hL⟩ := hinv
  -- The `z`-block of the joint derivative `D` is the invertible `L` (chain rule + fderiv unique).
  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hDL : D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) = (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt
        ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))) z₀ :=
      hjoint.hasFDerivAt.comp z₀ hk
    exact h1.unique hL
  have hDv : ∀ v : E, D (v, (0 : (ι → ℝ) × (ι → E))) = L v := by
    intro v
    have h := DFunLike.congr_fun hDL v
    simpa [ContinuousLinearMap.inl_apply] using h
  have hDsurj : Function.Surjective ⇑D := fun w =>
    ⟨(L.symm w, 0), by rw [hDv]; exact L.apply_symm_apply w⟩
  -- Assemble the `ImplicitFunctionData` for `G = chartCmEqn` (`rightFun := snd`).
  let φ : ImplicitFunctionData ℝ (E × ((ι → ℝ) × (ι → E))) E ((ι → ℝ) × (ι → E)) :=
    { leftFun := fun w => G w.1 w.2
      leftDeriv := D
      rightFun := Prod.snd
      rightDeriv := ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))
      pt := (z₀, params₀)
      hasStrictFDerivAt_leftFun := hjoint
      hasStrictFDerivAt_rightFun := hasStrictFDerivAt_snd
      range_leftDeriv := LinearMap.range_eq_top.mpr hDsurj
      range_rightDeriv := LinearMap.range_eq_top.mpr Prod.snd_surjective
      isCompl_ker := by
        constructor
        · rw [disjoint_iff, Submodule.eq_bot_iff]
          rintro ⟨z, q⟩ hmem
          rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hmem
          obtain ⟨hzD, hzS⟩ := hmem
          have hq : q = 0 := hzS
          subst hq
          have hLz : L z = 0 := by rw [← hDv]; exact hzD
          have hz : z = 0 := by have := congrArg L.symm hLz; simpa using this
          simp [hz]
        · rw [codisjoint_iff, Submodule.eq_top_iff']
          rintro ⟨z, q⟩
          rw [Submodule.mem_sup]
          refine ⟨(-(L.symm (D (0, q))), q), ?_, (z + L.symm (D (0, q)), 0), ?_, ?_⟩
          · rw [LinearMap.mem_ker]
            change D (-(L.symm (D ((0 : E), q))), q) = 0
            have hsplit : D (-(L.symm (D ((0 : E), q))), q)
                = D (-(L.symm (D ((0 : E), q))), (0 : (ι → ℝ) × (ι → E))) + D ((0 : E), q) := by
              rw [← ContinuousLinearMap.map_add]; congr 1; simp
            rw [hsplit, hDv]
            simp [map_neg, ContinuousLinearEquiv.apply_symm_apply]
          · rw [LinearMap.mem_ker]; rfl
          · simp }
  -- `f params₀ = z₀` : the implicit function at the base point is the base point.
  have hf0 : (φ.implicitFunction (φ.leftFun φ.pt) params₀).1 = z₀ := by
    have hpt : φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun φ.pt) = φ.pt := by
      rw [ImplicitFunctionData.implicitFunction_apply, ← ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      exact φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
    have hr : φ.rightFun φ.pt = params₀ := rfl
    rw [← hr, hpt]
  refine ⟨fun params => (φ.implicitFunction (φ.leftFun φ.pt) params).1,
    (ContinuousLinearMap.fst ℝ E ((ι → ℝ) × (ι → E))).comp
      (fderiv ℝ (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)),
    hf0, cmSolution_hasStrictFDerivAt φ, ?_, ?_⟩
  · -- `∀ᶠ params, G (f params, params) = 0` : the implicit function solves the equation.
    have htend : Filter.Tendsto
        (fun params : (ι → ℝ) × (ι → E) => (φ.leftFun φ.pt, params))
        (nhds params₀) (nhds (φ.prodFun φ.pt)) :=
      tendsto_const_nhds.prodMk_nhds Filter.tendsto_id
    have hleft := htend.eventually φ.leftFun_implicitFunction
    have hright := htend.eventually φ.rightFun_implicitFunction
    filter_upwards [hleft, hright] with params hl hr
    set x := φ.implicitFunction (φ.leftFun φ.pt) params with hx
    have hr' : x.2 = params := hr
    calc G x.1 params
        = φ.leftFun (x.1, params) := rfl
      _ = φ.leftFun x := by rw [← hr']
      _ = φ.leftFun φ.pt := hl
      _ = 0 := hz₀
  · -- **local uniqueness**: near `(z₀, params₀)` the `G = 0` solution is the implicit function.
    filter_upwards [φ.leftFun_eq_iff_implicitFunction] with zp hzp hGzp
    have hle : φ.leftFun zp = φ.leftFun φ.pt := hGzp.trans hz₀.symm
    exact congrArg Prod.fst (hzp.mp hle).symm

/-- The pinned map `(z, params) ↦ (G z params, params)` has an invertible strict
derivative whenever the `z`-partial derivative of `G` is invertible.  The
inverse block map is `(a, b) ↦ (L⁻¹ (a - ∂ₚG b), b)`. -/
theorem existsPinnedDeriv
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E)
    (params₀ : (ι → ℝ) × (ι → E)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hjoint : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀) :
    ∃ Deq : (E × ((ι → ℝ) × (ι → E))) ≃L[ℝ]
        (E × ((ι → ℝ) × (ι → E))),
      HasStrictFDerivAt
        (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
        (Deq : (E × ((ι → ℝ) × (ι → E))) →L[ℝ]
          (E × ((ι → ℝ) × (ι → E)))) (z₀, params₀) := by
  classical
  obtain ⟨L, hL⟩ := hinv
  have hjoint_strict : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
      (z₀, params₀) := hjoint.hasStrictFDerivAt hn
  set D := fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2)
    (z₀, params₀)
  have hjoint_hd : HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) D (z₀, params₀) :=
    hjoint_strict.hasFDerivAt
  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hDL : D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) =
      (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt
        ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))) z₀ :=
      hjoint_hd.comp z₀ hk
    exact h1.unique hL
  have hDv : ∀ v : E, D (v, (0 : (ι → ℝ) × (ι → E))) = L v := by
    intro v
    have h := DFunLike.congr_fun hDL v
    simpa [ContinuousLinearMap.inl_apply] using h
  have hDsplit : ∀ (v : E) (u : (ι → ℝ) × (ι → E)),
      D (v, u) = L v + D ((0 : E), u) := by
    intro v u
    have hsum : ((v, u) : E × ((ι → ℝ) × (ι → E))) =
        (v, (0 : (ι → ℝ) × (ι → E))) + ((0 : E), u) := by
      ext <;> simp
    rw [hsum, map_add, hDv]
  let Deq : (E × ((ι → ℝ) × (ι → E))) ≃L[ℝ]
      (E × ((ι → ℝ) × (ι → E))) :=
    ContinuousLinearEquiv.equivOfInverse
      (D.prod (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))
      (((L.symm : E →L[ℝ] E).comp
          (ContinuousLinearMap.fst ℝ E ((ι → ℝ) × (ι → E)) -
            (D.comp (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))).comp
              (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))).prod
        (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))
      (by
        rintro ⟨v, u⟩
        have hk2 : D (v, u) - D ((0 : E), u) = L v := by
          rw [hDsplit v u]
          abel
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply,
          ContinuousLinearEquiv.coe_coe, Prod.mk.injEq, and_true]
        rw [hk2]
        exact L.symm_apply_apply v)
      (by
        rintro ⟨a, b⟩
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply,
          ContinuousLinearEquiv.coe_coe, Prod.mk.injEq, and_true]
        rw [hDsplit (L.symm (a - D ((0 : E), b))) b, L.apply_symm_apply]
        abel)
  have hΦ_hd : HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (Deq : (E × ((ι → ℝ) × (ι → E))) →L[ℝ]
        (E × ((ι → ℝ) × (ι → E)))) (z₀, params₀) := by
    change HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (D.prod (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E)))) (z₀, params₀)
    exact hjoint_hd.prodMk hasFDerivAt_snd
  have hΦcd : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2)) (z₀, params₀) :=
    hjoint.prodMk contDiffAt_snd
  exact ⟨Deq, hΦcd.hasStrictFDerivAt' hΦ_hd hn⟩

/-- The pinned map is an open partial homeomorphism on a neighborhood of every
point where the joint equation is differentiable and its `z`-block is
invertible. -/
theorem existsPinnedLocal
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E)
    (params₀ : (ι → ℝ) × (ι → E)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hjoint : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀) :
    ∃ e : OpenPartialHomeomorph
        (E × ((ι → ℝ) × (ι → E))) (E × ((ι → ℝ) × (ι → E))),
      (z₀, params₀) ∈ e.source ∧
        (e : (E × ((ι → ℝ) × (ι → E))) →
          (E × ((ι → ℝ) × (ι → E)))) =
          fun w => (G w.1 w.2, w.2) := by
  obtain ⟨Deq, hΦ⟩ := existsPinnedDeriv G z₀ params₀ hn hjoint hinv
  exact ⟨hΦ.toOpenPartialHomeomorph _, hΦ.mem_toOpenPartialHomeomorph_source, rfl⟩

/-- **C2 endpoint at order `n` (`lbl430`(ii)) — the implicit solution is `C^n`.**  The order-`n`
companion of `implicitSol_hasStrictFDerivAt`, via the *pinned* map `Φ(z, params) := (G z params,
params)`.  Its Fréchet derivative is block-triangular `[[∂_zG, ∂_pG], [0, id]]`, invertible iff the
`z`-block `∂_zG` is (the same `CmHessianInput` datum `hinv`, order-independent), realized here as an
explicit `ContinuousLinearEquiv` with inverse `(a, b) ↦ (L⁻¹(a - ∂_pG·b), b)`.  Then
`ContDiffAt.to_localInverse` makes `Φ⁻¹` `C^n`, and the implicit function `f params := (Φ⁻¹ (0,
params)).1` is `C^n` (compose `Prod.fst`, `Φ⁻¹`, `params ↦ (0, params)`), solves `G (f params)
params = 0`, and is the unique local solution.  Keeps the `C¹` endpoints untouched. -/
theorem implicitSol_contDiffAt
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hjoint : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E, HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀ : G z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀, G (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          G zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  classical
  have hn0 : ((n : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨Deq, hΦstrict⟩ := existsPinnedDeriv G z₀ params₀ hn0 hjoint hinv
  have hΦ_hd := hΦstrict.hasFDerivAt
  have hΦcd : ContDiffAt ℝ (n : ℕ∞) (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (z₀, params₀) := hjoint.prodMk contDiffAt_snd
  set invF := hΦstrict.localInverse
    (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2)) Deq (z₀, params₀) with hinvF
  -- `invF` is `C^n` at `(0, params₀)` (type-ascribe the beta/projection-clean form, then `hz₀`).
  have hinvF_cd : ContDiffAt ℝ (n : ℕ∞) invF
      ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))) :=
    hΦcd.to_localInverse hΦ_hd hn0
  rw [hz₀] at hinvF_cd
  refine ⟨fun params => (invF ((0 : E), params)).1, ?_, ?_, ?_, ?_⟩
  · change (invF ((0 : E), params₀)).1 = z₀
    have him : invF ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))) = (z₀, params₀) :=
      hΦstrict.localInverse_apply_image
    rw [hz₀] at him
    rw [him]
  · have hg1 : ContDiffAt ℝ (n : ℕ∞)
        (fun params : (ι → ℝ) × (ι → E) => ((0 : E), params)) params₀ :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hinvF_cd.comp params₀ hg1).fst
  · have htend : Filter.Tendsto (fun params : (ι → ℝ) × (ι → E) => ((0 : E), params))
        (nhds params₀) (nhds ((0 : E), params₀)) :=
      tendsto_const_nhds.prodMk_nhds Filter.tendsto_id
    have hri : ∀ᶠ y in nhds ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))),
        (G (invF y).1 (invF y).2, (invF y).2) = y := hΦstrict.eventually_right_inverse
    rw [hz₀] at hri
    have hpb := htend.eventually hri
    filter_upwards [hpb] with params hq
    have hq2 : (invF ((0 : E), params)).2 = params := congrArg Prod.snd hq
    have hq1 : G (invF ((0 : E), params)).1 (invF ((0 : E), params)).2 = 0 :=
      congrArg Prod.fst hq
    change G (invF ((0 : E), params)).1 params = 0
    rw [hq2] at hq1; exact hq1
  · have hli : ∀ᶠ x in nhds ((z₀, params₀) : E × ((ι → ℝ) × (ι → E))),
        invF (G x.1 x.2, x.2) = x := hΦstrict.eventually_left_inverse
    filter_upwards [hli] with zp hzp
    intro hG
    have hΦzp : ((G zp.1 zp.2, zp.2) : E × ((ι → ℝ) × (ι → E))) = ((0 : E), zp.2) := by rw [hG]
    rw [hΦzp] at hzp
    change zp.1 = (invF ((0 : E), zp.2)).1
    rw [hzp]

/-- **Endpoint for `chartCmEqn`** — thin specialization of `implicitSol_hasStrictFDerivAt`. -/
theorem chartCm_hasStrictFDerivAt
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (D : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn (I := I) g p w.1 w.2) D (z₀, params₀))
    (hinv : CmHessianInput (I := I) g p z₀ params₀)
    (hz₀ : chartCmEqn (I := I) g p z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn (I := I) g p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn (I := I) g p zp.1 zp.2 = 0 → zp.1 = f zp.2) :=
  implicitSol_hasStrictFDerivAt (fun z params => chartCmEqn (I := I) g p z params)
    z₀ params₀ D hjoint hinv hz₀

end ChartEquation

section DiagExpIdentification

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Step-1 identification anchor.**  The E-valued fiber `(diagExpInv g hEnorm p (y, q)).snd` of
the moving-base inverse-exponential section (`DiagExpDerivative.diagExpInv`, the only jointly-`C¹`
producer) coincides with the normal-chart coordinate `normalChartAt g y q`.  Both invert the
exponential-side diffeomorphism `expMapDiffeo g y` at `q`: `diagExpInv`'s fiber via `hexp`
(`expMapDiffeo g y (diagExpInv.snd) = q`, the honest producer output = `expIntr_diagExpInv` after
`diagExpInv_proj` and the `expMapIntrinsic = expMapDiffeo` agreement on the small ball), the normal
chart by definition (`normalChartAt g y = (expMapDiffeo g y).symm`).  The identification is then the
`left_inv` of the diffeomorphism on the source — it pins the (E-valued) moving-base equation
`chartCmEqn` to the `diagExpInv` producer that `hjoint` will use.  `hsrc` places the fiber in the
diffeomorphism source. -/
theorem normalChart_eq_diagExpInv_snd
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hsrc : (diagExpInv (I := I) g hEnorm p (y, q)).snd ∈
      (NormalCoordinates.expMapDiffeo (I := I) g y).source)
    (hexp : NormalCoordinates.expMapDiffeo (I := I) g y
        (show TangentSpace I y from (diagExpInv (I := I) g hEnorm p (y, q)).snd) = q) :
    (NormalCoordinates.normalChartAt (I := I) g y q : E)
      = (diagExpInv (I := I) g hEnorm p (y, q)).snd := by
  have h := (NormalCoordinates.expMapDiffeo (I := I) g y).left_inv hsrc
  rw [hexp] at h
  exact h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Package the pointwise base projection and inverse-exponential fiber
identification into an equality in the tangent bundle. -/
theorem diagExpInv_eq_normal
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hproj : (diagExpInv (I := I) g hEnorm p (y, q)).proj = y)
    (hsrc : (diagExpInv (I := I) g hEnorm p (y, q)).snd ∈
      (NormalCoordinates.expMapDiffeo (I := I) g y).source)
    (hexp : NormalCoordinates.expMapDiffeo (I := I) g y
        (show TangentSpace I y from
          (diagExpInv (I := I) g hEnorm p (y, q)).snd) = q) :
    diagExpInv (I := I) g hEnorm p (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  refine TotalSpace.ext hproj ?_
  exact heq_of_eq
    (normalChart_eq_diagExpInv_snd (I := I) g hEnorm p y q hsrc hexp).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Identify the moving inverse-exponential branch with the moving normal
chart under the intrinsic branch identities and the named realized-exponential
smallness condition. -/
theorem diagInv_eq_normal_lt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hproj : (diagExpInv (I := I) g hEnorm p (y, q)).proj = y)
    (hintr : expMapIntrinsic (I := I) g hEnorm y
      (diagExpInv (I := I) g hEnorm p (y, q)).snd = q)
    (hsmall : Real.sqrt
      (g.inner y
        (diagExpInv (I := I) g hEnorm p (y, q)).snd
        (diagExpInv (I := I) g hEnorm p (y, q)).snd) <
      expDiffeoRadius (I := I) g hEnorm y) :
    diagExpInv (I := I) g hEnorm p (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  have hsrc := expDiffeo_mem_of_lt (I := I) g hEnorm y hsmall
  have hcompat := expDiffeo_eq_intr (I := I) g hEnorm y hsmall
  exact diagExpInv_eq_normal (I := I) g hEnorm p y q
    hproj hsrc (hcompat.trans hintr)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Step-2 crux (readout smoothness).**  The trivialization-at-`p` fiber *readout* of the
moving-base inverse exponential — `(y, q) ↦ (trivializationAt E (TangentSpace I) p (diagExpInv g
hEnorm p (y, q))).2 : E` — is jointly `C¹` at the diagonal `(p, p)`.  This is `contMDiffAt_totalSpace`
(Mathlib `VectorBundle/Basic.lean`, the `StepBInputs` pattern) applied to `diagExpInv_contMDiffAt`:
the readout of a `ContMDiffAt` map into the tangent bundle is `ContMDiffAt` — no fiber-transition
inverse is needed.  (`diagExpInv_center` identifies the trivialization base `(diagExpInv (p,p)).proj`
with `p`.) -/
theorem diagExpReadout_contMDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M =>
        (trivializationAt E (TangentSpace I) p (diagExpInv (I := I) g hEnorm p yq)).2) (p, p) := by
  have h := diagExpInv_contMDiffAt (I := I) g hEnorm p
  rw [contMDiffAt_totalSpace] at h
  have hproj : (diagExpInv (I := I) g hEnorm p (p, p)).proj = p := by
    rw [diagExpInv_center]
  rw [hproj] at h
  exact h.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Readout smoothness at order `n`** (`lbl430`(ii)).  The `C^n` version of
`diagExpReadout_contMDiffAt`: `contMDiffAt_totalSpace` applied to `diagExpInv_contMDiffAt_order`. -/
theorem diagExpReadout_contMDiffAt_order
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M =>
        (trivializationAt E (TangentSpace I) p (diagExpInv (I := I) g hEnorm p yq)).2) (p, p) := by
  have h := diagExpInv_contMDiffAt_order (I := I) g hEnorm p n hn
  rw [contMDiffAt_totalSpace] at h
  have hproj : (diagExpInv (I := I) g hEnorm p (p, p)).proj = p := by
    rw [diagExpInv_center]
  rw [hproj] at h
  exact h.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Read an off-diagonal `C^n` tangent-bundle inverse branch in the fixed
trivialization at `p`.  This is the generic adapter used by controlled branch
domains; unlike `diagExpReadout_contMDiffAt_order`, the base point need not be
`(p,p)`. -/
theorem diagReadout_of_md
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (yq : M × M) (n : ℕ)
    (hsm : ContMDiffAt (I.prod I) I.tangent (n : ℕ∞)
      (diagExpInv (I := I) g hEnorm p) yq)
    (hbase : (diagExpInv (I := I) g hEnorm p yq).proj ∈
      (trivializationAt E (TangentSpace I) p).baseSet) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun w : M × M =>
        (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p w)).2) yq := by
  exact (((trivializationAt E (TangentSpace I) p).contMDiffAt_iff
    ((trivializationAt E (TangentSpace I) p).mem_source.2 hbase)).mp hsm).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- An explicit finite-order off-diagonal readout domain.  It is an open
neighborhood of `(p,p)` on which the readout is `C^n` and the fixed inverse
branch has the pointwise right-inverse, projection, and intrinsic exponential
identities. -/
theorem exists_readoutDom
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ∀ y ∈ U,
        ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
          (fun w : M × M =>
            (trivializationAt E (TangentSpace I) p
              (diagExpInv (I := I) g hEnorm p w)).2) y ∧
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hU⟩ := exists_diagInvDom (I := I) g hEnorm p n hn
  let e := trivializationAt E (TangentSpace I) p
  let V := U ∩ Prod.fst ⁻¹' e.baseSet
  have hVopen : IsOpen V := hUopen.inter (e.open_baseSet.preimage continuous_fst)
  have hpV : (p, p) ∈ V :=
    ⟨hpU, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  refine ⟨V, hVopen, hpV, ?_⟩
  intro y hy
  have hbranch := hU y hy.1
  have hbase : (diagExpInv (I := I) g hEnorm p y).proj ∈ e.baseSet := by
    rw [hbranch.2.2.1]
    exact hy.2
  exact ⟨diagReadout_of_md (I := I) g hEnorm p y n hbranch.1 hbase,
    hbranch.2⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A single `C^∞` off-diagonal readout domain. It is the fixed
trivialization-at-`p` restriction of `exists_diagInvDom_inf`, and retains all
branch identities needed to identify the readout with moving normal
coordinates. -/
theorem exists_readoutDom_inf
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
        (fun y : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p y)).2) U ∧
      ∀ y ∈ U,
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hUsmooth, hU⟩ :=
    exists_diagInvDom_inf (I := I) g hEnorm p
  let e := trivializationAt E (TangentSpace I) p
  let V := U ∩ Prod.fst ⁻¹' e.baseSet
  have hVopen : IsOpen V := hUopen.inter (e.open_baseSet.preimage continuous_fst)
  have hpV : (p, p) ∈ V :=
    ⟨hpU, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  have hVsmooth : ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
      (fun y : M × M =>
        (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p y)).2) V := by
    intro y hy
    have hbranchAt : ContMDiffAt (I.prod I) I.tangent ∞
        (diagExpInv (I := I) g hEnorm p) y :=
      (hUsmooth y hy.1).contMDiffAt (hUopen.mem_nhds hy.1)
    have hbase : (diagExpInv (I := I) g hEnorm p y).proj ∈ e.baseSet := by
      rw [(hU y hy.1).2.1]
      exact hy.2
    have hreadAt : ContMDiffAt (I.prod I) 𝓘(ℝ, E) ∞
        (fun w : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p w)).2) y :=
      (((trivializationAt E (TangentSpace I) p).contMDiffAt_iff
        ((trivializationAt E (TangentSpace I) p).mem_source.2 hbase)).mp hbranchAt).2
    exact hreadAt.contMDiffWithinAt
  refine ⟨V, hVopen, hpV, hVsmooth, ?_⟩
  intro y hy
  exact hU y hy.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Riemannian extended-ball form of the common `C^∞` readout branch. It
extracts a positive finite radius without choosing a separate proper metric;
the domain is written explicitly using `riemannianEDist`, so it is stable under
later metric realizations. -/
theorem exists_readoutEBall
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < ⊤ ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
        (fun y : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p y)).2)
        {y : M × M |
          max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ} ∧
      ∀ y : M × M,
        max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ →
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hUsmooth, hU⟩ :=
    exists_readoutDom_inf (I := I) g hEnorm p
  have hextract : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < ⊤ ∧
      {y : M × M |
        max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ} ⊆ U := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    haveI : RegularSpace M := inferInstance
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    obtain ⟨ε, hεpos, hεball⟩ := EMetric.isOpen_iff.mp hUopen (p, p) hpU
    let δ : ℝ≥0∞ := min ε 1
    have hδpos : 0 < δ := lt_min hεpos (by norm_num)
    have hδtop : δ < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt (min_le_right ε 1) (by simp)
    have hball : Metric.eball (p, p) δ ⊆ U :=
      (Metric.eball_subset_eball (min_le_left ε 1)).trans hεball
    refine ⟨δ, hδpos, hδtop, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_eball, Prod.edist_eq]
    exact hy
  obtain ⟨δ, hδpos, hδtop, hball⟩ := hextract
  refine ⟨δ, hδpos, hδtop, hUsmooth.mono hball, ?_⟩
  intro y hy
  exact hU y (hball hy)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every center/point pair lies in a Riemannian extended product ball around
an auxiliary cage center `q` once the radius dominates
`dist p q + 2 * r`.  This separates the elementary triangle-inequality ledger
from the later finite-hat estimate `dist p q ≤ 4 * lambda`. -/
theorem centerPairs_lt_of
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M) {δ : ℝ≥0∞}
    (hδ :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (dist p q + 2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) q)
        (riemannianEDist I (pts i) q) < δ := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hriem (x y : M) :
      riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
    rw [HopfRinow.riemMetric_dist_eq (I := I) x y]
    exact (ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) x y)).symm
  have hcm :
      dist (centerOfMass (I := I) g μ pts join p r h) p ≤ 2 * r := by
    simpa [Metric.mem_closedBall, dist_comm] using
      (centerOfMass.mem (I := I) (g := g) (μ := μ) (pts := pts)
        (join := join) (p := p) (r := r) h)
  intro i
  apply max_lt
  · rw [hriem]
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hδ
    calc
      dist (centerOfMass (I := I) g μ pts join p r h) q
          ≤ dist (centerOfMass (I := I) g μ pts join p r h) p + dist p q :=
        dist_triangle _ _ _
      _ ≤ 2 * r + dist p q := add_le_add_left hcm _
      _ = dist p q + 2 * r := add_comm _ _
  · rw [hriem]
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hδ
    calc
      dist (pts i) q ≤ dist (pts i) p + dist p q := dist_triangle _ _ _
      _ ≤ r + dist p q := by
        apply add_le_add_left
        simpa [dist_comm] using (h.pts_mem i).le
      _ ≤ 2 * r + dist p q := by linarith [h.r_pos]
      _ = dist p q + 2 * r := add_comm _ _

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Caged form of `centerPairs_lt_of`: a real upper bound `R` for the distance
from the center-input base to the readout base may be used in place of the
exact distance.  The finite-hat consumer will take `R = 4 * lambda`. -/
theorem centerPairs_lt_le
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M) (R : ℝ) {δ : ℝ≥0∞}
    (hpq :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      dist p q ≤ R)
    (hδ : ENNReal.ofReal (R + 2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) q)
        (riemannianEDist I (pts i) q) < δ := by
  apply centerPairs_lt_of (I := I) g μ pts join p r h q
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (add_le_add_left hpq _)) hδ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every center/point pair lies in a Riemannian extended product ball once its
radius dominates the standard `2 * r` center-of-mass bound.  This is the local
configuration-containment bridge for `exists_readoutEBall`; it deliberately
makes no claim that the branch radius is uniform over a sequence. -/
theorem centerPairs_lt
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) {δ : ℝ≥0∞}
    (hδ : ENNReal.ofReal (2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) p)
        (riemannianEDist I (pts i) p) < δ := by
  simpa using
    (centerPairs_lt_of (I := I) g μ pts join p r h p (by simpa using hδ))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The readout-form center equation attached to an explicit selected inverse
branch.  Quantitative HCG consumers choose `B`; the legacy equation below uses
the standard qualitative branch. -/
noncomputable def chartCmEqnB
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    B.diagReadout
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The readout-form center-of-mass equation `G'`** (PLANNER RULING #3).  Same shape as
`chartCmEqn`, but each summand is the trivialization-at-`p` fiber *readout* of the moving-base
inverse exponential `(diagExpInv g hEnorm p (y, qᵢ)).snd` instead of the (non-smooth-to-project)
abstract fiber.  Since the trivialization is a linear iso on each fiber, `chartCmEqn' = A(y)·chartCmEqn`
(`chartCmEqn'_eq_clm`), so the two have the *same zero set* and the Banach IFT produces the same
implicit function — but `chartCmEqn'` is jointly `C¹` directly from `diagExpReadout_contMDiffAt`
(no `A(y)⁻¹`). -/
noncomputable def chartCmEqn'
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    (trivializationAt E (TangentSpace I) p
      (diagExpInv (I := I) g hEnorm p
        ((NormalCoordinates.framedChartAt (I := I) g p).symm z,
          (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)))).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The standard selected branch recovers the existing readout center
equation. -/
theorem chartCmEqnB_std
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) :
    chartCmEqnB (I := I) g hEnorm p (stdBranch (I := I) g hEnorm p) z params =
      chartCmEqn' (I := I) g hEnorm p z params := by
  unfold chartCmEqnB chartCmEqn' DiagInvBranch.diagReadout
  rw [std_inv_eq (I := I) g hEnorm p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Joint smoothness of the selected-branch readout equation at an arbitrary
order. -/
theorem chartCmEqnB_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ∞)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I n
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I n
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) n
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀) := by
  unfold chartCmEqnB
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hinner : ContMDiffAt
        𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) n
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.framedChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.framedChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp : ContMDiffAt
        𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          B.diagReadout
            ((NormalCoordinates.framedChartAt (I := I) g p).symm w.1,
              (NormalCoordinates.framedChartAt (I := I) g p).symm (w.2.2 i)))
        (z₀, params₀) :=
      ContMDiffAt.comp
        (I := 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))))
        (I' := I.prod I) (I'' := 𝓘(ℝ, E))
        (f := fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.framedChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.framedChartAt (I := I) g p).symm (w.2.2 i)))
        (g := fun yq : M × M => B.diagReadout yq)
        (z₀, params₀) (hsm i) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A selected-branch readout sum is the fixed-trivialization image of the
intrinsic normal-coordinate sum whenever the branch realizes those tangent
vectors. -/
theorem readoutB_sum_eq
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, B.inv (y, qs i) =
      (⟨y, (show TangentSpace I y from
        (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • B.diagReadout (y, qs i)) =
      (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
        (show TangentSpace I y from
          ∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
  have hterm : ∀ i, B.diagReadout (y, qs i) =
      (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
        (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
    intro i
    unfold DiagInvBranch.diagReadout
    rw [hpt i]
    exact congrArg Prod.snd
      ((trivializationAt E (TangentSpace I) p).apply_eq_prod_continuousLinearEquivAt ℝ y hy _)
  simp_rw [hterm]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (map_smul _ (μ i) _).symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The selected-branch readout sum vanishes exactly when the intrinsic normal
coordinate sum vanishes. -/
theorem readoutB_zero_iff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, B.inv (y, qs i) =
      (⟨y, (show TangentSpace I y from
        (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • B.diagReadout (y, qs i)) = 0 ↔
      (∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) = 0 := by
  rw [readoutB_sum_eq (I := I) g hEnorm p B μ y qs hy hpt]
  exact (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy |>.map_eq_zero_iff

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The selected-branch readout equation has a strictly differentiable local
implicit solution once its center derivative is invertible. -/
theorem readoutSolB_strict
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E)
      (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnB (I := I) g hEnorm p B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnB (I := I) g hEnorm p B zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀))
      (z₀, params₀) :=
    (chartCmEqnB_cdAt (I := I) g hEnorm p B z₀ params₀ 1 hchz hchξ hsm).hasStrictFDerivAt
      one_ne_zero
  exact implicitSol_hasStrictFDerivAt
    (fun z params => chartCmEqnB (I := I) g hEnorm p B z params)
    z₀ params₀ _ hjoint hinv hzero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The selected-branch readout equation has a finite-order smooth local
implicit solution once its center derivative is invertible. -/
theorem readoutSolB_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnB (I := I) g hEnorm p B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnB (I := I) g hEnorm p B zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀) :=
    chartCmEqnB_cdAt (I := I) g hEnorm p B z₀ params₀ n hchz hchξ hsm
  exact implicitSol_contDiffAt
    (fun z params => chartCmEqnB (I := I) g hEnorm p B z params)
    z₀ params₀ n hn hjoint hinv hzero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Factoring lemma (readout `=` trivialization-CLE of the abstract sum).**  Given, per index,
`hpt i : diagExpInv g hEnorm p (y, qs i) = ⟨y, normalChartAt g y (qs i)⟩` (the base is `y` by
`diagExpInv_proj` and the fiber is the normal-chart coordinate by `normalChart_eq_diagExpInv_snd`),
the weighted sum of readouts equals the trivialization fiber CLE at `y` applied to the abstract sum
`Σ μᵢ • normalChartAt g y qᵢ`.  Since that CLE is a linear iso, the readout sum vanishes iff the
abstract sum does — the zero-set bridge to `chartCmEqn`. -/
theorem readout_sum_eq_clm
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, diagExpInv (I := I) g hEnorm p (y, qs i)
      = (⟨y, (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p (y, qs i))).2)
      = (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
          (show TangentSpace I y from
            ∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
  have hterm : ∀ i, (trivializationAt E (TangentSpace I) p
      (diagExpInv (I := I) g hEnorm p (y, qs i))).2
      = (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
          (show TangentSpace I y from
            (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
    intro i
    rw [hpt i]
    exact congrArg Prod.snd
      ((trivializationAt E (TangentSpace I) p).apply_eq_prod_continuousLinearEquivAt ℝ y hy _)
  simp_rw [hterm]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (map_smul _ (μ i) _).symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Zero-set equivalence (readout ↔ abstract).**  The weighted sum of readouts vanishes iff the
abstract inverse-exponential sum `Σ μᵢ • normalChartAt g y qᵢ` (`= chartCmEqn`) does — the
trivialization fiber map is a linear iso, so it kills a vector iff the vector is zero.  This is the
`chartCmEqn' = 0 ↔ chartCmEqn = 0` bridge that keeps the implicit function identical. -/
theorem readout_sum_eq_zero_iff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, diagExpInv (I := I) g hEnorm p (y, qs i)
      = (⟨y, (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p (y, qs i))).2) = 0
      ↔ (∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) = 0 := by
  rw [readout_sum_eq_clm (I := I) g hEnorm p μ y qs hy hpt]
  exact (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy |>.map_eq_zero_iff

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Step-2 (`hjoint`) — the readout equation is jointly `C¹`.**  From the readout smoothness
(`hsm`, `diagExpReadout_contMDiffAt` transported to the configuration by the smallness discipline)
and the inverse-chart smoothness (`hchz`, `hchξ`, `expMapDiffeo`/`normalChartAt.symm` on their
source), `chartCmEqn'` is `ContDiffAt ℝ 1` at `(z₀, params₀)`: the finite `μ`-linear sum of
`(inverse chart) ∘ (readout)` composites — every factor jointly `C¹`, **no `A(y)⁻¹`**. -/
theorem chartCmEqn'_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ 1
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2) (z₀, params₀) := by
  unfold chartCmEqn'
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hinner : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.framedChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.framedChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp := (hsm i).comp (z₀, params₀) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`chartCmEqn'` is `C^n` at `(z₀, params₀)`, for every finite order `n`** (`lbl430`(ii)).  The
order-`n` version of `chartCmEqn'_contDiffAt`; the `ContDiffAt.sum/.smul/comp` assembly is
order-generic — every factor (`fun_prop` projections, the inverse charts `hchz`/`hchξ`, the readout
`hsm`) is supplied at order `n`. -/
theorem chartCmEqn'_contDiffAt_order
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      (z₀, params₀) := by
  unfold chartCmEqn'
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hinner : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.framedChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.framedChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp := (hsm i).comp (z₀, params₀) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Step-3 endpoint (readout form) — the chart center of mass is `C¹`, `hjoint` discharged.**
Applying the Banach IFT (`implicitSol_hasStrictFDerivAt`) to the readout equation `chartCmEqn'`: the
joint `C¹`-ness (`chartCmEqn'_contDiffAt`, PLANNER RULING #3) is now *proved*, so the only remaining
input is the Hessian nondegeneracy `hinv'` (`CmHessianInput` in readout form — the `A`-twist is
absorbed into the fresh invertible `L`).  The implicit solution `f` is strictly differentiable (`C¹`)
in the parameters and solves `chartCmEqn' = 0`; via `readout_sum_eq_zero_iff` this is the same
solution as the book's `Σ μᵢ exp_y⁻¹ qᵢ = 0`, hence the center of mass, giving MSM135 `lbl430`(i) at
`C¹` — conditional only on `hinv'` and the smallness data (`hchz`, `hchξ`, `hsm`, `hz₀'`). -/
theorem readoutSol_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn' (I := I) g hEnorm p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn' (I := I) g hEnorm p zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint' : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        (z₀, params₀)) (z₀, params₀) :=
    (chartCmEqn'_contDiffAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm).hasStrictFDerivAt
      one_ne_zero
  exact implicitSol_hasStrictFDerivAt
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀ _ hjoint' hinv' hz₀'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Step-3 endpoint at order `n` (`lbl430`(ii)) — the chart center of mass is `C^n`.**  The
order-`n` companion of `readoutSol_hasStrictFDerivAt`: joint `C^n`-ness of the readout equation is
`chartCmEqn'_contDiffAt_order`, and the `C^n` Banach implicit function theorem
`implicitSol_contDiffAt` (pinned-`Φ` route) delivers the implicit solution `f`, which is `C^n` in the
parameters, solves `chartCmEqn' = 0`, and is the unique local solution.  Same honest inputs as the
`C¹` version (`hinv'`, smallness), now at every finite order `n ≥ 1`. -/
theorem readoutSol_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn' (I := I) g hEnorm p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn' (I := I) g hEnorm p zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint_cd : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2) (z₀, params₀) :=
    chartCmEqn'_contDiffAt_order (I := I) g hEnorm p z₀ params₀ n hchz hchξ hsm
  exact implicitSol_contDiffAt
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀ n hn hjoint_cd hinv' hz₀'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A continuous center family solving the selected-branch readout equation
inherits the strict derivative of the local implicit solution. -/
theorem centerB_hasStrict
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqnB (I := I) g hEnorm p B
        (NormalCoordinates.framedChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E)) Df params₀ := by
  obtain ⟨f, Df, hf0, hfderiv, hsolves, huniq⟩ :=
    readoutSolB_strict (I := I) g hEnorm p B z₀ params₀ hchz hchξ hsm hinv hzero
  refine ⟨Df, ?_⟩
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfderiv.congr_of_eventuallyEq hid.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A continuous center family solving the selected-branch readout equation is
`C^n` whenever the selected branch and the implicit equation are `C^n`. -/
theorem centerB_contDiff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqnB (I := I) g hEnorm p B
        (NormalCoordinates.framedChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E)) params₀ := by
  obtain ⟨f, hf0, hfcd, hsolves, huniq⟩ :=
    readoutSolB_cdAt (I := I) g hEnorm p B z₀ params₀ n hn hchz hchξ hsm hinv hzero
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfcd.congr_of_eventuallyEq hid

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **C2 last-mile — MSM135 `lbl430`(i) at `C¹`: the center of mass is strictly differentiable in
the parameters.**  Let `c` be any center family solving the readout equation near `params₀`
(`hc_solves` — the defining equation `Σ μᵢ exp_y⁻¹ qᵢ = 0` in readout form, from `chartCmEqn_center`
+ `expInv_eqn_local` + `readout_sum_eq_zero_iff`) and continuous there (`hc_cont`).  The IFT-side
local uniqueness (`readoutSol_hasStrictFDerivAt`'s fourth conjunct — the `G = 0` solution near
`(z₀, params₀)` is the implicit function `f`) identifies `normalChartAt g p ∘ c` with `f` on a
neighborhood of `params₀`, so the chart center inherits `f`'s strict derivative.  Hence the center of
mass is `C¹` in `(weights, points)`, conditional only on the honest inputs (`hinv'` = `CmHessianInput`
in readout form, `StrictDistInput` via `c`'s center property, and the smallness data). -/
theorem center_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E)) Df params₀ := by
  obtain ⟨f, Df, hf0, hfderiv, hsolves, huniq⟩ :=
    readoutSol_hasStrictFDerivAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm hinv' hz₀'
  refine ⟨Df, ?_⟩
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfderiv.congr_of_eventuallyEq hid.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **C2 last-mile at order `n` (`lbl430`(ii)) — the chart center of mass is `C^n`.**  The order-`n`
companion of `center_hasStrictFDerivAt`: the `C^n` implicit solution `f` (`readoutSol_contDiffAt`)
carries the same local-uniqueness fourth conjunct, so the IFT identification `normalChartAt g p ∘ c
=ᶠ f` near `params₀` (from `hc_solves` + `hc_cont`, order-independent) transfers `f`'s `C^n`
smoothness to the chart center via `ContDiffAt.congr_of_eventuallyEq`.  Conditional only on the
honest inputs (`hinv'`, `StrictDistInput` via `c`, smallness), now at every finite order `n ≥ 1`. -/
theorem center_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E)) params₀ := by
  obtain ⟨f, hf0, hfcd, hsolves, huniq⟩ :=
    readoutSol_contDiffAt (I := I) g hEnorm p z₀ params₀ n hn hchz hchξ hsm hinv' hz₀'
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.framedChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfcd.congr_of_eventuallyEq hid

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **C2 endpoint at the project's own symbol — MSM135 `lbl430`(i): the literal `centerOfMass` is
`C¹` in `(weights, points)`.**  Specializes `center_hasStrictFDerivAt` to the concrete center family
`c params := centerOfMass g (params.1) (fun i => (normalChartAt g p).symm (params.2 i)) join p r
(H params)` — the center of mass of the configuration recovered from the `p`-chart parameters, with
`H` a per-parameter `CenterInput` family.  The chart center `normalChartAt g p ∘ c` is strictly
differentiable in the parameters.

The two per-parameter inputs it consumes:
- `hc_solves` — the center solves the readout equation near `params₀`.  Dischargeable per parameter
  from `expInv_eqn_local` (the center satisfies `Σ μᵢ exp_cm⁻¹ qᵢ = 0`, given the `grad_halfSqDist`
  smallness `√(g_cm(nc,nc)) < ρ` and `pts i ∈ normalChartAt g cm .source`) composed with
  `readout_sum_eq_zero_iff` (needs `hpt` and the trivialization `baseSet` per index) — the
  `CenterInput`-plus-smallness threading over a neighborhood of `params₀`.
- `hc_cont` — the chart center is continuous at `params₀` (`Tendsto … (𝓝 z₀)`).  **This is the one
  genuinely missing producer:** `centerOfMass.dist_le` / `centerEnergy_min_dist_le` give *distance
  bounds* on the center, but not its *continuity in the parameters* (the argmin-stability `Tendsto`).
  Building it — the unique minimizer of the jointly-continuous, strictly-convex center energy varies
  continuously in `(μ, q)` — is the remaining analytic lemma for the fully-unconditional endpoint. -/
theorem centerOfMass_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
            join p r (H params)) : E)) Df params₀ :=
  center_hasStrictFDerivAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm hinv' hz₀'
    (fun params => centerOfMass (I := I) g params.1
      (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r (H params))
    hc_solves hc_cont

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **C2 endpoint at the project's own symbol, order `n` (`lbl430`(ii)): the literal `centerOfMass`
is `C^n` in `(weights, points)`.**  Specializes `center_contDiffAt` to the concrete center family
`c params := centerOfMass g params.1 (fun i => (normalChartAt g p).symm (params.2 i)) join p r
(H params)`; the chart center `normalChartAt g p ∘ c` is `C^n` in the parameters, at every finite
order `n ≥ 1`, on the same two per-parameter inputs as the `C¹` endpoint (`hc_solves`, `hc_cont`). -/
theorem centerOfMass_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E)) params₀ :=
  center_contDiffAt (I := I) g hEnorm p z₀ params₀ n hn hchz hchξ hsm hinv' hz₀'
    (fun params => centerOfMass (I := I) g params.1
      (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r (H params))
    hc_solves hc_cont

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `hc_cont` producer (discharges the last C2 hypothesis).**  The chart center
`params ↦ normalChartAt g p (centerOfMass g params.1 (chart_p.symm ∘ params.2) join p r (H params))`
is continuous at `params₀`: compose `centerOfMass_cont` (argmin-stability, the point continuity of
the center) with the continuity of `normalChartAt g p` on its source (`normalChartAt_contMDiffOn`,
`continuousOn.continuousAt` at `hsrc : center ∈ source`).  Feeds `centerOfMass_hasStrictFDerivAt`'s
`hc_cont`, so the C2 endpoint is conditional only on `CmHessianInput` + `StrictDistInput` + the
smallness data (`hpts` = the config point-map continuity, `hsrc` = center in chart source). -/
theorem centerOfMassChart_cont
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) {ι : Type} [Fintype ι] (params₀ : (ι → ℝ) × (ι → E))
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hpts : Continuous (fun params : (ι → ℝ) × (ι → E) =>
      fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)))
    (hsrc : centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)) join p r
        (H params₀) ∈ (NormalCoordinates.framedChartAt (I := I) g p).source) :
    Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r
          (H params)) : E))
      (nhds params₀)
      (nhds (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)) join p r
          (H params₀)))) := by
  have hcm := centerOfMass_cont (I := I) g (fun params : (ι → ℝ) × (ι → E) => params.1)
    (fun params => fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
    join p r params₀ H continuous_fst hpts
  have hchart : ContinuousAt (fun q : M => (NormalCoordinates.framedChartAt (I := I) g p q : E))
      (centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)) join p r
        (H params₀)) :=
    (NormalCoordinates.framedChartAt (I := I) g p).contMDiffOn_toFun.continuousOn.continuousAt
      ((NormalCoordinates.framedChartAt (I := I) g p).open_source.mem_nhds hsrc)
  exact hchart.tendsto.comp hcm

end DiagExpIdentification

end HCGCompactness
end DifferentialGeometry
