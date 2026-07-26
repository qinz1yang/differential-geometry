import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartCoeffPullback
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.Support

/-!
# Chart-local integration-by-parts identity for the chart Voss–Weyl divergence

For a smooth tangent section `X` and a smooth function `φ : M → ℝ` with
compact support contained in `(chartAt H α).source`, the chart-local Voss–Weyl
divergence at `α` satisfies:
$$
\int_M (\text{localDivergence}_g\, \alpha\, X)(x) \cdot \phi(x)
    \,\mathrm{d}(\text{chartLocalMeasure}_g\,\alpha)(x)
  = -\int_M (\text{tangentSectionAction}\, X\, \phi)(x)
    \,\mathrm{d}(\text{chartLocalMeasure}_g\,\alpha)(x).
$$
This is the chart-local integration-by-parts formula. Together with the
intrinsic nature of `tangentSectionAction` and the chart-invariance of
`chartLocalMeasure` on overlaps (proved in
`DifferentialGeometry/Analysis/Integration/Measure/Invariance.lean`), it yields the
chart-invariance of the chart-local Voss–Weyl divergence.

The proof proceeds by pulling both integrals back to the chart target via the
extended chart, applying Mathlib's Euclidean integration by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) to each summand of the
chart formula, and pushing the result back to the manifold via the chart-local
representation of `tangentSectionAction`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The image of `tsupport φ` under the chart map. We will use this set as a
compact "barrier" that contains the supports of all the chart-pulled-back
integrands. -/
private def chartImageOfTsupport (α : M) (φ : M → ℝ) : Set E :=
  (extChartAt I α) '' tsupport φ

private lemma chartImageOfTsupport_isCompact
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    IsCompact (chartImageOfTsupport (I := I) α φ) := by
  unfold chartImageOfTsupport
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport φ) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_supp hx
  exact (hφ_compactSupp : IsCompact (tsupport φ)).image_of_continuousOn hcontOn

private lemma chartImageOfTsupport_subset_target
    (α : M) {φ : M → ℝ}
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    chartImageOfTsupport (I := I) α φ ⊆ (extChartAt I α).target := by
  intro y hy
  rcases hy with ⟨x, hxsupp, hxy⟩
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_supp hxsupp
  have : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  rwa [hxy] at this

private lemma chartImageOfTsupport_isClosed
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    IsClosed (chartImageOfTsupport (I := I) α φ) :=
  (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp).isClosed

/-- The chart-pulled-back integrand `X^i_α · ρ_α`, extended by zero outside
the chart target, viewed as a function `E → ℝ`. -/
private def vwIntegrandOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => (extChartAt I α).target.indicator
    (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y

private lemma vwIntegrandOnE_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y =
      chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y :=
  Set.indicator_of_mem hy _

private lemma vwIntegrandOnE_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y = 0 :=
  Set.indicator_of_notMem hy _

/-- Under `[I.Boundaryless]`, the chart target is open, so on the open
neighborhood `target` of any point in `target`, `vwIntegrandOnE` agrees with
the smooth function `chartCoeffOnE * chartDensityOnE`. Hence
`vwIntegrandOnE` is `C^∞` on the chart target. -/
private lemma vwIntegrandOnE_contDiffOn_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (vwIntegrandOnE (I := I) g α X i) (extChartAt I α).target := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun y : E => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  refine hsmooth.congr ?_
  intro y hy
  rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]

/-- Internal compatibility name for the public zero-extended chart pullback. -/
private abbrev phiOnE (α : M) (φ : M → ℝ) : E → ℝ :=
  chartPullZero (I := I) α φ

private lemma phiOnE_apply_of_mem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = φ ((extChartAt I α).symm y) :=
  Set.indicator_of_mem hy _

private lemma phiOnE_apply_of_notMem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = 0 :=
  Set.indicator_of_notMem hy _

/-- A chart coefficient extended by zero off the chart target. -/
private noncomputable def coeffZero
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  by
    classical
    exact (extChartAt I α).target.piecewise
      (chartCoeffOnE (I := I) α X i) (fun _ => 0)

/-- The measurable coordinate representative of a tangent action. -/
private def chartActionE
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (φ : M → ℝ) : E → ℝ := fun y =>
  ∑ i : Fin (Module.finrank ℝ E),
    coeffZero (I := I) α X i y *
      lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)

/-- The extended chart coordinate, with value zero off the chart source. -/
private noncomputable def chartCoordZero (α : M) : M → E :=
  by
    classical
    exact (chartAt H α).source.piecewise (fun x => extChartAt I α x) (fun _ => 0)

/-- The chart-coordinate tangent-action representative, extended by zero off
the chart source. -/
private noncomputable def chartActionM
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (φ : M → ℝ) : M → ℝ :=
  by
    classical
    exact (chartAt H α).source.indicator
      (fun x => chartActionE (I := I) α X φ (chartCoordZero (I := I) α x))

private lemma coeffZero_meas
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    Measurable (coeffZero (I := I) α X i) := by
  classical
  unfold coeffZero
  exact ContinuousOn.measurable_piecewise
    (chartCoeffOnE_contDiffOn (I := I) α X i).continuousOn
    continuousOn_const (measurableSet_extChartAt_target (I := I) α)

private lemma chartActionE_meas
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : Continuous (phiOnE (I := I) α φ)) :
    Measurable (chartActionE (I := I) α X φ) := by
  unfold chartActionE
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (coeffZero_meas (I := I) α X i).mul (measurable_lineDeriv hφ)

private lemma chartCoordZero_meas (α : M) :
    Measurable (chartCoordZero (I := I) α) := by
  classical
  unfold chartCoordZero
  have hsource : MeasurableSet (chartAt H α).source :=
    (chartAt H α).open_source.measurableSet
  have hext : ContinuousOn (fun x : M => extChartAt I α x)
      (chartAt H α).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact continuousOn_extChartAt α
  exact ContinuousOn.measurable_piecewise hext continuousOn_const hsource

private lemma chartActionM_meas
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : Continuous (phiOnE (I := I) α φ)) :
    Measurable (chartActionM (I := I) α X φ) := by
  unfold chartActionM
  exact ((chartActionE_meas (I := I) α X hφ).comp
    (chartCoordZero_meas (I := I) α)).indicator
      (chartAt H α).open_source.measurableSet

/-- The intrinsic tangent action agrees almost everywhere with its measurable
zero-extended chart representative at differentiability points of the pulled
back scalar function. -/
private lemma tangent_ae_chart [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (phiOnE (I := I) α φ))
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    tangentSectionAction (I := I) X φ =ᵐ[chartLocalMeasure (I := I) g α]
      chartActionM (I := I) α X φ := by
  classical
  have hdiff : ∀ᵐ y ∂(modelHaar (E := E)),
      DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    hφ_lip.ae_differentiableAt
  have hchart : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      x ∈ (chartAt H α).source →
        DifferentiableAt ℝ (phiOnE (I := I) α φ) (extChartAt I α x) :=
    ae_chart_of_haar (I := I) g α
      (measurableSet_of_differentiableAt ℝ (phiOnE (I := I) α φ)) hdiff
  filter_upwards [hchart] with x hx
  by_cases hxsrc : x ∈ (chartAt H α).source
  · have hxext : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxsrc
    have hxy : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxext
    rw [tangent_chart_diff (I := I) α X hxsrc (hx hxsrc)]
    unfold chartActionM
    rw [Set.indicator_of_mem hxsrc]
    unfold chartCoordZero
    rw [Set.piecewise_eq_of_mem _ _ _ hxsrc]
    unfold chartActionE
    refine Finset.sum_congr rfl ?_
    intro i _
    unfold coeffZero
    rw [Set.piecewise_eq_of_mem _ _ _ hxy]
    unfold chartCoeffOnE
    rw [(extChartAt I α).left_inv hxext]
  · have hxsupp : x ∉ tsupport φ := fun h => hxsrc (hφ_supp h)
    have hev : φ =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hxsupp
    have hmf : mfderiv I 𝓘(ℝ) φ x = 0 := by
      rw [hev.mfderiv_eq, mfderiv_const]
      rfl
    unfold tangentSectionAction chartActionM
    rw [hmf, Set.indicator_of_notMem hxsrc]
    rfl

/-- A chart-Lipschitz scalar with support inside the chart has a measurable
intrinsic tangent action for the corresponding chart-local measure. -/
theorem tangent_aesm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (chartPullZero (I := I) α φ))
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    AEStronglyMeasurable (tangentSectionAction (I := I) X φ)
      (chartLocalMeasure (I := I) g α) := by
  exact (chartActionM_meas (I := I) α X hφ_lip.continuous).aestronglyMeasurable.congr
    (tangent_ae_chart (I := I) g α X hφ_lip hφ_supp).symm

/-- A scalar function is globally continuous when its zero-extended chart
pullback is Lipschitz and its topological support stays inside the chart. -/
private lemma phi_cont_of_lip
    (α : M) {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (phiOnE (I := I) α φ))
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    Continuous φ := by
  have hext : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact continuousOn_extChartAt α
  have hcomp : ContinuousOn
      (fun x => phiOnE (I := I) α φ (extChartAt I α x))
      (chartAt H α).source :=
    hφ_lip.continuous.comp_continuousOn hext
  have hφ_on : ContinuousOn φ (chartAt H α).source := by
    refine hcomp.congr ?_
    intro x hx
    have hxext : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx
    have hxy : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxext
    change φ x = phiOnE (I := I) α φ (extChartAt I α x)
    rw [phiOnE_apply_of_mem (I := I) α φ hxy,
      (extChartAt I α).left_inv hxext]
  exact hφ_on.continuous_of_tsupport_subset
    (chartAt H α).open_source hφ_supp

/-- On the chart target, `phiOnE α φ` agrees with `scalarOnE α φ`. -/
private lemma phiOnE_eq_scalarOnE_on_target
    (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = scalarOnE (I := I) α φ y := by
  rw [phiOnE_apply_of_mem (I := I) α φ hy]
  rfl

/-- Under `[I.Boundaryless]`, `phiOnE α φ` is `C^∞` on the chart target. -/
private lemma phiOnE_contDiffOn_target [I.Boundaryless]
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    ContDiffOn ℝ ∞ (phiOnE (I := I) α φ) (extChartAt I α).target := by
  have hsmooth : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α φ) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hφ
  refine hsmooth.congr ?_
  intro y hy
  exact phiOnE_eq_scalarOnE_on_target (I := I) α φ hy

/-- If the function `f : E → ℝ` is `C^∞` on the open set `U` and identically
zero outside a closed set `K ⊆ U`, then `f` is `C^∞` on all of `E`. We split
`E = U ∪ (Kᶜ)` where the cover is open: on `U`, `f` is `C^∞`; on `Kᶜ`, `f` is
identically zero (hence `C^∞`). -/
private lemma contDiff_of_smooth_on_open_zero_outside
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → ℝ}
    (hf_smooth : ContDiffOn ℝ ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) y :=
      (contDiff_const).contDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

/-- Support of `phiOnE α φ` is contained in the chart image of the tsupport
of `φ`. -/
private lemma phiOnE_support_subset_chartImage
    (α : M) (φ : M → ℝ) :
    Function.support (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT] at hy
    refine ⟨(extChartAt I α).symm y, ?_, ?_⟩
    · exact subset_tsupport _ hy
    · exact (extChartAt I α).right_inv hyT
  · rw [phiOnE_apply_of_notMem (I := I) α φ hyT] at hy
    exact (hy rfl).elim

/-- `tsupport (phiOnE α φ)` ⊆ `chartImageOfTsupport α φ` (a closed bound). -/
private lemma phiOnE_tsupport_subset_chartImage
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    tsupport (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  refine closure_minimal (phiOnE_support_subset_chartImage (I := I) α φ) ?_
  exact chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp

/-- Under `[I.Boundaryless]`, with `tsupport φ ⊆ source` and `φ` continuous
with compact support, `phiOnE α φ` has compact tsupport in `E`, contained in
the chart target. -/
private lemma phiOnE_hasCompactSupport [I.Boundaryless]
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    HasCompactSupport (phiOnE (I := I) α φ) := by
  refine HasCompactSupport.intro
    (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
  intro y hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
    by_contra hne
    have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
    have : y ∈ chartImageOfTsupport (I := I) α φ :=
      ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
    exact hy this
  · exact phiOnE_apply_of_notMem (I := I) α φ hyT

/-- Under `[I.Boundaryless]`, `phiOnE α φ` is `C^∞` on all of `E`, provided
`φ` is `C^∞` and has compact tsupport contained in the chart source. -/
private lemma phiOnE_contDiff [I.Boundaryless]
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (phiOnE (I := I) α φ) := by
  refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
    (isOpen_extChartAt_target (I := I) α)
    (K := chartImageOfTsupport (I := I) α φ)
    (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
    (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
  · exact phiOnE_contDiffOn_target (I := I) α hφ
  · intro y hy
    by_cases hyT : y ∈ (extChartAt I α).target
    · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
      by_contra hne
      have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
      have : y ∈ chartImageOfTsupport (I := I) α φ :=
        ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
      exact hy this
    · exact phiOnE_apply_of_notMem (I := I) α φ hyT

/-- `vwIntegrandOnE` is differentiable at every point of the chart target. -/
private lemma vwIntegrandOnE_differentiableOn_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ y ∈ (extChartAt I α).target,
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y := by
  intro y hy
  have hOpen := isOpen_extChartAt_target (I := I) α
  have h_at : ContDiffWithinAt ℝ ∞
      (vwIntegrandOnE (I := I) g α X i) (extChartAt I α).target y :=
    vwIntegrandOnE_contDiffOn_target (I := I) g α X i y hy
  exact ((h_at.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by simp))

/-- The pointwise `fderiv` of `phiOnE α φ` agrees with the pointwise `fderiv`
of `scalarOnE α φ` on the open chart target. (This is `EventuallyEq.fderiv_eq`
after restricting to the target.) -/
private lemma fderiv_phiOnE_eq_fderiv_scalarOnE [I.Boundaryless]
    (α : M) (φ : M → ℝ)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    fderiv ℝ (phiOnE (I := I) α φ) y =
      fderiv ℝ (scalarOnE (I := I) α φ) y := by
  have hOpen : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_eq : phiOnE (I := I) α φ =ᶠ[𝓝 y] scalarOnE (I := I) α φ := by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact phiOnE_eq_scalarOnE_on_target (I := I) α φ hz
  exact Filter.EventuallyEq.fderiv_eq h_eq

/-- The chart-local IBP per index, expressed on the chart target via
extension by zero outside. The integration is over all of `E` against
`modelHaar`. -/
private theorem ibp_per_index [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    ∫ y, vwIntegrandOnE (I := I) g α X i y *
        fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) =
      -∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp
  have hphi_compactSupp : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupp hφ_supp
  have hvw_diff_on_target := vwIntegrandOnE_differentiableOn_target (I := I) g α X i
  have hphi_tsupp_in_target : tsupport (phiOnE (I := I) α φ) ⊆
      (extChartAt I α).target := by
    refine (phiOnE_tsupport_subset_chartImage (I := I) α hφ_compactSupp hφ_supp).trans ?_
    exact chartImageOfTsupport_subset_target (I := I) α hφ_supp
  have hvw_diff_tsupp_phi : ∀ y ∈ tsupport (phiOnE (I := I) α φ),
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y :=
    fun y hy => hvw_diff_on_target y (hphi_tsupp_in_target hy)
  have hphi_diff : ∀ y, DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y => hphi_smooth.differentiable (by simp) |>.differentiableAt
  have hphi_diff_tsupp_vw : ∀ y ∈ tsupport (vwIntegrandOnE (I := I) g α X i),
      DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y _ => hphi_diff y
  have hvw_cont : ContinuousOn (vwIntegrandOnE (I := I) g α X i)
      (extChartAt I α).target :=
    (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).continuousOn
  have hphi_cont : Continuous (phiOnE (I := I) α φ) := hphi_smooth.continuous
  have hvw_cont_on_tsupp : ContinuousOn (vwIntegrandOnE (I := I) g α X i)
      (tsupport (phiOnE (I := I) α φ)) :=
    hvw_cont.mono hphi_tsupp_in_target
  haveI : IsFiniteMeasureOnCompacts (modelHaar (E := E)) := by infer_instance
  have hI1_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
    · exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul
        ((phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI1_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  have hfg_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI1_smooth.continuous.integrable_of_hasCompactSupport hI1_compactSupp
  have hI2_smooth : ContDiff ℝ ∞
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target :=
        (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).fderiv_of_isOpen
          (isOpen_extChartAt_target (I := I) α) (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
              ((chartModelBasis E) i)) (extChartAt I α).target :=
        hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul ((phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI2_compactSupp : HasCompactSupport
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  have hf'g_int : Integrable
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI2_smooth.continuous.integrable_of_hasCompactSupport hI2_compactSupp
  have hI3_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
    · have hphi_smooth_total : ContDiff ℝ ∞ (phiOnE (I := I) α φ) := hphi_smooth
      have hphi_fderiv_total : ContDiff ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ)) := by
        have := hphi_smooth_total.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
        exact this
      have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (extChartAt I α).target := hphi_fderiv_total.contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
          (extChartAt I α).target :=
        hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [hfderiv_zero]
      have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
        rw [fderiv_const]
        rfl
      rw [hfderiv_const_zero]
      simp
  have hI3_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
        fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
      hphi_zero_on_nhd.fderiv_eq
    rw [hfderiv_zero]
    have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
      rw [fderiv_const]
      rfl
    rw [hfderiv_const_zero]
    simp
  have hfg'_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
      (modelHaar (E := E)) :=
    hI3_smooth.continuous.integrable_of_hasCompactSupport hI3_compactSupp
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g_int hfg'_int hfg_int
    hvw_diff_tsupp_phi hphi_diff_tsupp_vw

/-- The chart-local integration-by-parts identity for one coordinate direction
when the scalar factor is only Lipschitz. A compact plateau localizes the
smooth coefficient before applying Euclidean Lipschitz integration by parts. -/
private theorem ibp_lip_index [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (phiOnE (I := I) α φ))
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    (∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y ∂(modelHaar (E := E)) =
        -∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E))) ∧
      Integrable (fun y =>
        partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
          phiOnE (I := I) α φ y) (modelHaar (E := E)) ∧
      Integrable (fun y => vwIntegrandOnE (I := I) g α X i y *
        lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
        (modelHaar (E := E)) := by
  let K : Set E := chartImageOfTsupport (I := I) α φ
  let U : Set E := (extChartAt I α).target
  have hK : IsCompact K := by
    simpa only [K] using
      chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp
  have hU : IsOpen U := by
    simpa only [U] using isOpen_extChartAt_target (I := I) α
  have hKU : K ⊆ U := by
    simpa only [K, U] using
      chartImageOfTsupport_subset_target (I := I) α hφ_supp
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one, hχ_supp, _hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hK hU hKU
  let q : E → ℝ := fun y => χ y * vwIntegrandOnE (I := I) g α X i y
  have hq_smooth : ContDiff ℝ ∞ q := by
    have hsmul := DifferentialGeometry.Analysis.contDiff_cutoff_smul
      hU hχ_smooth hχ_supp
        (vwIntegrandOnE_contDiffOn_target (I := I) g α X i)
    simpa only [q, smul_eq_mul] using hsmul
  have hq_compact : HasCompactSupport q := by
    simpa only [q] using hχ_compact.mul_right
  obtain ⟨D, hq_lip⟩ : ∃ D, LipschitzWith D q :=
    ContDiff.lipschitzWith_of_hasCompactSupport hq_compact hq_smooth (by simp)
  let v : E := (chartModelBasis E) i
  have hq_vw_nhds {y : E} (hy : y ∈ K) :
      q =ᶠ[𝓝 y] vwIntegrandOnE (I := I) g α X i := by
    have hχ_one_y : χ =ᶠ[𝓝 y] (1 : E → ℝ) :=
      hχ_one.filter_mono (nhds_le_nhdsSet hy)
    filter_upwards [hχ_one_y] with z hz
    simp only [q, hz, Pi.one_apply, one_mul]
  have hleft_ae :
      (fun y => lineDeriv ℝ (phiOnE (I := I) α φ) y v * q y) =ᵐ[
        modelHaar (E := E)]
      (fun y => vwIntegrandOnE (I := I) g α X i y *
        lineDeriv ℝ (phiOnE (I := I) α φ) y v) :=
    Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ tsupport (phiOnE (I := I) α φ)
      · have hyK : y ∈ K := by
          simpa only [K] using
            phiOnE_tsupport_subset_chartImage (I := I) α hφ_compactSupp hφ_supp hy
        change lineDeriv ℝ (phiOnE (I := I) α φ) y v * q y =
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y v
        rw [(hq_vw_nhds hyK).self_of_nhds]
        ring
      · have hline :=
          ((HasFDerivAt.of_notMem_tsupport ℝ hy).hasLineDerivAt v).lineDeriv
        simp only [ContinuousLinearMap.zero_apply] at hline
        change lineDeriv ℝ (phiOnE (I := I) α φ) y v * q y =
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y v
        rw [hline]
        simp only [zero_mul, mul_zero]
  have hleft := integral_congr_ae hleft_ae
  have hright_ae :
      (fun y => lineDeriv ℝ q y (-v) * phiOnE (I := I) α φ y) =ᵐ[
        modelHaar (E := E)]
      (fun y => -(partialDeriv (E := E) i
        (vwIntegrandOnE (I := I) g α X i) y * phiOnE (I := I) α φ y)) :=
    Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ tsupport (phiOnE (I := I) α φ)
      · have hyK : y ∈ K := by
          simpa only [K] using
            phiOnE_tsupport_subset_chartImage (I := I) α hφ_compactSupp hφ_supp hy
        have hvw_diff : DifferentiableAt ℝ
            (vwIntegrandOnE (I := I) g α X i) y :=
          vwIntegrandOnE_differentiableOn_target (I := I) g α X i y (hKU hyK)
        have hline : lineDeriv ℝ q y (-v) =
            -partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y := by
          rw [(hq_vw_nhds hyK).lineDeriv_eq]
          rw [hvw_diff.lineDeriv_eq_fderiv]
          simp only [v, partialDeriv, map_neg]
        change lineDeriv ℝ q y (-v) * phiOnE (I := I) α φ y =
          -(partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y)
        rw [hline]
        ring
      · have hφ_zero : phiOnE (I := I) α φ y = 0 :=
          image_eq_zero_of_notMem_tsupport hy
        change lineDeriv ℝ q y (-v) * phiOnE (I := I) α φ y =
          -(partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y)
        rw [hφ_zero]
        simp only [mul_zero, neg_zero]
  have hright :
      ∫ y, lineDeriv ℝ q y (-v) * phiOnE (I := I) α φ y
          ∂(modelHaar (E := E)) =
        -∫ y, partialDeriv (E := E) i
              (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y
          ∂(modelHaar (E := E)) := by
    rw [← integral_neg]
    exact integral_congr_ae hright_ae
  have hibp := LipschitzWith.integral_lineDeriv_mul_eq
    (μ := modelHaar (E := E)) hφ_lip hq_lip hq_compact v
  rw [hleft, hright] at hibp
  have heq :
      ∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y ∂(modelHaar (E := E)) =
        -∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E)) := by
    simpa only [v] using (show
      ∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y ∂(modelHaar (E := E)) =
        -∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y v
          ∂(modelHaar (E := E)) by linarith)
  have hq_int : Integrable q (modelHaar (E := E)) :=
    hq_smooth.continuous.integrable_of_hasCompactSupport hq_compact
  have hphi_int : Integrable (phiOnE (I := I) α φ) (modelHaar (E := E)) :=
    hφ_lip.continuous.integrable_of_hasCompactSupport
      (phiOnE_hasCompactSupport (I := I) α hφ_compactSupp hφ_supp)
  have hleft0 : Integrable
      (fun y => lineDeriv ℝ (phiOnE (I := I) α φ) y v * q y)
      (modelHaar (E := E)) := by
    simpa only [smul_eq_mul, mul_comm] using
      hq_int.smul_of_top_left
        (hφ_lip.memLp_lineDeriv (μ := modelHaar (E := E)) v)
  have hrhs : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y *
        lineDeriv ℝ (phiOnE (I := I) α φ) y v)
      (modelHaar (E := E)) :=
    hleft0.congr hleft_ae
  have hright0 : Integrable
      (fun y => lineDeriv ℝ q y (-v) * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) := by
    simpa only [smul_eq_mul, mul_comm] using
      hphi_int.smul_of_top_left
        (hq_lip.memLp_lineDeriv (μ := modelHaar (E := E)) (-v))
  have hneg_lhs : Integrable
      (fun y => -(partialDeriv (E := E) i
        (vwIntegrandOnE (I := I) g α X i) y * phiOnE (I := I) α φ y))
      (modelHaar (E := E)) :=
    hright0.congr hright_ae
  have hlhs : Integrable
      (fun y => partialDeriv (E := E) i
        (vwIntegrandOnE (I := I) g α X i) y * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    integrable_neg_iff.mp (by simpa only [Pi.neg_apply] using hneg_lhs)
  refine ⟨heq, hlhs, ?_⟩
  simpa only [v] using hrhs

/-- On the chart target, `partialDeriv i (vwIntegrandOnE g α X i) y` equals
`partialDeriv i (chartCoeffOnE α X i · chartDensityOnE g α) y` (since the
two functions agree on the open neighborhood `target`). -/
private lemma partialDeriv_vwIntegrandOnE_eq_on_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y =
      partialDeriv (E := E) i
        (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y := by
  unfold partialDeriv
  have hOpen : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_eq : vwIntegrandOnE (I := I) g α X i =ᶠ[𝓝 y]
      (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) := by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact vwIntegrandOnE_apply_of_mem (I := I) g α X i hz
  rw [h_eq.fderiv_eq]

/-- On the chart target, `partialDeriv i (phiOnE α φ) y` equals
`partialDeriv i (scalarOnE α φ) y`. -/
private lemma partialDeriv_phiOnE_eq_on_target [I.Boundaryless]
    (α : M) (φ : M → ℝ) (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    partialDeriv (E := E) i (phiOnE (I := I) α φ) y =
      partialDeriv (E := E) i (scalarOnE (I := I) α φ) y := by
  unfold partialDeriv
  rw [fderiv_phiOnE_eq_fderiv_scalarOnE (I := I) α φ hy]

/-- The pointwise identity: `localDivergence g α X (symm y) · ρ_α(symm y) = ∑_i partialDeriv i (vwIntegrandOnE) y` for `y ∈ target`. -/
private lemma localDivergence_mul_chartDensity_chart_target_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartDensity (I := I) g α ((extChartAt I α).symm y) *
      localDivergence (I := I) g α X ((extChartAt I α).symm y) =
      ∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y := by
  classical
  have hsymm : (extChartAt I α) ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy
  have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hsymmbase : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
    exact hsymmsrc
  have hρ_pos : 0 < chartDensity (I := I) g α ((extChartAt I α).symm y) :=
    chartDensity_pos (I := I) g α hsymmbase
  rw [localDivergence_def]
  field_simp
  rw [hsymm]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (partialDeriv_vwIntegrandOnE_eq_on_target (I := I) g α X i hy).symm

/-- The pointwise identity at `symm y`: `tangentSectionAction X φ (symm y) =
∑_i chartCoeff α X i (symm y) · partialDeriv i (scalarOnE α φ) y`, for `y ∈ target`
under `[I.Boundaryless]`. -/
private lemma tangentSectionAction_chart_target_apply [I.Boundaryless]
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i ((extChartAt I α).symm y) *
          partialDeriv (E := E) i (scalarOnE (I := I) α φ) y := by
  classical
  have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hsymmchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
    exact hsymmsrc
  have htsa := tangentSectionAction_chartLocal_of_boundaryless (I := I) α X hφ hsymmchart
  rw [htsa]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [(extChartAt I α).right_inv hy]

/-- Continuity of `localDivergence g α X` on the chart base set under
`[I.Boundaryless]`. -/
lemma localDivergence_continuousOn_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (localDivergence (I := I) g α X) (chartAt H α).source := by
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    localDivergence_contMDiffOn (I := I) g α X
  have hdomain_eq : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target = (chartAt H α).source := by
    ext x
    constructor
    · intro hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
      · rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
        have : x ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
        exact (extChartAt I α).map_source this
  rw [← hdomain_eq]
  exact hsmooth.continuousOn

/-- Measurability of the product `localDivergence g α X · φ` when `φ` has
tsupport contained in the chart source. The integrand vanishes outside the
chart source, where `localDivergence` may take junk values. -/
lemma localDivergence_mul_phi_measurable [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ_cont : Continuous φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    Measurable (fun x => localDivergence (I := I) g α X x * φ x) := by
  set s : Set M := (chartAt H α).source
  have hs_open : IsOpen s := (chartAt H α).open_source
  have hs_meas : MeasurableSet s := hs_open.measurableSet
  have hldiv_cont_s : ContinuousOn (localDivergence (I := I) g α X) s :=
    localDivergence_continuousOn_baseSet (I := I) g α X
  have hφ_cont_s : ContinuousOn φ s := hφ_cont.continuousOn
  have hprod_cont_s : ContinuousOn
      (fun x => localDivergence (I := I) g α X x * φ x) s :=
    hldiv_cont_s.mul hφ_cont_s
  have h_zero_off : ∀ x ∉ s, localDivergence (I := I) g α X x * φ x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have : φ x = 0 := by
      by_contra hne
      exact hxsupp (subset_tsupport _ hne)
    rw [this, mul_zero]
  classical
  have hzero_cont : ContinuousOn (fun _ : M => (0 : ℝ)) sᶜ := continuousOn_const
  have hpiecewise_meas : Measurable (s.piecewise
      (fun x => localDivergence (I := I) g α X x * φ x)
      (fun _ : M => (0 : ℝ))) :=
    hprod_cont_s.measurable_piecewise hzero_cont hs_meas
  have h_eq : (fun x => localDivergence (I := I) g α X x * φ x) =
      s.piecewise (fun x => localDivergence (I := I) g α X x * φ x)
        (fun _ : M => (0 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h_zero_off x hx]
  rw [h_eq]
  exact hpiecewise_meas

/-- Pull the LHS of the IBP back to the chart target. The integrand on the
target is `(∑_i partialDeriv i (vwIntegrandOnE)) · phiOnE α φ`. -/
private lemma lhs_chart_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ_cont : Continuous φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  classical
  set h : M → ℝ := fun x => localDivergence (I := I) g α X x * φ x with hh_def
  have hh_meas : Measurable h :=
    localDivergence_mul_phi_measurable (I := I) g α X hφ_cont hφ_supp
  rw [integral_chartLocalMeasure (I := I) g α h hh_meas]
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  have hρ_localDiv :=
    localDivergence_mul_chartDensity_chart_target_apply (I := I) g α X hy
  change chartDensity (I := I) g α ((extChartAt I α).symm y) *
        (localDivergence (I := I) g α X ((extChartAt I α).symm y)
          * φ ((extChartAt I α).symm y)) = _
  rw [show chartDensity (I := I) g α ((extChartAt I α).symm y) *
          (localDivergence (I := I) g α X ((extChartAt I α).symm y) *
            φ ((extChartAt I α).symm y)) =
        (chartDensity (I := I) g α ((extChartAt I α).symm y) *
          localDivergence (I := I) g α X ((extChartAt I α).symm y)) *
            φ ((extChartAt I α).symm y) from by ring]
  rw [hρ_localDiv]
  rw [← phiOnE_apply_of_mem (I := I) α φ hy]

/-- Pull the RHS of the IBP back to the chart target. The integrand on the
target is `ρ_α(symm y) · ∑_i (X^i_α(symm y)) · partialDeriv i (φ ∘ symm) y`. -/
private lemma rhs_chart_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y in (extChartAt I α).target,
        chartDensityOnE (I := I) g α y *
          (∑ i : Fin (Module.finrank ℝ E),
            chartCoeffOnE (I := I) α X i y *
              partialDeriv (E := E) i (scalarOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
  classical
  have htsa_cont : Continuous (tangentSectionAction (I := I) X φ) :=
    (tangentSectionAction_contMDiff (I := I) X hφ).continuous
  rw [integral_chartLocalMeasure (I := I) g α (tangentSectionAction (I := I) X φ)
      htsa_cont.measurable]
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  have htsa_eq := tangentSectionAction_chart_target_apply (I := I) α X hφ hy
  change chartDensity (I := I) g α ((extChartAt I α).symm y) *
      tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) = _
  rw [htsa_eq]
  rfl

/-- Pull the tangent-action integral of a chart-Lipschitz scalar to its
almost-everywhere coordinate line-derivative representative. -/
private lemma rhs_lip_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (phiOnE (I := I) α φ))
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y in (extChartAt I α).target,
        ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) := by
  classical
  calc
    ∫ x, tangentSectionAction (I := I) X φ x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, chartActionM (I := I) α X φ x
          ∂(chartLocalMeasure (I := I) g α) :=
      integral_congr_ae (tangent_ae_chart (I := I) g α X hφ_lip hφ_supp)
    _ = _ := by
      rw [integral_chartLocalMeasure (I := I) g α
        (chartActionM (I := I) α X φ)
        (chartActionM_meas (I := I) α X hφ_lip.continuous)]
      refine setIntegral_congr_fun
        (measurableSet_extChartAt_target (I := I) α) ?_
      intro y hy
      have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      have hsymmchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
        rw [← extChartAt_source_eq_chartAt_source (I := I)]
        exact hsymmsrc
      have hcoord : chartCoordZero (I := I) α ((extChartAt I α).symm y) = y := by
        unfold chartCoordZero
        rw [Set.piecewise_eq_of_mem _ _ _ hsymmchart,
          (extChartAt I α).right_inv hy]
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          chartActionM (I := I) α X φ ((extChartAt I α).symm y) = _
      unfold chartActionM
      rw [Set.indicator_of_mem hsymmchart, hcoord]
      unfold chartActionE
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      unfold coeffZero
      rw [Set.piecewise_eq_of_mem _ _ _ hy,
        vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]
      unfold chartDensityOnE
      ring

/-- The intrinsic tangent action of a compactly supported chart-Lipschitz
scalar is integrable for the corresponding chart-local measure. -/
theorem tangent_lip_int [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (chartPullZero (I := I) α φ))
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    Integrable (tangentSectionAction (I := I) X φ)
      (chartLocalMeasure (I := I) g α) := by
  classical
  let μ₀ : Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I α).target
  let w : E → ENNReal := fun y =>
    ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))
  let μ₁ : Measure E := μ₀.withDensity w
  have htarget : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  have hsymm : AEMeasurable (extChartAt I α).symm μ₁ := by
    have hbase : AEMeasurable (extChartAt I α).symm μ₀ := by
      simpa only [μ₀] using
        aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) α
    exact hbase.mono_ac (withDensity_absolutelyContinuous μ₀ w)
  have hw : AEMeasurable w μ₀ := by
    simpa only [w, μ₀] using
      aemeasurable_chartDensity_symm_pullback (I := I) g α
  have hw_top : ∀ᵐ y ∂μ₀, w y < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => by simp only [w, ENNReal.ofReal_lt_top]
  have hidx (i : Fin (Module.finrank ℝ E)) :=
    ibp_lip_index (I := I) g α X hφ_lip hφ_compactSupp hφ_supp i
  have hsum : Integrable
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        vwIntegrandOnE (I := I) g α X i y *
          lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
      (modelHaar (E := E)) := by
    exact integrable_finset_sum _ fun i _ => (hidx i).2.2
  have hsum_on : Integrable
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        vwIntegrandOnE (I := I) g α X i y *
          lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) μ₀ := by
    simpa only [μ₀] using hsum.integrableOn
  have hweighted : Integrable
      (fun y => (w y).toReal •
        chartActionM (I := I) α X φ ((extChartAt I α).symm y)) μ₀ := by
    refine hsum_on.congr ?_
    filter_upwards [ae_restrict_mem htarget] with y hy
    have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    have hsymmchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      rw [← extChartAt_source_eq_chartAt_source (I := I)]
      exact hsymmsrc
    have hcoord : chartCoordZero (I := I) α ((extChartAt I α).symm y) = y := by
      unfold chartCoordZero
      rw [Set.piecewise_eq_of_mem _ _ _ hsymmchart,
        (extChartAt I α).right_inv hy]
    have hdens : (w y).toReal =
        chartDensity g α ((extChartAt I α).symm y) := by
      have hbase : (extChartAt I α).symm y ∈
          (trivializationAt E (TangentSpace I) α).baseSet := hsymmchart
      exact ENNReal.toReal_ofReal
        (chartDensity_pos (I := I) g α hbase).le
    symm
    change (w y).toReal *
        chartActionM (I := I) α X φ ((extChartAt I α).symm y) = _
    rw [hdens]
    unfold chartActionM
    rw [Set.indicator_of_mem hsymmchart, hcoord]
    unfold chartActionE
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    unfold coeffZero
    rw [Set.piecewise_eq_of_mem _ _ _ hy,
      vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]
    unfold chartDensityOnE
    ring
  have hrep : Integrable (chartActionM (I := I) α X φ)
      (chartLocalMeasure (I := I) g α) := by
    have hact := chartActionM_meas (I := I) α X hφ_lip.continuous
    have hmap : Integrable (chartActionM (I := I) α X φ)
        (Measure.map (extChartAt I α).symm μ₁) :=
      (integrable_map_measure hact.aestronglyMeasurable hsymm).2
        ((integrable_withDensity_iff_integrable_smul₀' hw hw_top).2 hweighted)
    simpa only [chartLocalMeasure, μ₁, μ₀, w] using hmap
  exact hrep.congr
    (tangent_ae_chart (I := I) g α X hφ_lip hφ_supp).symm

/-- Each summand `∂_i (vwIntegrandOnE) · phiOnE α φ` is `C^∞` on `E` and has
compact support. -/
private lemma summand_int [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
        phiOnE (I := I) α φ y) (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp
  have hphi_compactSupp : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupp hφ_supp
  have hI_smooth : ContDiff ℝ ∞
      (fun y => partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
        phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target :=
        (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).fderiv_of_isOpen
          (isOpen_extChartAt_target (I := I) α) (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target := hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul hphi_smooth.contDiffOn
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI_compactSupp : HasCompactSupport
      (fun y => partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
          phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupp

/-- Each summand `vwIntegrandOnE · ∂_i (phiOnE α φ)` is integrable. -/
private lemma summand_int' [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      vwIntegrandOnE (I := I) g α X i y *
        partialDeriv (E := E) i (phiOnE (I := I) α φ) y) (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp
  have hI_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          partialDeriv (E := E) i (phiOnE (I := I) α φ) y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_target (I := I) α hφ_supp) ?_ ?_
    · have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (extChartAt I α).target :=
        (hphi_smooth.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (partialDeriv (E := E) i (phiOnE (I := I) α φ))
          (extChartAt I α).target := hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hpartial_zero : partialDeriv (E := E) i (phiOnE (I := I) α φ) y = 0 := by
        unfold partialDeriv
        have hfderiv_eq : fderiv ℝ (phiOnE (I := I) α φ) y =
            fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
          hphi_zero_on_nhd.fderiv_eq
        rw [hfderiv_eq]
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl, fderiv_const]
        rfl
      rw [hpartial_zero, mul_zero]
  have hI_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          partialDeriv (E := E) i (phiOnE (I := I) α φ) y) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hpartial_zero : partialDeriv (E := E) i (phiOnE (I := I) α φ) y = 0 := by
      unfold partialDeriv
      have hfderiv_eq : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [hfderiv_eq]
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl, fderiv_const]
      rfl
    rw [hpartial_zero, mul_zero]
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupp

/-- The chart-local IBP. -/
theorem chart_local_ibp [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      -∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [lhs_chart_target (I := I) g α X hφ.continuous hφ_supp]
  rw [rhs_chart_target (I := I) g α X hφ]
  have hLHS_to_E :
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target)
      (f := fun y => (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y) ?_
    intro y hy
    have hphi_zero : phiOnE (I := I) α φ y = 0 :=
      phiOnE_apply_of_notMem (I := I) α φ hy
    simp only [hphi_zero, mul_zero]
  rw [hLHS_to_E]
  have h_sum_int :
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
    rw [show (fun y => (∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
              phiOnE (I := I) α φ y)
          = (fun y => ∑ i : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
              phiOnE (I := I) α φ y) from
      by funext y; rw [Finset.sum_mul]]
    rw [integral_finset_sum]
    intro i _
    exact summand_int (I := I) g α X hφ hφ_compactSupp hφ_supp i
  rw [h_sum_int]
  have h_each : ∀ i : Fin (Module.finrank ℝ E),
      ∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E))
      = -∫ y, vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y
          ∂(modelHaar (E := E)) := by
    intro i
    have h_ibp := ibp_per_index (I := I) g α X hφ hφ_compactSupp hφ_supp i
    change ∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)
        * phiOnE (I := I) α φ y
      ∂(modelHaar (E := E))
      = -∫ y, vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E))
    linarith [h_ibp]
  rw [Finset.sum_congr rfl (fun i _ => h_each i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          -∫ y, vwIntegrandOnE (I := I) g α X i y *
              partialDeriv (E := E) i (phiOnE (I := I) α φ) y
            ∂(modelHaar (E := E))) =
        - ∑ i : Fin (Module.finrank ℝ E),
          ∫ y, vwIntegrandOnE (I := I) g α X i y *
              partialDeriv (E := E) i (phiOnE (I := I) α φ) y
            ∂(modelHaar (E := E)) from by
      rw [← Finset.sum_neg_distrib]]
  have h_sum_back :
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y
          ∂(modelHaar (E := E)) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
    rw [← integral_finset_sum]
    intro i _
    exact summand_int' (I := I) g α X hφ hφ_compactSupp hφ_supp i
  rw [h_sum_back]
  have hE_to_target :
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target)
      (f := fun y => ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            partialDeriv (E := E) i (phiOnE (I := I) α φ) y) ?_]
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [vwIntegrandOnE_apply_of_notMem (I := I) g α X i hy, zero_mul]
  rw [hE_to_target]
  refine congrArg Neg.neg ?_
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  change (∑ i : Fin (Module.finrank ℝ E),
      vwIntegrandOnE (I := I) g α X i y *
          partialDeriv (E := E) i (phiOnE (I := I) α φ) y) =
      chartDensityOnE (I := I) g α y *
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α X i y *
            partialDeriv (E := E) i (scalarOnE (I := I) α φ) y
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]
  rw [partialDeriv_phiOnE_eq_on_target (I := I) α φ i hy]
  ring

/-- The chart-local integration-by-parts identity when the zero-extended chart
pullback of the scalar factor is Lipschitz. -/
theorem chart_local_ibp_lip [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} {C : NNReal}
    (hφ_lip : LipschitzWith C (chartPullZero (I := I) α φ))
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x
        ∂(chartLocalMeasure (I := I) g α) =
      -∫ x, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g α) := by
  classical
  have hφ_cont : Continuous φ :=
    phi_cont_of_lip (I := I) α hφ_lip hφ_supp
  rw [lhs_chart_target (I := I) g α X hφ_cont hφ_supp]
  rw [rhs_lip_target (I := I) g α X hφ_lip hφ_supp]
  have hidx (i : Fin (Module.finrank ℝ E)) :=
    ibp_lip_index (I := I) g α X hφ_lip hφ_compactSupp hφ_supp i
  have hLHS_to_E :
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := modelHaar (E := E)) (s := (extChartAt I α).target)
      (f := fun y => (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
          phiOnE (I := I) α φ y) ?_
    intro y hy
    change (∑ i : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
        phiOnE (I := I) α φ y = 0
    rw [phiOnE_apply_of_notMem (I := I) α φ hy, mul_zero]
  rw [hLHS_to_E]
  have h_sum_int :
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y
          ∂(modelHaar (E := E)) := by
    rw [show (fun y => (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y) from by
      funext y
      rw [Finset.sum_mul]]
    rw [integral_finset_sum]
    intro i _
    exact (hidx i).2.1
  rw [h_sum_int]
  rw [Finset.sum_congr rfl (fun i _ => (hidx i).1)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        -∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E))) =
      -∑ i : Fin (Module.finrank ℝ E),
        ∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E)) from by
    rw [← Finset.sum_neg_distrib]]
  have h_sum_back :
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E)) =
      ∫ y, ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) := by
    rw [← integral_finset_sum]
    intro i _
    exact (hidx i).2.2
  rw [h_sum_back]
  have hE_to_target :
      ∫ y, ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := modelHaar (E := E)) (s := (extChartAt I α).target)
      (f := fun y => ∑ i : Fin (Module.finrank ℝ E),
        vwIntegrandOnE (I := I) g α X i y *
          lineDeriv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) ?_]
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [vwIntegrandOnE_apply_of_notMem (I := I) g α X i hy, zero_mul]
  rw [hE_to_target]

end DivergenceTheorem
end Integral
end DifferentialGeometry
