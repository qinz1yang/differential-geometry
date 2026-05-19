import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.TangentAction
import RicciFlower.Analysis.DivergenceTheorem.Ibp
import RicciFlower.Analysis.DivergenceTheorem.ChartInvariance
import RicciFlower.Analysis.DivergenceTheorem.POUReduction
import RicciFlower.Analysis.Volume.Family
import RicciFlower.Analysis.Volume.Glue
import RicciFlower.Analysis.Volume.Invariance
import RicciFlower.Analysis.Volume.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

/-!
# Divergence theorem on a closed Riemannian manifold

For a smooth Riemannian metric `g` on a closed (compact and boundaryless)
smooth manifold `M`, and a smooth tangent section `X`, the integral of the
global divergence `divergence_g g X` against the canonical Riemannian volume
measure vanishes:
$$\int_M \operatorname{div}_g(X)\,d\mu_g = 0.$$

This is the divergence theorem for a manifold without boundary. The proof
proceeds by chart-localization through the canonical chart-atlas partition of
unity:

1. Decompose the global integral into a finite sum of chart-local integrals
   weighted by the partition of unity (from `Family.lean`).
2. On each chart, identify the global divergence with the Voss–Weyl chart-local
   divergence (`voss_weyl_divergence_formula`).
3. Apply the chart-local integration-by-parts identity (`chart_local_ibp`)
   with the partition function as the test function — this turns each summand
   into the integral of `tangentSectionAction X (ρ_α)` against the chart-local
   measure.
4. Use chart-invariance of the chart-local measure on overlap to rewrite each
   chart-local integral as an integral against the global measure.
5. Sum over the partition: by linearity of the tangent action and the fact
   that the partition sums to `1`, the total integrand is `tangentSectionAction
   X` of a constant function, which vanishes.

## Main results

* `chartLocalMeasure_integral_eq_of_support_in_overlap`: Bochner analogue of
  `chartLocalMeasure_lintegral_eq_of_support_in_overlap`.
* `integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart`: for a
  function `f : M → ℝ` continuous and supported inside a single chart, the
  integral against the global measure equals the integral against the
  chart-local measure at any chart whose source contains the support.
* `integral_divergence_eq_zero_of_compact`: the divergence theorem on a closed
  Riemannian manifold.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace RicciFlower
namespace Analysis
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open RicciFlower.Analysis.Volume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Bochner overlap-equality for the chart-local measure

If a real-valued function vanishes outside the overlap of two chart sources,
its Bochner integrals against the two chart-local measures coincide. This is
the Bochner analogue of `chartLocalMeasure_lintegral_eq_of_support_in_overlap`,
proved directly via `chartLocalMeasure_restrict_overlap_eq` and
`setIntegral_eq_integral_of_forall_compl_eq_zero`. -/

/-- Bochner version of `chartLocalMeasure_lintegral_eq_of_support_in_overlap`:
if `f : M → ℝ` vanishes outside the overlap of two chart sources, its Bochner
integrals against the two chart-local measures agree. -/
lemma chartLocalMeasure_integral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    (f : M → ℝ)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have h₀ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₀) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have h₁ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₁) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  rw [h₀, h₁]
  change ∫ x, f x ∂((chartLocalMeasure (I := I) g x₀).restrict U)
      = ∫ x, f x ∂((chartLocalMeasure (I := I) g x₁).restrict U)
  rw [chartLocalMeasure_restrict_overlap_eq (I := I) g x₀ x₁]

/-! ## Continuity and integrability of certain integrands -/

/-- A continuous real-valued function on a compact manifold whose topological
support sits inside a chart source is integrable against the chart-local
measure at that chart. The chart-local measure is finite on the support
because the support is compact and contained in the chart source. -/
private lemma integrable_of_compactSupport_subset_chartSource
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  -- `tsupport f` is closed in compact `M`, hence compact.
  have hsupp_compact : IsCompact (tsupport f) :=
    .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
  -- The chart-local measure of `tsupport f` is finite.
  have hμ_supp : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_supp
  -- Bound `f` in sup norm.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  -- Pointwise bound `‖f x‖ ≤ C * indicator (tsupport f) 1 x`.
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hfx_zero]; simp
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, ENNReal.ofReal C *
            (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
    _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α (tsupport f) := by
          rw [lintegral_const_mul _ ((measurable_const).indicator
            (isClosed_tsupport _).measurableSet)]
          rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
          rw [setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp

/-! ## Single-chart integral identity

For a continuous real-valued function `f : M → ℝ` whose topological support
sits inside a single chart source `(chartAt H α₀).source`, the integral of
`f` against the global Riemannian volume measure agrees with the integral
against the chart-local measure at `α₀`. -/

/-- If `f : M → ℝ` is continuous on a closed `M` and `tsupport f ⊆ (chartAt H
α₀).source`, then `∫ f dμ_g = ∫ f d(chartLocalMeasure g α₀)`. The identity
holds because the global measure decomposes as a finite sum over the
chart-atlas partition of unity, each summand can be transferred to the chart at
`α₀` via the overlap-equality lemma, and the partition sums to `1`. -/
lemma integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α₀).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g α₀) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  -- Step 1: the global integral as a finite sum of weighted chart-local integrals.
  have h_step1 : ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := f) hf_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step1]
  -- Step 2: For each α ∈ S, transfer the integral from `chartLocalMeasure g α` to
  -- `chartLocalMeasure g α₀`.
  have h_step2 : ∀ α ∈ S,
      ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) := by
    intro α _
    refine chartLocalMeasure_integral_eq_of_support_in_overlap (I := I) g α α₀
      (fun x => f x * ρ α x) ?_
    intro x hx
    simp only
    by_cases hxα : x ∈ (chartAt H α).source
    · -- `x ∉ chart α₀ source`, so `x ∉ tsupport f`, hence `f x = 0`.
      have hxα₀ : x ∉ (chartAt H α₀).source := fun hxα₀' => hx ⟨hxα, hxα₀'⟩
      have hxnotin : x ∉ tsupport f := fun h => hxα₀ (hf_supp h)
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hfx_zero, zero_mul]
    · -- `x ∉ chart α source`, so `x ∉ tsupport (ρ α)`, hence `ρ α x = 0`.
      have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hρα_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step2]
  -- Step 3: Pull the finite sum inside the integral.
  -- Each `f * ρ_α` is continuous, with `tsupport (f * ρ_α) ⊆ tsupport f ⊆ chart α₀ source`.
  have h_each_int : ∀ α ∈ S, Integrable (fun x : M => f x * ρ α x)
      (chartLocalMeasure (I := I) g α₀) := by
    intro α _
    have hcont : Continuous (fun x : M => f x * ρ α x) :=
      hf_cont.mul (ρ α).contMDiff.continuous
    -- `tsupport (f * ρ α) ⊆ tsupport f` (since the product vanishes wherever `f` does).
    have hsupp_sub : tsupport (fun x : M => f x * ρ α x) ⊆ tsupport f := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hfx : f x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by rw [hfx, zero_mul])
    exact integrable_of_compactSupport_subset_chartSource (I := I) g α₀
      hcont (hsupp_sub.trans hf_supp)
  rw [show (∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀))
      = ∫ x, ∑ α ∈ S, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) from
        (integral_finset_sum (μ := chartLocalMeasure (I := I) g α₀) S h_each_int).symm]
  -- Step 4: `∑ α ∈ S, f x * ρ α x = f x` pointwise.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [← Finset.mul_sum]
  have hsum_one : ∑ α ∈ S, ρ α x = 1 := by
    have hfins : ρ.finsupport x ⊆ S := by
      intro α hα
      rw [chartAtlasPOU_finset_mem]
      rw [ρ.mem_finsupport, Function.mem_support] at hα
      exact ⟨x, hα⟩
    exact ρ.sum_finsupport' x (mem_univ x) hfins
  rw [hsum_one, mul_one]

/-! ## The closed-manifold divergence theorem -/

/-- **Divergence theorem on a closed Riemannian manifold.**
For any smooth tangent section `X` on a closed (compact and boundaryless)
smooth Riemannian manifold `(M, g)`, the integral of the divergence
`divergence_g g X` against the canonical Riemannian volume measure vanishes. -/
theorem integral_divergence_eq_zero_of_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergence_g (I := I) g X x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  -- Setup: canonical chart-atlas POU and its finite support set on compact `M`.
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  -- `divergence_g g X` is smooth, hence continuous.
  have hdiv_smooth : ContMDiff I 𝓘(ℝ) ∞ (divergence_g (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  have hdiv_cont : Continuous (divergence_g (I := I) g X) := hdiv_smooth.continuous
  -- Each `ρ_α` has compact support on a compact manifold.
  have hρα_compactSupp : ∀ α : M, HasCompactSupport (ρ α : M → ℝ) := fun α =>
    HasCompactSupport.of_compactSpace _
  -- Step (a): expand the global integral as a finite sum of weighted chart-local integrals.
  have h_step_a : ∫ x, divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, divergence_g (I := I) g X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := divergence_g (I := I) g X) hdiv_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step_a]
  -- Step (b): on each `chart α` source, replace `divergence_g g X` with the
  -- chart-local Voss–Weyl divergence `localDivergence g α X` (Voss–Weyl formula).
  have h_step_b : ∀ α ∈ S,
      ∫ x, divergence_g (I := I) g X x * ρ α x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    -- Pointwise: either `x ∈ (chart α).source` (apply Voss–Weyl) or `ρ α x = 0`.
    by_cases hxα : x ∈ (chartAt H α).source
    · simp only [voss_weyl_divergence_formula (I := I) g α X hxα]
    · -- `x ∉ chart α source` ⇒ `x ∉ tsupport (ρ α)` ⇒ `ρ α x = 0`.
      have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      simp only [hρα_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step_b]
  -- Step (c): apply chart-local IBP at each α with test function `ρ_α`.
  -- This converts each chart-local divergence integral into minus the tangent-action integral.
  have h_step_c : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp (I := I) g α X (ρ α).contMDiff (hρα_compactSupp α) (hρsub α)
  rw [Finset.sum_congr rfl h_step_c]
  -- Pull the negation outside the finite sum.
  rw [show (∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α))
      = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α)) from by
    rw [← Finset.sum_neg_distrib]]
  -- Step (d): rewrite each chart-local integral of the tangent action against the
  -- chart-local measure as the corresponding integral against the global measure,
  -- using `integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart`.
  have hAct_smooth : ∀ α : M,
      ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X (ρ α : M → ℝ)) := fun α =>
    tangentSectionAction_contMDiff (I := I) X (ρ α).contMDiff
  have hAct_cont : ∀ α : M,
      Continuous (tangentSectionAction (I := I) X (ρ α : M → ℝ)) := fun α =>
    (hAct_smooth α).continuous
  -- `tsupport (tangentSectionAction X (ρ α)) ⊆ tsupport (ρ α) ⊆ (chart α).source`.
  have hAct_supp : ∀ α : M,
      tsupport (tangentSectionAction (I := I) X (ρ α : M → ℝ)) ⊆ (chartAt H α).source := by
    intro α
    refine subset_trans ?_ (hρsub α)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    -- `x ∈ support (tangentSectionAction X (ρ α))` ⇒ `mfderiv (ρ α) x (X x) ≠ 0`.
    -- This forces `x ∈ tsupport (ρ α)`: otherwise `ρ α` vanishes on a neighborhood of `x`,
    -- making `mfderiv (ρ α) x = 0`.
    rw [Function.mem_support] at hx
    by_contra hne
    have h_open : IsOpen (tsupport (ρ α : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev : (ρ α : M → ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hne] with z hz
      by_contra hne'
      exact hz (subset_tsupport _ hne')
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (ρ α : M → ℝ) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev]
      rw [mfderiv_const]; rfl
    have hAct_zero : tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
      change mfderiv I 𝓘(ℝ) (ρ α : M → ℝ) x (X x) = 0
      rw [hmfderiv_zero]; rfl
    exact hx hAct_zero
  have h_step_d : ∀ α ∈ S,
      ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    exact (integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
      (I := I) g α (hAct_cont α) (hAct_supp α)).symm
  rw [Finset.sum_congr rfl h_step_d]
  -- Step (e): swap the finite sum with the integral, then identify the integrand
  -- with `tangentSectionAction X (∑ α ∈ S, ρ α)`. Since `∑ α ∈ S, ρ α = 1` on M,
  -- the action vanishes by `tangentSectionAction_const`.
  -- Each summand is integrable: continuous on compact M, against finite μ_g.
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_each_int : ∀ α ∈ S, Integrable
      (fun x : M => tangentSectionAction (I := I) X (ρ α : M → ℝ) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    -- Continuous on compact M and μ_g is finite, so integrable.
    obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖tangentSectionAction (I := I) X (ρ α : M → ℝ) x‖ ≤ C := by
      have hCpt := (isCompact_univ (X := M)).image (hAct_cont α).norm
      obtain ⟨C, hCmem⟩ := hCpt.bddAbove
      exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
    exact (integrable_const C).mono' (hAct_cont α).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  rw [show (∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
        (integral_finset_sum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S h_each_int).symm]
  -- Now show the inner sum vanishes pointwise via `tangentSectionAction_finset_sum`
  -- and `tangentSectionAction_const`.
  have h_pt : ∀ x : M,
      ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
    intro x
    -- `∑ α ∈ S, tangentSectionAction X (ρ α) x = tangentSectionAction X (∑ α ∈ S, ρ α) x`.
    have hMDiff_each : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
      fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
    have hcomm := tangentSectionAction_finset_sum (I := I) X S
      (fun α => ((ρ α : M → ℝ))) x hMDiff_each
    rw [← hcomm]
    -- `∑ α ∈ S, ρ α` is `=ᶠ[𝓝 x] 1` (in fact, equal to `1` on all of `M`), so the action vanishes.
    have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
        (fun _ : M => (1 : ℝ)) := by
      filter_upwards [ρ.eventually_finsupport_subset x] with y hy
      have hyfins_sub_S : ρ.finsupport y ⊆ S := by
        intro α hα
        rw [chartAtlasPOU_finset_mem]
        rw [ρ.mem_finsupport, Function.mem_support] at hα
        exact ⟨y, hα⟩
      exact ρ.sum_finsupport' y (mem_univ y) hyfins_sub_S
    unfold tangentSectionAction
    -- `∑ α ∈ S, (ρ α : M → ℝ)` is a function `M → ℝ` whose value at `y` is `∑ α ∈ S, (ρ α : M → ℝ) y`.
    have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
      funext y
      rw [Finset.sum_apply]
    rw [h_fun_eq]
    rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one, mfderiv_const]
    rfl
  rw [show (fun x : M => ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x)
      = (fun _ : M => (0 : ℝ)) from funext h_pt]
  rw [integral_zero, neg_zero]

end DivergenceTheorem
end Analysis
end RicciFlower
