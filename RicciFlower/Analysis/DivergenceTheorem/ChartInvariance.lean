import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.TangentAction
import RicciFlower.Analysis.DivergenceTheorem.Ibp
import RicciFlower.Analysis.Volume.Properties
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.ENNReal.Basic

/-!
# Chart-invariance of the chart-local Voss–Weyl divergence

For a smooth Riemannian metric `g`, a smooth tangent section `X`, and two
points `α β : M`, the chart-local Voss–Weyl divergence agrees on the overlap
of the two chart sources:
$$\text{localDivergence}_g(\alpha, X)(x) = \text{localDivergence}_g(\beta, X)(x)$$
for every `x ∈ (chartAt H α).source ∩ (chartAt H β).source`.

The proof goes via integration testing. For any smooth bump function `φ` with
compact support inside the overlap, the chart-local IBP identity gives
$\int_M \text{localDivergence}_g(\alpha, X) \phi \, d\mu_\alpha = -\int_M \text{tangentSectionAction}(X, \phi) \, d\mu_\alpha$
(and likewise at `β`). The right-hand side is intrinsic — it does not depend
on the chart — and it integrates the same function against two measures that
agree on the overlap. Hence the two left-hand sides agree, and a
density argument upgrades this to pointwise equality on the overlap.
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

/-! ## Equality of integrals against bumps in the overlap

The key step in chart-invariance is the following: for any smooth bump function
`φ` with compact tsupport contained in the overlap of two chart sources, the
chart-local divergences integrate to the same quantity (the integral of
`tangentSectionAction X φ`, which is chart-independent). This uses the IBP at
each of `α, β` plus the chart-invariance of `chartLocalMeasure` on overlaps. -/

/-- For any smooth `φ` with compact tsupport inside the overlap of `α, β`'s
chart sources, the integrals of `localDivergence g α X · φ` against
`chartLocalMeasure g α` and of `localDivergence g β X · φ` against
`chartLocalMeasure g β` are equal. -/
theorem integral_localDivergence_eq_of_overlap_support [I.Boundaryless]
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source ∩ (chartAt H β).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ x, localDivergence (I := I) g β X x * φ x ∂(chartLocalMeasure (I := I) g β) := by
  -- Apply chart-local IBP at α and β.
  have hsupp_α : tsupport φ ⊆ (chartAt H α).source := hφ_supp.trans Set.inter_subset_left
  have hsupp_β : tsupport φ ⊆ (chartAt H β).source := hφ_supp.trans Set.inter_subset_right
  have hibp_α := chart_local_ibp (I := I) g α X hφ hφ_compactSupp hsupp_α
  have hibp_β := chart_local_ibp (I := I) g β X hφ hφ_compactSupp hsupp_β
  -- Both LHSs equal `-∫ tangentSectionAction X φ d·`. Suffices to show
  -- the two RHSs are equal.
  rw [hibp_α, hibp_β]
  -- Now the goal is `-∫ tangentSectionAction X φ dμ_α = -∫ tangentSectionAction X φ dμ_β`.
  refine congrArg Neg.neg ?_
  -- We use the fact that `tangentSectionAction X φ` is supported in
  -- `tsupport φ ⊆ overlap`, and on the overlap, the two measures agree by
  -- `chartLocalMeasure_restrict_overlap_eq`.
  --
  -- Let `U := overlap`. For any measurable `h` with support in `U`:
  --   ∫ h dμ_α = ∫ h dμ_β
  -- because both integrals equal `∫ h d(μ_α.restrict U) = ∫ h d(μ_β.restrict U)`.
  set U : Set M := (chartAt H α).source ∩ (chartAt H β).source with hU_def
  have hU_open : IsOpen U := IsOpen.inter (chartAt H α).open_source (chartAt H β).open_source
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have htsa_supp : ∀ x ∉ U, tangentSectionAction (I := I) X φ x = 0 := by
    intro x hx
    -- x ∉ U ⇒ x ∉ tsupport φ.
    have hxsupp : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    -- φ is identically zero on a neighborhood of x.
    have hOpen_compl : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
    have hphi_zero_on_nhd : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hOpen_compl.mem_nhds hxsupp] with z hz
      by_contra hne
      exact hz (subset_tsupport _ hne)
    -- mfderiv is determined by local behavior, so mfderiv φ x = 0.
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) φ x = 0 := by
      have h_eq : mfderiv I 𝓘(ℝ) φ x = mfderiv I 𝓘(ℝ) (fun _ : M => (0 : ℝ)) x :=
        Filter.EventuallyEq.mfderiv_eq hphi_zero_on_nhd
      rw [h_eq, mfderiv_const]; rfl
    change mfderiv I 𝓘(ℝ) φ x (X x) = 0
    rw [hmfderiv_zero]
    rfl
  -- Now use the restrict-overlap argument.
  have htsa_α : ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ x in U, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero htsa_supp]
  have htsa_β : ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g β) =
      ∫ x in U, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g β) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero htsa_supp]
  rw [htsa_α, htsa_β]
  -- Now both integrals are over `U` against `μ_α.restrict U` and `μ_β.restrict U`,
  -- which are equal by `chartLocalMeasure_restrict_overlap_eq`.
  have h_meas_eq : (chartLocalMeasure (I := I) g α).restrict U =
      (chartLocalMeasure (I := I) g β).restrict U :=
    chartLocalMeasure_restrict_overlap_eq (I := I) g α β
  rw [show ∫ x in U, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X φ x ∂((chartLocalMeasure (I := I) g α).restrict U) from
      rfl]
  rw [show ∫ x in U, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g β) =
        ∫ x, tangentSectionAction (I := I) X φ x ∂((chartLocalMeasure (I := I) g β).restrict U) from
      rfl]
  rw [h_meas_eq]

/-! ## Pointwise chart-invariance via density

For chart-invariance we need to upgrade integral equality (against bumps) to
pointwise equality. We use the open-positive property of `chartLocalMeasure`
on the chart base set. -/

/-- A chart-local measure `chartLocalMeasure g α` is positive on every open
nonempty subset of the chart source whose closure contains a manifold-interior
point. Under `[I.Boundaryless]`, every point is a manifold-interior point. -/
private lemma chartLocalMeasure_open_pos_under_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {V : Set M} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVsub : V ⊆ (chartAt H α).source) :
    0 < chartLocalMeasure (I := I) g α V := by
  classical
  -- Pick a point in V; under boundaryless, every point is interior.
  obtain ⟨x₁, hx₁V⟩ := hVne
  have hx₁_chart : x₁ ∈ (chartAt H α).source := hVsub hx₁V
  have hx₁_ext : x₁ ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx₁_chart
  have hx₁_target : extChartAt I α x₁ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx₁_ext
  have hx₁_int : extChartAt I α x₁ ∈ interior (range I) := by
    -- Under boundaryless, range I = univ, so interior (range I) = univ.
    rw [I.range_eq_univ, interior_univ]; trivial
  -- Apply the existing private lemma `chartLocalMeasure_open_pos_of_mem`.
  -- We need access; since it's private we replicate the proof ingredients.
  -- Direct approach: use `integral_chartLocalMeasure` -- but lemma is private.
  -- Workaround: open chart-local-measure positivity comes from
  -- `riemannianMeasure_isOpenPosMeasure` if we use the global measure.
  -- But we can do it directly via `chartLocalMeasure_lintegral`.
  -- Since `chartLocalMeasure_open_pos_of_mem` is private, prove a bypass.
  -- Replicate the proof structure quickly:
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hind_meas : Measurable (V.indicator (fun _ : M => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hVmeas
  have hlint := chartLocalMeasure_lintegral (I := I) g α hind_meas
  -- chartLocalMeasure V = ∫⁻ x, V.indicator 1 x ∂(chartLocalMeasure g α)
  --   = ∫⁻ y in target, ofReal (density (symm y)) * V.indicator 1 (symm y) d modelHaar
  have hVvol : chartLocalMeasure (I := I) g α V =
      ∫⁻ x, V.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ chartLocalMeasure (I := I) g α := by
    rw [lintegral_indicator hVmeas, setLIntegral_const, one_mul]
  rw [hVvol, hlint]
  -- Goal: 0 < ∫⁻ y in target, ofReal (density (symm y)) * V.indicator 1 (symm y) d modelHaar.
  -- Strategy: the image `(extChartAt I α) '' V` is an open subset of `target` containing `(extChartAt I α) x₁`.
  -- Under boundaryless, `target` is open. The image of an open set inside the chart source
  -- under the chart map is open in `E` (under boundaryless).
  set W : Set E := (extChartAt I α) '' V with hW_def
  have hW_open : IsOpen W :=
    extChartAt_image_isOpen_of_open_subset_source_of_boundaryless (I := I) α hVopen hVsub
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hW_ne : W.Nonempty := ⟨extChartAt I α x₁, x₁, hx₁V, rfl⟩
  have hW_pos : 0 < (modelHaar (E := E)) W := hW_open.measure_pos _ hW_ne
  -- W ⊆ target.
  have hW_sub_T : W ⊆ (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hVsub hxV
    have : (extChartAt I α) x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    rwa [hxy] at this
  -- On W, density > 0 and indicator V (symm y) = 1.
  have hdensity_on_W : ∀ y ∈ W, 0 < chartDensity g α ((extChartAt I α).symm y) := by
    intro y hyW
    rcases hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hVsub hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft]
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hVsub hxV
    exact chartDensity_pos (I := I) g α hxbase
  have hind_on_W : ∀ y ∈ W,
      V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 1 := by
    intro y hyW
    rcases hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hVsub hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft, Set.indicator_of_mem hxV]
  -- ∫⁻ over T ≥ ∫⁻ over W.
  have h_restrict_subset :
      ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E))
        ≤ ∫⁻ y in (extChartAt I α).target,
            ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E)) :=
    lintegral_mono_set hW_sub_T
  refine lt_of_lt_of_le ?_ h_restrict_subset
  -- ∫⁻ over W of `ofReal(density · 1) ≥ ε` for some ε > 0... Actually we need
  -- positivity of the integral over W. Since density > 0 on W and the indicator
  -- is 1 on W, the integrand is > 0 on W (a positive-measure set).
  by_contra h0
  have h0' : ¬ (0 < ∫⁻ y in W,
      ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
        ∂(modelHaar (E := E))) := h0
  have h0 : ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
          ∂(modelHaar (E := E)) ≤ 0 := not_lt.mp h0'
  have h0_eq : ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
          ∂(modelHaar (E := E)) = 0 :=
    le_antisymm h0 (zero_le _)
  -- Then the integrand is a.e. 0 on W. But it's > 0 on W (everywhere).
  -- This contradicts measure W > 0 unless... we need the integrand to be measurable.
  have hT_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  -- AEMeasurable on the restricted measure.
  have haem_density_T : AEMeasurable
      (fun y : E => chartDensity g α ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict (extChartAt I α).target) := by
    have hcontOn : ContinuousOn
        (fun y : E => chartDensity g α ((extChartAt I α).symm y)) (extChartAt I α).target := by
      refine (chartDensity_continuousOn (I := I) g α).comp
        (continuousOn_extChartAt_symm (I := I) α) ?_
      intro y hy
      have : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact hcontOn.aemeasurable hT_meas
  have haem_density_W : AEMeasurable
      (fun y : E => chartDensity g α ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) :=
    haem_density_T.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
  have h1 : AEMeasurable
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
      ((modelHaar (E := E)).restrict W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable haem_density_W
  have hsymm_aem_T : AEMeasurable (extChartAt I α).symm
      ((modelHaar (E := E)).restrict (extChartAt I α).target) :=
    (continuousOn_extChartAt_symm (I := I) α).aemeasurable hT_meas
  have hsymm_aem_W : AEMeasurable (extChartAt I α).symm
      ((modelHaar (E := E)).restrict W) :=
    hsymm_aem_T.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
  have h2 : AEMeasurable
      (fun y : E => V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) :=
    hind_meas.comp_aemeasurable hsymm_aem_W
  have haem_integrand : AEMeasurable
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) := h1.mul h2
  have hae_zero := (MeasureTheory.lintegral_eq_zero_iff' haem_integrand).mp h0_eq
  have hW_ae_zero :
      ∀ᵐ y ∂(modelHaar (E := E)), y ∈ W →
        ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 0 :=
    (MeasureTheory.ae_restrict_iff' hW_meas).mp hae_zero
  have hW_zero : (modelHaar (E := E)) W = 0 := by
    have hyNotW : ∀ᵐ y ∂(modelHaar (E := E)), y ∉ W := by
      filter_upwards [hW_ae_zero] with y hy
      intro hyW
      have hpos : 0 < ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) := by
        rw [hind_on_W y hyW, mul_one]
        exact ENNReal.ofReal_pos.mpr (hdensity_on_W y hyW)
      exact (ne_of_gt hpos) (hy hyW)
    exact measure_eq_zero_iff_ae_notMem.mpr hyNotW
  exact (ne_of_gt hW_pos) hW_zero

/-! ## Chart invariance of `localDivergence`

The proof of chart invariance proceeds by contradiction using the IBP identity
and the open-positive measure property. Given `α β : M` and `x` in the overlap
of their chart sources, suppose `localDivergence_α(x) ≠ localDivergence_β(x)`.
Then by continuity of both sides on the overlap, the difference is nonzero on
some open neighborhood `V` of `x` inside the overlap. Picking a smooth bump
function `φ` with tsupport in `V` and `φ(x) > 0` would yield a nonzero integral
of `(localDivergence_α - localDivergence_β) · φ` against the chart-local
measure (using positivity on open sets), but this integral is zero by the IBP
identity at `α, β` and the chart-invariance of the measure on overlap.
Contradiction. -/

/-- The continuous-function pointwise positivity, in the form we need for the
contradiction step: if `f` is continuous on an open `U`, `f x > 0` at some
`x ∈ U`, then there's an open neighborhood `V` of `x` (with `V ⊆ U`) on which
`f > f(x)/2`. -/
private lemma exists_open_nbhd_positive
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hfcont : ContinuousOn f U)
    {x : M} (hxU : x ∈ U) (hfx : 0 < f x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, f x / 2 < f y := by
  classical
  have hfx2 : 0 < f x / 2 := by positivity
  -- Use the preimage of `(f x / 2, ∞)` under the restriction.
  have hfcont_at : ContinuousAt f x :=
    (hfcont x hxU).continuousAt (hU.mem_nhds hxU)
  have hfx_lt : f x / 2 < f x := by linarith
  obtain ⟨V₀, hV₀_nhd, hV₀⟩ : ∃ V₀ ∈ 𝓝 x, ∀ y ∈ V₀, f x / 2 < f y := by
    have := hfcont_at.eventually (p := fun y => f x / 2 < y) ?_
    · exact ⟨_, this, fun y hy => hy⟩
    · -- p is open: `Ioi (f x / 2)`.
      exact eventually_nhds_iff.mpr ⟨Ioi (f x / 2), fun _ => id, isOpen_Ioi, hfx_lt⟩
  rcases mem_nhds_iff.mp hV₀_nhd with ⟨W, hW_sub, hW_open, hxW⟩
  refine ⟨W ∩ U, hW_open.inter hU, ⟨hxW, hxU⟩, Set.inter_subset_right, ?_⟩
  intro y hy
  exact hV₀ y (hW_sub hy.1)

/-- Smooth bump function existence, packaged: for any `x ∈ V` (open), there is
a `φ : M → ℝ`, `C^∞` with compact support, `0 ≤ φ`, `φ(x) > 0`, `tsupport φ ⊆
V`. We use Mathlib's `SmoothBumpFunction`. -/
private lemma exists_smooth_bump_in_open [T2Space M]
    {V : Set M} (hVopen : IsOpen V) {x : M} (hxV : x ∈ V) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ V ∧ (∀ y, 0 ≤ φ y) ∧ 0 < φ x := by
  classical
  -- Use `nhds_basis_support` (Mathlib `BumpFunction.lean`): for any V ∈ 𝓝 x,
  -- there's a SmoothBumpFunction f with tsupport f ⊆ V and x ∈ support f.
  have hVnhd : V ∈ 𝓝 x := hVopen.mem_nhds hxV
  -- The smooth bump function centered at `x` with tsupport in `V`.
  -- Take any `f : SmoothBumpFunction I x` (these exist by `Nonempty`).
  -- Then tsupport `f.updateRIn` for sufficiently small rIn... Actually let's use
  -- `nhds_basis_tsupport`: for any V ∈ 𝓝 x, ∃ f with tsupport f ⊆ V.
  obtain ⟨f, _, hfsupp_subset⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hVnhd
  refine ⟨f, f.contMDiff, f.hasCompactSupport, hfsupp_subset, ?_, ?_⟩
  · intro y
    exact f.nonneg
  · -- f x = 1 since x is the center.
    rw [f.eq_one]
    exact one_pos

/-! ## Chart invariance: the main theorem -/

/-- Helper for the positive case of chart invariance. -/
private theorem localDivergence_chart_invariance_pos [I.Boundaryless]
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) (hx_β : x ∈ (chartAt H β).source)
    (hΔpos : 0 < localDivergence (I := I) g α X x - localDivergence (I := I) g β X x) :
    False := by
  classical
  set U : Set M := (chartAt H α).source ∩ (chartAt H β).source with hU_def
  have hUopen : IsOpen U := IsOpen.inter (chartAt H α).open_source (chartAt H β).open_source
  have hxU : x ∈ U := ⟨hx_α, hx_β⟩
  set Δ : M → ℝ := fun y => localDivergence (I := I) g α X y - localDivergence (I := I) g β X y
    with hΔ_def
  have hα_contOn : ContinuousOn (localDivergence (I := I) g α X) U :=
    (localDivergence_continuousOn_baseSet (I := I) g α X).mono Set.inter_subset_left
  have hβ_contOn : ContinuousOn (localDivergence (I := I) g β X) U :=
    (localDivergence_continuousOn_baseSet (I := I) g β X).mono Set.inter_subset_right
  have hΔ_contOn : ContinuousOn Δ U := hα_contOn.sub hβ_contOn
  -- Find an open V ⊆ U with x ∈ V and Δ y > Δ x / 2 on V.
  obtain ⟨V, hVopen, hxV, hVU, hΔ_pos⟩ :=
    exists_open_nbhd_positive (M := M) hUopen hΔ_contOn hxU hΔpos
  -- Pick a smooth bump φ supported in V with φ ≥ 0 and φ x > 0.
  obtain ⟨φ, hφ_smooth, hφ_compactSupp, hφ_supp, hφ_nonneg, hφx_pos⟩ :=
    exists_smooth_bump_in_open (I := I) hVopen hxV
  -- Now consider ∫ Δ · φ d(chartLocalMeasure α). This integral is positive
  -- (since Δ > 0 on V ⊇ tsupport φ, φ ≥ 0, and chartLocalMeasure is open-positive
  -- on a nonempty open subset of V).
  -- But also: ∫ Δ φ dμ_α = ∫ (div_α - div_β) φ dμ_α
  --   = ∫ div_α φ dμ_α - ∫ div_β φ dμ_α
  --   = ∫ div_β φ dμ_β - ∫ div_β φ dμ_α     (by integral_localDivergence_eq_of_overlap_support)
  --   = ∫ div_β φ d(μ_β - μ_α restricted to overlap)
  --   = 0     (by chartLocalMeasure_restrict_overlap_eq, since tsupport φ ⊆ overlap).
  -- Contradiction.
  have hsupp_overlap : tsupport φ ⊆ U := hφ_supp.trans hVU
  -- Integral equality.
  have hint_eq := integral_localDivergence_eq_of_overlap_support (I := I) g α β X
    hφ_smooth hφ_compactSupp hsupp_overlap
  -- Restrict-overlap-eq for the chart-local measures.
  have hrestrict_eq := chartLocalMeasure_restrict_overlap_eq (I := I) g α β
  -- Express ∫ div_β · φ dμ_β = ∫ div_β · φ dμ_α (via restrict).
  -- Both sides equal `∫_U div_β · φ dμ_β = ∫_U div_β · φ dμ_α`. Since φ supported in U.
  have hβ_int_via_restrict :
      ∫ y, localDivergence (I := I) g β X y * φ y ∂(chartLocalMeasure (I := I) g β) =
        ∫ y, localDivergence (I := I) g β X y * φ y ∂(chartLocalMeasure (I := I) g α) := by
    -- Both equal the integral over U (via support of φ).
    have hzero_off : ∀ y ∉ U, localDivergence (I := I) g β X y * φ y = 0 := by
      intro y hy
      have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_overlap h)
      have : φ y = 0 := by
        by_contra hne
        exact hy_supp (subset_tsupport _ hne)
      rw [this, mul_zero]
    have hβ_to_U : ∫ y, localDivergence (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g β) =
        ∫ y in U, localDivergence (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g β) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off).symm
    have hα_to_U : ∫ y, localDivergence (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ y in U, localDivergence (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g α) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off).symm
    rw [hβ_to_U, hα_to_U]
    -- Both restricted measures agree on U.
    change ∫ y, localDivergence (I := I) g β X y * φ y
          ∂((chartLocalMeasure (I := I) g β).restrict U) =
        ∫ y, localDivergence (I := I) g β X y * φ y
          ∂((chartLocalMeasure (I := I) g α).restrict U)
    rw [← hrestrict_eq]
  -- We need integrability of div_α · φ and div_β · φ.
  have h1_int : Integrable
      (fun y => localDivergence (I := I) g α X y * φ y)
      (chartLocalMeasure (I := I) g α) := by
      -- The integrand is continuous on U (open) and zero outside `tsupport φ ⊆ U`.
      -- It has compact support (in tsupport φ).
      -- Therefore continuous and compactly supported on M (using a similar argument
      -- as in `vwIntegrandOnE`).
      have hsupp_α : tsupport φ ⊆ (chartAt H α).source := hsupp_overlap.trans Set.inter_subset_left
      have hmeas := localDivergence_mul_phi_measurable (I := I) g α X hφ_smooth.continuous hsupp_α
      -- Continuity on a closed set = tsupport φ.
      have hsmooth : ContinuousOn (fun y => localDivergence (I := I) g α X y * φ y) U :=
        hα_contOn.mul hφ_smooth.continuous.continuousOn
      -- Argue integrability via compact support.
      -- Standard pattern: continuous on M (extended) + compact support => integrable.
      -- localDivergence is NOT continuous on M (only on chart source), but the
      -- product with φ IS continuous everywhere (product is 0 outside tsupport φ ⊆ source,
      -- continuous on source where both factors are).
      have h_cont_total : Continuous (fun y => localDivergence (I := I) g α X y * φ y) := by
        rw [continuous_iff_continuousAt]
        intro y
        by_cases hy : y ∈ (chartAt H α).source
        · -- Continuous on the open chart source.
          have hy_cont_src : ContinuousAt
              (fun z => localDivergence (I := I) g α X z * φ z) y := by
            have hα_at : ContinuousAt (localDivergence (I := I) g α X) y :=
              ((localDivergence_continuousOn_baseSet (I := I) g α X) y hy).continuousAt
                ((chartAt H α).open_source.mem_nhds hy)
            exact hα_at.mul hφ_smooth.continuous.continuousAt
          exact hy_cont_src
        · -- y outside chart source: y ∉ tsupport φ (since tsupport ⊆ source).
          have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_α h)
          -- φ = 0 on a neighborhood of y.
          have h_open : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
          have hphi_zero_nhd : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
            filter_upwards [h_open.mem_nhds hy_supp] with z hz
            by_contra hne
            exact hz (subset_tsupport _ hne)
          -- The product is also zero on this neighborhood.
          have hzero_nhd : (fun z => localDivergence (I := I) g α X z * φ z) =ᶠ[𝓝 y]
              (fun _ => (0 : ℝ)) := by
            filter_upwards [hphi_zero_nhd] with z hz
            rw [hz, mul_zero]
          rw [show (fun z => localDivergence (I := I) g α X z * φ z) =
                (fun z => localDivergence (I := I) g α X z * φ z) from rfl]
          exact (continuous_const.continuousAt.congr hzero_nhd.symm)
      have h_compact_supp : HasCompactSupport (fun y =>
          localDivergence (I := I) g α X y * φ y) :=
        hφ_compactSupp.mul_left
      have hsupp_α' : tsupport (fun y => localDivergence (I := I) g α X y * φ y) ⊆
          (chartAt H α).source := by
        refine subset_trans ?_ hsupp_α
        refine closure_minimal ?_ (isClosed_tsupport φ)
        intro y hy
        rw [Function.mem_support] at hy
        by_contra hne
        have : φ y = 0 := by
          by_contra hne'
          exact hne (subset_tsupport _ hne')
        exact hy (by rw [this, mul_zero])
      have hμ_supp_bound : chartLocalMeasure (I := I) g α
            (tsupport (fun y => localDivergence (I := I) g α X y * φ y)) < ⊤ :=
        chartLocalMeasure_compact_lt_top (I := I) g α h_compact_supp hsupp_α'
      have hbounded : ∃ C, ∀ y, ‖localDivergence (I := I) g α X y * φ y‖ ≤ C := by
        rcases (h_compact_supp.exists_bound_of_continuous h_cont_total) with ⟨C, hC⟩
        exact ⟨C, fun y => hC y⟩
      obtain ⟨C, hC⟩ := hbounded
      refine ⟨h_cont_total.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      have hbnd : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
          ENNReal.ofReal (‖localDivergence (I := I) g α X y * φ y‖) ≤
          ENNReal.ofReal C *
            (tsupport (fun y => localDivergence (I := I) g α X y * φ y)).indicator
              (fun _ => (1 : ℝ≥0∞)) y := by
        refine Filter.Eventually.of_forall (fun y => ?_)
        by_cases hy : y ∈ tsupport (fun y => localDivergence (I := I) g α X y * φ y)
        · rw [Set.indicator_of_mem hy, mul_one]
          exact ENNReal.ofReal_le_ofReal (hC y)
        · rw [Set.indicator_of_notMem hy, mul_zero]
          have : localDivergence (I := I) g α X y * φ y = 0 := by
            by_contra hne
            exact hy (subset_tsupport _ hne)
          rw [this]; simp
      calc ∫⁻ y, ENNReal.ofReal ‖localDivergence (I := I) g α X y * φ y‖
            ∂(chartLocalMeasure (I := I) g α)
          ≤ ∫⁻ y, ENNReal.ofReal C *
              (tsupport (fun y => localDivergence (I := I) g α X y * φ y)).indicator
                (fun _ => (1 : ℝ≥0∞)) y
            ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
        _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α
              (tsupport (fun y => localDivergence (I := I) g α X y * φ y)) := by
              rw [lintegral_const_mul _ ((measurable_const).indicator
                (isClosed_tsupport _).measurableSet)]
              rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
              rw [setLIntegral_const, one_mul]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp_bound
  have h2_int : Integrable
      (fun y => localDivergence (I := I) g β X y * φ y)
      (chartLocalMeasure (I := I) g α) := by
    -- φ has support in `(chartAt H β).source` (since `tsupport φ ⊆ U ⊆ (chartAt H β).source`).
    -- Product `localDivergence g β X · φ` is continuous on the chart source of `β`.
    -- For integrability against `chartLocalMeasure g α` we need... actually we need the
    -- product continuous everywhere with compact support.
    -- The key issue: `localDivergence g β X` is continuous on `(chartAt H β).source`.
    -- The product with φ is zero outside `tsupport φ ⊆ (chartAt H β).source`. Hence the
    -- product is continuous everywhere (smooth on the chart source, zero on a neighborhood
    -- of any point outside).
    have hsupp_β : tsupport φ ⊆ (chartAt H β).source := hsupp_overlap.trans Set.inter_subset_right
    have h_cont_total : Continuous (fun y => localDivergence (I := I) g β X y * φ y) := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ (chartAt H β).source
      · have hβ_at : ContinuousAt (localDivergence (I := I) g β X) y :=
          ((localDivergence_continuousOn_baseSet (I := I) g β X) y hy).continuousAt
            ((chartAt H β).open_source.mem_nhds hy)
        exact hβ_at.mul hφ_smooth.continuous.continuousAt
      · have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_β h)
        have h_open : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
        have hphi_zero_nhd : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy_supp] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        have hzero_nhd : (fun z => localDivergence (I := I) g β X z * φ z) =ᶠ[𝓝 y]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [hphi_zero_nhd] with z hz
          rw [hz, mul_zero]
        exact (continuous_const.continuousAt.congr hzero_nhd.symm)
    have h_compact_supp : HasCompactSupport
        (fun y => localDivergence (I := I) g β X y * φ y) := hφ_compactSupp.mul_left
    -- Direct integrability proof. Use that the support is in chart-α-source where
    -- the chart-local measure is finite on compacts.
    have hsupp_α' : tsupport (fun y => localDivergence (I := I) g β X y * φ y) ⊆
        (chartAt H α).source := by
      refine subset_trans ?_ (hsupp_overlap.trans Set.inter_subset_left)
      refine closure_minimal ?_ (isClosed_tsupport φ)
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hne
      have : φ y = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hy (by rw [this, mul_zero])
    have hμ_supp_bound : chartLocalMeasure (I := I) g α
          (tsupport (fun y => localDivergence (I := I) g β X y * φ y)) < ⊤ :=
      chartLocalMeasure_compact_lt_top (I := I) g α h_compact_supp hsupp_α'
    -- Bound the integrand uniformly.
    have hbounded : ∃ C, ∀ y, ‖localDivergence (I := I) g β X y * φ y‖ ≤ C := by
      rcases (h_compact_supp.exists_bound_of_continuous h_cont_total) with ⟨C, hC⟩
      exact ⟨C, fun y => hC y⟩
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨h_cont_total.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hbnd : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
        ENNReal.ofReal (‖localDivergence (I := I) g β X y * φ y‖) ≤
        ENNReal.ofReal C *
          (tsupport (fun y => localDivergence (I := I) g β X y * φ y)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      by_cases hy : y ∈ tsupport (fun y => localDivergence (I := I) g β X y * φ y)
      · rw [Set.indicator_of_mem hy, mul_one]
        exact ENNReal.ofReal_le_ofReal (hC y)
      · rw [Set.indicator_of_notMem hy, mul_zero]
        have : localDivergence (I := I) g β X y * φ y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        rw [this]
        simp
    calc ∫⁻ y, ENNReal.ofReal ‖localDivergence (I := I) g β X y * φ y‖
          ∂(chartLocalMeasure (I := I) g α)
        ≤ ∫⁻ y, ENNReal.ofReal C *
            (tsupport (fun y => localDivergence (I := I) g β X y * φ y)).indicator
              (fun _ => (1 : ℝ≥0∞)) y
          ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
      _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α
            (tsupport (fun y => localDivergence (I := I) g β X y * φ y)) := by
            rw [lintegral_const_mul _ ((measurable_const).indicator
              (isClosed_tsupport _).measurableSet)]
            rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
            rw [setLIntegral_const, one_mul]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp_bound
  -- ∫ Δ · φ dμ_α = 0 by IBP-equality.
  have hΔ_int_zero :
      ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) = 0 := by
    have hexpand : (fun y => Δ y * φ y) =
        fun y => localDivergence (I := I) g α X y * φ y -
          localDivergence (I := I) g β X y * φ y := by
      funext y; simp [Δ, sub_mul]
    rw [hexpand]
    rw [integral_sub h1_int h2_int]
    rw [hint_eq]
    rw [← hβ_int_via_restrict]
    ring
  -- But ∫ Δ · φ dμ_α > 0 (positivity).
  have hΔ_int_pos :
      0 < ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := by
    -- Strategy: pointwise Δ · φ ≥ 0, equals 0 outside V, ≥ Δ x / 2 · φ on V.
    -- So integral ≥ (Δ x / 2) · ∫ φ ≥ (Δ x / 2) · ∫_V φ
    -- And ∫_V φ ≥ φ x · μ(small open neighborhood of x in V) by continuity > 0.
    -- This is technical; let me use that ∫ Δ φ > 0 via a positivity argument.
    -- Steps:
    -- 1. ∫ Δ · φ dμ_α = ∫_V Δ · φ dμ_α (since Δ · φ = 0 outside V because φ supported in V).
    -- 2. On V: Δ ≥ Δ x / 2 (by hΔ_pos), φ ≥ 0 (by hφ_nonneg).
    -- 3. So Δ · φ ≥ (Δ x / 2) · φ on V.
    -- 4. ∫_V (Δ x / 2) · φ dμ_α = (Δ x / 2) · ∫_V φ dμ_α.
    -- 5. ∫_V φ dμ_α > 0 (since φ continuous, φ x > 0, V open, x ∈ V, μ_α open-positive on V).
    -- Need positivity of `chartLocalMeasure g α` on `V` (using `chartLocalMeasure_open_pos_under_boundaryless`).
    have hV_sub_α : V ⊆ (chartAt H α).source := hVU.trans Set.inter_subset_left
    -- Find an open V₀ ⊆ V containing x where φ > φ x / 2 > 0 (by continuity of φ at x).
    have hφx_half_pos : 0 < φ x / 2 := by linarith
    obtain ⟨V₀, hV₀_open, hxV₀, hV₀_sub_V, hφ_pos_V₀⟩ :
        ∃ V₀ : Set M, IsOpen V₀ ∧ x ∈ V₀ ∧ V₀ ⊆ V ∧ ∀ y ∈ V₀, φ x / 2 < φ y :=
      exists_open_nbhd_positive (M := M) hVopen hφ_smooth.continuous.continuousOn
        hxV hφx_pos
    have hV₀_sub_α : V₀ ⊆ (chartAt H α).source := hV₀_sub_V.trans hV_sub_α
    have hμ_V₀_pos : 0 < chartLocalMeasure (I := I) g α V₀ :=
      chartLocalMeasure_open_pos_under_boundaryless (I := I) g α hV₀_open ⟨x, hxV₀⟩ hV₀_sub_α
    -- We also need finiteness `μ_α(V₀) < ⊤` to make the bound work. We pick a
    -- small compact subset of V₀ inside the chart source. Since M is locally compact
    -- (under finite-dim model), every point has a compact nbhd, but for the bound
    -- we use a slightly different strategy: bound `∫ Δ φ dμ` from below by
    -- `c * ∫ V₀ ∩ K dμ` where `K` is a closed nbhd of x with compact closure ⊆ V₀.
    -- Simpler: shrink V₀ to a compact-closure open neighborhood.
    -- Use that M is locally compact (manifolds modeled on finite-dim normed spaces).
    have hLC : LocallyCompactSpace M := by
      have _hE : ProperSpace E := FiniteDimensional.proper ℝ E
      have _hH : LocallyCompactSpace H := I.locallyCompactSpace
      exact ChartedSpace.locallyCompactSpace H M
    -- Find K compact, x ∈ interior K ⊆ K ⊆ V₀.
    obtain ⟨K, hK_compact, hxK_int, hK_sub_V₀⟩ :=
      exists_compact_subset hV₀_open hxV₀
    -- Replace V₀ by interior K.
    set V₁ : Set M := interior K with hV₁_def
    have hV₁_open : IsOpen V₁ := isOpen_interior
    have hxV₁ : x ∈ V₁ := hxK_int
    have hV₁_sub_V₀ : V₁ ⊆ V₀ := interior_subset.trans hK_sub_V₀
    have hV₁_sub_K : V₁ ⊆ K := interior_subset
    have hV₁_sub_α : V₁ ⊆ (chartAt H α).source := hV₁_sub_V₀.trans hV₀_sub_α
    have hμ_V₁_pos : 0 < chartLocalMeasure (I := I) g α V₁ :=
      chartLocalMeasure_open_pos_under_boundaryless (I := I) g α hV₁_open ⟨x, hxV₁⟩ hV₁_sub_α
    have hμ_V₁_lt_top : chartLocalMeasure (I := I) g α V₁ < ⊤ := by
      apply lt_of_le_of_lt (measure_mono hV₁_sub_K)
      have hK_chart_α : K ⊆ (chartAt H α).source := hK_sub_V₀.trans hV₀_sub_α
      exact chartLocalMeasure_compact_lt_top (I := I) g α hK_compact hK_chart_α
    -- Now bound the integral below.
    -- Δ · φ ≥ (Δ x / 2) · (φ x / 2) on V₀ (since Δ > Δ x / 2 on V₀ ⊆ V and φ > φ x / 2 on V₀).
    -- Δ · φ ≥ 0 on V (since Δ > Δ x / 2 > 0 on V and φ ≥ 0).
    -- Δ · φ = 0 outside V (since tsupport φ ⊆ V).
    -- So ∫ Δ · φ dμ_α ≥ ∫_V₀ (Δ x / 2)(φ x / 2) dμ_α = (Δ x · φ x / 4) · μ_α(V₀) > 0.
    --
    -- We need integrability of Δ · φ. Δ · φ is the difference of two integrable functions
    -- (`localDivergence_α · φ` and `localDivergence_β · φ`), hence integrable.
    have hΔ_int : Integrable (fun y => Δ y * φ y) (chartLocalMeasure (I := I) g α) := by
      have hexpand : (fun y => Δ y * φ y) =
          fun y => localDivergence (I := I) g α X y * φ y -
            localDivergence (I := I) g β X y * φ y := by
        funext y; simp [Δ, sub_mul]
      rw [hexpand]
      exact Integrable.sub h1_int h2_int
    -- Compare against (Δx / 2)(φx / 2) · indicator V₀.
    set c : ℝ := Δ x / 2 * (φ x / 2) with hc_def
    have hc_pos : 0 < c := by
      have h1 : 0 < Δ x / 2 := by linarith
      exact mul_pos h1 hφx_half_pos
    -- The pointwise lower bound on V₁.
    have hbound_V₁ : ∀ y ∈ V₁, c ≤ Δ y * φ y := by
      intro y hy
      have hy_V₀ : y ∈ V₀ := hV₁_sub_V₀ hy
      have hy_V : y ∈ V := hV₀_sub_V hy_V₀
      have hΔy : Δ x / 2 < Δ y := hΔ_pos y hy_V
      have hφy : φ x / 2 < φ y := hφ_pos_V₀ y hy_V₀
      have hΔy_pos : 0 < Δ y := by linarith
      have hφy_pos : 0 < φ y := by linarith
      calc c = Δ x / 2 * (φ x / 2) := rfl
        _ ≤ Δ y * (φ x / 2) := by
            apply mul_le_mul_of_nonneg_right hΔy.le; linarith
        _ ≤ Δ y * φ y := by
            apply mul_le_mul_of_nonneg_left hφy.le; linarith
    -- Δ · φ ≥ 0 on M (it's 0 outside tsupport φ ⊆ V, ≥ 0 on V).
    have hΔphi_nonneg : ∀ y, 0 ≤ Δ y * φ y := by
      intro y
      by_cases hy : y ∈ V
      · have hΔy : Δ x / 2 < Δ y := hΔ_pos y hy
        have hΔy_pos : 0 < Δ y := by linarith
        exact mul_nonneg hΔy_pos.le (hφ_nonneg y)
      · -- y ∉ V ⇒ y ∉ tsupport φ ⇒ φ y = 0.
        have hy_supp : y ∉ tsupport φ := fun h => hy (hφ_supp h)
        have hφy : φ y = 0 := by
          by_contra hne
          exact hy_supp (subset_tsupport _ hne)
        rw [hφy, mul_zero]
    -- Now: ∫ (Δ φ) dμ_α ≥ ∫_V₁ (Δ φ) dμ_α ≥ ∫_V₁ c dμ_α = c · μ_α(V₁) > 0.
    have hV₁_meas : MeasurableSet V₁ := hV₁_open.measurableSet
    -- Step 1: Integral of constant c on V₁.
    have hint_const : ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) =
        (chartLocalMeasure (I := I) g α V₁).toReal * c := by
      rw [setIntegral_const]
      change (chartLocalMeasure (I := I) g α).real V₁ * c = _
      rw [Measure.real]
    -- Step 2: Integrability of Δ · φ on V₁ (subset of integrability on M).
    have hΔphi_int_on_V₁ : IntegrableOn (fun y => Δ y * φ y) V₁
        (chartLocalMeasure (I := I) g α) := hΔ_int.integrableOn
    have hc_int_on_V₁ : IntegrableOn (fun _ => c) V₁
        (chartLocalMeasure (I := I) g α) :=
      integrableOn_const (hs := hμ_V₁_lt_top.ne)
    -- Step 3: Lower bound the V₁-restricted integral.
    have hLB_V₁ : ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) ≤
        ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := by
      refine setIntegral_mono_on hc_int_on_V₁ hΔphi_int_on_V₁ hV₁_meas ?_
      intro y hy
      exact hbound_V₁ y hy
    -- Step 4: Total integral ≥ V₁-restricted integral (since Δ · φ ≥ 0).
    have hLB_total : ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) ≤
        ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) :=
      MeasureTheory.setIntegral_le_integral hΔ_int
        (Filter.Eventually.of_forall hΔphi_nonneg)
    -- Combine.
    calc 0 < (chartLocalMeasure (I := I) g α V₁).toReal * c := by
            apply mul_pos
            · rw [ENNReal.toReal_pos_iff]
              exact ⟨hμ_V₁_pos, hμ_V₁_lt_top⟩
            · exact hc_pos
      _ = ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) := hint_const.symm
      _ ≤ ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := hLB_V₁
      _ ≤ ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := hLB_total
  linarith

/-- **Chart invariance of `localDivergence`.** Under `[I.Boundaryless]`, for any
two base points `α β : M` and any `x` in the overlap of their chart sources,
the chart-local Voss–Weyl divergence at `α` and at `β` agree at `x`. -/
theorem localDivergence_chart_invariance [I.Boundaryless]
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) (hx_β : x ∈ (chartAt H β).source) :
    localDivergence (I := I) g α X x = localDivergence (I := I) g β X x := by
  classical
  -- Argue by contradiction; both `(α, β)` and `(β, α)` give exfalso via `_pos`.
  by_contra hne
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hΔneg | hΔpos
  · -- localDivergence_α x - localDivergence_β x < 0 ⇒ localDivergence_β x - localDivergence_α x > 0.
    refine localDivergence_chart_invariance_pos (I := I) g β α X hx_β hx_α ?_
    linarith
  · -- localDivergence_α x - localDivergence_β x > 0.
    exact localDivergence_chart_invariance_pos (I := I) g α β X hx_α hx_β hΔpos

/-! ## Voss–Weyl identity and global smoothness

With chart invariance proved, the global divergence
`divergence_g g X := λ x, localDivergence g x X x` agrees with the chart-local
representative in any chart whose source contains `x`. This is the Voss–Weyl
identity. From it we deduce smoothness of `divergence_g g X` on `M`. -/

/-- **Voss–Weyl divergence formula.** Under `[I.Boundaryless]`, for any base
point `α : M` and any `x ∈ (chartAt H α).source`, the global divergence
`divergence_g g X` evaluated at `x` equals the chart-local Voss–Weyl divergence
`localDivergence g α X x`. -/
theorem voss_weyl_divergence_formula [I.Boundaryless]
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) :
    divergence_g (I := I) g X x = localDivergence (I := I) g α X x := by
  unfold divergence_g
  -- `divergence_g g X x = localDivergence g x X x = localDivergence g α X x`
  -- by chart-invariance applied to `(x, α)`.
  exact localDivergence_chart_invariance (I := I) g x α X (mem_chart_source H x) hx_α

/-- Under `[I.Boundaryless]`, the chart-local Voss–Weyl divergence is `C^∞` on
the entire chart base set (the smoothness domain reduces to the chart source
under boundaryless). -/
theorem localDivergence_contMDiffOn_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X) (chartAt H α).source := by
  refine (localDivergence_contMDiffOn (I := I) g α X).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · -- Under `Boundaryless`, target is open ⇒ interior target = target.
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    have hx_ext : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    exact (extChartAt I α).map_source hx_ext

/-- The global divergence `divergence_g g X` is `C^∞` on `M` under
`[I.Boundaryless]`. The proof is local-to-global via the Voss–Weyl identity. -/
theorem divergence_g_contMDiff [I.Boundaryless]
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (divergence_g (I := I) g X) := by
  intro x
  -- In a neighborhood of `x`, `divergence_g g X = localDivergence g x X` (by Voss–Weyl).
  -- The latter is smooth on the chart base set at `x` (under boundaryless).
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g x X)
      (chartAt H x).source :=
    localDivergence_contMDiffOn_baseSet (I := I) g x X
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen (chartAt H x).source := (chartAt H x).open_source
  -- The two functions agree on `(chartAt H x).source` by Voss–Weyl.
  have h_eq : ∀ y ∈ (chartAt H x).source,
      divergence_g (I := I) g X y = localDivergence (I := I) g x X y := by
    intro y hy
    exact voss_weyl_divergence_formula (I := I) g x X hy
  -- Now: smoothness at x reduces to smoothness on the chart source.
  refine ((hsmooth x hxsrc).contMDiffAt (hsrc_open.mem_nhds hxsrc)).congr_of_eventuallyEq ?_
  filter_upwards [hsrc_open.mem_nhds hxsrc] with y hy
  exact h_eq y hy

end DivergenceTheorem
end Analysis
end RicciFlower
