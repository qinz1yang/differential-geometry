import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuant
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseHelpers

/-!
# Chart-based Sobolev algebra at first order, super-critical exponent

For a closed Riemannian manifold `(M, g)` of dimension `n ≥ 1` and an exponent
`p > n`, the chart-based Sobolev space `W^{1,p}_{chart}(M)` admits a
multiplicative bound for *smooth* inputs. This file delivers this estimate.

The headline theorem `mul_smooth_chart_bound_C1` shows: for every smooth
`u : M → ℝ`, there is a finite constant `C_u ≥ 0` such that for every smooth
`v : M → ℝ`,

  `wkpNormChart g 1 p (u · v) ≤ C_u · wkpNormChart g 1 p v`.

The constant depends on `u` (specifically on its `C^1` norm in chart
coordinates) and on the manifold geometry. Density extension to general
`MemWkpChart` inputs and the fully bilinear form of the bound are intentionally
outside the scope of this file.

## Strategy

For each chart `α` in the canonical partition-of-unity finset:

1. Choose a smooth manifold-side cutoff `b_α : M → ℝ` with `b_α ≡ 1` on
   `tsupport ρ_α` and `tsupport b_α ⊆ (chartAt H α).source`.
2. Define `mulFactor α u := smoothExtension α (b_α · u)` — smooth and
   compactly supported on `EuclideanSpace ℝ (Fin n)`, with first-order bounds.
3. Show `chartPushed ρ α (u · v) = mulFactor α u · chartPushed ρ α v`
   pointwise on `chartTargetEuclid α`. This uses the identity `b_α · ρ_α = ρ_α`,
   valid pointwise because `b_α ≡ 1` on `tsupport ρ_α` and `ρ_α = 0` outside.
4. Apply the existing Euclidean `wkpNorm_smul_smooth_bounded_le_one` to bound
   `wkpNorm 1 p (mulFactor α u · chartPushed ρ α v)` by a constant times
   `wkpNorm 1 p (chartPushed ρ α v)`.
5. Sum the per-chart bounds across the canonical POU finset (a finite set on
   compact `M`). Outside the finset `ρ_α ≡ 0`, so `chartPushed ρ α (u v)` and
   `chartPushed ρ α v` both vanish a.e. and contribute nothing.

## Future work

The fully bilinear estimate

  `wkpNormChart g 1 p (u · v) ≤ C · wkpNormChart g 1 p u · wkpNormChart g 1 p v`

requires a manifold-level `C^{0,α}` Hölder Morrey embedding (or equivalent
`C^1` Sobolev embedding for `p > n`), so that the gradient of `u` in chart
coordinates can be bounded by `wkpNormChart u`. The current
`morrey_C0_embedding_of_compact` gives only the `C^0` bound. Extending to the
bilinear estimate is intentionally outside the scope of this development.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For each chart point `α : M` on a closed manifold there exists a smooth
manifold-side cutoff `b_α : M → ℝ` taking values in `[0,1]`, equal to `1` on
`tsupport ρ_α`, and with `tsupport b_α ⊆ (chartAt H α).source`. -/
private lemma exists_chart_cutoff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ b ∧
      Set.range b ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) ∧
      tsupport b ⊆ (chartAt H α).source := by
  classical
  obtain ⟨K, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
    exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) α
  obtain ⟨η, hη_smooth, hη_range, _hη_support, hη_one_on_tsupp, hη_tsupport_in_K⟩ :=
    exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) α hK_compact
      h_tsupp_in_int_K
  refine ⟨η, hη_smooth, hη_range, hη_one_on_tsupp, ?_⟩
  exact hη_tsupport_in_K.trans hK_chart

/-- The smooth global extension of `f : M → ℝ` to `EuclN`, equal to
`f ((extChartAt I α).symm (toEuclidean.symm y))` on the chart-target image and
`0` outside. -/
private def smoothExtension (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [IsManifold I ∞ M] in
private lemma smoothExtension_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    smoothExtension (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

omit [IsManifold I ∞ M] in
private lemma smoothExtension_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

private lemma smoothExtension_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  apply smoothExtension_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

private lemma smoothExtension_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  apply smoothExtension_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

/-- If `f : M → ℝ` is smooth, the formula
`y ↦ f ((extChartAt I α).symm (toEuclidean.symm y))` is smooth on
`chartTargetEuclid α`. -/
private lemma contDiffOn_smoothExtension_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hf
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps

private lemma contDiffAt_smoothExtension_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (smoothExtension (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_smoothExtension_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

/-- If `f` has compact support contained in `(chartAt H α).source`, the smooth
extension `smoothExtension α f` vanishes outside the toEuclidean image of
`(extChartAt I α) '' (tsupport f)`. -/
private lemma smoothExtension_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt H α).source) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
  · exact smoothExtension_apply_of_notMem_chartTargetEuclid
      (I := I) (M := M) α f hy_target

private lemma image_extChartAt_tsupport_isCompact
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE := image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M) (u := f) (α := α) hf_supp
  exact hKE.1.image (toEuclidean (E := E)).continuous

private lemma image_extChartAt_tsupport_subset_chartTarget
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_supp

/-- `smoothExtension α f` is smooth on all of `EuclN` whenever `f` is smooth on
`M` with compact support contained in `(chartAt H α).source`. -/
private lemma contDiff_smoothExtension
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (smoothExtension (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_smoothExtension_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_extChartAt_tsupport_subset_chartTarget
        (I := I) (M := M) (f := f) (α := α) hf_supp hy_in
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :=
      image_extChartAt_tsupport_isCompact
        (I := I) (M := M) (f := f) (α := α) hf_supp
    have hK_compl_open : IsOpen _ := hK_compact.isClosed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    exact smoothExtension_eq_zero_off_image_tsupport
      (I := I) (M := M) α (f := f) hf_supp hz

/-- `smoothExtension α f` has compact support whenever `f` is smooth on `M` with
`tsupport f ⊆ (chartAt H α).source`. -/
private lemma hasCompactSupport_smoothExtension
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (smoothExtension (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_isCompact (I := I) (M := M) (f := f) (α := α) hf_supp
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact smoothExtension_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_supp hyK

/-- For a smooth function `ψ : EuclN → ℝ` with compact support, the iterated
derivative at any point is bounded by its sup over the support. -/
private lemma iteratedFDeriv_bound_of_compactSupport
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_compact : HasCompactSupport ψ)
    (k : ℕ) :
    ∃ Mk : ℝ, 0 ≤ Mk ∧ ∀ y : EuclN, ‖iteratedFDeriv ℝ k ψ y‖ ≤ Mk := by
  classical
  have h_iterCont : Continuous (fun y : EuclN => iteratedFDeriv ℝ k ψ y) :=
    hψ_smooth.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)
  have h_iter_supp : HasCompactSupport (fun y : EuclN => iteratedFDeriv ℝ k ψ y) :=
    hψ_compact.iteratedFDeriv (𝕜 := ℝ) k
  obtain ⟨C, hC⟩ := h_iterCont.bounded_above_of_compact_support h_iter_supp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y
  exact (hC y).trans (le_max_left _ _)

/-- A uniform bound for `‖iteratedFDeriv ℝ j (smoothExtension α f)‖` for
`j ∈ {0, 1}`, packaged as a single constant. Applies whenever `f` is smooth on
`M` with `tsupport f ⊆ (chartAt H α).source`. -/
private lemma smoothExtension_first_order_bound
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ j ≤ 1, ∀ y : EuclN,
      ‖iteratedFDeriv ℝ j (smoothExtension (I := I) (M := M) α f) y‖ ≤ Cf := by
  classical
  have hψ_smooth : ContDiff ℝ ∞ (smoothExtension (I := I) (M := M) α f) :=
    contDiff_smoothExtension (I := I) (M := M) α hf hf_supp
  have hψ_compact : HasCompactSupport (smoothExtension (I := I) (M := M) α f) :=
    hasCompactSupport_smoothExtension (I := I) (M := M) α hf_supp
  obtain ⟨M0, hM0_nn, hM0⟩ :=
    iteratedFDeriv_bound_of_compactSupport hψ_smooth hψ_compact 0
  obtain ⟨M1, hM1_nn, hM1⟩ :=
    iteratedFDeriv_bound_of_compactSupport hψ_smooth hψ_compact 1
  refine ⟨max M0 M1, le_max_of_le_left hM0_nn, ?_⟩
  intro j hj y
  interval_cases j
  · exact (hM0 y).trans (le_max_left _ _)
  · exact (hM1 y).trans (le_max_right _ _)

/-- For each chart `α` and any choice of cutoff `b_α` with `b_α ≡ 1` on
`tsupport ρ_α`, the chart-pushed product
`chartPushed ρ α (u · v)` equals `smoothExtension α (b_α · u) · chartPushed ρ α v`
pointwise on `chartTargetEuclid α`. -/
private lemma chartPushed_mul_eq_smoothExtension_mul_chartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      smoothExtension (I := I) (M := M) α (fun x => b x * u x) y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hLHS :
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * (u x * v x) := rfl
  have hRHS1 : smoothExtension (I := I) (M := M) α (fun x => b x * u x) y =
      b x * u x := by
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
      (fun x => b x * u x) hy]
  have hRHS2 : chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * v x := rfl
  rw [hLHS, hRHS1, hRHS2]
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

/-- Per-chart sub-multiplicative bound. For each chart `α : M`, smooth
`u : M → ℝ`, and any `1 ≤ p < ∞`, there is a finite constant `K_α(u) ≥ 0` such
that for every smooth `v : M → ℝ`,

  `wkpNorm 1 p (chartPushed ρ α (u · v)) Ω_α ≤ K_α(u) · wkpNorm 1 p (chartPushed ρ α v) Ω_α`. -/
private lemma per_chart_mul_smooth_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ K_α : ℝ, 0 ≤ K_α ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (fun x => u x * v x))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K_α *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 p
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff (I := I) (M := M) α
  have hbu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => b x * u x) := hb_smooth.mul hu
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  obtain ⟨Cα, hCα_nn, hCα_bound⟩ :=
    smoothExtension_first_order_bound (I := I) (M := M) α hbu_smooth hbu_supp
  set η : EuclN → ℝ := smoothExtension (I := I) (M := M) α (fun x : M => b x * u x)
    with hη_def
  have hη_smooth : ContDiff ℝ ∞ η := by
    rw [hη_def]
    exact contDiff_smoothExtension (I := I) (M := M) α hbu_smooth hbu_supp
  have hη_smooth_top : ContDiff ℝ (⊤ : ℕ∞) η := hη_smooth
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCα_on_Ω : ∀ j ≤ 1, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j η y‖ ≤ Cα := fun j hj y _ =>
    hCα_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      (d := Module.finrank ℝ E) (k := 1) (le_refl _) hp_one hp_top hΩ_open
      hη_smooth_top hCα_nn hCα_on_Ω
  refine ⟨K, hK_pos.le, ?_⟩
  intro v hv
  have h_factorize :
      (fun y : EuclN => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y)
        =ᵐ[volume.restrict Ω]
      (fun y : EuclN => η y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y) := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [hη_def]
    exact chartPushed_mul_eq_smoothExtension_mul_chartPushed
      (I := I) (M := M) α (b := b) (u := u) (v := v) hb_one_on_tsupp hy
  have hv_chartPushed_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v) Ω := by
    have h := DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_one hv
    exact h α
  have h_eucl_bound :=
    hK_bound (u := chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
      hv_chartPushed_mem
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one hΩ_open h_factorize]
  exact h_eucl_bound

/-- **Smooth-input chart-Sobolev algebra at first order.** For a closed
Riemannian manifold of dimension `n ≥ 1` and an exponent `p > n`, the
chart-based Sobolev norm of a product `u · v` of smooth functions is
controlled by a smooth-`u`-dependent constant times the chart-based Sobolev
norm of `v`:

  `wkpNormChart g 1 p (u · v) ≤ C_u · wkpNormChart g 1 p v`,

with `0 ≤ C_u` finite. The constant depends on `u` (its `C^1` profile through
each chart) and on the manifold geometry, but not on `v`. -/
theorem mul_smooth_chart_bound_C1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ Cu : ℝ, 0 ≤ Cu ∧
        ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
          wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p)
              (fun x => u x * v x) ≤
            ENNReal.ofReal Cu *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  intro u hu
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : ENNReal.ofReal p ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  have h_per_α : ∀ α ∈ S, ∃ K_α : ℝ, 0 ≤ K_α ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (fun x => u x * v x))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K_α *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := fun α _ =>
    per_chart_mul_smooth_bound (I := I) (M := M) g hp_enn_one hp_enn_top α hu
  set Kfun : M → ℝ := fun α =>
    if hα : α ∈ S then Classical.choose (h_per_α α hα) else 0 with hKfun_def
  have hKfun_eq_of_mem : ∀ α (hα : α ∈ S), Kfun α = Classical.choose (h_per_α α hα) := by
    intro α hα
    change (if hα' : α ∈ S then Classical.choose (h_per_α α hα') else 0) =
      Classical.choose (h_per_α α hα)
    rw [dif_pos hα]
  have hKfun_nn : ∀ α ∈ S, 0 ≤ Kfun α := by
    intro α hα
    rw [hKfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).1
  have hKfun_bound : ∀ α ∈ S, ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => u x * v x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Kfun α) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro α hα v hv
    have hbnd := (Classical.choose_spec (h_per_α α hα)).2 hv
    rw [hKfun_eq_of_mem α hα]
    exact hbnd
  refine ⟨∑ α ∈ S, Kfun α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α hα => hKfun_nn α hα)
  intro v hv
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one (fun x => u x * v x),
    wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one v]
  refine (Finset.sum_le_sum (fun α hα => hKfun_bound α hα hv)).trans ?_
  set sumK : ℝ := ∑ α ∈ S, Kfun α with hsumK_def
  have hKfun_sum_le : ∀ α ∈ S, ENNReal.ofReal (Kfun α) ≤ ENNReal.ofReal sumK := by
    intro α hα
    apply ENNReal.ofReal_le_ofReal
    rw [hsumK_def]
    exact Finset.single_le_sum (f := Kfun) (fun β hβ => hKfun_nn β hβ) hα
  have h_step1 : (∑ α ∈ S,
      ENNReal.ofReal (Kfun α) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ α ∈ S,
          ENNReal.ofReal sumK *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := by
    refine Finset.sum_le_sum (fun α hα => ?_)
    exact mul_le_mul' (hKfun_sum_le α hα) (le_refl _)
  refine h_step1.trans ?_
  rw [← Finset.mul_sum]

/-- The unweighted chart-Euclidean pull-back of `v : M → ℝ`. On
`chartTargetEuclid α`, this equals `v ((extChartAt I α).symm (toEuclidean.symm y))`.
Outside `chartTargetEuclid α`, the value involves the partial inverse and is
formally well-typed but mathematically irrelevant. -/
private def chartLifted (α : M) (v : M → ℝ) : EuclN → ℝ :=
  fun y => v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

/-- Pointwise factorization: `chartPushed ρ α (u · v) y =
chartPushed ρ α u y · chartLifted α v y` everywhere. -/
private lemma chartPushed_mul_eq_chartPushed_mul_chartLifted
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u v : M → ℝ) (y : EuclN) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x * v x) y =
      chartPushed (I := I) (M := M) ρ α u y *
        chartLifted (I := I) (M := M) α v y := by
  unfold chartPushed chartLifted
  ring

/-- For any `y : EuclN`, `chartLifted α v y = v(...)` for some manifold point.
Combined with a manifold sup bound on `v`, this gives a uniform sup bound on
`chartLifted α v`. -/
private lemma chartLifted_apply_norm_le
    (α : M) (v : M → ℝ) {Cv : ℝ} (hCv : ∀ x : M, ‖v x‖ ≤ Cv) (y : EuclN) :
    ‖chartLifted (I := I) (M := M) α v y‖ ≤ Cv := by
  unfold chartLifted
  exact hCv _

/-- For each `y : EuclN`, `‖chartPushed (chartAtlasPOU I M) α u y‖ ≤ ‖u‖_∞^M`
provided `Cu : ℝ` is a uniform sup bound for `u`. The bound exploits
`|ρ_α| ≤ 1`. -/
private lemma chartPushed_norm_le_sup
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) {Cu : ℝ} (hCu : ∀ x : M, ‖u x‖ ≤ Cu) (y : EuclN) :
    ‖chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y‖ ≤ Cu := by
  unfold chartPushed
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have hρ_range :
      Set.range ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro r ⟨z, hz⟩
    refine ⟨?_, ?_⟩
    · have := (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α z
      rw [← hz]; exact this
    · have := (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α z
      rw [← hz]; exact this
  have hρ_x_nonneg : 0 ≤ (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x :=
    (hρ_range ⟨x, rfl⟩).1
  have hρ_x_le_one : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x ≤ 1 :=
    (hρ_range ⟨x, rfl⟩).2
  calc
    ‖((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x‖
        = |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * ‖u x‖ := by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    _ = ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * ‖u x‖ := by
          rw [abs_of_nonneg hρ_x_nonneg]
    _ ≤ 1 * ‖u x‖ := by
          gcongr
    _ = ‖u x‖ := one_mul _
    _ ≤ Cu := hCu x

/-- The "left" smooth factor `Eu_α := smoothExtension α (b_α · u)`. Smooth and
compactly supported on `EuclN`. Agrees with `u_lifted` on `chart_image of
tsupport ρ_α` (where `b_α = 1`). -/
private noncomputable def leftSmoothFactor (α : M) (b u : M → ℝ) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α (fun x => b x * u x)

/-- Sup bound on the left smooth factor: `‖leftSmoothFactor α b u y‖ ≤
‖u‖_∞ · ‖b‖_∞`. -/
private lemma leftSmoothFactor_norm_le
    (α : M) (b u : M → ℝ) {Cu Cb : ℝ}
    (hCu : ∀ x : M, ‖u x‖ ≤ Cu) (hCb : ∀ x : M, ‖b x‖ ≤ Cb) (hCu_nn : 0 ≤ Cu)
    (hCb_nn : 0 ≤ Cb) (y : EuclN) :
    ‖leftSmoothFactor (I := I) (M := M) α b u y‖ ≤ Cb * Cu := by
  classical
  unfold leftSmoothFactor smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ Cb * Cu
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    calc
      ‖b x * u x‖ = ‖b x‖ * ‖u x‖ := norm_mul _ _
      _ ≤ Cb * Cu := mul_le_mul (hCb x) (hCu x) (norm_nonneg _) hCb_nn
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ Cb * Cu
    rw [if_neg hy]
    rw [norm_zero]
    exact mul_nonneg hCb_nn hCu_nn

/-- For each chart point `α`, there is a smooth manifold cutoff `b_α : M → ℝ`
in `[0, 1]`, equal to `1` on `tsupport ρ_α`, with `tsupport b_α ⊆ chart_source`. -/
private lemma exists_chart_cutoff_with_data
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x : M, 0 ≤ b x ∧ b x ≤ 1) ∧
      (∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) ∧
      tsupport b ⊆ (chartAt H α).source := by
  obtain ⟨b, hb_smooth, hb_range, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff (I := I) (M := M) α
  refine ⟨b, hb_smooth, ?_, hb_one_on_tsupp, hb_supp⟩
  intro x
  exact hb_range ⟨x, rfl⟩

/-- Auxiliary form of `wkpNorm_smul_smooth_bounded_le_one` returning a constant
that splits into an `‖η‖_∞` part and an `‖∇η‖_∞` part. Specialized to `k = 1`. -/
private lemma wkpNorm_eta_target_le_split
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C0 C1 : ℝ} (hC0_nn : 0 ≤ C0) (_hC1_nn : 0 ≤ C1)
    (hη0 : ∀ x ∈ Ω, ‖η x‖ ≤ C0)
    (hη1 : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C1)
    {u : EuclN → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p u Ω) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω ≤
      ENNReal.ofReal C0 *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p u Ω +
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) * ENNReal.ofReal C1 *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p u Ω := by
  classical
  letI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hLHS_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω =
        eLpNorm (fun x => η x * u x) p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) p 1 α' (fun x => η x * u x) Ω) p
            (volume.restrict Ω) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h0_unique : ∀ α' : Fin 0 → Fin (Module.finrank ℝ E),
        α' = (fun i : Fin 0 => i.elim0) := fun α' => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α' => (h0_unique α').symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) p 0 α' (fun x => η x * u x) Ω) p
              (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have hRHS_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p u Ω =
        eLpNorm u p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) p 1 α' u Ω) p
            (volume.restrict Ω) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h0_unique : ∀ α' : Fin 0 → Fin (Module.finrank ℝ E),
        α' = (fun i : Fin 0 => i.elim0) := fun α' => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α' => (h0_unique α').symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) p 0 α' u Ω) p
              (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have hIter1_eta_u : ∀ α' : Fin 1 → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 α' (fun x => η x * u x) Ω =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω := by
    intro α'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]; rfl
  have hIter1_u : ∀ α' : Fin 1 → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 α' u Ω =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p (α' 0) u Ω := by
    intro α'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]; rfl
  have hLHS_unfold' : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω =
        eLpNorm (fun x => η x * u x) p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω) p
            (volume.restrict Ω) := by
    rw [hLHS_unfold]
    refine congrArg (eLpNorm (fun x => η x * u x) p (volume.restrict Ω) + ·) ?_
    refine Finset.sum_congr rfl (fun α' _ => ?_)
    rw [hIter1_eta_u α']
  have hRHS_unfold' : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p u Ω =
        eLpNorm u p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p
            (volume.restrict Ω) := by
    rw [hRHS_unfold]
    refine congrArg (eLpNorm u p (volume.restrict Ω) + ·) ?_
    refine Finset.sum_congr rfl (fun α' _ => ?_)
    rw [hIter1_u α']
  have hLp_bound : eLpNorm (fun x => η x * u x) p (volume.restrict Ω) ≤
      ENNReal.ofReal C0 * eLpNorm u p (volume.restrict Ω) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := u) (c := C0) ?_ p
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    calc
      ‖η x * u x‖ = ‖η x‖ * ‖u x‖ := norm_mul _ _
      _ ≤ C0 * ‖u x‖ := by gcongr; exact hη0 x hx
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω := hu.memW1p
  set Cmax : ℝ := max C0 C1 with hCmax_def
  have hCmax_nn : 0 ≤ Cmax := le_max_of_le_left hC0_nn
  have hη0_max : ∀ x ∈ Ω, ‖η x‖ ≤ Cmax := fun x hx =>
    (hη0 x hx).trans (le_max_left _ _)
  have hη1_max : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ Cmax := fun x hx =>
    (hη1 x hx).trans (le_max_right _ _)
  have h_chosen_bnd : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p i (fun x => η x * u x) Ω) p
          (volume.restrict Ω) ≤
        ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) := by
    intro i
    classical
    have hae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := Module.finrank ℝ E) hp_one hΩ_open hη_smooth hη0_max hη1_max hu_W1p i
    have hηcwp_meas : AEStronglyMeasurable
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x)
        (volume.restrict Ω) :=
      hη_smooth.continuous.aestronglyMeasurable.mul
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
          hu_W1p i).aestronglyMeasurable
    have hderiv_cont : Continuous
        (fun x : EuclN => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))) :=
      (hη_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hdηu_meas : AEStronglyMeasurable
        (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
        (volume.restrict Ω) :=
      hderiv_cont.aestronglyMeasurable.mul hu.memLp.aestronglyMeasurable
    rw [eLpNorm_congr_ae hae]
    have hSumEq :
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x +
          (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) =
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x) +
        (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) := by
      funext x
      simp [Pi.add_apply]
    rw [hSumEq]
    have htriangle :
        eLpNorm
            ((fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) +
              fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
            p (volume.restrict Ω)
          ≤ eLpNorm (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) p (volume.restrict Ω) +
            eLpNorm
              (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
              p (volume.restrict Ω) :=
      eLpNorm_add_le hηcwp_meas hdηu_meas hp_one
    refine htriangle.trans ?_
    have hbnd1 :
        eLpNorm (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) p (volume.restrict Ω) ≤
          ENNReal.ofReal C0 *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) p i u Ω) p (volume.restrict Ω) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_eta_mul_le
        (d := Module.finrank ℝ E) hΩ_open hη0
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i u Ω)
    have hbnd2 :
        eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) p
            (volume.restrict Ω) ≤
          ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_partial_eta_mul_le
        (d := Module.finrank ℝ E) hΩ_open hη1 i u
    exact add_le_add hbnd1 hbnd2
  rw [hLHS_unfold', hRHS_unfold']
  have hGrad_LHS_bnd :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω) p
          (volume.restrict Ω) ≤
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        (ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) :=
    Finset.sum_le_sum (fun α' _ => h_chosen_bnd (α' 0))
  refine (add_le_add hLp_bound hGrad_LHS_bnd).trans ?_
  have hSum_split :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        (ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) =
        (∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          ENNReal.ofReal C0 *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω)) +
        ∑ _α' : Fin 1 → Fin (Module.finrank ℝ E),
          ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) := Finset.sum_add_distrib
  rw [hSum_split]
  have hCard : (Finset.univ : Finset (Fin 1 → Fin (Module.finrank ℝ E))).card =
      Module.finrank ℝ E := by
    rw [Finset.card_univ]; simp
  have hSum_const :
      ∑ _α' : Fin 1 → Fin (Module.finrank ℝ E),
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) =
        ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) := by
    rw [Finset.sum_const, hCard, nsmul_eq_mul]
  rw [hSum_const]
  have hSum_factor :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) =
      ENNReal.ofReal C0 * ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) := by
    rw [Finset.mul_sum]
  rw [hSum_factor]
  set Au : ℝ≥0∞ := eLpNorm u p (volume.restrict Ω) with hAu_def
  set SBu : ℝ≥0∞ := ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
    eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) with hSBu_def
  set OC0 : ℝ≥0∞ := ENNReal.ofReal C0 with hOC0_def
  set OC1 : ℝ≥0∞ := ENNReal.ofReal C1 with hOC1_def
  set Nat_d : ℝ≥0∞ := ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) with hNd_def
  change OC0 * Au + (OC0 * SBu + Nat_d * (OC1 * Au)) ≤
    OC0 * (Au + SBu) + Nat_d * OC1 * (Au + SBu)
  rw [mul_add OC0 Au SBu, mul_add (Nat_d * OC1) Au SBu]
  have hAssoc : Nat_d * (OC1 * Au) = Nat_d * OC1 * Au := by ring
  rw [hAssoc]
  have hRearrange : OC0 * Au + (OC0 * SBu + Nat_d * OC1 * Au) =
      OC0 * Au + OC0 * SBu + Nat_d * OC1 * Au := by ring
  rw [hRearrange]
  refine add_le_add (le_refl _) ?_
  exact le_self_add

/-- For smooth manifold functions `f, g` with `tsupport f ⊆ (chartAt H α).source`,
the chart-target product `smoothExtension α f · smoothExtension α g` equals
`smoothExtension α (f · g)` pointwise on `EuclN`. -/
private lemma smoothExtension_mul_eq
    (α : M) (f g : M → ℝ) :
    (fun y : EuclN => smoothExtension (I := I) (M := M) α f y *
      smoothExtension (I := I) (M := M) α g y) =
    smoothExtension (I := I) (M := M) α (fun x : M => f x * g x) := by
  classical
  funext y
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · rw [smoothExtension_apply_of_mem_target (I := I) (M := M) α f hy,
      smoothExtension_apply_of_mem_target (I := I) (M := M) α g hy,
      smoothExtension_apply_of_mem_target (I := I) (M := M) α (fun x => f x * g x) hy]
  · rw [smoothExtension_apply_of_notMem_target (I := I) (M := M) α f hy,
      smoothExtension_apply_of_notMem_target (I := I) (M := M) α g hy,
      smoothExtension_apply_of_notMem_target (I := I) (M := M) α (fun x => f x * g x) hy,
      mul_zero]

/-- The pointwise factorization `smoothExtension α (ρ_α · u · v) =
smoothExtension α (ρ_α · u) · smoothExtension α (b · v)` (provided `b = 1` on
`tsupport ρ_α`) — for the bilinear bound. -/
private lemma smoothExtension_three_factor
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) =
      (fun y : EuclN =>
        smoothExtension (I := I) (M := M) α
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) y *
        smoothExtension (I := I) (M := M) α (fun x => b x * v x) y) := by
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)
    (fun x => b x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

/-- Symmetric version: `smoothExtension α (ρ_α · u · v) =
smoothExtension α (b · u) · smoothExtension α (ρ_α · v)`. -/
private lemma smoothExtension_three_factor_symm
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) =
      (fun y : EuclN =>
        smoothExtension (I := I) (M := M) α (fun x => b x * u x) y *
        smoothExtension (I := I) (M := M) α
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x) y) := by
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    (fun x => b x * u x)
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

/-- Equality between `smoothExtension α (ρ_α · u · v)` and
`chartPushed (chartAtlasPOU) α (u · v)` pointwise on `chartTargetEuclid α`. -/
private lemma smoothExtension_eq_chartPushed_uv
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u v : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y := by
  classical
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x * v x) hy]
  unfold chartPushed
  ring

private lemma chartSmoothExt_pou_mul_eq_chartPushed
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y := by
  classical
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  rfl

/-- The classical partial of a smooth+compactly-supported `f` agrees a.e. with
`chosenWeakPartial' p i f Ω`. -/
private lemma chosenWeakPartial_eq_classical_ae
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {f : EuclN → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ Ω) (i : Fin (Module.finrank ℝ E)) :
    (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ)))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i f Ω := by
  classical
  have hf_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := Module.finrank ℝ E) hΩ_open hf_smooth hf_compact hf_supp hp_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ))) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i f Ω) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ)))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ))) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i f Ω) (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hp_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

/-- Helper: tsupport of `smoothExtension α f` is in the toEuclidean image of
`(extChartAt α) '' (tsupport f)`, which is a compact subset of chart-target. -/
private lemma tsupport_smoothExtension_subset_image
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (smoothExtension (I := I) (M := M) α f) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_isCompact (I := I) (M := M) (f := f) (α := α) hf_supp
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (smoothExtension (I := I) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact smoothExtension_eq_zero_off_image_tsupport (I := I) (M := M) α
      (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

/-- The toEuclidean image of `(extChartAt α) '' (tsupport f)` is contained in
`chartTargetEuclid α`. -/
private lemma image_tsupport_subset_chartTarget
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_extChartAt_tsupport_subset_chartTarget (I := I) (M := M) (f := f) (α := α) hf_supp

/-- The lifted POU weight `R_α := smoothExtension α (ρ_α : M → ℝ)`, globally
smooth and compactly supported on `EuclN`. -/
private noncomputable def liftedPou
    [T2Space M] [SigmaCompactSpace M] (α : M) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)

/-- The chart-α smooth-extension of `ρ_α · u`, denoted `Pu_α`. Globally smooth
and compactly supported. -/
private noncomputable def smoothPushed
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)

/-- A chart-α geometric compact set that contains the support of `liftedPou α`
and `smoothPushed α u` for any `u`: the toEuclidean image of the chart-α
extChartAt image of `tsupport ρ_α`. (Local copy of `chartCarrier` from
`MorreyManifold.lean`, since that one is private.) -/
private noncomputable def chartCarrierLocal
    [T2Space M] [SigmaCompactSpace M] (α : M) : Set EuclN :=
  (toEuclidean (E := E)) ''
    ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

private lemma chartCarrierLocal_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (chartCarrierLocal (I := I) (M := M) α) := by
  classical
  unfold chartCarrierLocal
  exact image_extChartAt_tsupport_isCompact (I := I) (M := M)
    (f := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma chartCarrierLocal_subset_chartTarget
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    chartCarrierLocal (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold chartCarrierLocal
  exact image_tsupport_subset_chartTarget (I := I) (M := M)
    (f := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma tsupport_liftedPou_subset_chartCarrierLocal
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    tsupport (liftedPou (I := I) (M := M) α) ⊆
      chartCarrierLocal (I := I) (M := M) α := by
  classical
  unfold liftedPou chartCarrierLocal
  exact tsupport_smoothExtension_subset_image (I := I) (M := M) α
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma liftedPou_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) : ContDiff ℝ ∞ (liftedPou (I := I) (M := M) α) := by
  classical
  unfold liftedPou
  refine contDiff_smoothExtension (I := I) (M := M) α
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff ?_
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

private lemma liftedPou_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) : HasCompactSupport (liftedPou (I := I) (M := M) α) := by
  classical
  unfold liftedPou
  refine hasCompactSupport_smoothExtension (I := I) (M := M) α ?_
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

private lemma smoothPushed_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (smoothPushed (I := I) (M := M) α u) := by
  classical
  unfold smoothPushed
  have hpou_u_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact contDiff_smoothExtension (I := I) (M := M) α hpou_u_smooth hpou_u_supp

private lemma smoothPushed_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    HasCompactSupport (smoothPushed (I := I) (M := M) α u) := by
  classical
  unfold smoothPushed
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact hasCompactSupport_smoothExtension (I := I) (M := M) α hpou_u_supp

private lemma leftSmoothFactor_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (leftSmoothFactor (I := I) (M := M) α b u) := by
  classical
  unfold leftSmoothFactor
  have hbu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => b x * u x) := hb.mul hu
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact contDiff_smoothExtension (I := I) (M := M) α hbu_smooth hbu_supp

private lemma leftSmoothFactor_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) {b u : M → ℝ}
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    HasCompactSupport (leftSmoothFactor (I := I) (M := M) α b u) := by
  classical
  unfold leftSmoothFactor
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact hasCompactSupport_smoothExtension (I := I) (M := M) α hbu_supp

private lemma tsupport_smoothExtension_subset_chartTarget
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (smoothExtension (I := I) (M := M) α f) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (tsupport_smoothExtension_subset_image (I := I) (M := M) α hf_supp).trans
    (image_tsupport_subset_chartTarget (I := I) (M := M) hf_supp)

private lemma tsupport_leftSmoothFactor_subset_chartTarget
    [CompactSpace M] (α : M) {b u : M → ℝ}
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    tsupport (leftSmoothFactor (I := I) (M := M) α b u) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold leftSmoothFactor
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact tsupport_smoothExtension_subset_chartTarget (I := I) (M := M) α hbu_supp

private lemma tsupport_smoothPushed_subset_chartTarget
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (smoothPushed (I := I) (M := M) α u) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold smoothPushed
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact tsupport_smoothExtension_subset_chartTarget (I := I) (M := M) α hpou_u_supp

private lemma leftSmoothFactor_memW1p
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (α : M) {b u : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hb_supp : tsupport b ⊆ (chartAt H α).source)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (leftSmoothFactor (I := I) (M := M) α b u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hSmooth : ContDiff ℝ ∞ (leftSmoothFactor (I := I) (M := M) α b u) :=
    leftSmoothFactor_smooth (I := I) (M := M) α hb hu hb_supp
  have hCompact : HasCompactSupport (leftSmoothFactor (I := I) (M := M) α b u) :=
    leftSmoothFactor_hasCompactSupport (I := I) (M := M) α hb_supp
  have h_tsupp : tsupport (leftSmoothFactor (I := I) (M := M) α b u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_leftSmoothFactor_subset_chartTarget (I := I) (M := M) α hb_supp
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
    (d := Module.finrank ℝ E) hΩ_open hSmooth hCompact h_tsupp hp_one 1).memW1p

private lemma smoothPushed_memW1p
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (smoothPushed (I := I) (M := M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hSmooth : ContDiff ℝ ∞ (smoothPushed (I := I) (M := M) α u) :=
    smoothPushed_smooth (I := I) (M := M) α hu
  have hCompact : HasCompactSupport (smoothPushed (I := I) (M := M) α u) :=
    smoothPushed_hasCompactSupport (I := I) (M := M) α u
  have h_tsupp : tsupport (smoothPushed (I := I) (M := M) α u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_smoothPushed_subset_chartTarget (I := I) (M := M) α u
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
    (d := Module.finrank ℝ E) hΩ_open hSmooth hCompact h_tsupp hp_one 1).memW1p

/-- `liftedPou α` takes values in `[0, 1]`. -/
private lemma liftedPou_apply_in_unit_interval
    [T2Space M] [SigmaCompactSpace M] (α : M) (y : EuclN) :
    0 ≤ liftedPou (I := I) (M := M) α y ∧ liftedPou (I := I) (M := M) α y ≤ 1 := by
  classical
  unfold liftedPou smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change 0 ≤ (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) ∧ _ ≤ 1
    rw [if_pos hy]
    exact ⟨(DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α _,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α _⟩
  · change 0 ≤ (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) ∧ _ ≤ 1
    rw [if_neg hy]
    exact ⟨le_refl 0, zero_le_one⟩

private lemma liftedPou_norm_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (y : EuclN) :
    ‖liftedPou (I := I) (M := M) α y‖ ≤ 1 := by
  obtain ⟨h_nn, h_le⟩ := liftedPou_apply_in_unit_interval (I := I) (M := M) α y
  rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
  exact h_le

private lemma exists_liftedPou_grad_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) : ∃ Cα : ℝ, 0 ≤ Cα ∧
      ∀ y : EuclN, ‖fderiv ℝ (liftedPou (I := I) (M := M) α) y‖ ≤ Cα := by
  classical
  unfold liftedPou
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hf_supp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨C, hC_nn, hC⟩ :=
    smoothExtension_first_order_bound (I := I) (M := M) α hf_smooth hf_supp
  refine ⟨C, hC_nn, fun y => ?_⟩
  have h := hC 1 (le_refl _) y
  rwa [norm_iteratedFDeriv_one] at h

/-- Sup-bound on `‖smoothPushed α u‖_∞` by `uMax` (uses `|ρ_α| ≤ 1`). -/
private lemma smoothPushed_norm_le_of_bound
    [T2Space M] [SigmaCompactSpace M] (α : M) {u : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax) (y : EuclN) :
    ‖smoothPushed (I := I) (M := M) α u y‖ ≤ uMax := by
  classical
  unfold smoothPushed smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M =>
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    have hρ_x_nonneg : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x
    have hρ_x_le_one : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x
    calc
      ‖((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x‖
          = ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * ‖u x‖ := by
            rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs,
              abs_of_nonneg hρ_x_nonneg]
      _ ≤ 1 * ‖u x‖ := by gcongr
      _ = ‖u x‖ := one_mul _
      _ ≤ uMax := hu_bound x
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M =>
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_neg hy, norm_zero]
    exact huMax_nn

/-- Sup-bound on `‖leftSmoothFactor α b u‖_∞` by `uMax` (uses `0 ≤ b ≤ 1`). -/
private lemma leftSmoothFactor_norm_le_of_bound
    (α : M) {b u : M → ℝ}
    (hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1) {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax) (y : EuclN) :
    ‖leftSmoothFactor (I := I) (M := M) α b u y‖ ≤ uMax := by
  classical
  unfold leftSmoothFactor smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    have hb_x_nn : 0 ≤ b x := (hb_le_one x).1
    have hb_x_le_one : b x ≤ 1 := (hb_le_one x).2
    calc
      ‖b x * u x‖ = b x * ‖u x‖ := by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_of_nonneg hb_x_nn]
      _ ≤ 1 * ‖u x‖ := by gcongr
      _ = ‖u x‖ := one_mul _
      _ ≤ uMax := hu_bound x
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_neg hy, norm_zero]
    exact huMax_nn

/-- For any cutoff `b` with `b ≡ 1` on `tsupport ρ_α`,
`liftedPou α · leftSmoothFactor α b v = smoothPushed α v` pointwise on `EuclN`. -/
private lemma liftedPou_mul_leftSmoothFactor_eq_smoothPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    (fun y : EuclN => liftedPou (I := I) (M := M) α y *
      leftSmoothFactor (I := I) (M := M) α b v y) =
    smoothPushed (I := I) (M := M) α v := by
  classical
  unfold liftedPou leftSmoothFactor smoothPushed
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    (fun x : M => b x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

/-- `smoothPushed α u · leftSmoothFactor α b v = smoothExtension α (ρ_α · u · v)`
(for `b ≡ 1` on `tsupport ρ_α`). -/
private lemma smoothPushed_mul_leftSmoothFactor_eq_smoothExtension_uv
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    (fun y : EuclN => smoothPushed (I := I) (M := M) α u y *
      leftSmoothFactor (I := I) (M := M) α b v y) =
    smoothExtension (I := I) (M := M) α
      (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x * v x) := by
  classical
  unfold smoothPushed leftSmoothFactor
  exact (smoothExtension_three_factor (I := I) (M := M) α hb_one).symm

/-- If `f : EuclN → ℝ` has support in a measurable set `K` and `‖f‖ ≤ C`
pointwise, then `eLpNorm f p (volume.restrict Ω) ≤ ENNReal.ofReal C *
(volume K)^{1/p.toReal}`. -/
private lemma eLpNorm_restrict_le_ofReal_mul_volume_pow
    {p : ℝ≥0∞} {Ω : Set EuclN}
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    {f : EuclN → ℝ} {C : ℝ} (hC_nn : 0 ≤ C)
    (h_supp : ∀ y, y ∉ K → f y = 0)
    (h_bound : ∀ y, ‖f y‖ ≤ C) :
    eLpNorm f p (volume.restrict Ω) ≤
      ENNReal.ofReal C * (volume K) ^ (1 / p.toReal) := by
  classical
  have h_pointwise : ∀ y, ‖f y‖ ≤ ‖K.indicator (fun _ : EuclN => C) y‖ := by
    intro y
    by_cases hy : y ∈ K
    · have h_ind : K.indicator (fun _ : EuclN => C) y = C := Set.indicator_of_mem hy _
      rw [h_ind]
      have : ‖C‖ = C := by rw [Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [this]
      exact h_bound y
    · have h_ind : K.indicator (fun _ : EuclN => C) y = 0 := Set.indicator_of_notMem hy _
      rw [h_supp y hy, h_ind, norm_zero]
  have h_ae : ∀ᵐ y ∂(volume.restrict Ω),
      ‖f y‖ ≤ ‖K.indicator (fun _ : EuclN => C) y‖ :=
    Filter.Eventually.of_forall h_pointwise
  refine (eLpNorm_mono_ae h_ae).trans ?_
  have h_indicator_bd : eLpNorm (K.indicator (fun _ : EuclN => C)) p (volume.restrict Ω) ≤
      ‖C‖ₑ * (volume.restrict Ω) K ^ (1 / p.toReal) :=
    eLpNorm_indicator_const_le (μ := volume.restrict Ω) (s := K) (c := C) (p := p)
  refine h_indicator_bd.trans ?_
  have h_meas_le : (volume.restrict Ω) K ≤ volume K := by
    rw [Measure.restrict_apply hK_meas]
    exact measure_mono Set.inter_subset_left
  refine mul_le_mul' ?_ ?_
  · rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_nn]
  · exact ENNReal.rpow_le_rpow h_meas_le (by positivity)

/-- The eLpNorm of `Eu · (∂ᵢR) · Ev` on `Ω` is bounded by
`ENNReal.ofReal (uMax · vMax · C_R) · (volume K_α)^{1/p.toReal}`,
where `K_α = chartCarrierLocal α`. The function is supported in `K_α`. -/
private lemma eLpNorm_Eu_dR_Ev_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1)
    {uMax vMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax)
    (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax) (hvMax_nn : 0 ≤ vMax)
    {C_R : ℝ} (hC_R_nn : 0 ≤ C_R)
    (hC_R_bound : ∀ y : EuclN, ‖fderiv ℝ (liftedPou (I := I) (M := M) α) y‖ ≤ C_R)
    (i : Fin (Module.finrank ℝ E)) {p : ℝ≥0∞} :
    eLpNorm (fun y : EuclN => leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y) p
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
    ENNReal.ofReal (uMax * vMax * C_R) *
      (volume (chartCarrierLocal (I := I) (M := M) α)) ^ (1 / p.toReal) := by
  classical
  set K_α : Set EuclN := chartCarrierLocal (I := I) (M := M) α
  have hK_compact : IsCompact K_α := chartCarrierLocal_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K_α := hK_compact.isClosed.measurableSet
  have hC_nn : 0 ≤ uMax * vMax * C_R :=
    mul_nonneg (mul_nonneg huMax_nn hvMax_nn) hC_R_nn
  have h_R_supp_in_K : tsupport (liftedPou (I := I) (M := M) α) ⊆ K_α :=
    tsupport_liftedPou_subset_chartCarrierLocal (I := I) (M := M) α
  have h_supp : ∀ y : EuclN, y ∉ K_α →
      leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y = 0 := by
    intro y hy_off
    have h_R_zero_nhd : ∀ᶠ z in nhds y, liftedPou (I := I) (M := M) α z = 0 := by
      have h_compl_open : IsOpen (tsupport (liftedPou (I := I) (M := M) α))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hy_off_R_supp : y ∉ tsupport (liftedPou (I := I) (M := M) α) :=
        fun h => hy_off (h_R_supp_in_K h)
      filter_upwards [h_compl_open.mem_nhds hy_off_R_supp] with z hz
      have hz_off_supp : z ∉ Function.support (liftedPou (I := I) (M := M) α) :=
        fun h_supp_z => hz (subset_tsupport _ h_supp_z)
      simpa using hz_off_supp
    have h_fderiv_zero : fderiv ℝ (liftedPou (I := I) (M := M) α) y = 0 := by
      have h_eq : liftedPou (I := I) (M := M) α =ᶠ[nhds y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_R_zero_nhd] with z hz
        exact hz
      rw [Filter.EventuallyEq.fderiv_eq h_eq]
      exact fderiv_const_apply (0 : ℝ)
    rw [h_fderiv_zero]
    simp
  have h_bound : ∀ y : EuclN,
      ‖leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y‖ ≤ uMax * vMax * C_R := by
    intro y
    have hEu_bd := leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α
      hb_le_one hu_bound huMax_nn y
    have hEv_bd := leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α
      hb_le_one hv_bound hvMax_nn y
    have h_dR_bd : ‖(fderiv ℝ (liftedPou (I := I) (M := M) α) y)
        (EuclideanSpace.single i (1 : ℝ))‖ ≤ C_R := by
      have h := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y)
        (EuclideanSpace.single i (1 : ℝ))
      have h_one : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
      rw [h_one, mul_one] at h
      exact h.trans (hC_R_bound y)
    calc
      ‖leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y‖
        = ‖leftSmoothFactor (I := I) (M := M) α b u y‖ *
          ‖(fderiv ℝ (liftedPou (I := I) (M := M) α) y)
            (EuclideanSpace.single i (1 : ℝ))‖ *
          ‖leftSmoothFactor (I := I) (M := M) α b v y‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ uMax * C_R * vMax := by gcongr
      _ = uMax * vMax * C_R := by ring
  exact eLpNorm_restrict_le_ofReal_mul_volume_pow hK_meas hC_nn h_supp h_bound

/-- Per-chart bilinear bound. For each chart `α : M`, smooth `u, v : M → ℝ`
with sup-bounds `uMax, vMax`, there is a chart-`α` geometric constant
`Bα ≥ 0` (independent of `u, v`) such that

  `wkpNorm 1 p (chartPushed ρ α (u · v)) Ω ≤
       vMax · wkpNorm 1 p (chartPushed ρ α u) Ω
     + uMax · wkpNorm 1 p (chartPushed ρ α v) Ω
     + Bα · uMax · vMax`. -/
private lemma per_chart_bilinear_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ (⊤ : ℝ≥0∞)) (α : M) :
    ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 p
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
                (fun x => u x * v x))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal vMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
                (d := Module.finrank ℝ E) 1 p
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal uMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
                (d := Module.finrank ℝ E) 1 p
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal (Bα * uMax * vMax) := by
  classical
  obtain ⟨b, hb_smooth, hb_range, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_with_data (I := I) (M := M) α
  have hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1 := hb_range
  obtain ⟨C_R, hC_R_nn, hC_R_bound⟩ :=
    exists_liftedPou_grad_bound (I := I) (M := M) α
  set d : ℕ := Module.finrank ℝ E with hd_def
  set vol_K : ℝ≥0∞ := volume (chartCarrierLocal (I := I) (M := M) α) with hvolK_def
  have hK_compact : IsCompact (chartCarrierLocal (I := I) (M := M) α) :=
    chartCarrierLocal_isCompact (I := I) (M := M) α
  have hvolK_finite : vol_K < ⊤ := hK_compact.measure_lt_top
  have hvolK_ne_top : vol_K ≠ ⊤ := hvolK_finite.ne
  set vol_K_pow : ℝ := (vol_K.toReal) ^ (1 / p.toReal) with hvolK_pow_def
  have hvolK_pow_nn : 0 ≤ vol_K_pow := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set Bα : ℝ := (d : ℝ) * C_R * vol_K_pow with hBα_def
  have hd_real_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hBα_nn : 0 ≤ Bα :=
    mul_nonneg (mul_nonneg hd_real_nn hC_R_nn) hvolK_pow_nn
  refine ⟨Bα, hBα_nn, ?_⟩
  intro u v hu hv uMax vMax huMax_nn hvMax_nn hu_bound hv_bound
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set Pu := smoothPushed (I := I) (M := M) α u
  set Pv := smoothPushed (I := I) (M := M) α v
  set Eu := leftSmoothFactor (I := I) (M := M) α b u
  set Ev := leftSmoothFactor (I := I) (M := M) α b v
  set R := liftedPou (I := I) (M := M) α
  have h_chartPushed_uv_eq : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
      (fun x => u x * v x) y) =ᵐ[volume.restrict Ω]
      fun y : EuclN => Pu y * Ev y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have h1 : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y := by
      classical
      rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
      unfold chartPushed
      ring
    have h2 := smoothPushed_mul_leftSmoothFactor_eq_smoothExtension_uv (I := I) (M := M)
      α (b := b) (u := u) (v := v) hb_one_on_tsupp
    have h2' : smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y = Pu y * Ev y := by
      have hh := congrFun h2 y
      simp only at hh
      exact hh.symm
    exact h1.trans h2'
  have h_chartPushed_u_eq_Pu : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y) =ᵐ[volume.restrict Ω]
      fun y => Pu y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    classical
    change chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y =
      smoothExtension (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) y
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
    rfl
  have h_chartPushed_v_eq_Pv : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y) =ᵐ[volume.restrict Ω]
      fun y => Pv y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    classical
    change chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y =
      smoothExtension (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x) y
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
    rfl
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := d) hp_one hΩ_open h_chartPushed_uv_eq,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := d) hp_one hΩ_open h_chartPushed_u_eq_Pu,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := d) hp_one hΩ_open h_chartPushed_v_eq_Pv]
  letI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p (fun y => Pu y * Ev y) Ω,
      DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p Pu Ω,
      DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p Pv Ω]
  simp_rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero
    (d := d) p _ Ω]
  set ePu : ℝ≥0∞ := eLpNorm Pu p (volume.restrict Ω) with hePu_def
  set ePv : ℝ≥0∞ := eLpNorm Pv p (volume.restrict Ω) with hePv_def
  set gPu : Fin d → ℝ≥0∞ := fun i => eLpNorm
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pu Ω) p (volume.restrict Ω) with hgPu_def
  set gPv : Fin d → ℝ≥0∞ := fun i => eLpNorm
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pv Ω) p (volume.restrict Ω) with hgPv_def
  set vMax_e : ℝ≥0∞ := ENNReal.ofReal vMax with hvMax_e_def
  set uMax_e : ℝ≥0∞ := ENNReal.ofReal uMax with huMax_e_def
  have h_Pu_bound : ∀ y, ‖Pu y‖ ≤ uMax := smoothPushed_norm_le_of_bound
    (I := I) (M := M) α hu_bound huMax_nn
  have h_Pv_bound : ∀ y, ‖Pv y‖ ≤ vMax := smoothPushed_norm_le_of_bound
    (I := I) (M := M) α hv_bound hvMax_nn
  have h_Eu_bound : ∀ y, ‖Eu y‖ ≤ uMax :=
    leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α hb_le_one hu_bound huMax_nn
  have h_Ev_bound : ∀ y, ‖Ev y‖ ≤ vMax :=
    leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α hb_le_one hv_bound hvMax_nn
  have h_Lp_bound : eLpNorm (fun y => Pu y * Ev y) p (volume.restrict Ω) ≤
      vMax_e * ePu := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := Pu) (c := vMax) ?_ p
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun y _ => ?_)
    calc
      ‖Pu y * Ev y‖ = ‖Ev y‖ * ‖Pu y‖ := by rw [norm_mul, mul_comm]
      _ ≤ vMax * ‖Pu y‖ := by gcongr; exact h_Ev_bound y
  have h_grad_bound : ∀ i : Fin d,
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i (fun y => Pu y * Ev y) Ω) p (volume.restrict Ω) ≤
        vMax_e * gPu i + uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
    intro i
    have hPu_smooth : ContDiff ℝ (⊤ : ℕ∞) Pu := smoothPushed_smooth (I := I) (M := M) α hu
    obtain ⟨Cu0, hCu0_nn, hCu0_bd⟩ := iteratedFDeriv_bound_of_compactSupport
      hPu_smooth (smoothPushed_hasCompactSupport (I := I) (M := M) α u) 0
    obtain ⟨Cu1, hCu1_nn, hCu1_bd⟩ := iteratedFDeriv_bound_of_compactSupport
      hPu_smooth (smoothPushed_hasCompactSupport (I := I) (M := M) α u) 1
    set Cu := max Cu0 Cu1
    have hCu_nn : 0 ≤ Cu := le_max_of_le_left hCu0_nn
    have hPu_bd_C : ∀ y ∈ Ω, ‖Pu y‖ ≤ Cu := fun y _ => by
      have h := hCu0_bd y; rw [norm_iteratedFDeriv_zero] at h
      exact h.trans (le_max_left _ _)
    have hPu_grad_bd_C : ∀ y ∈ Ω, ‖fderiv ℝ Pu y‖ ≤ Cu := fun y _ => by
      have h := hCu1_bd y; rw [norm_iteratedFDeriv_one] at h
      exact h.trans (le_max_right _ _)
    have hEv_mem : DeGiorgi.MemW1p (d := d) p Ev Ω :=
      leftSmoothFactor_memW1p (I := I) (M := M) α hb_smooth hv hb_supp hp_one
    have h_PuEv_ae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := d) hp_one hΩ_open hPu_smooth hPu_bd_C hPu_grad_bd_C hEv_mem i
    have hR_smooth : ContDiff ℝ (⊤ : ℕ∞) R := liftedPou_smooth (I := I) (M := M) α
    have hR_bd : ∀ y ∈ Ω, ‖R y‖ ≤ max 1 C_R := fun y _ =>
      (liftedPou_norm_le_one (I := I) (M := M) α y).trans (le_max_left _ _)
    have hR_grad_bd : ∀ y ∈ Ω, ‖fderiv ℝ R y‖ ≤ max 1 C_R := fun y _ =>
      (hC_R_bound y).trans (le_max_right _ _)
    have h_REv_ae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := d) hp_one hΩ_open hR_smooth hR_bd hR_grad_bd hEv_mem i
    have h_R_Ev_eq_Pv : (fun y : EuclN => R y * Ev y) = Pv :=
      liftedPou_mul_leftSmoothFactor_eq_smoothPushed (I := I) (M := M)
        α (b := b) (v := v) hb_one_on_tsupp
    have h_chosen_Pv_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i Pv Ω =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i (fun y => R y * Ev y) Ω := by
      rw [h_R_Ev_eq_Pv]
    have h_Pv_ae : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i Pv Ω
      =ᵐ[volume.restrict Ω]
      (fun y => R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Ev Ω y +
        (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) := by
      rw [h_chosen_Pv_eq]
      exact h_REv_ae
    have h_Pu_eq_R_Eu : (fun y : EuclN => R y * Eu y) = Pu :=
      liftedPou_mul_leftSmoothFactor_eq_smoothPushed (I := I) (M := M)
        α (b := b) (v := u) hb_one_on_tsupp
    have h_combined : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i (fun y => Pu y * Ev y) Ω
      =ᵐ[volume.restrict Ω]
      (fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω y -
        Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y +
        (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) := by
      filter_upwards [h_PuEv_ae, h_Pv_ae] with y hy1 hy2
      have hPu_y : Pu y = R y * Eu y := by
        have := congrFun h_Pu_eq_R_Eu y
        exact this.symm
      rw [hy1, hPu_y]
      have h_eq_R_Ev :
          R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y -
            (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y := by
        linarith
      have h_factor :
          R y * Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y =
            Eu y * (R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y) := by ring
      rw [h_factor, h_eq_R_Ev]
      ring
    rw [eLpNorm_congr_ae h_combined]
    set f1 : EuclN → ℝ := fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pv Ω y with hf1_def
    set f2 : EuclN → ℝ := fun y => Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y
      with hf2_def
    set f3 : EuclN → ℝ := fun y => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y
      with hf3_def
    have h_Eu_cont : Continuous Eu :=
      (leftSmoothFactor_smooth (I := I) (M := M) α hb_smooth hu hb_supp).continuous
    have h_Ev_cont : Continuous Ev :=
      (leftSmoothFactor_smooth (I := I) (M := M) α hb_smooth hv hb_supp).continuous
    have h_dR_cont : Continuous
        (fun y : EuclN => (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ))) :=
      (hR_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have h_dPu_cont : Continuous
        (fun y : EuclN => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ))) :=
      (hPu_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have h_chosen_cont_AESM : AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω)
        (volume.restrict Ω) := by
      have hPv_W1p : DeGiorgi.MemW1p (d := d) p Pv Ω :=
        smoothPushed_memW1p (I := I) (M := M) α hv hp_one
      exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        hPv_W1p i).aestronglyMeasurable
    have h_AESM_f1 : AEStronglyMeasurable f1 (volume.restrict Ω) :=
      h_Eu_cont.aestronglyMeasurable.mul h_chosen_cont_AESM
    have h_AESM_f2 : AEStronglyMeasurable f2 (volume.restrict Ω) :=
      (h_Eu_cont.mul h_dR_cont).aestronglyMeasurable.mul h_Ev_cont.aestronglyMeasurable
    have h_AESM_f3 : AEStronglyMeasurable f3 (volume.restrict Ω) :=
      h_dPu_cont.aestronglyMeasurable.mul h_Ev_cont.aestronglyMeasurable
    have h_eq_pointwise :
        (fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y -
          Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y +
          (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) =
        fun y => f1 y + (-f2 y) + f3 y := by
      funext y
      show _ = _
      ring
    rw [h_eq_pointwise]
    have h_AESM_neg_f2 : AEStronglyMeasurable (fun y => -f2 y) (volume.restrict Ω) := by
      have : AEStronglyMeasurable (-f2) (volume.restrict Ω) := h_AESM_f2.neg
      exact this
    have h_AESM_f1_neg_f2 : AEStronglyMeasurable (fun y => f1 y + -f2 y) (volume.restrict Ω) := by
      have : AEStronglyMeasurable (f1 + -f2) (volume.restrict Ω) := h_AESM_f1.add h_AESM_f2.neg
      exact this
    have h_addLR : (fun y => f1 y + -f2 y + f3 y) = (fun y => f1 y + -f2 y) + f3 := by
      funext y
      show _ = _
      rfl
    rw [h_addLR]
    refine (eLpNorm_add_le h_AESM_f1_neg_f2 h_AESM_f3 hp_one).trans ?_
    have h_addLR2 : (fun y => f1 y + -f2 y) = f1 + (-f2) := by
      funext y; rfl
    have h_tri_2 : eLpNorm (fun y => f1 y + -f2 y) p (volume.restrict Ω) ≤
        eLpNorm f1 p (volume.restrict Ω) + eLpNorm f2 p (volume.restrict Ω) := by
      rw [h_addLR2]
      have h := eLpNorm_add_le h_AESM_f1 h_AESM_f2.neg hp_one
      rwa [eLpNorm_neg] at h
    refine (add_le_add h_tri_2 (le_refl (eLpNorm f3 p (volume.restrict Ω)))).trans ?_
    have h_f1_bd : eLpNorm f1 p (volume.restrict Ω) ≤ uMax_e * gPv i := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (g := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω)
        (c := uMax) ?_ p
      refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y _ => ?_)
      change ‖Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω y‖ ≤ uMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y‖
      calc
        ‖Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y‖
          = ‖Eu y‖ * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y‖ := norm_mul _ _
        _ ≤ uMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y‖ := by gcongr; exact h_Eu_bound y
    have h_f2_bd : eLpNorm f2 p (volume.restrict Ω) ≤
        ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
      exact eLpNorm_Eu_dR_Ev_bound (I := I) (M := M) α hb_le_one
        hu_bound huMax_nn hv_bound hvMax_nn hC_R_nn hC_R_bound i
    have h_f3_bd : eLpNorm f3 p (volume.restrict Ω) ≤ vMax_e * gPu i := by
      have h_classical_eq_chosen :
          (fun y : EuclN => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)))
          =ᵐ[volume.restrict Ω]
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω := by
        have hPu_compact : HasCompactSupport Pu :=
          smoothPushed_hasCompactSupport (I := I) (M := M) α u
        have hPu_tsupp : tsupport Pu ⊆ Ω :=
          tsupport_smoothPushed_subset_chartTarget (I := I) (M := M) α u
        exact chosenWeakPartial_eq_classical_ae hp_one hΩ_open
          hPu_smooth hPu_compact hPu_tsupp i
      have h_f3_ae : f3 =ᵐ[volume.restrict Ω]
          (fun y => Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y) := by
        filter_upwards [h_classical_eq_chosen] with y hy
        change (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y =
          Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y
        rw [hy]
        ring
      rw [eLpNorm_congr_ae h_f3_ae]
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (g := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pu Ω)
        (c := vMax) ?_ p
      refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y _ => ?_)
      calc
        ‖Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y‖
          = ‖Ev y‖ * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pu Ω y‖ := norm_mul _ _
        _ ≤ vMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pu Ω y‖ := by gcongr; exact h_Ev_bound y
    calc
      eLpNorm f1 p (volume.restrict Ω) +
        eLpNorm f2 p (volume.restrict Ω) +
        eLpNorm f3 p (volume.restrict Ω)
        ≤ uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) +
          vMax_e * gPu i := by gcongr
      _ = vMax_e * gPu i + uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by ring
  refine (add_le_add h_Lp_bound (Finset.sum_le_sum (fun i _ => h_grad_bound i))).trans ?_
  have h_sum_split :
      ∑ i : Fin d, (vMax_e * gPu i + uMax_e * gPv i +
        ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) =
      (∑ i : Fin d, vMax_e * gPu i) + (∑ i : Fin d, uMax_e * gPv i) +
        ∑ _i : Fin d, ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [h_sum_split]
  rw [show (∑ i : Fin d, vMax_e * gPu i) = vMax_e * ∑ i : Fin d, gPu i from
        (Finset.mul_sum _ _ _).symm,
      show (∑ i : Fin d, uMax_e * gPv i) = uMax_e * ∑ i : Fin d, gPv i from
        (Finset.mul_sum _ _ _).symm]
  rw [show ∑ _i : Fin d, ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) =
        (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  rw [mul_add vMax_e ePu (∑ i, gPu i), mul_add uMax_e ePv (∑ i, gPv i)]
  have h_const_bound : (d : ℝ≥0∞) *
      (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) ≤
      ENNReal.ofReal (Bα * uMax * vMax) := by
    have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast _).symm
    have hvol_pow_eq : vol_K ^ (1 / p.toReal) = ENNReal.ofReal vol_K_pow := by
      have h_eq1 : vol_K = ENNReal.ofReal vol_K.toReal :=
        (ENNReal.ofReal_toReal hvolK_ne_top).symm
      have h_inv : 0 ≤ (1 : ℝ) / p.toReal := by positivity
      have h_rpow : (ENNReal.ofReal vol_K.toReal) ^ (1 / p.toReal) =
          ENNReal.ofReal (vol_K.toReal ^ (1 / p.toReal)) :=
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg h_inv
      rw [h_eq1, h_rpow, hvolK_pow_def]
    have h_uvCR_nn : 0 ≤ uMax * vMax * C_R := by positivity
    have h_uvCR_volK_nn : 0 ≤ (uMax * vMax * C_R) * vol_K_pow :=
      mul_nonneg h_uvCR_nn hvolK_pow_nn
    have hBα_eq : Bα * uMax * vMax = (d : ℝ) * ((uMax * vMax * C_R) * vol_K_pow) := by
      rw [hBα_def]; ring
    have h_eq : (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal))
        = ENNReal.ofReal (Bα * uMax * vMax) := by
      calc (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal))
          = ENNReal.ofReal (d : ℝ) *
              (ENNReal.ofReal (uMax * vMax * C_R) * ENNReal.ofReal vol_K_pow) := by
            rw [hd_eq, hvol_pow_eq]
        _ = ENNReal.ofReal (d : ℝ) * ENNReal.ofReal ((uMax * vMax * C_R) * vol_K_pow) := by
            rw [ENNReal.ofReal_mul h_uvCR_nn]
        _ = ENNReal.ofReal ((d : ℝ) * ((uMax * vMax * C_R) * vol_K_pow)) := by
            rw [← ENNReal.ofReal_mul hd_real_nn]
        _ = ENNReal.ofReal (Bα * uMax * vMax) := by
            rw [← hBα_eq]
    rw [h_eq]
  calc
    vMax_e * ePu + (vMax_e * ∑ i : Fin d, gPu i + uMax_e * ∑ i : Fin d, gPv i +
      (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)))
      ≤ vMax_e * ePu + (vMax_e * ∑ i, gPu i + uMax_e * ∑ i, gPv i +
        ENNReal.ofReal (Bα * uMax * vMax)) := by gcongr
    _ = (vMax_e * ePu + vMax_e * ∑ i, gPu i) + uMax_e * ∑ i, gPv i +
          ENNReal.ofReal (Bα * uMax * vMax) := by ring
    _ ≤ (vMax_e * ePu + vMax_e * ∑ i, gPu i) + (uMax_e * ePv + uMax_e * ∑ i, gPv i) +
          ENNReal.ofReal (Bα * uMax * vMax) := by
        gcongr
        exact le_add_self

/-- Explicit bilinear bound (sup-bounds form): for smooth `u, v` with sup-bounds
`uMax, vMax`,

  `wkpNormChart g 1 p (u · v) ≤ vMax · wkpNormChart g 1 p u +
                                uMax · wkpNormChart g 1 p v +
                                B · uMax · vMax`,

where `B ≥ 0` is a manifold-level geometric constant (independent of `u, v`). -/
private lemma mul_smooth_chart_bound_explicit_form
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p)
              (fun x => u x * v x) ≤
            ENNReal.ofReal vMax *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u +
            ENNReal.ofReal uMax *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v +
            ENNReal.ofReal (B * uMax * vMax) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : ENNReal.ofReal p ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  have h_per_α : ∀ α ∈ S, ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
                (fun x => u x * v x))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal vMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
                (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal uMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
                (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal (Bα * uMax * vMax) := fun α _ =>
    per_chart_bilinear_bound (I := I) (M := M) hp_enn_one hp_enn_top α
  set Bfun : M → ℝ := fun α =>
    if hα : α ∈ S then Classical.choose (h_per_α α hα) else 0 with hBfun_def
  have hBfun_eq_of_mem : ∀ α (hα : α ∈ S), Bfun α = Classical.choose (h_per_α α hα) := by
    intro α hα
    change (if hα' : α ∈ S then Classical.choose (h_per_α α hα') else 0) =
      Classical.choose (h_per_α α hα)
    rw [dif_pos hα]
  have hBfun_nn : ∀ α ∈ S, 0 ≤ Bfun α := by
    intro α hα
    rw [hBfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).1
  refine ⟨∑ α ∈ S, Bfun α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α hα => hBfun_nn α hα)
  intro u v hu hv uMax vMax huMax_nn hvMax_nn hu_bound hv_bound
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one (fun x => u x * v x),
      wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one u,
      wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one v]
  have hBfun_bound : ∀ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => u x * v x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal vMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) +
        ENNReal.ofReal uMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
            (chartTargetEuclid (I := I) (M := M) α) +
        ENNReal.ofReal (Bfun α * uMax * vMax) := by
    intro α hα
    rw [hBfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).2 hu hv huMax_nn hvMax_nn hu_bound hv_bound
  refine (Finset.sum_le_sum (fun α hα => hBfun_bound α hα)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  set X : M → ℝ≥0∞ := fun α => DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
    (chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
    (chartTargetEuclid (I := I) (M := M) α) with hX_def
  set Y : M → ℝ≥0∞ := fun α => DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
    (chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
    (chartTargetEuclid (I := I) (M := M) α) with hY_def
  rw [show (∑ α ∈ S, ENNReal.ofReal vMax * X α) = ENNReal.ofReal vMax * ∑ α ∈ S, X α from
        (Finset.mul_sum _ _ _).symm,
      show (∑ α ∈ S, ENNReal.ofReal uMax * Y α) = ENNReal.ofReal uMax * ∑ α ∈ S, Y α from
        (Finset.mul_sum _ _ _).symm]
  refine add_le_add (le_refl _) ?_
  have h_sum_ofReal : ∑ α ∈ S, ENNReal.ofReal (Bfun α * uMax * vMax) =
      ENNReal.ofReal (∑ α ∈ S, Bfun α * uMax * vMax) := by
    refine (ENNReal.ofReal_sum_of_nonneg ?_).symm
    intro α hα
    have h := mul_nonneg (mul_nonneg (hBfun_nn α hα) huMax_nn) hvMax_nn
    exact h
  rw [h_sum_ofReal]
  have h_factor : ∑ α ∈ S, Bfun α * uMax * vMax = (∑ α ∈ S, Bfun α) * uMax * vMax := by
    rw [show (∑ α ∈ S, Bfun α * uMax * vMax) = ∑ α ∈ S, Bfun α * (uMax * vMax) from
      Finset.sum_congr rfl (fun α _ => by ring),
      ← Finset.sum_mul]
    ring
  rw [h_factor]

/-- **Bilinear chart-Sobolev algebra estimate at first order, super-critical
exponent.** For a closed Riemannian manifold of dimension `n ≥ 1` and an
exponent `p > n`, the chart-based Sobolev norm satisfies

  `wkpNormChart g 1 p (u · v) ≤ C · wkpNormChart g 1 p u · wkpNormChart g 1 p v`

for all smooth `u, v : M → ℝ`. The constant `C ≥ 0` depends on the metric `g`,
the exponent `p`, and the manifold geometry, but not on `u` or `v`. -/
theorem mul_smooth_chart_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u v : M → ℝ},
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (fun x => u x * v x) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u *
            wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨B, hB_nn, hB_bound⟩ :=
    mul_smooth_chart_bound_explicit_form (I := I) (M := M) g hp
  obtain ⟨M_M, hM_M_nn, hM_M_bound⟩ :=
    smooth_manifold_morrey_sup_bound_uniform (I := I) (M := M) g hp
  set C : ℝ := 2 * M_M + B * M_M ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by
    have h1 : 0 ≤ 2 * M_M := mul_nonneg (by norm_num) hM_M_nn
    have h2 : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    linarith
  refine ⟨C, hC_nn, ?_⟩
  intro u v hu hv
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set NU : ℝ≥0∞ := wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u with hNU_def
  set NV : ℝ≥0∞ := wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v with hNV_def
  have hNU_lt : NU < ⊤ := wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_enn_one
    (DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_enn_one hu)
  have hNV_lt : NV < ⊤ := wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_enn_one
    (DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_enn_one hv)
  have hNU_ne_top : NU ≠ ⊤ := hNU_lt.ne
  have hNV_ne_top : NV ≠ ⊤ := hNV_lt.ne
  set uMax : ℝ := M_M * NU.toReal with huMax_def
  set vMax : ℝ := M_M * NV.toReal with hvMax_def
  have huMax_nn : 0 ≤ uMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hvMax_nn : 0 ≤ vMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hu_bound : ∀ x : M, ‖u x‖ ≤ uMax := fun x => hM_M_bound hu x
  have hv_bound : ∀ x : M, ‖v x‖ ≤ vMax := fun x => hM_M_bound hv x
  have h_explicit := hB_bound hu hv huMax_nn hvMax_nn hu_bound hv_bound
  refine h_explicit.trans ?_
  have h_ofReal_vMax : ENNReal.ofReal vMax = ENNReal.ofReal M_M * NV := by
    rw [hvMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNV_ne_top]
  have h_ofReal_uMax : ENNReal.ofReal uMax = ENNReal.ofReal M_M * NU := by
    rw [huMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNU_ne_top]
  have h_ofReal_B_uMax_vMax : ENNReal.ofReal (B * uMax * vMax) =
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV := by
    have h_eq : B * uMax * vMax = B * M_M ^ 2 * NU.toReal * NV.toReal := by
      rw [huMax_def, hvMax_def]
      ring
    rw [h_eq]
    have h_BM2_nn : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    have h_BM2_NU_nn : 0 ≤ B * M_M ^ 2 * NU.toReal :=
      mul_nonneg h_BM2_nn ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_mul h_BM2_NU_nn, ENNReal.ofReal_mul h_BM2_nn,
      ENNReal.ofReal_toReal hNU_ne_top, ENNReal.ofReal_toReal hNV_ne_top]
  rw [h_ofReal_vMax, h_ofReal_uMax, h_ofReal_B_uMax_vMax]
  have h_sum_le : ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2) ≤
      ENNReal.ofReal C := by
    rw [show (ENNReal.ofReal M_M + ENNReal.ofReal M_M : ℝ≥0∞) =
      ENNReal.ofReal (M_M + M_M) from
      (ENNReal.ofReal_add hM_M_nn hM_M_nn).symm,
      show (ENNReal.ofReal (M_M + M_M) + ENNReal.ofReal (B * M_M ^ 2) : ℝ≥0∞) =
        ENNReal.ofReal ((M_M + M_M) + (B * M_M ^ 2)) from
      (ENNReal.ofReal_add (by linarith) (mul_nonneg hB_nn (sq_nonneg _))).symm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_def]
    linarith
  have h_LHS_eq : ENNReal.ofReal M_M * NV * NU + ENNReal.ofReal M_M * NU * NV +
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV =
    (ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2)) * NU * NV := by
    ring
  rw [h_LHS_eq]
  exact mul_le_mul' (mul_le_mul' h_sum_le (le_refl _)) (le_refl _)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
