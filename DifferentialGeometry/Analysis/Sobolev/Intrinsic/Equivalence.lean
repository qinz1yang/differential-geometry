import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Defs
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.Measure.Glue
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Equivalence between chart-based `W^{1,p}` and intrinsic `W^{1,p}` on smooth functions

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and an
exponent `1 ≤ p ≤ ∞` (`p ≠ ∞`), this file establishes that the chart-based
predicate `MemWkpChart g 1 p u` (defined in `Sobolev/Chart.lean`) and the
intrinsic predicate `MemW1pIntrinsic g p u` (defined in `Sobolev/Intrinsic.lean`)
both hold for every smooth scalar function `u : M → ℝ`. As a consequence, the
two predicates are equivalent on smooth inputs.

## Main results

* `MemWkpChart_of_contMDiff` : every smooth function on a closed Riemannian
  manifold satisfies the chart-based `W^{1,p}` predicate at order `k = 1`.
* `MemW1pIntrinsic_of_contMDiff_explicit` : the corresponding fact for the
  intrinsic `W^{1,p}` predicate (re-exporting the existing
  `MemW1pIntrinsic_of_contMDiff`).
* `memWkpChart_iff_memW1pIntrinsic_of_contMDiff` : both predicates are
  equivalent on smooth inputs (each side is automatically `True`).
* `wkpNormChart_lt_top_of_contMDiff` and
  `w1pNormIntrinsic_lt_top_of_contMDiff` : both norms are finite for smooth
  inputs on a closed manifold.

## Strategy

For each chart `α`, we extend the chart-pushed function `chartPushed ρ α u`
to a globally smooth, compactly supported function on
`EuclideanSpace ℝ (Fin (finrank ℝ E))` by overriding the value to be `0`
outside the chart-target image. The two functions agree pointwise on the
chart-target image, and the extension is smooth with compact support contained
in the chart-target image. Hence `MemW1p p (chartPushed ρ α u)` (on the chart
target) follows directly from the existential structure of `MemW1p` together
with `HasWeakPartialDeriv.of_contDiff`, transferred via `MemW1p_congr_ae`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart

/-- Local notation for the standard Euclidean space of dimension
`Module.finrank ℝ E`. -/
private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The smooth global extension `chartPushedExt α f` of a function `f : M → ℝ`,
defined as `f ((extChartAt I α).symm (toEuclidean.symm y))` if
`y ∈ chartTargetEuclid α` and `0` otherwise. -/
private def chartPushedExt (α : M) (f : M → ℝ) : EuclN E → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

private lemma chartPushedExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

private lemma chartPushedExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

/-- On the chart-target image, `chartPushedExt α f` pointwise equals
the formula `f ((extChartAt I α).symm (toEuclidean.symm y))`. -/
private lemma chartPushedExt_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  apply chartPushedExt_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

/-- For `y ∉ chartTargetEuclid α`, `chartPushedExt α f y = 0`. -/
private lemma chartPushedExt_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  apply chartPushedExt_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

/-- On the chart-target image, `chartPushed ρ α u` agrees pointwise with
`chartPushedExt α (ρα * u)`. -/
private lemma chartPushedExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M) ρ α u y := by
  classical
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
  unfold chartPushed
  rfl

/-- For a smooth chart-source-supported function `f : M → ℝ` with compact
support, the toEuclidean image of the chart image of `tsupport f` is compact
in `EuclN E`. -/
private lemma image_toEuclidean_chart_tsupport_isCompact
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE := image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M) (u := f) (α := α) hf_supp
  exact hKE.1.image (toEuclidean (E := E)).continuous

/-- The toEuclidean image of the chart image of `tsupport f` is contained in
`chartTargetEuclid α`. -/
private lemma image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_supp

/-- Outside the toEuclidean image of the chart image of `tsupport f`, the
extension `chartPushedExt α f` vanishes. This is the "extended-by-zero" property
that gives compact support. -/
private lemma chartPushedExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt H α).source) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hz_target
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
  · exact chartPushedExt_apply_of_notMem_chartTargetEuclid (I := I) (M := M) α f hy_target

/-- The function `chartPushedExt α f` has compact support, when `f` is supported
in the chart source on a compact manifold. -/
private lemma hasCompactSupport_chartPushedExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedExt (I := I) (M := M) α f) := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_chart_tsupport_isCompact
      (I := I) (M := M) (f := f) (α := α) hf_supp
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_supp hyK

/-- The composition `f ∘ (extChartAt I α).symm ∘ toEuclidean.symm` is smooth
on `chartTargetEuclid α` when `f` is smooth on `M`. -/
private lemma contDiffOn_chartPushedExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN E =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target := by
    have h := scalarOnE_contDiffOn (I := I) α hf
    exact h
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hcomp := hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  exact hcomp

/-- `chartPushedExt α f` is smooth at every point in the open
`chartTargetEuclid α`. -/
private lemma contDiffAt_chartPushedExt_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_chartPushedExt_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

/-- Compactness-based version: when `tsupport f` is compact (e.g., on a compact
manifold, or for compactly supported f), the function `chartPushedExt α f` is
smooth at every point outside the toEuclidean image of the chart image of
`tsupport f`. -/
private lemma contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I α).source := by
      intro x hx
      rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]
      exact hf_supp hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
      hf_compact.image_of_continuousOn hcont
    exact h1.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN E => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_supp hz

/-- The function `chartPushedExt α f` is globally smooth on `EuclN E`, when
`f` is smooth on `M` with `tsupport f` compact and contained in
`(chartAt H α).source`. -/
private lemma contDiff_chartPushedExt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless]
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_chartPushedExt_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) (f := f) (α := α) hf_supp hy_in
    exact contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
      (I := I) (M := M) α (f := f) hf_supp hf_compact hy_off

/-- The (private) chart-target image is open in `EuclN E` (re-exported from
`Sobolev/Chart.lean`). -/
private lemma chartTargetEuclid_isOpen' [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

/-- For smooth `u : M → ℝ` on a closed manifold, `chartPushedExt α (ρα * u)`
is in `L^p` of `volume.restrict (chartTargetEuclid α)` for every `p ≥ 1`. -/
private lemma memLp_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞) :
    MemLp (chartPushedExt (I := I) (M := M) α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_supp hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_supp
  have hmemLp_global : MemLp (chartPushedExt (I := I) (M := M) α f) p volume :=
    hsmooth.continuous.memLp_of_hasCompactSupport hcs
  exact hmemLp_global.restrict _

/-- The classical fderiv of the smooth extension is itself smooth and
compactly supported, hence in `L^p` of any restriction. -/
private lemma fderiv_chartPushedExt_memLp
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞)
    (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun x : EuclN E =>
        (fderiv ℝ (chartPushedExt (I := I) (M := M) α
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) x)
          (EuclideanSpace.single i 1))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_supp hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_supp
  have hderiv_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    (hsmooth.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  have hderiv_cs : HasCompactSupport
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    hcs.fderiv_apply (𝕜 := ℝ) _
  have hmemLp_global : MemLp _ p volume :=
    hderiv_smooth.continuous.memLp_of_hasCompactSupport hderiv_cs
  exact hmemLp_global.restrict _

/-- `chartPushedExt α (ρα * u)` is in `MemW1p p` on `chartTargetEuclid α`. -/
private lemma memW1p_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (_hp : 1 ≤ p) :
    DeGiorgi.MemW1p p (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_supp hf_compact
  refine ⟨?_, ?_⟩
  · exact memLp_chartPushedExt (I := I) (M := M) α ρ hρ hu p
  · intro i
    refine ⟨fun x : EuclN E =>
      (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1), ?_, ?_⟩
    · exact fderiv_chartPushedExt_memLp (I := I) (M := M) α ρ hρ hu p i
    · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff
        (chartTargetEuclid_isOpen' (I := I) (M := M) α)
        (hsmooth.of_le (by norm_cast))

/-- For smooth `u : M → ℝ` on a closed Riemannian manifold, the chart-pushed
function for chart `α` lies in `MemW1p p` of `chartTargetEuclid α`. -/
private theorem memW1p_chartPushed_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    DeGiorgi.MemW1p p
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set ρ := chartAtlasPOU I M with hρ_def
  have hρ_sub : ρ.IsSubordinate (fun β : M => (chartAt H β).source) :=
    chartAtlasPOU_isSubordinate I M
  have hExt_memW1p : DeGiorgi.MemW1p p
      (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) :=
    memW1p_chartPushedExt (I := I) (M := M) α ρ hρ_sub hu hp
  have hae_eq : chartPushedExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
    refine
      (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact chartPushedExt_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u hy
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen' (I := I) (M := M) α) hae_eq).mp hExt_memW1p

/-- **Smooth bridge for `MemWkpChart`**: every smooth function on a closed
Riemannian manifold lies in the chart-based `W^{1,p}` space (at order `k = 1`). -/
theorem MemWkpChart_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) g 1 p u := by
  intro α
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  refine ⟨?_, ?_⟩
  · exact memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
  · intro i
    have hMW1p : DeGiorgi.MemW1p p
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
      memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      (d := Module.finrank ℝ E) hMW1p i

/-- **Smooth bridge for `MemW1pIntrinsic`** (re-export). Every smooth function
on a closed Riemannian manifold lies in `W^{1,p}_{int}` for every exponent `p`. -/
theorem MemW1pIntrinsic_of_contMDiff_explicit
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic
      (I := I) (M := M) g p u :=
  DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic_of_contMDiff
    (I := I) (M := M) g p hu

/-- **Equivalence on smooth inputs.** For a smooth function `u` on a closed
Riemannian manifold, the chart-based `W^{1,p}` predicate (at order 1) is
equivalent to the intrinsic `W^{1,p}` predicate. Both sides hold automatically
on smooth inputs, so the equivalence is `True ↔ True`. -/
theorem memWkpChart_iff_memW1pIntrinsic_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) g 1 p u ↔
      DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic
        (I := I) (M := M) g p u := by
  let _ := hp_top
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact MemW1pIntrinsic_of_contMDiff_explicit (I := I) (M := M) g p hu_smooth
  · exact MemWkpChart_of_contMDiff (I := I) (M := M) g hp_one hu_smooth

/-- The chart-based `W^{1,p}` norm is finite for smooth `u` on a closed
manifold. -/
theorem wkpNormChart_lt_top_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
  wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp
    (MemWkpChart_of_contMDiff (I := I) (M := M) g hp hu)

/-- The intrinsic `W^{1,p}` norm is finite for smooth `u` on a closed
manifold. -/
theorem w1pNormIntrinsic_lt_top_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.Intrinsic.w1pNormIntrinsic
        (I := I) (M := M) g p u < ⊤ :=
  (MemW1pIntrinsic_of_contMDiff_explicit (I := I) (M := M) g p hu).w1pNormIntrinsic_lt_top

end Equivalence
end Sobolev
end Analysis
end DifferentialGeometry
