import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanMorrey
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

/-!
# Manifold Morrey embedding `W^{1,p}_chart(M) ↪ C^0(M)` for `p > n`,
half-space (with-boundary) variant — smooth-input case

This is the with-boundary parallel of `Analysis/Sobolev/MorreyManifold.lean`.
For a smooth manifold `M` modelled on the canonical Euclidean half-space
`EuclideanHalfSpace n` (`n ≥ 1`) with a smooth Riemannian metric `g`, and for
`p > n`, every smooth `u : M → ℝ` whose canonical-POU-localised chart-pushed
functions all have `tsupport` strictly in the open interior parts of the
chart targets satisfies a uniform-in-`u` sup-norm bound

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`

The constant `C ≥ 0` depends only on the metric, the canonical chart-atlas
partition of unity, and the exponent `p`.

## Strategy

The chart-based with-boundary Sobolev predicate `MemWkpChart` and norm
`wkpNormChart` are by construction the Dirichlet-half-space variants:
the chart-target carriers `chartTargetEuclid α = (extChartAt I α).target`
are half-space-relatively-open subsets of `EuclideanSpace ℝ (Fin n)`, and the
underlying iterated Sobolev predicate is the boundaryless `MemWkp` evaluated
on the open interior part `interiorHalfSpace Ω = Ω ∩ openHalfSpace`.

When the chart-pushed function `chartPushed ρ_α α u` has `tsupport` strictly
inside `interiorHalfSpace (chartTargetEuclid α)`, its smooth extension by
zero across the boundary face is globally smooth on `EuclideanSpace ℝ (Fin n)`.
We apply the boundaryless smooth Morrey
`smooth_morrey_sup_bound_uniform` on a Euclidean ball containing the
chart-pushed carrier, and sum the per-chart bounds over the canonical
chart-atlas partition of unity.

Two parallel uniform-in-`u` per-chart bounds are delivered:

1. **Sup-norm per-chart**: each chart-extended `chartSmoothExt α (ρ_α · u)`
   is bounded uniformly in `u` by `(C_α : ℝ) · (wkpNormChart g 1 p u).toReal`.
2. **Hölder pair per-chart**: each chart-extended function is Hölder
   continuous with exponent `1 - n/p` on the chart-pushed carrier, with
   modulus uniformly controlled by `(wkpNormChart g 1 p u).toReal`.

These per-chart bounds combine via the canonical chart-atlas POU sum
identity to give the manifold-level sup-norm and per-chart Hölder modulus.

## Main results

### Smooth manifold-level Morrey sup-bound (with boundary)

* `smooth_manifold_morrey_sup_bound_uniform_withBoundary` — for smooth
  `u : M → ℝ` whose chart-pushed `tsupport`s lie in the open interior parts
  of all chart targets, `‖u(x)‖ ≤ C · (wkpNormChart u).toReal` for every
  `x ∈ M`.

### Per-chart smooth Hölder modulus (with boundary)

* `smooth_manifold_morrey_holder_modulus_per_chart_withBoundary` — for each
  chart `α`, smooth `u : M → ℝ` with chart-pushed `tsupport` strictly
  interior, and `p > n`, the canonical-POU-localised function `(ρ_α · u)`
  satisfies a chart-α Hölder modulus on `tsupport ρ_α`.

### Manifold-level decomposition

* `norm_sub_le_sum_pou_diff_withBoundary` — re-export of the canonical-POU
  triangle inequality `‖u(x) - u(y)‖ ≤ ∑_α ‖(ρ_α · u)(x) - (ρ_α · u)(y)‖`.

## Scope note

The fully general manifold Morrey embedding `W^{1,p}_chart(M) ↪ C^0(M)`
extending to all measurable `u ∈ MemWkpChart` (rather than just smooth
inputs) requires a smooth-density argument in `MemWkpChart` (analogous to
the boundaryless `contMDiff_dense_in_WkpChart`). In the with-boundary
setting this requires the boundary-trace / mollification-near-boundary
infrastructure that is currently developed only chart-locally
(`WithBoundary/EuclideanDensity.lean`); a manifold-level density bridge
is a downstream concern and out of scope for the present file. The
smooth-input version delivered here, together with the per-chart Hölder
modulus, is the engine used by every downstream parabolic / elliptic
regularity application.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The chart-extended function on `EuN`: equals `f ∘ (extChartAt I α).symm`
on the chart target, and `0` outside. -/
def chartSmoothExt (α : M) (f : M → ℝ) : EuN → ℝ := by
  classical
  exact fun y =>
    if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y =
      f ((extChartAt I_hs α).symm y) := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = f ((extChartAt I_hs α).symm y)
  rw [if_pos hy]

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I_hs ∞ M] in
/-- On the chart target, `chartSmoothExt α (ρ_α · u)` agrees pointwise with
`chartPushed ρ α u`. -/
private lemma chartSmoothExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) y =
      chartPushed (n := n) (M := M) ρ α u y := by
  classical
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hy]
  unfold chartPushed
  rfl

private lemma image_extChartAt_tsupport_compact_subset_target
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    IsCompact ((extChartAt I_hs α) '' (tsupport f)) ∧
      (extChartAt I_hs α) '' (tsupport f) ⊆ (extChartAt I_hs α).target := by
  classical
  have h_supp_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_supp_ext_src : tsupport f ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  have h_cont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
    (continuousOn_extChartAt α).mono h_supp_ext_src
  refine ⟨h_supp_compact.image_of_continuousOn h_cont, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (h_supp_ext_src hx)

private lemma chartSmoothExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ (extChartAt I_hs α).target
  · rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hy_target]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I_hs α).symm y ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hy_eq : (extChartAt I_hs α) ((extChartAt I_hs α).symm y) = y :=
      (extChartAt I_hs α).right_inv hy_target
    refine ⟨(extChartAt I_hs α).symm y, hsymm_in_supp, hy_eq⟩
  · exact chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy_target

private lemma hasCompactSupport_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hyK

/-- `tsupport (chartSmoothExt α f) ⊆ extChartAt α image of tsupport f`. -/
private lemma tsupport_chartSmoothExt_subset
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    tsupport (chartSmoothExt (n := n) (M := M) α f) ⊆
      (extChartAt I_hs α) '' (tsupport f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (chartSmoothExt (n := n) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact chartSmoothExt_eq_zero_off_image_tsupport
      (n := n) (M := M) α (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

private lemma contDiffOn_chartSmoothExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuN => f ((extChartAt I_hs α).symm y))
        (extChartAt I_hs α).target := by
  classical
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I_hs) α hf

/-- Predicate on a smooth `f : M → ℝ`: the chart-pushed image of `tsupport f`
under `extChartAt I α` lies strictly inside the open interior part of
the chart target. -/
def chartSmoothExtInteriorSupport
    (α : M) (f : M → ℝ) : Prop :=
  (extChartAt I_hs α) '' (tsupport f) ⊆
    DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

private lemma chartSmoothExtInteriorSupport_image_subset_interior
    {α : M} {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    (extChartAt I_hs α) '' (tsupport f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨?_, h_int ⟨x, hx, rfl⟩⟩
  have h_src : x ∈ (extChartAt I_hs α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  exact (extChartAt I_hs α).map_source h_src

private lemma contDiffAt_chartSmoothExt_of_mem_interior_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) {y : EuN}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have hy_target : y ∈ (extChartAt I_hs α).target := hy.1
  have hContDiffOn := contDiffOn_chartSmoothExt_formula (n := n) (M := M) α hf
  have h_within : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (extChartAt I_hs α).target y := hContDiffOn y hy_target
  have hInt_sub : DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α) ⊆ (extChartAt I_hs α).target := by
    intro z hz
    exact hz.1
  have h_within_int : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) y :=
    h_within.mono hInt_sub
  have h_contDiffAt : ContDiffAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y)) y :=
    h_within_int.contDiffAt (hOpen.mem_nhds hy)
  apply h_contDiffAt.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hz.1]

private lemma contDiffAt_chartSmoothExt_of_notMem_image_tsupport
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I_hs α).source := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hf_supp hx
    have hcont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    exact hf_compact.image_of_continuousOn hcont
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuN => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hz

private lemma contDiff_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  by_cases hyK : y ∈ K
  · have hy_int : y ∈
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) hf_supp h_int hyK
    exact contDiffAt_chartSmoothExt_of_mem_interior_target
      (n := n) (M := M) α hf hy_int
  · have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
    exact contDiffAt_chartSmoothExt_of_notMem_image_tsupport
      (n := n) (M := M) α hf_supp hf_compact hyK

omit [IsManifold I_hs ∞ M] in
private lemma tsupport_pou_mul_subset_chart_source
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      (chartAt (EuclideanHalfSpace n) α).source := by
  have h1 : tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  exact h1.trans (hρ α)

private lemma contDiff_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I_hs, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact contDiff_chartSmoothExt (n := n) (M := M) α hf_smooth hf_supp h_int

private lemma hasCompactSupport_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (u : M → ℝ) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact hasCompactSupport_chartSmoothExt (n := n) (M := M) α hf_supp

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The compact support carrier in `EuN`: the `extChartAt I α` image of
`tsupport ρ_α` for the canonical POU weight `ρ_α`. -/
private def chartCarrier (α : M) : Set EuN :=
  (extChartAt I_hs α) ''
    (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ))

private lemma chartCarrier_isCompact (α : M) :
    IsCompact (chartCarrier (n := n) (M := M) α) := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  have hcont_ext : ContinuousOn (extChartAt I_hs α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_src
  exact hTα_compact.image_of_continuousOn hcont_ext

private lemma chartCarrier_subset_chartTarget (α : M) :
    chartCarrier (n := n) (M := M) α ⊆ (extChartAt I_hs α).target := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (hTα_ext_src hx)

/-- A radius `R_α` such that `chartCarrier α ⊆ Metric.ball 0 (R_α / 2)` and
`R_α > 0`. -/
private noncomputable def chartRadius (α : M) : ℝ :=
  (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) * 2 + 1

private lemma chartRadius_pos (α : M) : 0 < chartRadius (n := n) (M := M) α := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  linarith [h.1]

private lemma chartCarrier_subset_half_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  have h1 : 0 < (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) := h.1
  have h2 : chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN)
        (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
          0 (0 : EuN)).choose) := h.2
  refine h2.trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h_ineq : (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) ≤
      (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
        0 (0 : EuN)).choose * 2 + 1) / 2 := by
    linarith
  linarith

private lemma chartCarrier_subset_full_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α) := by
  refine (chartCarrier_subset_half_ball (n := n) (M := M) α).trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h := chartRadius_pos (n := n) (M := M) α
  linarith

/-- Predicate version: the canonical-POU chart-pushed image of
`(ρ_α · u)` has tsupport strictly inside the open interior part of the
chart target, for every chart `α`. -/
def AllChartsInteriorSupport (u : M → ℝ) : Prop :=
  ∀ α : M,
    chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)

/-- For smooth `u : M → ℝ` whose canonical POU localisation has chart-
pushed `tsupport` strictly inside the open interior part of every chart
target, `chartSmoothExt α (ρ_α · u)` is supported in `chartCarrier α`. -/
private lemma tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
    (α : M) (u : M → ℝ) :
    tsupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) ⊆
      chartCarrier (n := n) (M := M) α := by
  classical
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have h_pou_supp_sub_tα : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ Tα := by
    have h_eq : (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_pou_supp_chart_src : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    h_pou_supp_sub_tα.trans hTα_chart_src
  have hstep := tsupport_chartSmoothExt_subset (n := n) (M := M) α (f :=
    fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) h_pou_supp_chart_src
  refine hstep.trans ?_
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h_pou_supp_sub_tα hx, rfl⟩

/-- The function `chartSmoothExt α (ρ_α · u)` vanishes outside
`Metric.ball 0 (chartRadius α / 2)`. -/
private lemma chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∉ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)) :
    chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) y = 0 := by
  by_contra hne
  apply hy
  have h_in_supp : y ∈ Function.support (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := Function.mem_support.mpr hne
  have h_in_tsupport := subset_tsupport _ h_in_supp
  exact chartCarrier_subset_half_ball (n := n) (M := M) α
    (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
      h_in_tsupport)

private lemma chartSmoothExt_morrey_sup_uniform
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          ((eLpNorm (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
           (eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (n := n) (M := M) α := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_sup_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := chartRadius (n := n) (M := M) α) hR_pos
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int y
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    have : ContDiff ℝ ∞ f := hf_smooth
    exact this
  by_cases hy_half : y ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · have hf_y_zero : f y = 0 :=
      chartSmoothExt_pou_mul_eq_zero_off_half_ball (n := n) (M := M) α u hy_half
    rw [hf_y_zero, norm_zero]
    have h_nn1 : 0 ≤ (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_nn2 : 0 ≤ (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_RHS_nn : 0 ≤ C *
        ((eLpNorm f (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
         (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
      apply mul_nonneg hC_nn
      linarith
    exact h_RHS_nn

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] in
private lemma chartSmoothExt_eq_zero_off_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 :=
  chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy

/-- For a function `h` with `tsupport h ⊆ K` and `K` closed, `fderiv h = 0`
outside `K`. -/
private lemma fderiv_eq_zero_off_tsupport_subset_closed
    {h : EuN → ℝ} {K : Set EuN} (hK_closed : IsClosed K)
    (hh_supp : tsupport h ⊆ K) {y : EuN} (hy : y ∉ K) :
    fderiv ℝ h y = 0 := by
  have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (hh_supp hyt)
  have h_compl : Kᶜ ∈ 𝓝 y := hK_closed.isOpen_compl.mem_nhds hy
  have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_compl ?_
    intro z hz
    have hz_off_tsupp : z ∉ tsupport h := fun hzt => hz (hh_supp hzt)
    exact image_eq_zero_of_notMem_tsupport hz_off_tsupp
  rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
  simp

/-- The full-space eLpNorm of `chartSmoothExt α (ρ_α · u)` equals the
eLpNorm restricted to a ball containing the carrier. -/
private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have h_eq_BR : h = BR.indicator h := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hyK (hK_supp hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q (volume.restrict BR)
      = eLpNorm (BR.indicator h) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm h q volume := by rw [← h_eq_BR]

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_supp hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]

omit [CompactSpace M] in
/-- `chartSmoothExt α (ρ_α · u)` and `chartPushed ρ α u` agree a.e. on
`volume.restrict (interiorHalfSpace (chartTargetEuclid α))`. -/
private lemma chartSmoothExt_ae_eq_chartPushed_interior
    (α : M) (u : M → ℝ) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u := by
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  refine (MeasureTheory.ae_restrict_iff' hOpen.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartSmoothExt_eq_chartPushed_on_target
    (n := n) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u hy.1

/-- The eLpNorm of `chartSmoothExt α (ρ_α · u)` on the interior part of the
chart target equals the eLpNorm of `chartPushed ρ α u` there. -/
private lemma eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) =
      eLpNorm (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) :=
  eLpNorm_congr_ae (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  have h_eq_IntΩ : h = IntΩ.indicator h := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q volume
      = eLpNorm (IntΩ.indicator h) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm h q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  have hK_closed_int : IsClosed (tsupport h) := isClosed_tsupport _
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_IntΩ : fnNorm = IntΩ.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      have h_fderiv_zero : fderiv ℝ h y = 0 := by
        have h_compl : (tsupport h)ᶜ ∈ 𝓝 y :=
          hK_closed_int.isOpen_compl.mem_nhds hy_off_tsupp
        have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
          refine Filter.eventuallyEq_of_mem h_compl ?_
          intro z hz
          exact image_eq_zero_of_notMem_tsupport hz
        rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
        simp
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q volume
      = eLpNorm (IntΩ.indicator fnNorm) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm fnNorm q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

private lemma eLpNorm_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  rw [eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (n := n) (M := M) α u q]
  set Ω : Set EuN := chartTargetEuclid (n := n) (M := M) α with hΩ_def
  have h_zero_eq : eLpNorm (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 0 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero]
  rw [h_zero_eq]
  have h_le_succ : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) 0 q
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 0 q,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q]
    rw [Finset.sum_range_one]
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    rw [show Finset.range 2 = {0, 1} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    refine le_add_of_nonneg_right ?_
    exact zero_le _
  refine h_le_succ.trans ?_
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-- `‖w‖ ≤ ∑ i, ‖w i‖` in `EuclideanSpace`. -/
private lemma euN_norm_le_sum_components_norms (w : EuN) :
    ‖w‖ ≤ ∑ i : Fin n, ‖w i‖ := by
  classical
  have h_w_sum :
      w = ∑ i : Fin n, EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

/-- `‖fderiv ℝ ψ y‖ = ‖(WithLp.toLp 2 (...components...))‖` for ψ : EuN → ℝ. -/
private lemma norm_fderiv_eq_norm_partials_local
    {ψ : EuN → ℝ} (y : EuN) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : EuN)‖ := by
  classical
  set v : EuN :=
    (InnerProductSpace.toDual ℝ EuN).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuN) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin n =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

/-- For ψ : EuN → ℝ, `‖fderiv ℝ ψ y‖ ≤ ∑ i, ‖(fderiv ℝ ψ y) (e_i)‖`. -/
private lemma norm_fderiv_le_sum_partials_local
    (ψ : EuN → ℝ) (y : EuN) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin n, ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
  rw [norm_fderiv_eq_norm_partials_local (n := n) y]
  refine (euN_norm_le_sum_components_norms _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

/-- For smooth `f` with compact support, `eLpNorm (norm fderiv f) ≤ ∑_i eLpNorm partial_i f`. -/
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuN}
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin n,
      AEStronglyMeasurable
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuN,
      ‖fderiv ℝ f z‖ ≤ ∑ i : Fin n,
        ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local f z
  have h_step1 : eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      eLpNorm (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ f z‖‖ = ‖fderiv ℝ f z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin n,
          fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

/-- The classical partial of a smooth `f`, compactly supported in open `Ω`,
agrees a.e. with `chosenWeakPartial' p i f Ω`. -/
private lemma classical_partial_ae_eq_chosenWeakPartial_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω)
    (i : Fin n) :
    (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω := by
  classical
  have hf_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := n) 1 q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := n) hΩ_open hf_smooth hf_compact hf_supp hq_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := n) q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
      (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

/-- For smooth `f` with compact support inside open `Ω`, the eLpNorm of
`‖fderiv ℝ f‖` is bounded by `n * wkpNorm 1 q f Ω`. -/
private lemma eLpNorm_norm_fderiv_le_n_mul_wkpNorm
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q (volume.restrict Ω) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    (q := q) hq_one (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin n,
      eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
        q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local
      hq_one hΩ_open hf_smooth hf_compact hf_supp i)
  have h_step1 :
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin n,
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := n) q j β f Ω)
              q (volume.restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω) q (volume.restrict Ω)) =
        ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin n,
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := n) q 1 β f Ω) q (volume.restrict Ω) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
            q (volume.restrict Ω) := by
      intro β
      have hit :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω := by
        rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
        simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin n) ≃ Fin n :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
          q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
          q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le _
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < n := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((n : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    (d := n) 1 q f Ω = 1 *
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := n) 1 q f Ω from
    (one_mul _).symm]
  gcongr

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q
          (chartSmoothExt (n := n) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x))
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) := by
  classical
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  set Ω : Set EuN := DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
    (chartTargetEuclid (n := n) (M := M) α) with hΩ_def
  have hΩ_open : IsOpen Ω :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  have hf_compact : HasCompactSupport f := by
    rw [hf_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
  have hf_supp : tsupport f ⊆ Ω := by
    rw [hf_def, hΩ_def]
    set ff : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hff_def
    have hff_supp_chart_src : tsupport ff ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport ff) ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := ff) hff_supp_chart_src (h_int α)
    have h1 : tsupport (chartSmoothExt (n := n) (M := M) α ff) ⊆
        (extChartAt I_hs α) '' (tsupport ff) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hff_supp_chart_src
    exact h1.trans hint_image
  exact eLpNorm_norm_fderiv_le_n_mul_wkpNorm hq_one hΩ_open hf_smooth_top hf_compact hf_supp

/-- The Euclidean wkpNorm of `chartSmoothExt α (ρ_α · u)` on the interior part
equals that of `chartPushed ρ α u`. -/
private lemma wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := n) 1 q
        (chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x))
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := n) hq_one
    (interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

/-- The Euclidean half-space wkpNormHalfSpace of `chartPushed ρ α u` at chart α
is bounded by `wkpNormChart u`. -/
private lemma wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-- Bound `eLpNorm fderiv chartSmoothExt q (B(0, R_α))` by `n · wkpNormChart`. -/
private lemma eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  refine (eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    (n := n) (M := M) hq_one hu h_int α).trans ?_
  rw [wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    (n := n) (M := M) hq_one α u]
  gcongr
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
    wkpNormChart (n := n) (M := M) g 1 q u
  exact wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (n := n) (M := M) g α u

private lemma per_chart_smooth_sup_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast NeZero.pos n
    have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_sup_uniform (n := n) (M := M) α hp
  refine ⟨Cmorrey * (1 + (n : ℝ)), ?_, ?_⟩
  · have hd_nn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  · intro u hu h_int y
    have hbound_y := hbound hu h_int y
    set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
    have hLp_bd := eLpNorm_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g h_int α (ENNReal.ofReal p)
    have hgrad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g hp_enn_one hu h_int α
    have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
      have h_per_α_mem : ∀ β : M,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (chartTargetEuclid (n := n) (M := M) β) := by
        intro β
        set fβ : M → ℝ := fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
            : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
        have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
          tsupport_pou_mul_subset_chart_source (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            β u
        have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) :=
          chartSmoothExtInteriorSupport_image_subset_interior
            (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
        set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
        have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
          rw [hext_β_def]
          exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            hu (h_int β)
        have hext_β_compact : HasCompactSupport ext_β := by
          rw [hext_β_def]
          exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
        have hext_β_supp : tsupport ext_β ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) := by
          have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
            rw [hext_β_def]
            exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
          exact h1.trans hint_image
        have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
          interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
        have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p) ext_β
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
            (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
        have h_ae : ext_β =ᵐ[volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β))]
            chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
          rw [hext_β_def, hfβ_def]
          exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
        have h_chartPushed_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
            (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
        exact h_chartPushed_W1p
      have h_mem_chart : MemWkpChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u :=
        h_per_α_mem
      exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_mem_chart
    have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
      hwkp_lt_top.ne
    set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
    have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
    have hLp_real : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ N := by
      apply ENNReal.toReal_mono hwkp_ne_top
      exact hLp_bd
    have hgrad_real : (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ (n : ℝ) * N := by
      have h_ne_top : ((n : ℕ) : ℝ≥0∞) *
          wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
      have h_le := ENNReal.toReal_mono h_ne_top hgrad_bd
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    have h_combined : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal ≤
      N + (n : ℝ) * N := by
      linarith
    have h_final : Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) ≤
      Cmorrey * (1 + (n : ℝ)) * N := by
      have h1 : Cmorrey * (N + (n : ℝ) * N) = Cmorrey * (1 + (n : ℝ)) * N := by ring
      calc Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
        (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal)
          ≤ Cmorrey * (N + (n : ℝ) * N) :=
            mul_le_mul_of_nonneg_left h_combined hCmorrey_nn
        _ = Cmorrey * (1 + (n : ℝ)) * N := h1
    rw [hf_def] at h_final
    exact le_trans hbound_y h_final

omit [CompactSpace M] in
/-- For `x ∈ chartAt α source`, `(ρ_α · u)(x) = chartSmoothExt α (ρ_α · u) (extChartAt I α x)`. -/
private lemma chartSmoothExt_pou_mul_apply_at_chart_image
    (α : M) (u : M → ℝ) {x : M} (hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source) :
    chartSmoothExt (n := n) (M := M) α
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y)
        (extChartAt I_hs α x) =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
  classical
  have hx_target : extChartAt I_hs α x ∈ (extChartAt I_hs α).target :=
    (extChartAt I_hs α).map_source (by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hx)
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hx_target]
  rw [(extChartAt I_hs α).left_inv (by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hx)]

/-- For each `x : M`, `‖(ρ_α · u)(x)‖` is bounded by the sup norm of
`chartSmoothExt α (ρ_α · u)`. -/
private lemma norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (α : M) (u : M → ℝ) (x : M) {Cmod : ℝ}
    (hbound : ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
      (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤ Cmod) (hCmod : 0 ≤ Cmod) :
    ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x‖ ≤ Cmod := by
  classical
  by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · have h_eq := chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx
    rw [← h_eq]
    exact hbound _
  · have hρ_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x = 0 := by
      have hsubord :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).IsSubordinate
            (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M
      have h_supp := hsubord α
      by_contra hne
      apply hx
      apply h_supp
      apply subset_tsupport
      exact Function.mem_support.mpr hne
    rw [hρ_zero, zero_mul, norm_zero]
    exact hCmod

/-- Per-chart constant from `per_chart_smooth_sup_bound`, packaged as a
function `M → ℝ`. -/
private noncomputable def perChartMorreyConst
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)

private lemma perChartMorreyConst_nn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).1

private lemma perChartMorreyConst_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (y : EuN) :
    ‖chartSmoothExt (n := n) (M := M) α
        (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤
      perChartMorreyConst (n := n) (M := M) g hp α *
        (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).2 hu h_int y

/-- **Smooth manifold-level Morrey sup bound, with-boundary case** (uniform in
`u`). For a closed Riemannian manifold-with-boundary modelled on the
canonical Euclidean half-space `EuclideanHalfSpace n` and `p > n`, there is
a constant `C ≥ 0` (depending on `g`, `p`, and the canonical chart-atlas
POU) such that for every smooth `u : M → ℝ` whose canonical-POU chart-pushed
functions all have `tsupport` strictly inside the open interior parts of
the chart targets and every `x : M`,

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`. -/
theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  refine ⟨∑ α ∈ S, perChartMorreyConst (n := n) (M := M) g hp α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α _ =>
      perChartMorreyConst_nn (n := n) (M := M) g hp α)
  intro u hu h_int x
  have h_decomp : u x = ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x := by
    have hsum : ∑ α ∈ S,
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I_hs) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_decomp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  have hC_α_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
    perChartMorreyConst_nn (n := n) (M := M) g hp α
  have hCN_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α *
      (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
    mul_nonneg hC_α_nn ENNReal.toReal_nonneg
  refine norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (n := n) (M := M) α u x ?_ hCN_nn
  intro y
  exact perChartMorreyConst_bound (n := n) (M := M) g hp α hu h_int y

private lemma chartSmoothExt_holder_uniform_half_ball
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y₁ y₂ : EuN,
          y₁ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          y₂ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          ‖chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₁ -
            chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₂‖ ≤
            C * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hd_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : 1 ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set R : ℝ := chartRadius (n := n) (M := M) α with hR_def
  have hR_pos : 0 < R := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C₀, hC₀_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_pair_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := R) hR_pos
  refine ⟨C₀ * (n : ℝ), mul_nonneg hC₀_nn (Nat.cast_nonneg _), ?_⟩
  intro u hu h_int y₁ y₂ hy₁ hy₂
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have h_pair := hbound (u := f) hf_smooth_top hy₁ hy₂
  have h_grad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (n := n) (M := M) g (q := ENNReal.ofReal p) hp_enn_one hu h_int α
  have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
    have h_per_α_mem : ∀ β : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
          (chartTargetEuclid (n := n) (M := M) β) := by
      intro β
      set fβ : M → ℝ := fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
          : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
      have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
        tsupport_pou_mul_subset_chart_source (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          β u
      have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) :=
        chartSmoothExtInteriorSupport_image_subset_interior
          (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
      set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
      have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
        rw [hext_β_def]
        exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          hu (h_int β)
      have hext_β_compact : HasCompactSupport ext_β := by
        rw [hext_β_def]
        exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
      have hext_β_supp : tsupport ext_β ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) := by
        have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
          rw [hext_β_def]
          exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
        exact h1.trans hint_image
      have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) β)) :=
        interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
      have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := n) 1 (ENNReal.ofReal p) ext_β
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
          (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
      have h_ae : ext_β =ᵐ[volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β))]
          chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
        rw [hext_β_def, hfβ_def]
        exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
      exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
        (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
    exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_per_α_mem
  have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    hwkp_lt_top.ne
  set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_d_wkp_ne_top : ((n : ℕ) : ℝ≥0∞) *
      wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
  have h_grad_real :
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) R))).toReal ≤
        (n : ℝ) * N := by
    have h_le := ENNReal.toReal_mono h_d_wkp_ne_top h_grad_bd
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    exact h_le
  have h_dist_eq : dist y₁ y₂ = ‖y₁ - y₂‖ := dist_eq_norm y₁ y₂
  have h_dist_pow_nn : 0 ≤ dist y₁ y₂ ^ (1 - (n : ℝ) / p) :=
    Real.rpow_nonneg dist_nonneg _
  calc ‖f y₁ - f y₂‖
      ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) *
          (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) R))).toReal := h_pair
    _ ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) * ((n : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_left h_grad_real
        exact mul_nonneg hC₀_nn h_dist_pow_nn
    _ = C₀ * (n : ℝ) * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) * N := by
        rw [h_dist_eq]; ring

/-- For `x ∈ tsupport ρ_α`, `extChartAt I α x ∈ Metric.ball 0 (R_α / 2)`. -/
private lemma extChartAt_mem_half_ball_of_mem_tsupport_pou
    (α : M) {x : M}
    (hx : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)) :
    extChartAt I_hs α x ∈
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  classical
  have h_in : extChartAt I_hs α x ∈ chartCarrier (n := n) (M := M) α :=
    ⟨x, hx, rfl⟩
  exact chartCarrier_subset_half_ball (n := n) (M := M) α h_in

/-- **Per-chart smooth Hölder modulus on the partition-of-unity-localized
function (with-boundary)**. For each chart `α`, smooth `u : M → ℝ` with
all-charts strict-interior support, and `p > n`, the canonical-POU
localised function `(ρ_α · u)` satisfies a Hölder modulus on the compact
`tsupport ρ_α`:

  `‖(ρ_α x · u x) - (ρ_α y · u y)‖ ≤
      C_α · ‖extChartAt I α x - extChartAt I α y‖^(1 - n/p) ·
        (wkpNormChart g 1 p u).toReal`,

uniformly in `u`. -/
private lemma pou_mul_holder_chart_uniform_tsupport
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
        ∀ y ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    chartSmoothExt_holder_uniform_half_ball (n := n) (M := M) g α hp
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int x hx y hy
  have h_subord :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hx_src : x ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hx
  have hy_src : y ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hy
  set y₁ : EuN := extChartAt I_hs α x with hy₁_def
  set y₂ : EuN := extChartAt I_hs α y with hy₂_def
  have hy₁_R2 : y₁ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hx
  have hy₂_R2 : y₂ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hy
  have h_pair := hbound hu h_int y₁ y₂ hy₁_R2 hy₂_R2
  have h_eq_x :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₁ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
    rw [hy₁_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx_src
  have h_eq_y :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₂ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y := by
    rw [hy₂_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hy_src
  rw [h_eq_x, h_eq_y] at h_pair
  exact h_pair

/-- **Smooth manifold-level Hölder modulus on the canonical POU localization,
per chart, with-boundary**. For a closed Riemannian manifold-with-boundary
modelled on `EuclideanHalfSpace n` and `p > n`, for each chart `α : M`,
there exists a compact `K_α ⊆ chart α source` and a constant `C_α ≥ 0`
(depending on `g`, `p`, the canonical POU and the chart `α`, but **not**
on `u`) such that for every smooth `u : M → ℝ` whose canonical-POU
chart-pushed functions all have strict-interior support and every
`x, y ∈ K_α`, the canonical chart-atlas POU localization `(ρ_α · u)`
satisfies the chart-α Hölder modulus

  `‖(ρ_α x · u x) - (ρ_α y · u y)‖ ≤
      C_α · ‖extChartAt I α x - extChartAt I α y‖^(1 - n/p) ·
        (wkpNormChart g 1 p u).toReal`,

with the compact set `K_α := tsupport ρ_α`. -/
theorem smooth_manifold_morrey_holder_modulus_per_chart_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ (chartAt (EuclideanHalfSpace n) α).source ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ K, ∀ y ∈ K,
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  refine ⟨Tα, (isClosed_tsupport _).isCompact, ?_, ?_⟩
  · exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  · obtain ⟨C, hC_nn, hbound⟩ :=
      pou_mul_holder_chart_uniform_tsupport (n := n) (M := M) g α hp
    exact ⟨C, hC_nn, fun {u} hu h_int x hx y hy => hbound hu h_int x hx y hy⟩

/-- The triangle decomposition: `‖u(x) - u(y)‖ ≤ ∑_α ‖(ρ_α x · u x) -
(ρ_α y · u y)‖`, with the sum over the canonical chart-atlas POU finset `S`. -/
theorem norm_sub_le_sum_pou_diff_withBoundary
    (u : M → ℝ) (x y : M) :
    ‖u x - u y‖ ≤
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I_hs) (M := M),
        ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  have hsum_x : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) x
  have hsum_y : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) y
  have h_diff_eq : u x - u y =
      ∑ α ∈ S,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hsum_x, hsum_y, one_mul, one_mul]
  rw [h_diff_eq]
  exact norm_sum_le (E := ℝ) S (fun α =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y)

/-- **The even-reflection point map.** For `y ∈ EuclideanSpace ℝ (Fin n)`,
return the point in the closed half-space whose `0`-th coordinate is `|y 0|`
and whose other coordinates match `y`. -/
def evenReflectFun (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    (WithLp.toLp 2 (fun j : Fin n => if j = 0 then |y 0| else y j) :
      EuclideanSpace ℝ (Fin n))

/-- The reflection map sets the `0`-th coordinate to `|y 0|`. -/
lemma evenReflectFun_apply_zero {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n y 0 = |y 0| := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then |y 0| else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) 0 = |y 0|
  rw [PiLp.toLp_apply]
  simp

/-- The reflection map preserves coordinates other than `0`. -/
lemma evenReflectFun_apply_ne {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) (hj : j ≠ 0) :
    evenReflectFun n y j = y j := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then |y 0| else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j = y j
  rw [PiLp.toLp_apply]
  simp [if_neg hj]

/-- The reflection of any point lies in the closed half-space. -/
lemma evenReflectFun_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n y ∈
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  change (0 : ℝ) ≤ evenReflectFun n y 0
  rw [evenReflectFun_apply_zero]
  exact abs_nonneg _

/-- For points already in the closed half-space, the reflection map is the
identity. -/
lemma evenReflectFun_eq_self_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    evenReflectFun n y = y := by
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [evenReflectFun_apply_zero]
    have : (0 : ℝ) ≤ y 0 := hy
    exact abs_of_nonneg this
  · exact evenReflectFun_apply_ne y j hj

/-- The reflection map is idempotent: applying it twice has no effect. -/
lemma evenReflectFun_idempotent {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n (evenReflectFun n y) = evenReflectFun n y := by
  exact evenReflectFun_eq_self_of_mem_closedHalfSpace
    (evenReflectFun_mem_closedHalfSpace y)

/-- The reflection map sends all of `EuN` into the closed half-space. -/
lemma evenReflectFun_image_univ_subset_closedHalfSpace {n : ℕ} [NeZero n] :
    Set.range (evenReflectFun n) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  rintro y ⟨z, rfl⟩
  exact evenReflectFun_mem_closedHalfSpace z

/-- The image of the closed half-space under the reflection map equals the
closed half-space. -/
lemma evenReflectFun_image_closedHalfSpace_eq {n : ℕ} [NeZero n] :
    evenReflectFun n ''
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, _, rfl⟩
    exact evenReflectFun_mem_closedHalfSpace z
  · intro hy
    refine ⟨y, hy, ?_⟩
    exact evenReflectFun_eq_self_of_mem_closedHalfSpace hy

/-- The reflection map is continuous. -/
lemma continuous_evenReflectFun {n : ℕ} [NeZero n] :
    Continuous (evenReflectFun n) := by
  classical
  have h_cont_components : ∀ j : Fin n, Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        if j = 0 then |y 0| else y j) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      have h_proj : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => y 0) :=
        PiLp.continuous_apply 2 _ 0
      exact (continuous_abs.comp h_proj).congr (fun y => by simp)
    · have h_proj : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => y j) :=
        PiLp.continuous_apply 2 _ j
      exact h_proj.congr (fun y => by simp [hj])
  have h_pi_cont : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        fun j : Fin n => if j = 0 then |y 0| else y j) :=
    continuous_pi h_cont_components
  have hWithLp : Continuous
      (fun g : Fin n → ℝ => (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))) := by
    have h_lin_eq : (fun g : Fin n → ℝ =>
          (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))) =
        ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm :
          (Fin n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n))) := by
      funext g; rfl
    rw [h_lin_eq]
    exact LinearMap.continuous_of_finiteDimensional _
  exact hWithLp.comp h_pi_cont

/-- The reflection map is measurable. -/
lemma measurable_evenReflectFun {n : ℕ} [NeZero n] :
    Measurable (evenReflectFun n) :=
  (continuous_evenReflectFun (n := n)).measurable

/-- **The even reflection of a scalar function** `f : EuN → ℝ`. Defined by
`evenReflect n f y := f (evenReflectFun n y)`. -/
def evenReflect (n : ℕ) [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => f (evenReflectFun n y)

/-- On the closed half-space, the even reflection equals the original function. -/
lemma evenReflect_eq_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    evenReflect n f y = f y := by
  unfold evenReflect
  rw [evenReflectFun_eq_self_of_mem_closedHalfSpace hy]

/-- The even reflection is continuous when the original function is continuous. -/
lemma continuous_evenReflect {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) :
    Continuous (evenReflect n f) := by
  unfold evenReflect
  exact hf.comp (continuous_evenReflectFun (n := n))

/-- The even reflection is measurable when the original is measurable. -/
lemma measurable_evenReflect {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    Measurable (evenReflect n f) := by
  unfold evenReflect
  exact hf.comp (continuous_evenReflectFun (n := n)).measurable

lemma evenReflect_eq_on_inter_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {S : Set (EuclideanSpace ℝ (Fin n))} :
    ∀ y ∈ S ∩ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
      evenReflect n f y = f y := by
  intro y hy
  exact evenReflect_eq_of_mem_closedHalfSpace f hy.2

/-- Norm identity for the reflection. -/
lemma norm_evenReflect_eq {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflect n f y‖ = ‖f (evenReflectFun n y)‖ := rfl

/-- On the closed half-space, `‖evenReflect n f y‖ = ‖f y‖`. -/
lemma norm_evenReflect_eq_norm_self_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    ‖evenReflect n f y‖ = ‖f y‖ := by
  rw [evenReflect_eq_of_mem_closedHalfSpace f hy]

/-- The reflection of a function with bounded sup is bounded by the same sup
(on the closed half-space side; off it the values are images of half-space
points so still bounded). -/
lemma norm_evenReflect_le_sup_norm_on_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : ℝ}
    (hfC : ∀ z ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
      ‖f z‖ ≤ C) :
    ∀ y : EuclideanSpace ℝ (Fin n), ‖evenReflect n f y‖ ≤ C := by
  intro y
  rw [norm_evenReflect_eq]
  exact hfC _ (evenReflectFun_mem_closedHalfSpace y)

/-- The support of the even reflection is contained in the preimage under
`evenReflectFun n` of the support of the original function. -/
lemma support_evenReflect_subset {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.support (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' Function.support f := by
  intro y hy
  exact hy

/-- If `f` has compact support, then `evenReflect n f`'s support is contained
in the preimage of `support f` under the continuous reflection map. The
preimage is closed in `EuN`. -/
lemma tsupport_evenReflect_subset {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f := by
  classical
  have h_supp : Function.support (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' Function.support f := support_evenReflect_subset f
  have h_supp_le_tsupp : evenReflectFun n ⁻¹' Function.support f ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    fun y hy => Set.preimage_mono (subset_tsupport _) hy
  refine Set.Subset.trans (closure_mono (h_supp.trans h_supp_le_tsupp)) ?_
  exact (isClosed_tsupport _).preimage continuous_evenReflectFun |>.closure_subset

/-- Composing `evenReflectFun n` after `evenReflectFun n` agrees with
`evenReflectFun n` itself (the reflection is idempotent), so in particular
the reflection equals its own composition with itself. -/
lemma evenReflectFun_comp_self {n : ℕ} [NeZero n] :
    evenReflectFun n ∘ evenReflectFun n = evenReflectFun n := by
  funext y
  exact evenReflectFun_idempotent y

/-- **The sign-flip on the `0`-th coordinate.** Negates `y 0`, leaves all other
coordinates unchanged. This is a linear isometry self-equivalence of
`EuclideanSpace ℝ (Fin n)`. -/
def signFlipFun (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    (WithLp.toLp 2 (fun j : Fin n => if j = 0 then -y 0 else y j) :
      EuclideanSpace ℝ (Fin n))

@[simp] lemma signFlipFun_apply_zero {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipFun n y 0 = -y 0 := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then -y 0 else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) 0 = -y 0
  rw [PiLp.toLp_apply]
  simp

@[simp] lemma signFlipFun_apply_ne {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) (hj : j ≠ 0) :
    signFlipFun n y j = y j := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then -y 0 else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j = y j
  rw [PiLp.toLp_apply]
  simp [if_neg hj]

/-- The sign-flip is its own inverse. -/
@[simp] lemma signFlipFun_signFlipFun {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipFun n (signFlipFun n y) = y := by
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj; simp
  · simp [signFlipFun_apply_ne _ _ hj]

/-- The sign-flip as a linear endomorphism of `EuclideanSpace ℝ (Fin n)`. -/
def signFlipLinear (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := signFlipFun n
  map_add' x y := by
    classical
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [signFlipFun_apply_zero]
      ring
    · simp [signFlipFun_apply_ne _ _ hj]
  map_smul' c x := by
    classical
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [signFlipFun_apply_zero]
    · simp [signFlipFun_apply_ne _ _ hj]

@[simp] lemma signFlipLinear_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipLinear n y = signFlipFun n y := rfl

/-- The sign-flip preserves the Euclidean norm. -/
lemma norm_signFlipFun {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖signFlipFun n y‖ = ‖y‖ := by
  classical
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · subst hj
    change ‖signFlipFun n y 0‖ ^ 2 = ‖y 0‖ ^ 2
    rw [signFlipFun_apply_zero]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_neg]
  · change ‖signFlipFun n y j‖ ^ 2 = ‖y j‖ ^ 2
    rw [signFlipFun_apply_ne _ _ hj]

/-- The sign-flip is a linear isometry equivalence. -/
def signFlipLIE (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv :=
    { toFun := signFlipFun n
      map_add' := (signFlipLinear n).map_add'
      map_smul' := (signFlipLinear n).map_smul'
      invFun := signFlipFun n
      left_inv := signFlipFun_signFlipFun
      right_inv := signFlipFun_signFlipFun }
  norm_map' := norm_signFlipFun

@[simp] lemma signFlipLIE_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipLIE n y = signFlipFun n y := rfl

@[simp] lemma signFlipLIE_symm_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    (signFlipLIE n).symm y = signFlipFun n y := rfl

/-- The sign-flip is continuous. -/
lemma continuous_signFlipFun {n : ℕ} [NeZero n] :
    Continuous (signFlipFun n) :=
  (signFlipLIE n).toContinuousLinearEquiv.continuous

/-- The sign-flip is measurable. -/
lemma measurable_signFlipFun {n : ℕ} [NeZero n] :
    Measurable (signFlipFun n) :=
  (continuous_signFlipFun (n := n)).measurable

/-- The sign-flip preserves the Lebesgue volume. -/
lemma measurePreserving_signFlipFun {n : ℕ} [NeZero n] :
    MeasurePreserving (signFlipFun n)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have h := (signFlipLIE n).measurePreserving
  exact h

/-- The sign-flip swaps the open upper and open lower half-spaces. -/
lemma signFlipFun_image_openHalfSpace_eq {n : ℕ} [NeZero n] :
    signFlipFun n ''
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace =
      {y : EuclideanSpace ℝ (Fin n) | y 0 < 0} := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    change signFlipFun n z 0 < 0
    rw [signFlipFun_apply_zero]
    have : (0 : ℝ) < z 0 := hz
    linarith
  · intro hy
    refine ⟨signFlipFun n y, ?_, signFlipFun_signFlipFun y⟩
    change (0 : ℝ) < signFlipFun n y 0
    rw [signFlipFun_apply_zero]
    have : y 0 < 0 := hy
    linarith

/-- For `y` in the open lower half-space, the even reflection equals `f` of the
sign-flip of `y`. -/
lemma evenReflect_eq_comp_signFlip_of_lower {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0) :
    evenReflect n f y = f (signFlipFun n y) := by
  unfold evenReflect
  congr 1
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
    exact abs_of_neg hy
  · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]

/-- For `y` in the closed upper half-space, the even reflection equals `f`. -/
lemma evenReflect_eq_self_of_upper {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    evenReflect n f y = f y :=
  evenReflect_eq_of_mem_closedHalfSpace f hy

/-- **Auxiliary smoothness via composition.** When `f` is smooth on `E` and `y`
is in the open lower half-space, the even reflection equals `f ∘ signFlipFun n`
near `y`, and is smooth there. Stated as a local Continuity result for use in
the global continuity & L^p arguments. -/
lemma continuous_evenReflect_of_continuous {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) :
    Continuous (evenReflect n f) :=
  continuous_evenReflect (n := n) hf

/-- **L^p membership of the even reflection.** When `f` is smooth and has
compact support, the even reflection is also continuous with compact support
contained in the preimage of the support under the reflection map. Hence it
is in `L^p` for any `p`. -/
theorem memLp_evenReflect_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) :
    MemLp (evenReflect n f) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have h_cont : Continuous (evenReflect n f) :=
    continuous_evenReflect (n := n) hf.continuous
  have h_supp_sub : tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    tsupport_evenReflect_subset (n := n) f
  have h_supp_compact :
      HasCompactSupport (evenReflect n f) := by
    apply IsCompact.of_isClosed_subset
      (((hf_supp.image continuous_signFlipFun).union hf_supp))
      (isClosed_tsupport _)
    intro y hy
    have h1 : y ∈ evenReflectFun n ⁻¹' tsupport f := h_supp_sub hy
    rcases le_or_gt 0 (y 0) with hupper | hlower
    · right
      have : evenReflectFun n y = y :=
        evenReflectFun_eq_self_of_mem_closedHalfSpace
          (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
      rw [Set.mem_preimage, this] at h1
      exact h1
    · left
      have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
          exact abs_of_neg hlower
        · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
      rw [Set.mem_preimage, h_eq_sf] at h1
      refine ⟨signFlipFun n y, h1, ?_⟩
      exact signFlipFun_signFlipFun y
  exact h_cont.memLp_of_hasCompactSupport h_supp_compact

/-- The componentwise gradient of `f` at `y`, returning a Euclidean vector. -/
private noncomputable def fderivVec
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => (fderiv ℝ f y) (EuclideanSpace.single i 1))

@[simp] lemma fderivVec_apply
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderivVec f y i = (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
  unfold fderivVec
  rw [PiLp.toLp_apply]

/-- **The even-reflection gradient field.** On the upper half: classical
gradient of `f`. On the lower half: classical gradient of `f` at the reflected
point, with the `0`-th component negated. Defined to agree with the upper-half
formula on the boundary `{y_0 = 0}`. -/
noncomputable def evenReflectGrad (n : ℕ) [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    if 0 ≤ y 0 then
      fderivVec f y
    else
      WithLp.toLp 2 (fun i : Fin n =>
        if i = 0 then -(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)
        else (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1))

lemma evenReflectGrad_apply_upper
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    evenReflectGrad n f y = fderivVec f y := by
  unfold evenReflectGrad
  rw [if_pos hy]

lemma evenReflectGrad_apply_lower_component_zero
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0) :
    evenReflectGrad n f y 0 = -(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1) := by
  classical
  unfold evenReflectGrad
  rw [if_neg (not_le.mpr hy)]
  rw [PiLp.toLp_apply]
  simp

lemma evenReflectGrad_apply_lower_component_ne
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0)
    {i : Fin n} (hi : i ≠ 0) :
    evenReflectGrad n f y i = (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1) := by
  classical
  unfold evenReflectGrad
  rw [if_neg (not_le.mpr hy)]
  rw [PiLp.toLp_apply]
  simp [if_neg hi]

/-- For `y` in the upper half (i.e. `0 ≤ y 0`), each component of
`evenReflectGrad` is the corresponding partial derivative of `f`. -/
lemma evenReflectGrad_apply_component_upper
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) (i : Fin n) :
    evenReflectGrad n f y i = (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
  rw [evenReflectGrad_apply_upper f hy, fderivVec_apply]

/-- For `i ≠ 0`, the `i`-th component of `evenReflectGrad n f` equals
`(fderiv ℝ f) (evenReflectFun n y)` applied to `EuclideanSpace.single i 1` —
because the formulas on the upper and lower halves agree there. -/
lemma evenReflectGrad_apply_component_eq_compReflect_of_ne_zero
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {i : Fin n} (hi : i ≠ 0) (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectGrad n f y i =
      (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1) := by
  classical
  have h_evRefl_lower : ∀ {z : EuclideanSpace ℝ (Fin n)},
      z 0 < 0 → evenReflectFun n z = signFlipFun n z := fun {z} hz => by
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
      exact abs_of_neg hz
    · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
  rcases lt_or_ge (y 0) 0 with hlt | hge
  · rw [evenReflectGrad_apply_lower_component_ne f hlt hi]
    rw [h_evRefl_lower hlt]
  · rw [evenReflectGrad_apply_component_upper f hge i]
    rw [evenReflectFun_eq_self_of_mem_closedHalfSpace hge]

/-- For `i ≠ 0`, the `i`-th component of `evenReflectGrad n f` is continuous
when `f` is smooth. -/
theorem continuous_evenReflectGrad_component_of_contDiff_ne_zero
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {i : Fin n} (hi : i ≠ 0) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) := by
  classical
  have hderiv_cont : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have h_eq : (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) =
      fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1) := by
    funext y
    exact evenReflectGrad_apply_component_eq_compReflect_of_ne_zero f hi y
  rw [h_eq]
  exact hderiv_cont.comp continuous_evenReflectFun

/-- The `0`-th component of `evenReflectGrad n f` equals
`(Real.sign (y 0)) * (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single 0 1)`
**off the boundary hyperplane** `{y : y 0 = 0}`. On the boundary itself the
formula gives the upper-half value `(fderiv ℝ f y) (EuclideanSpace.single 0 1)`,
which need not be zero — so the component is not continuous in general at
`y_0 = 0`. However, the boundary hyperplane has Lebesgue measure zero, so the
component agrees a.e. with a continuous function. -/
lemma evenReflectGrad_apply_zero_off_boundary
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 ≠ 0) :
    evenReflectGrad n f y 0 =
      (Real.sign (y 0)) *
        (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single 0 1) := by
  classical
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · rw [evenReflectGrad_apply_lower_component_zero f hlt]
    rw [Real.sign_of_neg hlt]
    have h_evRefl : evenReflectFun n y = signFlipFun n y := by
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlt
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [h_evRefl]
    ring
  · have h_le : (0 : ℝ) ≤ y 0 := le_of_lt hgt
    rw [evenReflectGrad_apply_component_upper f h_le 0]
    have h_evRefl : evenReflectFun n y = y := by
      apply evenReflectFun_eq_self_of_mem_closedHalfSpace h_le
    rw [h_evRefl]
    rw [Real.sign_of_pos hgt]
    ring

/-- The `0`-th component of `evenReflectGrad n f` is bounded pointwise by
`‖fderiv ℝ f (evenReflectFun n y)‖`. -/
lemma norm_evenReflectGrad_apply_zero_le
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflectGrad n f y 0‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ := by
  classical
  rcases lt_or_ge (y 0) 0 with hlt | hge
  · rw [evenReflectGrad_apply_lower_component_zero f hlt]
    have h_evRefl : evenReflectFun n y = signFlipFun n y := by
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlt
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [h_evRefl]
    rw [norm_neg]
    have h_op : ‖(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)‖ ≤
        ‖fderiv ℝ f (signFlipFun n y)‖ * ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ = 1 := by
      simp
    rw [h_unit, mul_one] at h_op
    exact h_op
  · rw [evenReflectGrad_apply_component_upper f hge 0]
    have h_evRefl : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace hge
    rw [h_evRefl]
    have h_op : ‖(fderiv ℝ f y) (EuclideanSpace.single 0 1)‖ ≤
        ‖fderiv ℝ f y‖ * ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ = 1 := by simp
    rw [h_unit, mul_one] at h_op
    exact h_op

/-- For any `i`, the `i`-th component of `evenReflectGrad n f` is bounded
pointwise by `‖fderiv ℝ f (evenReflectFun n y)‖`. -/
lemma norm_evenReflectGrad_apply_le
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖evenReflectGrad n f y i‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ := by
  classical
  by_cases hi : i = 0
  · subst hi
    exact norm_evenReflectGrad_apply_zero_le f y
  · rw [evenReflectGrad_apply_component_eq_compReflect_of_ne_zero f hi y]
    have h_op : ‖(fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1)‖ ≤
        ‖fderiv ℝ f (evenReflectFun n y)‖ * ‖(EuclideanSpace.single i (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
    rw [h_unit, mul_one] at h_op
    exact h_op

/-- The closed half-space `{y : E | 0 ≤ y 0}` is closed, hence measurable. -/
lemma measurableSet_closedHalfSpace_aux {n : ℕ} [NeZero n] :
    MeasurableSet
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
        (d := n)) := by
  classical
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => y 0) :=
    PiLp.continuous_apply 2 _ 0
  have heq : DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
      (d := n) = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' Set.Ici 0 := rfl
  rw [heq]
  exact hcont.measurable measurableSet_Ici

/-- The `i`-th component of `evenReflectGrad n f` is `AEStronglyMeasurable`
when `f` is smooth, on Lebesgue volume. The `i = 0` case uses the fact that
the discontinuity at `y 0 = 0` lives on a Lebesgue-null hyperplane. -/
theorem aestronglyMeasurable_evenReflectGrad_component_of_contDiff
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n) :
    AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hderiv_cont : ∀ j : Fin n, Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single j 1)) := fun j =>
    (hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  by_cases hi : i = 0
  · subst hi
    have h_uppercont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single 0 1)) := hderiv_cont 0
    have h_lowercont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1))) :=
      ((hderiv_cont 0).comp continuous_signFlipFun).neg
    have h_eq : (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y 0) =
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
          (d := n)).piecewise
          (fun y => (fderiv ℝ f y) (EuclideanSpace.single 0 1))
          (fun y => -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1))) := by
      funext y
      classical
      by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
        (d := n)
      · rw [Set.piecewise_eq_of_mem _ _ _ hy]
        rw [evenReflectGrad_apply_component_upper f hy 0]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
        have hlt : y 0 < 0 := lt_of_not_ge (fun h => hy h)
        rw [evenReflectGrad_apply_lower_component_zero f hlt]
    rw [h_eq]
    refine AEStronglyMeasurable.piecewise (μ := volume)
      measurableSet_closedHalfSpace_aux ?_ ?_
    · exact h_uppercont.aestronglyMeasurable.restrict
    · exact h_lowercont.aestronglyMeasurable.restrict
  · exact (continuous_evenReflectGrad_component_of_contDiff_ne_zero hf hi).aestronglyMeasurable

/-- The map `y ↦ ‖fderiv ℝ f (evenReflectFun n y)‖` is continuous when `f` is
smooth. -/
lemma continuous_norm_fderiv_compReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f (evenReflectFun n y)‖) := by
  have h_cont_fderiv : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  exact (h_cont_fderiv.comp continuous_evenReflectFun).norm

/-- The map `y ↦ ‖fderiv ℝ f (evenReflectFun n y)‖` has compact support when
`f` has compact support. The support is contained in
`evenReflectFun n ⁻¹' tsupport f`. -/
lemma hasCompactSupport_norm_fderiv_compReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) :
    HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f (evenReflectFun n y)‖) := by
  classical
  have h_fderiv_supp : HasCompactSupport (fderiv ℝ f) :=
    hf_supp.fderiv ℝ
  have h_compact_union :
      IsCompact (signFlipFun n '' tsupport f ∪ tsupport f) :=
    (hf_supp.image continuous_signFlipFun).union hf_supp
  apply IsCompact.of_isClosed_subset h_compact_union
    (isClosed_tsupport _)
  intro y hy
  have h_supp_pre : Function.support
      (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆
      evenReflectFun n ⁻¹' Function.support (fderiv ℝ f) := by
    intro z hz
    simp only [Function.mem_support, ne_eq, norm_eq_zero] at hz
    exact hz
  have h_pre_subset_t : evenReflectFun n ⁻¹' Function.support (fderiv ℝ f) ⊆
      evenReflectFun n ⁻¹' tsupport (fderiv ℝ f) :=
    Set.preimage_mono (subset_tsupport _)
  have h_pre_subset_t_f : evenReflectFun n ⁻¹' tsupport (fderiv ℝ f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    Set.preimage_mono (tsupport_fderiv_subset (𝕜 := ℝ))
  have h_closed : IsClosed (evenReflectFun n ⁻¹' tsupport f) :=
    (isClosed_tsupport _).preimage continuous_evenReflectFun
  have h_y_in : y ∈ evenReflectFun n ⁻¹' tsupport f := by
    have h_subset : tsupport (fun y : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆ evenReflectFun n ⁻¹' tsupport f := by
      have h1 : Function.support
          (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆
          evenReflectFun n ⁻¹' tsupport f :=
        h_supp_pre.trans (h_pre_subset_t.trans h_pre_subset_t_f)
      exact h_closed.closure_subset_iff.mpr h1
    exact h_subset hy
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · right
    have h_eq_self : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace
        (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
    rw [Set.mem_preimage, h_eq_self] at h_y_in
    exact h_y_in
  · left
    have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
      classical
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlower
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [Set.mem_preimage, h_eq_sf] at h_y_in
    refine ⟨signFlipFun n y, h_y_in, ?_⟩
    exact signFlipFun_signFlipFun y

/-- For each `i : Fin n`, the `i`-th component of `evenReflectGrad n f` is in
`L^p(volume)` when `f` is smooth with compact support. -/
theorem memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) (i : Fin n) :
    MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have h_aesm : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aestronglyMeasurable_evenReflectGrad_component_of_contDiff hf i
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ‖fderiv ℝ f (evenReflectFun n y)‖ with hg_def
  have h_g_cont : Continuous g := continuous_norm_fderiv_compReflect hf
  have h_g_supp : HasCompactSupport g :=
    hasCompactSupport_norm_fderiv_compReflect hf hf_supp
  have h_g_memLp : MemLp g p (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    h_g_cont.memLp_of_hasCompactSupport h_g_supp
  refine MemLp.of_le_mul (g := g) (c := 1) h_g_memLp h_aesm ?_
  filter_upwards
  intro y
  rw [one_mul]
  have h1 : ‖evenReflectGrad n f y i‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ :=
    norm_evenReflectGrad_apply_le f y i
  have h2 : ‖fderiv ℝ f (evenReflectFun n y)‖ ≤ ‖g y‖ := by
    rw [hg_def]
    exact Real.le_norm_self _
  exact h1.trans h2

/-- The gradient field `evenReflectGrad n f` is in `MemLp p volume` when `f`
is smooth with compact support. -/
theorem memLp_evenReflectGrad_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MemLp (evenReflectGrad n f) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply MemLp.of_eval_piLp
  intro i
  exact memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf hf_supp p i

/-- **Smoothness of `signFlipFun n`.** The sign-flip is a continuous linear
self-equivalence of `EuclideanSpace ℝ (Fin n)`, hence smooth. -/
lemma contDiff_signFlipFun {n : ℕ} [NeZero n] {k : WithTop ℕ∞} :
    ContDiff ℝ k (signFlipFun n) :=
  (signFlipLIE n).toContinuousLinearEquiv.contDiff

/-- **Smoothness of `f ∘ signFlipFun n`** when `f` is smooth. -/
lemma contDiff_comp_signFlipFun {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin n) => f (signFlipFun n y)) :=
  hf.comp contDiff_signFlipFun

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection
agrees pointwise with `f + f ∘ signFlipFun n`. -/
lemma evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace) :
    evenReflect n f =
      fun y : EuclideanSpace ℝ (Fin n) => f y + f (signFlipFun n y) := by
  funext y
  classical
  rcases lt_trichotomy (y 0) 0 with hlt | heq | hgt
  · have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_y_zero : f y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_supp
    rw [evenReflect_eq_comp_signFlip_of_lower f hlt]
    rw [h_y_zero, zero_add]
  · have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_y_zero : f y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_supp
    have h_sfy_zero : f (signFlipFun n y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hin
      have : signFlipFun n y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      have : (0 : ℝ) < -y 0 := hopen
      linarith
    have h_y_in_closed :
        y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
      le_of_eq heq.symm
    rw [evenReflect_eq_self_of_upper f h_y_in_closed]
    rw [h_y_zero, h_sfy_zero, add_zero]
  · have h_y_in_closed :
        y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
      le_of_lt hgt
    rw [evenReflect_eq_self_of_upper f h_y_in_closed]
    have h_sfy_not_supp : signFlipFun n y ∉ tsupport f := by
      intro hin
      have : signFlipFun n y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      have : (0 : ℝ) < -y 0 := hopen
      linarith
    have h_sfy_zero : f (signFlipFun n y) = 0 :=
      image_eq_zero_of_notMem_tsupport h_sfy_not_supp
    rw [h_sfy_zero, add_zero]

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection is
`C^∞` on all of `E`. -/
theorem contDiff_evenReflect_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n] {k : WithTop ℕ∞}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ k f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace) :
    ContDiff ℝ k (evenReflect n f) := by
  rw [evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace hf_supp]
  exact hf.add (contDiff_comp_signFlipFun hf)

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection has
compact support contained in `tsupport f ∪ signFlipFun n '' tsupport f`. -/
theorem hasCompactSupport_evenReflect_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp_compact : HasCompactSupport f) :
    HasCompactSupport (evenReflect n f) := by
  classical
  have h_compact_union :
      IsCompact (signFlipFun n '' tsupport f ∪ tsupport f) :=
    (hf_supp_compact.image continuous_signFlipFun).union hf_supp_compact
  apply IsCompact.of_isClosed_subset h_compact_union
    (isClosed_tsupport _)
  have h_supp_sub : tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    tsupport_evenReflect_subset (n := n) f
  intro y hy
  have h1 : y ∈ evenReflectFun n ⁻¹' tsupport f := h_supp_sub hy
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · right
    have h_eq_self : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace
        (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
    rw [Set.mem_preimage, h_eq_self] at h1
    exact h1
  · left
    have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
      classical
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlower
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [Set.mem_preimage, h_eq_sf] at h1
    refine ⟨signFlipFun n y, h1, ?_⟩
    exact signFlipFun_signFlipFun y

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the partial derivative
in coordinate `i` of `evenReflect n f` matches the `i`-th component of
`evenReflectGrad n f`. -/
theorem fderiv_evenReflect_apply_single_eq_evenReflectGrad
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1) =
      evenReflectGrad n f y i := by
  classical
  have h_eq : evenReflect n f =
      fun z : EuclideanSpace ℝ (Fin n) => f z + f (signFlipFun n z) :=
    evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace hf_supp
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) :=
    contDiff_comp_signFlipFun hf
  have hg_diff : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) :=
    hg.differentiable (by simp)
  rw [h_eq]
  rw [fderiv_fun_add hf_diff.differentiableAt hg_diff.differentiableAt]
  rw [ContinuousLinearMap.add_apply]
  set iso : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (signFlipLIE n).toContinuousLinearEquiv with hiso_def
  have h_iso_apply : ∀ z, (iso : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z = signFlipFun n z := by
    intro z; rfl
  have h_fderiv_comp_eq : (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z))
      = f ∘ iso := by
    funext z
    simp [h_iso_apply]
  have h_fderiv_comp : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) y =
      (fderiv ℝ f (signFlipFun n y)).comp
        (iso : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [h_fderiv_comp_eq]
    have h := iso.comp_right_fderiv (f := f) (x := y)
    rw [h_iso_apply] at h
    exact h
  rw [h_fderiv_comp]
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have h_clm_eval :
      (iso : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single i 1) = signFlipFun n (EuclideanSpace.single i 1) :=
    h_iso_apply _
  rw [h_clm_eval]
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · have h_sfy_not_supp : signFlipFun n y ∉ tsupport f := by
      intro hin
      have : signFlipFun n y ∈
          DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      linarith
    have h_fderiv_sfy_zero : fderiv ℝ f (signFlipFun n y) = 0 := by
      have h_eventually : ∀ᶠ z in nhds (signFlipFun n y), f z = 0 := by
        rw [eventually_iff_exists_mem]
        exact ⟨(tsupport f)ᶜ,
          (isClosed_tsupport f).isOpen_compl.mem_nhds h_sfy_not_supp,
          fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
      have h_filt_eq : f =ᶠ[nhds (signFlipFun n y)] 0 := h_eventually
      rw [Filter.EventuallyEq.fderiv_eq h_filt_eq]
      simp
    rw [h_fderiv_sfy_zero, ContinuousLinearMap.zero_apply, add_zero]
    rw [evenReflectGrad_apply_component_upper f hupper i]
  · have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_fderiv_y_zero : fderiv ℝ f y = 0 := by
      have h_eventually : ∀ᶠ z in nhds y, f z = 0 := by
        rw [eventually_iff_exists_mem]
        exact ⟨(tsupport f)ᶜ,
          (isClosed_tsupport f).isOpen_compl.mem_nhds h_y_not_supp,
          fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
      have h_filt_eq : f =ᶠ[nhds y] 0 := h_eventually
      rw [Filter.EventuallyEq.fderiv_eq h_filt_eq]
      simp
    rw [h_fderiv_y_zero, ContinuousLinearMap.zero_apply, zero_add]
    by_cases hi : i = 0
    · subst hi
      rw [evenReflectGrad_apply_lower_component_zero f hlower]
      have h_sf_eval : signFlipFun n (EuclideanSpace.single 0 (1 : ℝ)) =
          -EuclideanSpace.single 0 (1 : ℝ) := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [signFlipFun_apply_zero]
          rw [PiLp.neg_apply]
        · rw [signFlipFun_apply_ne _ _ hj]
          have h_single_zero : (EuclideanSpace.single 0 (1 : ℝ)) j = 0 := by
            rw [show EuclideanSpace.single 0 (1 : ℝ) = PiLp.single 2 (0 : Fin n) (1 : ℝ) from rfl,
              PiLp.single_apply]
            simp [hj]
          rw [h_single_zero, PiLp.neg_apply, h_single_zero]
          simp
      rw [h_sf_eval]
      rw [map_neg]
    · rw [evenReflectGrad_apply_lower_component_ne f hlower hi]
      have h_sf_eval : signFlipFun n (EuclideanSpace.single i (1 : ℝ)) =
          EuclideanSpace.single i (1 : ℝ) := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [signFlipFun_apply_zero]
          have hi' : i ≠ 0 := hi
          rw [show (EuclideanSpace.single i (1 : ℝ)) 0 = 0 by
            rw [show EuclideanSpace.single i (1 : ℝ) = PiLp.single 2 i (1 : ℝ) from rfl,
              PiLp.single_apply]
            simp [hi'.symm]]
          simp
        · rw [signFlipFun_apply_ne _ _ hj]
      rw [h_sf_eval]

/-- **HasWeakGrad for the even reflection.** When `f` is smooth with
`tsupport f ⊆ openHalfSpace ∩ Ω` (`Ω` open), the even reflection has
`evenReflectGrad n f` as its weak gradient on `Ω`. -/
theorem hasWeakGrad_evenReflectGrad_evenReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    DeGiorgi.HasWeakGrad (evenReflectGrad n f) (evenReflect n f) Ω := by
  intro i
  have h_evRefl_smooth : ContDiff ℝ (⊤ : ℕ∞) (evenReflect n f) :=
    contDiff_evenReflect_of_tsupport_in_openHalfSpace hf hf_supp
  have h_classical : DeGiorgi.HasWeakPartialDeriv i
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1))
      (evenReflect n f) Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ (h_evRefl_smooth.of_le (by norm_cast))
  have h_eq : (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1)) =
      fun y => evenReflectGrad n f y i := by
    funext y
    exact fderiv_evenReflect_apply_single_eq_evenReflectGrad hf hf_supp y i
  rw [← h_eq]
  exact h_classical

/-- **Even-reflection W^{1,p}-witness construction (strict-interior case).**
For a smooth function `f` on `E := EuclideanSpace ℝ (Fin n)` (n ≥ 1) supported
in the open half-ball `openHalfSpace ∩ Metric.ball x₀ R` (where `x₀` is any
point in `closedHalfSpace`), the even reflection `evenReflect f` admits a
`MemW1pWitness` on `Metric.ball x₀ R`.

This is the strict version where `f` vanishes in a neighborhood of the
boundary hyperplane `{y_0 = 0}`, which makes the reflection itself globally
smooth. The general version (with `closedHalfSpace` instead of `openHalfSpace`)
is the natural extension via density and IBP across the boundary. -/
noncomputable def evenReflect_memW1pWitness_of_smooth_strictInterior
    {n : ℕ} [NeZero n]
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (_hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace ∩
          Metric.ball x₀ R)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    DeGiorgi.MemW1pWitness p (evenReflect (n := n) f) (Metric.ball x₀ R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hf_supp_open :
      tsupport f ⊆ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace :=
    hf_supp.trans Set.inter_subset_left
  have hf_compact : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ R)
    intro x hx
    have h_x_not_in_ball : x ∉ Metric.ball x₀ R := by
      intro hx_in
      exact hx (Metric.ball_subset_closedBall hx_in)
    apply image_eq_zero_of_notMem_tsupport
    intro h_x_in_tsupp
    exact h_x_not_in_ball ((hf_supp h_x_in_tsupp).2)
  refine
    { memLp := ?_
      weakGrad := evenReflectGrad n f
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · have h_full : MemLp (evenReflect n f) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflect_of_contDiff_hasCompactSupport hf_smooth hf_compact p
    exact h_full.restrict (Metric.ball x₀ R)
  · intro i
    have h_full : MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf_smooth hf_compact p i
    exact h_full.restrict (Metric.ball x₀ R)
  · exact hasWeakGrad_evenReflectGrad_evenReflect hf_smooth hf_supp_open Metric.isOpen_ball

/-- **The basis vector `e_0`** in `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def basisE0 (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single (0 : Fin n) (1 : ℝ)

@[simp] lemma basisE0_apply_zero {n : ℕ} [NeZero n] :
    (basisE0 n) 0 = 1 := by
  unfold basisE0
  rw [PiLp.single_apply]
  simp

@[simp] lemma basisE0_apply_ne {n : ℕ} [NeZero n] {j : Fin n} (hj : j ≠ 0) :
    (basisE0 n) j = 0 := by
  unfold basisE0
  rw [PiLp.single_apply]
  simp [hj]

lemma norm_basisE0 {n : ℕ} [NeZero n] : ‖basisE0 n‖ = 1 := by
  unfold basisE0
  simp

/-- **The smooth inward shift** `y ↦ y - δ · e_0`. -/
private noncomputable def shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y => y - δ • basisE0 n

@[simp] lemma shiftDownE0_apply_zero {n : ℕ} [NeZero n]
    (δ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    (shiftDownE0 δ y) 0 = y 0 - δ := by
  unfold shiftDownE0
  rw [PiLp.sub_apply, PiLp.smul_apply, basisE0_apply_zero, smul_eq_mul, mul_one]

@[simp] lemma shiftDownE0_apply_ne {n : ℕ} [NeZero n]
    (δ : ℝ) (y : EuclideanSpace ℝ (Fin n)) {j : Fin n} (hj : j ≠ 0) :
    (shiftDownE0 δ y) j = y j := by
  unfold shiftDownE0
  rw [PiLp.sub_apply, PiLp.smul_apply, basisE0_apply_ne hj, smul_eq_mul, mul_zero,
    sub_zero]

lemma contDiff_shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (shiftDownE0 (n := n) δ) := by
  unfold shiftDownE0
  exact contDiff_id.sub contDiff_const

lemma fderiv_shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (shiftDownE0 (n := n) δ) y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  unfold shiftDownE0
  rw [fderiv_sub_const, fderiv_id']

/-- The shifted function `f_δ(y) := f(y - δ · e_0)`. -/
private noncomputable def shiftDownFun {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => f (shiftDownE0 δ y)

lemma contDiff_shiftDownFun {n : ℕ} [NeZero n] (δ : ℝ) {k : WithTop ℕ∞}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (shiftDownFun (n := n) δ f) :=
  hf.comp (contDiff_shiftDownE0 (n := n) δ)

/-- The chain rule for the shifted function: `∂_i (shiftDownFun δ f) y =
∂_i f (y - δ · e_0)`. -/
lemma fderiv_shiftDownFun_apply
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (fderiv ℝ (shiftDownFun (n := n) δ f) y) (EuclideanSpace.single i 1) =
      (fderiv ℝ f (shiftDownE0 δ y)) (EuclideanSpace.single i 1) := by
  classical
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg_diff : Differentiable ℝ (shiftDownE0 (n := n) δ) :=
    (contDiff_shiftDownE0 (n := n) (k := (1 : WithTop ℕ∞)) δ).differentiable_one
  have h_fun_eq : shiftDownFun (n := n) δ f = f ∘ shiftDownE0 δ := rfl
  rw [h_fun_eq]
  rw [fderiv_comp y hf_diff.differentiableAt hg_diff.differentiableAt]
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_shiftDownE0]
  simp

/-- The shift `shiftDownE0 δ` packaged as a homeomorphism. -/
private noncomputable def shiftDownE0Homeo {n : ℕ} [NeZero n] (δ : ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := shiftDownE0 (n := n) δ
  invFun := fun y => y + δ • basisE0 n
  left_inv := by intro y; unfold shiftDownE0; simp
  right_inv := by intro y; unfold shiftDownE0; simp
  continuous_toFun :=
    (contDiff_shiftDownE0 (n := n) (k := (0 : WithTop ℕ∞)) δ).continuous
  continuous_invFun := continuous_id.add continuous_const

/-- The function `shiftDownFun δ f` factors through `shiftDownE0Homeo`. -/
private lemma shiftDownFun_eq_comp {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    shiftDownFun (n := n) δ f = f ∘ (shiftDownE0Homeo (n := n) δ) :=
  rfl

/-- The tsupport of `shiftDownFun δ f` is the preimage of `tsupport f` under
the shift. -/
private lemma tsupport_shiftDownFun_eq_preimage {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (shiftDownFun (n := n) δ f) =
      shiftDownE0 (n := n) δ ⁻¹' tsupport f := by
  classical
  have h_supp_eq : Function.support (shiftDownFun (n := n) δ f) =
      shiftDownE0 (n := n) δ ⁻¹' Function.support f := by
    ext y
    simp [shiftDownFun, Function.support]
  unfold tsupport
  rw [h_supp_eq]
  have h_eq := (shiftDownE0Homeo (n := n) δ).preimage_closure (Function.support f)
  exact h_eq.symm

/-- For `δ > 0` and `f` with `tsupport f ⊆ closedHalfSpace`, the shifted
function `f_δ(y) := f(y - δ · e_0)` has `tsupport ⊆ openHalfSpace`. -/
lemma tsupport_shiftDownFun_subset_openHalfSpace
    {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    tsupport (shiftDownFun (n := n) δ f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  classical
  rw [tsupport_shiftDownFun_eq_preimage]
  intro y hy
  have h_y_in_closed : shiftDownE0 δ y ∈
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
    hf_supp hy
  have h0 : (0 : ℝ) ≤ (shiftDownE0 δ y) 0 := h_y_in_closed
  rw [shiftDownE0_apply_zero] at h0
  change (0 : ℝ) < y 0
  linarith

/-- The shifted function has compact support when `f` does. -/
lemma hasCompactSupport_shiftDownFun
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_compact : HasCompactSupport f) :
    HasCompactSupport (shiftDownFun (n := n) δ f) := by
  classical
  change IsCompact (tsupport _)
  rw [tsupport_shiftDownFun_eq_preimage]
  set inv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => y + δ • basisE0 n with hinv_def
  have h_inv_cont : Continuous inv := continuous_id.add continuous_const
  have h_preimage_eq : shiftDownE0 (n := n) δ ⁻¹' tsupport f =
      inv '' tsupport f := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, hinv_def]
    constructor
    · intro hy
      refine ⟨shiftDownE0 (n := n) δ y, hy, ?_⟩
      unfold shiftDownE0
      abel
    · rintro ⟨z, hz, rfl⟩
      have h_simplify : shiftDownE0 (n := n) δ (z + δ • basisE0 n) = z := by
        unfold shiftDownE0
        abel
      rw [h_simplify]
      exact hz
  rw [h_preimage_eq]
  exact hf_compact.image h_inv_cont

/-- For `δ > 0` and `f` smooth with `tsupport f ⊆ closedHalfSpace ∩ B(x₀, R)`,
the shifted function has `tsupport ⊆ openHalfSpace ∩ B(x₀, R + δ)`. -/
lemma tsupport_shiftDownFun_subset_ball
    {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    {x₀ : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ∩
          Metric.ball x₀ R) :
    tsupport (shiftDownFun (n := n) δ f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace ∩
        Metric.ball x₀ (R + δ) := by
  classical
  refine Set.subset_inter ?_ ?_
  · exact tsupport_shiftDownFun_subset_openHalfSpace hδ
      (hf_supp.trans Set.inter_subset_left)
  · rw [tsupport_shiftDownFun_eq_preimage]
    intro y hy
    have h_in_ball : shiftDownE0 δ y ∈ Metric.ball x₀ R := (hf_supp hy).2
    rw [Metric.mem_ball] at h_in_ball ⊢
    have h_eq : y - x₀ = (shiftDownE0 δ y - x₀) + δ • basisE0 n := by
      unfold shiftDownE0
      abel
    have hdist_eq : dist y x₀ = ‖y - x₀‖ := dist_eq_norm _ _
    have hdist_eq' : dist (shiftDownE0 δ y) x₀ = ‖shiftDownE0 δ y - x₀‖ :=
      dist_eq_norm _ _
    have h_norm_e0 : ‖δ • basisE0 (n := n)‖ = δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, norm_basisE0, mul_one]
    calc dist y x₀ = ‖y - x₀‖ := hdist_eq
      _ = ‖(shiftDownE0 δ y - x₀) + δ • basisE0 n‖ := by rw [h_eq]
      _ ≤ ‖shiftDownE0 δ y - x₀‖ + ‖δ • basisE0 n‖ := norm_add_le _ _
      _ = dist (shiftDownE0 δ y) x₀ + δ := by rw [hdist_eq', h_norm_e0]
      _ < R + δ := by linarith

/-- Helper: As `δ → 0`, `shiftDownE0 δ z → z` for any fixed `z`. -/
private lemma tendsto_shiftDownE0 {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto (fun δ : ℝ => shiftDownE0 δ z) (nhds 0) (nhds z) := by
  unfold shiftDownE0
  have h_smul_tendsto : Filter.Tendsto (fun δ : ℝ => δ • basisE0 (n := n))
      (nhds 0) (nhds 0) := by
    have h_smul_cont : Continuous (fun s : ℝ => s • basisE0 (n := n)) :=
      continuous_id.smul continuous_const
    have := h_smul_cont.tendsto 0
    simpa [zero_smul] using this
  have h_const_tendsto : Filter.Tendsto (fun _ : ℝ => z) (nhds 0) (nhds z) :=
    tendsto_const_nhds
  have := h_const_tendsto.sub h_smul_tendsto
  simpa using this

/-- **Pointwise convergence of `evenReflect f_δ` to `evenReflect f`** as `δ →
0⁺`. -/
lemma tendsto_evenReflect_shiftDownFun
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (y : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto (fun δ : ℝ => evenReflect n (shiftDownFun (n := n) δ f) y)
      (nhds 0) (nhds (evenReflect n f y)) := by
  classical
  have h_eq :
      ∀ δ : ℝ,
        evenReflect n (shiftDownFun (n := n) δ f) y =
          f (shiftDownE0 δ (evenReflectFun n y)) := by
    intro δ
    unfold evenReflect shiftDownFun
    rfl
  have h_eq_lim :
      evenReflect n f y = f (evenReflectFun n y) := by
    unfold evenReflect; rfl
  simp_rw [h_eq]
  rw [h_eq_lim]
  exact (hf.tendsto _).comp (tendsto_shiftDownE0 (evenReflectFun n y))

/-- Helper: As `δ → 0`, `(fderiv f (shiftDownE0 δ z)) (single i 1) →
(fderiv f z) (single i 1)`. -/
private lemma tendsto_fderiv_apply_shiftDownE0
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Filter.Tendsto (fun δ : ℝ =>
        (fderiv ℝ f (shiftDownE0 δ z)) (EuclideanSpace.single i 1))
      (nhds 0)
      (nhds ((fderiv ℝ f z) (EuclideanSpace.single i 1))) := by
  have h_fderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_eval_cont : Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i (1 : ℝ))) :=
    continuous_id.clm_apply continuous_const
  have h_fderiv_tendsto :
      Filter.Tendsto (fun δ : ℝ => fderiv ℝ f (shiftDownE0 δ z))
        (nhds 0) (nhds (fderiv ℝ f z)) :=
    (h_fderiv_cont.tendsto _).comp (tendsto_shiftDownE0 z)
  exact (h_eval_cont.tendsto _).comp h_fderiv_tendsto

/-- **Pointwise convergence of `evenReflectGrad (shiftDownFun δ f) y i` to
`evenReflectGrad f y i`** as `δ → 0⁺`, for `y` off the boundary hyperplane. -/
lemma tendsto_evenReflectGrad_shiftDownFun_off_boundary
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y 0 ≠ 0) (i : Fin n) :
    Filter.Tendsto (fun δ : ℝ =>
        evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
      (nhds 0) (nhds (evenReflectGrad n f y i)) := by
  classical
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · by_cases hi : i = 0
    · subst hi
      have h_eq_δ : ∀ δ : ℝ,
          evenReflectGrad n (shiftDownFun (n := n) δ f) y 0 =
            -((fderiv ℝ f
              (shiftDownE0 δ (signFlipFun n y))) (EuclideanSpace.single 0 1)) := by
        intro δ
        rw [evenReflectGrad_apply_lower_component_zero
          (shiftDownFun (n := n) δ f) hlt]
        rw [fderiv_shiftDownFun_apply δ hf (signFlipFun n y) 0]
      have h_eq_lim :
          evenReflectGrad n f y 0 =
            -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)) := by
        rw [evenReflectGrad_apply_lower_component_zero f hlt]
      rw [h_eq_lim]
      simp_rw [h_eq_δ]
      exact (tendsto_fderiv_apply_shiftDownE0 hf (signFlipFun n y) 0).neg
    · have h_eq_δ : ∀ δ : ℝ,
          evenReflectGrad n (shiftDownFun (n := n) δ f) y i =
            (fderiv ℝ f
              (shiftDownE0 δ (signFlipFun n y))) (EuclideanSpace.single i 1) := by
        intro δ
        rw [evenReflectGrad_apply_lower_component_ne
          (shiftDownFun (n := n) δ f) hlt hi]
        rw [fderiv_shiftDownFun_apply δ hf (signFlipFun n y) i]
      have h_eq_lim :
          evenReflectGrad n f y i =
            (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1) := by
        rw [evenReflectGrad_apply_lower_component_ne f hlt hi]
      rw [h_eq_lim]
      simp_rw [h_eq_δ]
      exact tendsto_fderiv_apply_shiftDownE0 hf (signFlipFun n y) i
  · have h_y_in_closed : (0 : ℝ) ≤ y 0 := le_of_lt hgt
    have h_eq_δ : ∀ δ : ℝ,
        evenReflectGrad n (shiftDownFun (n := n) δ f) y i =
          (fderiv ℝ f (shiftDownE0 δ y)) (EuclideanSpace.single i 1) := by
      intro δ
      rw [evenReflectGrad_apply_component_upper
        (shiftDownFun (n := n) δ f) h_y_in_closed i]
      rw [fderiv_shiftDownFun_apply δ hf y i]
    have h_eq_lim :
        evenReflectGrad n f y i =
          (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
      rw [evenReflectGrad_apply_component_upper f h_y_in_closed i]
    rw [h_eq_lim]
    simp_rw [h_eq_δ]
    exact tendsto_fderiv_apply_shiftDownE0 hf y i

/-- The boundary hyperplane `{y_0 = 0}` is Lebesgue-null. -/
lemma volume_boundaryHyperplane_eq_zero {n : ℕ} [NeZero n] :
    volume
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) :
        Set (EuclideanSpace ℝ (Fin n))) = 0 := by
  classical
  let φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun y => y 0
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let H : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.ker φ
  have h_set_eq : (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
      (d := n) : Set (EuclideanSpace ℝ (Fin n))) = (H : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    simp only [DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def,
      Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker, H, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
  rw [h_set_eq]
  apply Measure.addHaar_submodule volume H
  intro h_top
  have h_basisE0_in : basisE0 (n := n) ∈ H := by
    rw [h_top]; exact Submodule.mem_top
  have h_basisE0_zero : (basisE0 (n := n) : EuclideanSpace ℝ (Fin n)) 0 = 0 := by
    have := h_basisE0_in
    simp only [LinearMap.mem_ker, H, φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this
  rw [basisE0_apply_zero] at h_basisE0_zero
  exact one_ne_zero h_basisE0_zero

/-- **Pointwise convergence of `evenReflectGrad (shiftDownFun δ f) y i` to
`evenReflectGrad f y i`** as `δ → 0⁺` is valid almost everywhere on `volume`. -/
lemma tendsto_evenReflectGrad_shiftDownFun_ae
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin n) :
    ∀ᵐ y : EuclideanSpace ℝ (Fin n) ∂volume,
      Filter.Tendsto (fun δ : ℝ =>
          evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
        (nhds 0) (nhds (evenReflectGrad n f y i)) := by
  classical
  have h_null : volume
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) :
        Set (EuclideanSpace ℝ (Fin n))) = 0 :=
    volume_boundaryHyperplane_eq_zero
  have h_outside :
      ∀ y ∈ (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) : Set (EuclideanSpace ℝ (Fin n)))ᶜ,
        Filter.Tendsto (fun δ : ℝ =>
            evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
          (nhds 0) (nhds (evenReflectGrad n f y i)) := by
    intro y hy
    have hy_ne : y 0 ≠ 0 := hy
    exact tendsto_evenReflectGrad_shiftDownFun_off_boundary hf y hy_ne i
  rw [Filter.eventually_iff]
  rw [MeasureTheory.mem_ae_iff]
  refine measure_mono_null ?_ h_null
  intro y hy
  by_contra hy_outside
  exact hy (h_outside y hy_outside)

/-- **Uniform bound** on `‖evenReflect (shiftDownFun δ f) y‖`. -/
lemma norm_evenReflect_shiftDownFun_le_sup
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hfC : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ C)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflect n (shiftDownFun (n := n) δ f) y‖ ≤ C := by
  unfold evenReflect shiftDownFun
  exact hfC _

/-- **Uniform bound** on `‖evenReflectGrad (shiftDownFun δ f) y i‖` by `‖fderiv f‖`
at the appropriate (shifted) point. -/
lemma norm_evenReflectGrad_shiftDownFun_apply_le_sup
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ}
    (hfC : ∀ z : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f z‖ ≤ C)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖evenReflectGrad n (shiftDownFun (n := n) δ f) y i‖ ≤ C := by
  classical
  have h_bound :=
    norm_evenReflectGrad_apply_le (shiftDownFun (n := n) δ f) y i
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg_diff : Differentiable ℝ (shiftDownE0 (n := n) δ) :=
    (contDiff_shiftDownE0 (n := n) (k := (1 : WithTop ℕ∞)) δ).differentiable_one
  have h_fderiv_eq :
      fderiv ℝ (shiftDownFun (n := n) δ f) (evenReflectFun n y) =
        fderiv ℝ f (shiftDownE0 δ (evenReflectFun n y)) := by
    have h_fun_eq : shiftDownFun (n := n) δ f = f ∘ shiftDownE0 δ := rfl
    rw [h_fun_eq]
    rw [fderiv_comp _ hf_diff.differentiableAt hg_diff.differentiableAt]
    rw [fderiv_shiftDownE0]
    ext v
    simp
  rw [h_fderiv_eq] at h_bound
  exact h_bound.trans (hfC _)

/-- **HasWeakGrad for the even reflection (closed-half-space case).**
When `f` is smooth with compact support and `tsupport f ⊆ closedHalfSpace`,
the even reflection has `evenReflectGrad n f` as its weak gradient on every
open `Ω`. -/
theorem hasWeakGrad_evenReflectGrad_evenReflect_closedHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_compact : HasCompactSupport f)
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    DeGiorgi.HasWeakGrad (evenReflectGrad n f) (evenReflect n f) Ω := by
  classical
  intro i φ hφ_smooth hφ_compact hφ_sub
  set δseq : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ) with hδseq_def
  have hδ_pos : ∀ k, 0 < δseq k := fun k => by
    rw [hδseq_def]; positivity
  have hδ_tendsto : Filter.Tendsto δseq Filter.atTop (nhds (0 : ℝ)) := by
    rw [hδseq_def]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set f_seq : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k => shiftDownFun (n := n) (δseq k) f with hf_seq_def
  have hf_seq_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f_seq k) := by
    intro k; exact contDiff_shiftDownFun (n := n) (δseq k) hf
  have hf_seq_supp_open : ∀ k,
      tsupport (f_seq k) ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
    intro k
    exact tsupport_shiftDownFun_subset_openHalfSpace (hδ_pos k) hf_supp
  have h_seq_ibp : ∀ k,
      ∫ x in Ω, evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x := by
    intro k
    have h_grad_seq :
        DeGiorgi.HasWeakGrad (evenReflectGrad n (f_seq k))
          (evenReflect n (f_seq k)) Ω :=
      hasWeakGrad_evenReflectGrad_evenReflect (hf_seq_smooth k)
        (hf_seq_supp_open k) hΩ
    exact h_grad_seq i φ hφ_smooth hφ_compact hφ_sub
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have h_fderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_fderiv_compact : HasCompactSupport (fderiv ℝ f) :=
    hf_compact.fderiv ℝ
  have h_norm_fderiv_cont : Continuous (fun z => ‖fderiv ℝ f z‖) :=
    h_fderiv_cont.norm
  have h_norm_fderiv_compact : HasCompactSupport (fun z => ‖fderiv ℝ f z‖) := by
    apply HasCompactSupport.intro h_fderiv_compact.isCompact
    intro x hx
    have : fderiv ℝ f x = 0 := by
      by_contra h
      exact hx (subset_tsupport _ h)
    rw [this]
    simp
  obtain ⟨C₀, hC₀_bound⟩ : ∃ C₀ : ℝ, ∀ z, ‖f z‖ ≤ C₀ :=
    hf.continuous.bounded_above_of_compact_support hf_compact
  obtain ⟨C₁, hC₁_bound⟩ : ∃ C₁ : ℝ, ∀ z, ‖fderiv ℝ f z‖ ≤ C₁ := by
    obtain ⟨C₁, hC₁⟩ := h_norm_fderiv_cont.bounded_above_of_compact_support h_norm_fderiv_compact
    refine ⟨C₁, fun z => ?_⟩
    have h := hC₁ z
    simpa using h
  have hdφ_cont : Continuous (fun x =>
      (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
    (hφ_smooth.continuous_fderiv
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport (fun x =>
      (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
    hφ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_LHS_tendsto :
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        Filter.atTop
        (nhds (∫ x in Ω, evenReflect n f x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
    set bound_LHS : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ with hbound_LHS_def
    have h_bound_LHS_cont : Continuous bound_LHS :=
      continuous_const.mul hdφ_cont.norm
    have h_bound_LHS_supp : HasCompactSupport bound_LHS := by
      apply HasCompactSupport.intro hdφ_compact.isCompact
      intro x hx
      have hx0 : (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
        by_contra h
        exact hx (subset_tsupport _ h)
      change C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ = 0
      rw [hx0]
      simp
    have h_bound_LHS_int : Integrable bound_LHS (volume.restrict Ω) :=
      (h_bound_LHS_cont.integrable_of_hasCompactSupport h_bound_LHS_supp).restrict
    have h_F_meas : ∀ k, AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
      intro k
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_evenReflect (hf_seq_smooth k).continuous).aestronglyMeasurable
      · exact hdφ_cont.aestronglyMeasurable
    have h_F_lim_meas : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          evenReflect n f x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_evenReflect hf.continuous).aestronglyMeasurable
      · exact hdφ_cont.aestronglyMeasurable
    have h_F_bound : ∀ k, ∀ᵐ x ∂(volume.restrict Ω),
        ‖evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ ≤ bound_LHS x := by
      intro k
      refine Filter.Eventually.of_forall (fun x => ?_)
      change ‖evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ ≤
        C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖
      rw [norm_mul]
      have h1 : ‖evenReflect n (f_seq k) x‖ ≤ C₀ :=
        norm_evenReflect_shiftDownFun_le_sup (δseq k) hC₀_bound x
      have h2 : (0 : ℝ) ≤ ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ :=
        norm_nonneg _
      exact mul_le_mul_of_nonneg_right h1 h2
    have h_F_lim : ∀ᵐ x ∂(volume.restrict Ω),
        Filter.Tendsto (fun k : ℕ =>
            evenReflect n (f_seq k) x *
              (fderiv ℝ φ x) (EuclideanSpace.single i 1))
          Filter.atTop
          (nhds (evenReflect n f x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_evRefl_lim :
          Filter.Tendsto (fun k : ℕ => evenReflect n (f_seq k) x)
            Filter.atTop (nhds (evenReflect n f x)) :=
        (tendsto_evenReflect_shiftDownFun (n := n) hf.continuous x).comp hδ_tendsto
      exact h_evRefl_lim.mul tendsto_const_nhds
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound_LHS h_F_meas h_bound_LHS_int h_F_bound h_F_lim
  have h_RHS_tendsto :
      Filter.Tendsto
        (fun k : ℕ => -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x)
        Filter.atTop
        (nhds (-∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
    have h_inner :
        Filter.Tendsto
          (fun k : ℕ => ∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x)
          Filter.atTop
          (nhds (∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
      set bound_RHS : EuclideanSpace ℝ (Fin n) → ℝ :=
        fun x => C₁ * ‖φ x‖ with hbound_RHS_def
      have h_bound_RHS_cont : Continuous bound_RHS :=
        continuous_const.mul hφ_smooth.continuous.norm
      have h_bound_RHS_supp : HasCompactSupport bound_RHS := by
        apply HasCompactSupport.intro hφ_compact.isCompact
        intro x hx
        have hx0 : φ x = 0 := by
          by_contra h
          exact hx (subset_tsupport _ h)
        change C₁ * ‖φ x‖ = 0
        rw [hx0]
        simp
      have h_bound_RHS_int : Integrable bound_RHS (volume.restrict Ω) :=
        (h_bound_RHS_cont.integrable_of_hasCompactSupport h_bound_RHS_supp).restrict
      have h_G_meas : ∀ k, AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            evenReflectGrad n (f_seq k) x i * φ x) (volume.restrict Ω) := by
        intro k
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact aestronglyMeasurable_evenReflectGrad_component_of_contDiff
            (hf_seq_smooth k) i |>.mono_measure (Measure.restrict_le_self)
        · exact hφ_smooth.continuous.aestronglyMeasurable
      have h_G_bound : ∀ k, ∀ᵐ x ∂(volume.restrict Ω),
          ‖evenReflectGrad n (f_seq k) x i * φ x‖ ≤ bound_RHS x := by
        intro k
        refine Filter.Eventually.of_forall (fun x => ?_)
        change ‖evenReflectGrad n (f_seq k) x i * φ x‖ ≤ C₁ * ‖φ x‖
        rw [norm_mul]
        have h1 : ‖evenReflectGrad n (f_seq k) x i‖ ≤ C₁ :=
          norm_evenReflectGrad_shiftDownFun_apply_le_sup (δseq k) hf hC₁_bound x i
        have h2 : (0 : ℝ) ≤ ‖φ x‖ := norm_nonneg _
        exact mul_le_mul_of_nonneg_right h1 h2
      have h_G_lim : ∀ᵐ x ∂(volume.restrict Ω),
          Filter.Tendsto (fun k : ℕ =>
              evenReflectGrad n (f_seq k) x i * φ x)
            Filter.atTop
            (nhds (evenReflectGrad n f x i * φ x)) := by
        have h_ae : ∀ᵐ x ∂volume,
            Filter.Tendsto (fun k : ℕ => evenReflectGrad n (f_seq k) x i)
              Filter.atTop (nhds (evenReflectGrad n f x i)) :=
          tendsto_evenReflectGrad_shiftDownFun_ae hf i |>.mp
            (Filter.Eventually.of_forall (fun x h_lim_δ =>
              h_lim_δ.comp hδ_tendsto))
        exact (ae_restrict_of_ae h_ae).mono fun x hx => hx.mul tendsto_const_nhds
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        bound_RHS h_G_meas h_bound_RHS_int h_G_bound h_G_lim
    exact h_inner.neg
  have h_lhs_eq_rhs :
      (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
        fun k : ℕ => -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x := by
    funext k
    exact h_seq_ibp k
  have h_LHS_eq_lim :
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        Filter.atTop
        (nhds (-∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
    rw [h_lhs_eq_rhs]
    exact h_RHS_tendsto
  exact tendsto_nhds_unique h_LHS_tendsto h_LHS_eq_lim

/-- **Even-reflection W^{1,p}-witness construction (closed-half-space case).**
For a smooth function `f` on `E := EuclideanSpace ℝ (Fin n)` (n ≥ 1) supported
in the closed half-ball `closedHalfSpace ∩ Metric.ball x₀ R`, the even
reflection `evenReflect f` admits a `MemW1pWitness` on `Metric.ball x₀ R`.

Compared to the strict-interior version, this allows `f` to be nonzero at the
boundary hyperplane `{y_0 = 0}`. The proof reduces to the strict-interior case
via an inward shift `f_δ(y) := f(y - δ · e_0)` and bounded convergence on the
integration-by-parts identity. -/
noncomputable def evenReflect_memW1pWitness_of_smooth_closedHalfSpace
    {n : ℕ} [NeZero n]
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (_hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ∩
          Metric.ball x₀ R)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    DeGiorgi.MemW1pWitness p (evenReflect (n := n) f) (Metric.ball x₀ R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hf_compact : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ R)
    intro x hx
    have h_x_not_in_ball : x ∉ Metric.ball x₀ R := by
      intro hx_in
      exact hx (Metric.ball_subset_closedBall hx_in)
    apply image_eq_zero_of_notMem_tsupport
    intro h_x_in_tsupp
    exact h_x_not_in_ball ((hf_supp h_x_in_tsupp).2)
  have hf_supp_closed :
      tsupport f ⊆ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
    hf_supp.trans Set.inter_subset_left
  refine
    { memLp := ?_
      weakGrad := evenReflectGrad n f
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · have h_full : MemLp (evenReflect n f) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflect_of_contDiff_hasCompactSupport hf_smooth hf_compact p
    exact h_full.restrict (Metric.ball x₀ R)
  · intro i
    have h_full : MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf_smooth hf_compact p i
    exact h_full.restrict (Metric.ball x₀ R)
  · exact hasWeakGrad_evenReflectGrad_evenReflect_closedHalfSpace
      hf_smooth hf_compact hf_supp_closed Metric.isOpen_ball

/-- **Smooth manifold-level Morrey sup bound, with-boundary case.**

For a closed Riemannian manifold-with-boundary modelled on the canonical
Euclidean half-space `EuclideanHalfSpace n` and `p > n`, every smooth `u : M →
ℝ` whose canonical-POU chart-pushed functions all have `tsupport` strictly
inside the open interior parts of the chart targets satisfies a uniform-in-`u`
sup-norm bound:

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`.

This is a re-export of `smooth_manifold_morrey_sup_bound_uniform_withBoundary`
from `MorreyManifold.lean`, packaged together with the foundational even-
reflection layer so a single import suffices for downstream callers wanting
both.

When the chart-pushed function takes nonzero values at boundary points
`{y_0 = 0}` of the chart target, the chart-extended function
`chartSmoothExt α (ρ_α · u)` is no longer smooth on `EuN`, so the
boundaryless smooth Morrey cannot be applied directly with that function as
input. The closed-half-space W^{1,p} witness construction
`evenReflect_memW1pWitness_of_smooth_closedHalfSpace` delivered above
provides the corresponding W^{1,p} ingredient: for any smooth `f : EuN → ℝ`
with `tsupport ⊆ closedHalfSpace ∩ Metric.ball x₀ R`, the even reflection
admits a `MemW1pWitness` on the ball, suitable for `morrey_sup_bound`. -/
theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary_unconditional
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (n := n) (M := M) g hp

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
