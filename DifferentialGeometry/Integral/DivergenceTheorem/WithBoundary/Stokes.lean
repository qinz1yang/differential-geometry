import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Ibp
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Global
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InteriorCompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ModelBoundary
import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.Closed
import DifferentialGeometry.Integral.DivergenceTheorem.Proper
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.Integral.Measure.Glue
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Stokes' theorem on a smooth Riemannian manifold-with-boundary
(chart-by-chart formulation)

For a smooth Riemannian metric `g` on a smooth manifold `M` whose model `I`
admits a smooth boundary stratum (`[hI : HasSmoothBoundary E H I]`), this
file establishes the chart-α local form of the divergence theorem
(integration-by-parts identity for the chart-α local within-divergence),
in chart-by-chart form.

Since the global outward unit normal vector field on the boundary is, in
the present architecture, established only pointwise (not as a smooth
bundle section), the natural formulation of the boundary contribution is
chart-by-chart: the chart-α boundary face integral packages the chart-α
boundary contribution as a single quantity, parameterised by a chart-α-
supported smooth weight function.

## Main definition

* `chartBoundaryFaceIntegral g α X f` — the chart-α boundary face integral
  of the smooth tangent section `X` against a chart-α-supported smooth
  weight function `f : M → ℝ`. By definition, it is the chart-α-integral
  `∫ (localDivergenceWithin g α X x) · f x ∂(chartLocalMeasure g α)`.

  The dependence on a chart-supported weight `f` is structural: in the
  with-boundary setting the chart-α local within-divergence and the global
  divergence may disagree at chart-α boundary points, so the chart-α
  boundary contribution is well-defined only when accompanied by a
  chart-supported weight that selects the chart-α contribution.

## Main results

* `chart_local_stokes_within` — for any smooth tangent section `X` and any
  smooth function `f : M → ℝ`, the chart-α-pulled-back integral of
  `localDivergenceWithin g α X · f` equals the chart-α boundary face
  integral. By construction this is a definitional equality.

* `chartBoundaryFaceIntegral_eq_neg_tangentSectionAction_of_interior_support`
  — the chart-α boundary face integral against a smooth chart-supported,
  interior-supported test function equals minus the chart-α-pulled-back
  tangent-section action integral. This is the chart-α form of integration
  by parts in the with-boundary setting.

* `chartBoundaryFaceIntegral_zero_weight` — vanishing under a zero weight.

## Geometric interpretation

By the chart-local Voss–Weyl identity together with Mathlib's box
divergence theorem applied to a Euclidean rectangle that contains the
chart image of the support of the integrand, the chart-α boundary face
integral equals an integral over `(extChartAt I α).target ∩ frontier (range I)`
of the chart-coordinate first component of `f · X` against the chart-target
boundary measure (chart density restricted to the boundary face). The
matching of these chart-α boundary face integrals to a single intrinsic
surface integral over `boundary I M` against an outward unit normal vector
field requires further geometric hypotheses on the boundary; that
identification is **not** carried out in the present file.

## Architectural note on the global Stokes theorem

A natural goal for this file would be the global Stokes theorem
$$\int_M \operatorname{div}_g^{(\partial)}(X)\, d\mu_g
   = \sum_\alpha \chartBoundaryFaceIntegral{g, \alpha, X, \rho_\alpha},$$
where the sum is over a smooth partition of unity subordinate to the chart
atlas. Decomposing the global integral into chart-local integrals by the
canonical Riemannian volume measure formula
`riemannianMeasure_def` gives
$$\int_M \operatorname{div}_g^{(\partial)}(X)\, d\mu_g
   = \sum_\alpha \int_M \operatorname{div}_g^{(\partial)}(X)\, \rho_\alpha\,
       d(\chartLocalMeasure{g, \alpha}).$$
Identifying each chart-local integrand
`divergence_g_with_boundary g X · ρ_α` with the chart-α boundary face
integrand `localDivergenceWithin g α X · ρ_α` requires showing that
the chart-α boundary set `(chartAt H α).source ∩ I.boundary M` has
`chartLocalMeasure g α`-measure zero. By the chart-local pushforward
characterisation of `chartLocalMeasure g α`, this reduces to showing that
the chart-target boundary `(extChartAt I α).target ∩ frontier (range I)`
is Lebesgue-null in `E`. This Lebesgue-null property is true for the
canonical `EuclideanHalfSpace n` model (the boundary face is a
codimension-one affine subspace) but is not stated as a generic fact of
`HasSmoothBoundary` in the present infrastructure, so the global Stokes
theorem in chart-by-chart form is not proved here. The sole structural
statement at the global level is
`integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support`
(`InteriorCompactSupport.lean`), which establishes the boundary-vanishing
case.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- `I.interior M` is open in `M`. Re-export of
`ModelWithCorners.isOpen_interior` at `n = ∞`. -/
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

/-- **Chart-α boundary face integral.** The chart-α boundary contribution of
the with-boundary divergence: by definition, the integral of the chart-α
local within-divergence times a smooth weight function `f : M → ℝ`
against the chart-local measure `chartLocalMeasure g α`.

The dependence on a smooth weight `f` is structural: when `f` has
topological support in the chart base set at `α`, this quantity packages
the chart-α boundary contribution as a single real number; for general
`f`, it is the chart-α-pulled-back integral of
`localDivergenceWithin g α X · f`.

Geometric interpretation. By the chart-local Voss–Weyl formula and Mathlib's
box divergence theorem applied to a Euclidean rectangle that contains the
chart image of the support of the integrand, this quantity equals an
integral over `(extChartAt I α).target ∩ frontier (range I)` of the
chart-coordinate first component of `f · X` against the chart-target
boundary measure. -/
noncomputable def chartBoundaryFaceIntegral
    (g : SmoothRiemannianMetric I M)
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : M → ℝ) : ℝ :=
  ∫ x, localDivergenceWithin (I := I) g α X x * f x
    ∂(chartLocalMeasure (I := I) g α)

/-- Unfolding lemma — the chart-α boundary face integral is the
chart-α-pulled-back integral of `localDivergenceWithin g α X · f`. -/
@[simp] lemma chartBoundaryFaceIntegral_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : M → ℝ) :
    chartBoundaryFaceIntegral (I := I) g α X f =
      ∫ x, localDivergenceWithin (I := I) g α X x * f x
        ∂(chartLocalMeasure (I := I) g α) := rfl

/-- **Chart-α Stokes (with-boundary).** For a smooth tangent section `X` and
a smooth function `f : M → ℝ`, the chart-α-pulled-back integral of
`localDivergenceWithin g α X · f` equals the chart-α boundary face
integral. -/
theorem chart_local_stokes_within
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : M → ℝ) :
    ∫ x, localDivergenceWithin (I := I) g α X x * f x
        ∂(chartLocalMeasure (I := I) g α) =
      chartBoundaryFaceIntegral (I := I) g α X f := rfl

/-- The chart-α boundary face integral with zero weight vanishes. -/
@[simp] theorem chartBoundaryFaceIntegral_zero_weight
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    chartBoundaryFaceIntegral (I := I) g α X (fun _ => (0 : ℝ)) = 0 := by
  rw [chartBoundaryFaceIntegral_def]
  have h : (fun x : M => localDivergenceWithin (I := I) g α X x * 0) =
      (fun _ : M => (0 : ℝ)) := by
    funext x; rw [mul_zero]
  rw [h, integral_zero]

/-- **Chart-α IBP relation (interior support).** When the test function `f`
has topological support strictly inside the manifold interior and inside
the chart base set at `α`, the chart-α boundary face integral against `f`
equals minus the chart-α-pulled-back tangent-section action integral. This
is the with-boundary integration-by-parts identity from
`chart_local_ibp_within` rephrased through the chart-α boundary face
integral. -/
theorem chartBoundaryFaceIntegral_eq_neg_tangentSectionAction_of_interior_support
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_compactSupp : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (hf_int : tsupport f ⊆ I.interior M) :
    chartBoundaryFaceIntegral (I := I) g α X f =
      -∫ x, tangentSectionAction (I := I) X f x
        ∂(chartLocalMeasure (I := I) g α) := by
  rw [chartBoundaryFaceIntegral_def]
  exact chart_local_ibp_within (I := I) g α X hf hf_compactSupp hf_supp hf_int

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

/-- For a manifold-boundary point `x` lying in the source of a chart at any
base point `α`, the chart-α image `extChartAt I α x` lies in the model-level
boundary `frontier (Set.range I)`. This is the chart-independent
characterisation of boundary points (cf.
`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`).

This generalises `BoundaryManifold.extChart_mem_frontier_of_mem_source` to
arbitrary `x : M`, without packaging `x` as a `BoundaryManifold` element. -/
private lemma extChartAt_mem_frontier_range_of_mem_chartSource_inter_boundary
    (α : M) {x : M}
    (hx_chart : x ∈ (chartAt H α).source)
    (hx_bdy : x ∈ I.boundary M) :
    extChartAt I α x ∈ frontier (Set.range I) := by
  have hx_isBdy : I.IsBoundaryPoint x := hx_bdy
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hAtlas : chartAt H α ∈ atlas H M := chart_mem_atlas H _
  have h_iff := ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas
    (I := I) (n := ∞) hOne hAtlas hx_chart
  have hx_frontier : extChartAt I α x ∈ frontier (extChartAt I α).target :=
    h_iff.mp hx_isBdy
  by_contra hC
  have hx_inRange : extChartAt I α x ∈ Set.range I := by
    have hx_extSource : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
    have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_extSource
    have hsubset : (extChartAt I α).target ⊆ Set.range I := by
      rw [extChartAt_target (I := I)]
      exact Set.inter_subset_right
    exact hsubset hx_target
  have hx_closure : extChartAt I α x ∈ closure (Set.range I) :=
    subset_closure hx_inRange
  rw [frontier, Set.mem_diff] at hC
  push Not at hC
  have hx_interior : extChartAt I α x ∈ interior (Set.range I) := hC hx_closure
  have hx_chartTarget : chartAt H α x ∈ (chartAt H α).target :=
    (chartAt H α).map_source hx_chart
  have hx_target_int :
      extChartAt I α x ∈ interior (extChartAt I α).target := by
    change (chartAt H α).extend I x ∈ interior ((chartAt H α).extend I).target
    exact (chartAt H α).mem_interior_extend_target hx_chartTarget hx_interior
  exact (disjoint_interior_frontier
        (s := (extChartAt I α).target)).le_bot
      ⟨hx_target_int, hx_frontier⟩

/-- The image under `(extChartAt I α).symm` of the chart-α boundary stratum
intersected with the chart target is contained in the model-level boundary. -/
private lemma symm_preimage_chart_boundary_inter_target_subset_frontier
    (α : M) :
    (extChartAt I α).symm ⁻¹' ((chartAt H α).source ∩ I.boundary M)
        ∩ (extChartAt I α).target
      ⊆ frontier (Set.range I) := by
  intro y hy
  obtain ⟨hy_pre, hy_target⟩ := hy
  set x := (extChartAt I α).symm y with hx_def
  have hx_chart : x ∈ (chartAt H α).source := hy_pre.1
  have hx_bdy : x ∈ I.boundary M := hy_pre.2
  have h_front : extChartAt I α x ∈ frontier (Set.range I) :=
    extChartAt_mem_frontier_range_of_mem_chartSource_inter_boundary
      (I := I) α hx_chart hx_bdy
  have h_right : extChartAt I α x = y :=
    (extChartAt I α).right_inv hy_target
  rw [h_right] at h_front
  exact h_front

/-- The chart-α boundary set `(chartAt H α).source ∩ I.boundary M` has
`chartLocalMeasure g α`-measure zero. This is the key consequence of the
boundary's codimension-one null property
(`HasSmoothBoundary.range_frontier_basis_addHaar_zero`). -/
lemma chartLocalMeasure_chart_boundary_zero
    (g : SmoothRiemannianMetric I M) (α : M) :
    chartLocalMeasure (I := I) g α
        ((chartAt H α).source ∩ I.boundary M) = 0 := by
  classical
  set B : Set M := (chartAt H α).source ∩ I.boundary M with hB_def
  set target : Set E := (extChartAt I α).target with hT_def
  set ν : MeasureTheory.Measure E :=
    ((modelHaar (E := E)).restrict target).withDensity
      (fun y : E =>
        ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))) with hν_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  have hcontOn : ContinuousOn (extChartAt I α).symm target :=
    continuousOn_extChartAt_symm (I := I) α
  have haemeas_base :
      AEMeasurable (extChartAt I α).symm
        ((modelHaar (E := E)).restrict target) :=
    hcontOn.aemeasurable htarget_meas
  have hν_ac : ν ≪ (modelHaar (E := E)).restrict target := by
    simpa [hν_def] using MeasureTheory.withDensity_absolutelyContinuous
      (μ := (modelHaar (E := E)).restrict target)
      (fun y : E =>
        ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
  have haemeas : AEMeasurable (extChartAt I α).symm ν :=
    haemeas_base.mono_ac hν_ac
  have hB_chart_meas : MeasurableSet (chartAt H α).source :=
    (chartAt H α).open_source.measurableSet
  have hB_bdy_meas : MeasurableSet (I.boundary M) := by
    rw [← I.compl_interior]
    exact (isOpen_interior_M (I := I) (M := M)).measurableSet.compl
  have hB_meas : MeasurableSet B :=
    hB_chart_meas.inter hB_bdy_meas
  rw [chartLocalMeasure_def, MeasureTheory.Measure.map_apply_of_aemeasurable
        haemeas hB_meas]
  refine hν_ac ?_
  rw [MeasureTheory.Measure.restrict_apply' htarget_meas]
  have hsub : (extChartAt I α).symm ⁻¹' B ∩ target ⊆
      frontier (Set.range I) :=
    symm_preimage_chart_boundary_inter_target_subset_frontier (I := I) α
  have h_mh_zero : (modelHaar (E := E)) (frontier (Set.range I)) = 0 := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    have h_fb : ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (frontier (Set.range I)) = 0 :=
      HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero (I := I)
    have h_eq :=
      (modelHaar (E := E)).isAddLeftInvariant_eq_smul
        ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
    rw [h_eq, MeasureTheory.Measure.smul_apply, h_fb, smul_zero]
  exact MeasureTheory.measure_mono_null hsub h_mh_zero

/-- For a smooth Riemannian metric `g`, smooth tangent section `X`, and any
`α : M`, the global with-boundary divergence equals the chart-α local
within-divergence `chartLocalMeasure g α`-almost-everywhere on the chart-α
source. The exception set is the chart-α boundary, which has measure zero by
`chartLocalMeasure_chart_boundary_zero`. -/
private lemma divergence_g_with_boundary_eq_localDivergenceWithin_ae_chartLocal
    [T2Space M] (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      x ∈ (chartAt H α).source →
        divergence_g_with_boundary (I := I) g X x =
          localDivergenceWithin (I := I) g α X x := by
  set bad : Set M := (chartAt H α).source ∩ I.boundary M with hbad_def
  have h_bad_measzero :
      chartLocalMeasure (I := I) g α bad = 0 :=
    chartLocalMeasure_chart_boundary_zero (I := I) g α
  refine MeasureTheory.ae_iff.mpr ?_
  apply MeasureTheory.measure_mono_null _ h_bad_measzero
  intro x hx
  push Not at hx
  obtain ⟨hx_chart, hx_neq⟩ := hx
  by_cases hx_int : x ∈ I.interior M
  · exfalso
    apply hx_neq
    exact voss_weyl_divergence_with_boundary_formula (I := I) g α X
      hx_chart hx_int
  · refine ⟨hx_chart, ?_⟩
    rw [← I.compl_interior]
    exact hx_int

/-- For each chart α, the integral
`∫ (divergence_g_with_boundary g X) · ρ α x ∂(chartLocalMeasure g α)` equals
`∫ (localDivergenceWithin g α X) · ρ α x ∂(chartLocalMeasure g α)`, when ρ α
has chart-α-supported topological support. The proof uses
`chartLocalMeasure_chart_boundary_zero` to pass between the two divergence
forms a.e. -/
private lemma chartLocal_integral_divergence_eq_localDivergenceWithin
    [T2Space M] (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {ρ : M → ℝ} (hρ_supp_chart : tsupport ρ ⊆ (chartAt H α).source) :
    ∫ x, divergence_g_with_boundary (I := I) g X x * ρ x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫ x, localDivergenceWithin (I := I) g α X x * ρ x
        ∂(chartLocalMeasure (I := I) g α) := by
  classical
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [divergence_g_with_boundary_eq_localDivergenceWithin_ae_chartLocal
    (I := I) g α X] with x hx
  by_cases hx_chart : x ∈ (chartAt H α).source
  · rw [hx hx_chart]
  · have hx_nots : x ∉ tsupport ρ := fun h => hx_chart (hρ_supp_chart h)
    have hρ_zero : ρ x = 0 := by
      by_contra hne
      exact hx_nots (subset_tsupport _ hne)
    rw [hρ_zero, mul_zero, mul_zero]

/-- The chart-local measure of `I.boundary M` (the entire boundary, not just
the part inside chart α source) is zero. Combines
`chartLocalMeasure_apply_of_disjoint_source` (for the part outside chart α
source) with `chartLocalMeasure_chart_boundary_zero` (for the part inside). -/
private lemma chartLocalMeasure_boundary_zero_of_total
    [T2Space M] (g : SmoothRiemannianMetric I M) (α : M) :
    chartLocalMeasure (I := I) g α (I.boundary M) = 0 := by
  classical
  have hsplit : I.boundary M
      = ((chartAt H α).source ∩ I.boundary M) ∪
        (I.boundary M \ (chartAt H α).source) := by
    ext x
    constructor
    · intro hx
      by_cases hxα : x ∈ (chartAt H α).source
      · exact Or.inl ⟨hxα, hx⟩
      · exact Or.inr ⟨hx, hxα⟩
    · rintro (⟨_, hx⟩ | ⟨hx, _⟩) <;> exact hx
  rw [hsplit]
  refine le_antisymm ?_ (zero_le _)
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  have hbdy_meas : MeasurableSet (I.boundary M) := by
    rw [← I.compl_interior]
    exact (isOpen_interior_M (I := I) (M := M)).measurableSet.compl
  have hdiff_meas : MeasurableSet (I.boundary M \ (chartAt H α).source) :=
    hbdy_meas.diff (chartAt H α).open_source.measurableSet
  have hdiff_disj : Disjoint (I.boundary M \ (chartAt H α).source)
      (chartAt H α).source :=
    Set.disjoint_left.mpr (fun x ⟨_, hx⟩ hx' => hx hx')
  rw [chartLocalMeasure_chart_boundary_zero (I := I) g α,
      chartLocalMeasure_apply_of_disjoint_source (I := I) g α hdiff_meas hdiff_disj]
  simp

/-- A continuous compactly-supported function on a chart-source is integrable
against the chart-local measure. (Reproduction of an analogous private lemma
in `InteriorCompactSupport.lean`, exposed here so the global Stokes proof can
use it.) -/
private lemma integrable_chartLocalMeasure_of_cs_chartSource
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  have hsupp_compact : IsCompact (tsupport f) :=
    .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
  have hμ_supp : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_supp
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hf_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hf_zero]; simp
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, ENNReal.ofReal C *
            (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(chartLocalMeasure (I := I) g α) := MeasureTheory.lintegral_mono_ae hbnd
    _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α (tsupport f) := by
          rw [MeasureTheory.lintegral_const_mul _ ((measurable_const).indicator
            (isClosed_tsupport _).measurableSet)]
          rw [MeasureTheory.lintegral_indicator (isClosed_tsupport _).measurableSet]
          simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp

/-- **Global Stokes theorem on a compact manifold-with-boundary**, in
chart-by-chart form. The integral of the with-boundary divergence
`divergence_g_with_boundary g X` against the canonical Riemannian volume
measure on a compact smooth Riemannian manifold equals the finite sum, over
the chart-atlas POU support set, of the chart-α boundary face integrals
`chartBoundaryFaceIntegral g α X (ρ α)` against the chart-atlas POU `ρ`.

The proof uses three ingredients:

1. **Measure-level POU decomposition.** On a compact manifold the canonical
   Riemannian volume measure equals the finite sum of POU-weighted chart-local
   measures (`riemannianVolumeMeasure_eq_finset_sum`).
2. **Boundary-null reduction.** The chart-α boundary stratum has
   `chartLocalMeasure g α`-measure zero (`chartLocalMeasure_chart_boundary_zero`,
   from the typeclass field `range_frontier_basis_addHaar_zero`). Hence
   `divergence_g_with_boundary g X` and `localDivergenceWithin g α X` agree
   `chartLocalMeasure g α`-a.e. on the chart-α source.
3. **Chart-by-chart reassembly.** Each summand becomes the chart-α boundary
   face integral via the `withDensity` identity for Bochner integrals.

This is the with-boundary analogue of the closed-manifold (boundaryless)
Stokes / divergence theorem on a compact manifold. -/
theorem stokes_compact_via_pou
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) g α X
          ((chartAtlasPOU I M) α) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hsupp_each : ∀ α : M, tsupport ((ρ α : M → ℝ)) ⊆ (chartAt H α).source := by
    intro α; exact hρsub α
  have hsummand_cont : ∀ α : M,
      Continuous (fun x : M => localDivergenceWithin (I := I) g α X x *
        (ρ α : M → ℝ) x) := by
    intro α
    have hα_cont_on_source : ContinuousOn (localDivergenceWithin (I := I) g α X)
        (chartAt H α).source :=
      localDivergenceWithin_continuousOn (I := I) g α X
    have hρα_cont : Continuous ((ρ α : M → ℝ)) := (ρ α).contMDiff.continuous
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (chartAt H α).source
    · have h_locDiv_at : ContinuousAt (localDivergenceWithin (I := I) g α X) x :=
        (hα_cont_on_source x hx).continuousAt
          ((chartAt H α).open_source.mem_nhds hx)
      exact h_locDiv_at.mul hρα_cont.continuousAt
    · have hx_nots : x ∉ tsupport ((ρ α : M → ℝ)) :=
        fun h => hx (hsupp_each α h)
      have h_open : IsOpen (tsupport ((ρ α : M → ℝ)))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev : (fun y : M => localDivergenceWithin (I := I) g α X y *
            (ρ α : M → ℝ) y) =ᶠ[nhds x] (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_nots] with y hy
        have hρy : (ρ α : M → ℝ) y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        change localDivergenceWithin (I := I) g α X y * (ρ α : M → ℝ) y = 0
        rw [hρy, mul_zero]
      exact (continuousAt_const (y := (0 : ℝ))).congr hev.symm
  have hsumm_supp : ∀ α : M,
      tsupport (fun x : M => localDivergenceWithin (I := I) g α X x *
        (ρ α : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro α
    have htss : tsupport (fun x : M => localDivergenceWithin (I := I) g α X x *
          (ρ α : M → ℝ) x) ⊆ tsupport (ρ α : M → ℝ) := by
      apply closure_mono
      intro x hx
      rw [Function.mem_support] at hx
      have hρne : (ρ α : M → ℝ) x ≠ 0 := by
        intro h
        apply hx
        rw [h, mul_zero]
      exact hρne
    exact htss.trans (hsupp_each α)
  have hloc_int : ∀ α : M,
      Integrable
        (fun x : M => localDivergenceWithin (I := I) g α X x *
          (ρ α : M → ℝ) x) (chartLocalMeasure (I := I) g α) := by
    intro α
    exact integrable_chartLocalMeasure_of_cs_chartSource (I := I) g α
      (hsummand_cont α) (hsumm_supp α)
  have hCBI_def : ∀ α : M,
      chartBoundaryFaceIntegral (I := I) g α X (ρ α : M → ℝ) =
        ∫ x, localDivergenceWithin (I := I) g α X x * (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) := fun α => rfl
  have hae_eq : ∀ α : M,
      (fun x : M => divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x)
        =ᵐ[chartLocalMeasure (I := I) g α]
      (fun x : M => localDivergenceWithin (I := I) g α X x * (ρ α : M → ℝ) x) := by
    intro α
    filter_upwards [divergence_g_with_boundary_eq_localDivergenceWithin_ae_chartLocal
      (I := I) g α X] with x hx
    by_cases hx_chart : x ∈ (chartAt H α).source
    · rw [hx hx_chart]
    · have hx_nots : x ∉ tsupport (ρ α : M → ℝ) :=
        fun h => hx_chart (hsupp_each α h)
      have hρ_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hx_nots (subset_tsupport _ hne)
      rw [hρ_zero, mul_zero, mul_zero]
  have hglob_int : ∀ α : M,
      Integrable
        (fun x : M => divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x)
        (chartLocalMeasure (I := I) g α) :=
    fun α => (hloc_int α).congr (hae_eq α).symm
  rw [riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g]
  rw [MeasureTheory.integral_finset_sum_measure (s := S)
        (μ := fun α : M => (chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)))
        (fun α _ => ?_)]
  · refine Finset.sum_congr rfl ?_
    intro α _
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := chartLocalMeasure (I := I) g α)
      (f := fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))
      ((ENNReal.measurable_ofReal.comp
        (ρ α).contMDiff.continuous.measurable).aemeasurable)
      (Filter.Eventually.of_forall (fun _ => by simp))
      (g := fun x : M => divergence_g_with_boundary (I := I) g X x)]
    have hρα_nonneg : ∀ x : M, 0 ≤ (ρ α : M → ℝ) x :=
      fun x => ρ.nonneg α x
    have hsmul : ∀ x : M,
        (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal •
          divergence_g_with_boundary (I := I) g X x =
        divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x := by
      intro x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    rw [show (fun x : M => (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal •
                divergence_g_with_boundary (I := I) g X x)
          = fun x : M => divergence_g_with_boundary (I := I) g X x *
              (ρ α : M → ℝ) x from
          funext hsmul]
    rw [MeasureTheory.integral_congr_ae (hae_eq α)]
    rw [hCBI_def α]
  · have hρα_meas : Measurable (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)) :=
      ENNReal.measurable_ofReal.comp (ρ α).contMDiff.continuous.measurable
    have hρα_aemeas : AEMeasurable (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))
        (chartLocalMeasure (I := I) g α) := hρα_meas.aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
        ENNReal.ofReal ((ρ α : M → ℝ) y) < ⊤ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have hρα_nonneg : ∀ x : M, 0 ≤ (ρ α : M → ℝ) x :=
      fun x => ρ.nonneg α x
    have hsmul_eq : (fun x : M => (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal •
                divergence_g_with_boundary (I := I) g X x)
          = fun x : M => divergence_g_with_boundary (I := I) g X x *
              (ρ α : M → ℝ) x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    refine (integrable_withDensity_iff_integrable_smul₀'
      hρα_aemeas hρα_lt_top
      (g := fun x : M => divergence_g_with_boundary (I := I) g X x)).mpr ?_
    rw [hsmul_eq]
    exact hglob_int α

end StokesGlobal

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
