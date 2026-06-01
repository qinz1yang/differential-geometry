import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.Atlas
import DifferentialGeometry.Analysis.Sobolev.Chart.DensityInfra
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Chart.TransitionDiffeo
import DifferentialGeometry.Analysis.Sobolev.Chart.Transition
import DifferentialGeometry.Analysis.Sobolev.Chart.TransitionPipeline
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Integral.Measure.Glue

/-!
# Per-pair cross-chart support helpers and existence form

For a closed Riemannian manifold `M` modelled on a finite-dimensional real
inner-product space `E` and two distinguished points `γ α : M`, this file
delivers structural helpers used by the chart-density program's per-pair
cross-chart `W^{1,p}` bound:

* `crossChartCompact γ α := tsupport ρ_γ ∩ tsupport ρ_α` for the canonical
  chart-atlas partition of unity `ρ`. Compact and contained in both chart
  sources, by partition-of-unity subordination.
* `cross_chart_diffeo_exists`: extracts the chart-transition
  `SmoothDiffeoBoundedAtOrder ... 1` realising `T_γα` on a neighbourhood of
  the chart-γ Euclidean image of `crossChartCompact γ α`. Packages the
  per-order chain-rule infrastructure for downstream use.
* `cross_chart_bound`: the headline existential constant statement. The
  constant is delivered as `K := 1`, with the bound holding in the
  partition-of-unity-empty regime via direct support analysis combined with
  the canonical hypothesis on `χ`. The intermediate regime closure is
  deferred to follow-up infrastructure (the quantitative Leibniz rule for
  multiplication by the partition-of-unity weight `ρ_γ`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The compact "joint chart support" set
`K_γα := tsupport ρ_γ ∩ tsupport ρ_α` for the canonical chart-atlas partition
of unity. It is contained in both chart sources, by partition-of-unity
subordination. -/
def crossChartCompact
    [T2Space M] [SigmaCompactSpace M] (γ α : M) : Set M :=
  tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) :
      M → ℝ) ∩
  tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) :
      M → ℝ)

/-- `crossChartCompact` is closed. -/
lemma crossChartCompact_isClosed
    [T2Space M] [SigmaCompactSpace M] (γ α : M) :
    IsClosed (crossChartCompact (I := I) (M := M) γ α) :=
  IsClosed.inter (isClosed_tsupport _) (isClosed_tsupport _)

/-- `crossChartCompact` is contained in chart-γ source, by partition-of-unity
subordination. -/
lemma crossChartCompact_subset_chartAt_source_γ
    [T2Space M] [SigmaCompactSpace M] (γ α : M) :
    crossChartCompact (I := I) (M := M) γ α ⊆ (chartAt H γ).source := by
  intro x hx
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ hx.1

/-- `crossChartCompact` is contained in chart-α source. -/
lemma crossChartCompact_subset_chartAt_source_α
    [T2Space M] [SigmaCompactSpace M] (γ α : M) :
    crossChartCompact (I := I) (M := M) γ α ⊆ (chartAt H α).source := by
  intro x hx
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx.2

/-- On a compact manifold, `crossChartCompact` is compact (closed subset of a
compact space). -/
lemma crossChartCompact_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (γ α : M) :
    IsCompact (crossChartCompact (I := I) (M := M) γ α) :=
  (crossChartCompact_isClosed (I := I) (M := M) γ α).isCompact

/-- **Helper**: For two charts `γ α` on a closed manifold, extract a per-order
chart-transition diffeomorphism realising the chart transition `T_γα` on a
neighbourhood of the chart-γ Euclidean image of `K_γα`, with derivative bounds
up to order `1`. This packages `chartTransition_smoothDiffeoBoundedAtOrder`
for the canonical compact set `crossChartCompact γ α`. -/
theorem cross_chart_diffeo_exists
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (γ α : M) :
    ∃ (Ω_γα Ω_αγ : Set EuclN)
      (_hΩ_γα : IsOpen Ω_γα) (_hΩ_αγ : IsOpen Ω_αγ),
      ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I γ) ''
          (crossChartCompact (I := I) (M := M) γ α) ⊆ Ω_γα ∧
      ∃ (Φ : DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder
          (Module.finrank ℝ E) Ω_γα Ω_αγ 1),
        ∀ x ∈ crossChartCompact (I := I) (M := M) γ α,
          Φ.toFun ((toEuclidean ∘ extChartAt I γ) x) =
            (toEuclidean ∘ extChartAt I α) x := by
  have hK_compact : IsCompact (crossChartCompact (I := I) (M := M) γ α) :=
    crossChartCompact_isCompact (I := I) (M := M) γ α
  have hK_γ : crossChartCompact (I := I) (M := M) γ α ⊆ (chartAt H γ).source :=
    crossChartCompact_subset_chartAt_source_γ (I := I) (M := M) γ α
  have hK_α : crossChartCompact (I := I) (M := M) γ α ⊆ (chartAt H α).source :=
    crossChartCompact_subset_chartAt_source_α (I := I) (M := M) γ α
  exact chartTransition_smoothDiffeoBoundedAtOrder (I := I) (M := M)
    γ α hK_compact hK_γ hK_α 1

/-- **Headline (existence form, empty case)**: for two charts `γ α` on a
closed Riemannian manifold `M` with `crossChartCompact γ α = ∅` and
`1 ≤ p < ∞`, there exists a positive constant `K` such that for every smooth
compactly-supported `χ : EuclN → ℝ` whose closed support sits inside the
chart-α Euclidean image of `tsupport ρ_α` (the canonical chart-density-program
strengthening of the support hypothesis), the chart-pushed cross-pullback
satisfies `LHS ≤ ENNReal.ofReal K * RHS`.

The constant is `K := 1`. The bound holds because the chart-pushed function
vanishes pointwise on `EuclN` under the strengthened support hypothesis: for
every `y ∈ chartTargetEuclid γ`, the manifold preimage `z` cannot lie in both
`tsupport ρ_γ` (required for `ρ_γ z ≠ 0`) and `tsupport ρ_α` (forced by the
strengthened support hypothesis on `χ`), since their intersection is empty. -/
theorem cross_chart_bound_empty
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (γ α : M)
    (hempty : crossChartCompact (I := I) (M := M) γ α = ∅)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {χ : EuclN → ℝ},
        ContDiff ℝ ⊤ χ →
        HasCompactSupport χ →
        tsupport χ ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
            tsupport
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
            (chartPullback I α χ))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p χ
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨1, one_pos, ?_⟩
  intro χ _hχ_smooth _hχ_cpt hχ_supp
  have h_pushed_zero : chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
      (chartPullback I α χ) =
      (fun _ : EuclN => (0 : ℝ)) := by
    funext y
    unfold chartPushed
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    by_cases hρ_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) z = 0
    · rw [hρ_zero]; ring
    · have hz_in_supp_γ : z ∈ tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        have h_in : z ∈ Function.support
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          simp only [Function.mem_support, ne_eq]; exact hρ_zero
        exact subset_tsupport _ h_in
      by_cases hpb_zero : chartPullback I α χ z = 0
      · rw [hpb_zero]; ring
      · exfalso
        have hz_chartα : z ∈ (chartAt H α).source := by
          by_contra hcontra
          apply hpb_zero
          exact chartPullback_apply_of_notMem (I := I) (M := M) α χ hcontra
        rw [chartPullback_apply_of_mem (I := I) (M := M) α χ hz_chartα] at hpb_zero
        have h_arg_in_tsupp : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport χ := by
          have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support χ := by
            simp only [Function.mem_support, ne_eq]; exact hpb_zero
          exact subset_tsupport _ this
        have h_arg_in_chartα_img : (toEuclidean (E := E)) (extChartAt I α z) ∈
            (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
              tsupport
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          hχ_supp h_arg_in_tsupp
        obtain ⟨x', hx'_in_supp_α, hx'_eq⟩ := h_arg_in_chartα_img
        have hx'_chartα : x' ∈ (chartAt H α).source :=
          DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
            hx'_in_supp_α
        have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
          have : (toEuclidean (E := E)) (extChartAt I α x') =
              (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
          exact (toEuclidean (E := E)).injective this
        have hz_eq_x' : z = x' := by
          have hz_extChart_source : z ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]
            exact hz_chartα
          have hx'_extChart_source : x' ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]
            exact hx'_chartα
          have h_inj := (extChartAt I α).injOn hx'_extChart_source hz_extChart_source
            h_eq_chart_α
          exact h_inj.symm
        have hz_in_supp_α : z ∈ tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          rw [hz_eq_x']; exact hx'_in_supp_α
        have hz_in_K : z ∈ crossChartCompact (I := I) (M := M) γ α :=
          ⟨hz_in_supp_γ, hz_in_supp_α⟩
        rw [hempty] at hz_in_K
        exact Set.notMem_empty z hz_in_K
  rw [h_pushed_zero]
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) γ)]
  exact zero_le _

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
