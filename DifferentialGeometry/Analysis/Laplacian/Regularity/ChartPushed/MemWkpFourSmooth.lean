import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.DerivedDataCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.TwiceDerivedH2Interior
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpThreeSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Final assembly: chart-`H⁴` regularity of the chart-pushed function

For a closed Riemannian manifold `(M, g)` and an element
`u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed POU-cut
representative

  `chartPushed POU α (H1ComplToLp g u_h).coeFn`

lies in `MemWkp 4 2 (chartTargetEuclid α)`, conditioned on a per-pair
hypothesis of the twice-differentiated chart-bilinear variational identity
(one identity per ordered pair `(l₁, l₂)`).

## Strategy

By two applications of `MemWkp_succ`:

* `MemWkp 4 2 u Ω ↔ MemW1p 2 u Ω ∧ ∀ i, MemWkp 3 2 (chosen weak i-partial of u) Ω`
* `MemWkp 3 2 v Ω ↔ MemW1p 2 v Ω ∧ ∀ j, MemWkp 2 2 (chosen weak j-partial of v) Ω`

The chart-`H³` regularity of the chart-pushed function and of each chosen
first weak partial follows unconditionally from
`chartPushed_memWkp_three_two_of_laplacianDomainPow_two`. The remaining
piece is the chart-`H²` regularity of each chosen second mixed weak partial
on the full chart target.

The chart-`H²` regularity of the chosen second mixed weak partial on a
precompact open subdomain `Ω''` of the chart target is given by
`twiceDerivedChartBilinear_memWkp_two_two_interior`. This module extends
the interior regularity to the full chart target by multiplying the chosen
second mixed weak partial against a smooth cutoff supported inside `Ω''`
and equal to `1` on a neighborhood of the POU support
`chartImagePOUTsupport α`, then transferring the membership via
`MemWkp.extend_zero` and `MemWkp_congr_ae`, exactly as in the chart-`H³`
template.

## Main results

* `chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity` —
  chart-`H²` of the chosen second mixed weak partial on the full chart
  target, hypothesis-bearing on the twice-differentiated variational
  identity for the fixed pair `(l₁, l₂)`.
* `chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities` —
  chart-`H³` of each chosen first weak partial on the full chart target,
  hypothesis-bearing on the family of twice-differentiated identities for
  all pairs `(l₁, l₂)`.
* `chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities` —
  chart-`H⁴` of the chart-pushed function on the full chart target,
  hypothesis-bearing on the family of twice-differentiated identities.
* `chartSideH2kBridge_two_of_twice_diff_identities` — discharge of the
  per-chart `ChartSideH2kBridge g 2` from the family of twice-differentiated
  identities (one per chart point `α` and ordered pair `(l₁, l₂)`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpFourSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataCanonical
open DifferentialGeometry.Analysis.Laplacian.TwiceDerivedChartBilinearH2Interior
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThreeSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Cutoff-based extension of `MemWkp k 2` from a precompact open
subdomain.** A function in `MemWkp k 2` of an open precompact `Ω' ⊆ Ω`
that vanishes a.e. on `Ω \ K` (for some compact `K ⊆ Ω'`) lies in
`MemWkp k 2 Ω`.

The proof multiplies by a smooth cutoff equal to `1` on a neighborhood of
`K` and supported inside `Ω'`, applies `MemWkp.smul_smooth_bounded` to
obtain the product in `MemWkp k 2 Ω'`, extends by zero via
`MemWkp.extend_zero` to `Ω`, and transfers back to the original function
via `MemWkp_congr_ae`. -/
private theorem MemWkp_two_extend_via_cutoff_aux
    (k : ℕ)
    {Ω Ω' K : Set EuclN}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hΩ'_in_Ω : Ω' ⊆ Ω)
    (hK_compact : IsCompact K) (hK_in_Ω' : K ⊆ Ω')
    {u : EuclN → ℝ}
    (hu_local : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω')
    (hu_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ K)),
      u y = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact hΩ'_open hK_in_Ω'
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hη_smooth hη_compact_support k
  have h_eta_u_in_Ω' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω' :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    have hx_ne : η x * u x ≠ 0 := hx
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  have h_eta_u_in_Ω : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set U_K : Set EuclN := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict Ω] u := by
    have h_eq_on_U_K : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict U_K] u := by
      refine (ae_restrict_iff' hU_K_meas).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx_eta : η x = 1 := hη_one_on_cthick x hx
      change η x * u x = u x
      rw [hx_eta]; ring
    have h_diff_meas : MeasurableSet (Ω \ U_K) := hΩ_meas.diff hU_K_meas
    have h_K_in_U_K : Ω \ U_K ⊆ Ω \ K := by
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hK_in_U_K hxK)⟩
    have hu_ae_zero_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ U_K)),
        u y = 0 := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ U_K) ≪
          (volume : Measure EuclN).restrict (Ω \ K) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_K_in_U_K le_rfl)
      exact h_abs.ae_le hu_ae_zero
    have h_eq_on_diff : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict (Ω \ U_K)] u := by
      filter_upwards [hu_ae_zero_diff] with x hx
      rw [hx]; ring
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

/-- **Chart-`H²` of the chosen second mixed weak partial on the full chart
target.**

For `u_h ∈ laplacianDomainPow g 2`, fixed coordinate directions `l₁, l₂`,
and the twice-differentiated chart-bilinear variational identity for that
pair supplied as a hypothesis, the chosen second mixed weak partial
`chosenSecondPartialChartPushedU g α u_h l₁ l₂` lies in
`MemWkp 2 2 (chartTargetEuclid α)`.

The proof obtains the chart-`H²` regularity on a precompact open
neighborhood `Ω''` of `chartImagePOUTsupport α` from
`twiceDerivedChartBilinear_memWkp_two_two_interior`, and promotes it to
the entire chart target via the cutoff-based extension lemma, using the
ae-vanishing of the chosen second mixed partial off
`chartImagePOUTsupport α`. -/
theorem chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))
        + (∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
            ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
          ∂(volume : Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenSecondPartialChartPushedU
        (I := I) (M := M) g α u_h l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨Ω'', hΩ''_open, hK_α_in_Ω'', hΩ''_compact_closure,
    h_closureΩ''_in_chart, h_memWkp22_Ω''⟩ :=
    twiceDerivedChartBilinear_memWkp_two_two_interior
      (I := I) (M := M) g α hu_h l₁ l₂ h_twice_identity
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    subset_trans subset_closure h_closureΩ''_in_chart
  have h_ae_zero_off_K_α :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α)),
        chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h l₁ l₂ y = 0 :=
    chosenSecondPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α hu_h l₁ l₂
  exact MemWkp_two_extend_via_cutoff_aux (E := E) 2
    h_chart_open hΩ''_open hΩ''_in_chart hK_α_compact hK_α_in_Ω''
    h_memWkp22_Ω'' h_ae_zero_off_K_α

/-- **Chart-`H³` of each chosen first weak partial on the full chart target.**

For `u_h ∈ laplacianDomainPow g 2` and the family of twice-differentiated
chart-bilinear variational identities (one per ordered pair `(l₁, l₂)`),
the canonical chosen first weak partial in any direction `i` of the
chart-pushed POU-cut representative lies in
`MemWkp 3 2 (chartTargetEuclid α)`.

The proof uses `MemWkp_succ` at order `3`: chart-`H³` of the first weak
partial decomposes into `MemW1p 2` of the first weak partial (unconditional
via `chartPushedChosenFirstPartial_memW1p_two`) and chart-`H²` of every
chosen second mixed weak partial (the per-pair hypothesis-bearing result
above). -/
theorem chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(volume : Measure EuclN))
    (l₁ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨chartPushedChosenFirstPartial_memW1p_two
    (I := I) (M := M) g α hu_h l₁, ?_⟩
  intro l₂
  have h_chosenSecond :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chosenSecondPartialChartPushedU_memWkp_two_two_of_twice_diff_identity
      (I := I) (M := M) g α hu_h l₁ l₂ (h_twice_identities l₁ l₂)
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
    (chartTargetEuclid (I := I) (M := M) α)
  exact h_chosenSecond

/-- **Chart-`H⁴` of the chart-pushed function on the full chart target.**

For `u_h ∈ laplacianDomainPow g 2` and the family of twice-differentiated
chart-bilinear variational identities (one per ordered pair `(l₁, l₂)`),
the canonical chart-pushed POU-cut representative
`chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp 4 2 (chartTargetEuclid α)`.

The proof uses `MemWkp_succ` at order `4`: chart-`H⁴` decomposes into
`MemW1p 2` of the chart-pushed function (unconditional via
`chartPushed_memW1p_two_of_laplacianDomainPow_two`) and chart-`H³` of
every chosen first weak partial (the per-pair hypothesis-bearing result
above). -/
theorem chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(volume : Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  refine ⟨chartPushed_memW1p_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h, ?_⟩
  intro l₁
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 3 2
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
    (chartTargetEuclid (I := I) (M := M) α)
  exact chartPushedChosenFirstPartial_memWkp_three_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h h_twice_identities l₁

/-- **Discharge of `ChartSideH2kBridge g 2` for the canonical function
representative.**

For `u_h ∈ laplacianDomainPow g 2` and the family of twice-differentiated
chart-bilinear variational identities (now indexed by chart points
`α : M` and ordered pairs `(l₁, l₂)`), the predicate
`ChartSideH2kBridge g 2 ((H1ComplToLp g u_h).coeFn)` holds.

Combined with `laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge`,
this discharges the manifold-level `MemWkpChart g 4 2` for the canonical
function representative, with a finite chart-based norm. Equivalently, by
`chartSideH4Bridge_of_chartSideH2kBridge_two`, it discharges the
`ChartSideH4Bridge` predicate from the `H⁴` infrastructure. -/
theorem chartSideH2kBridge_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ α : M, ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(volume : Measure EuclN)) :
    ChartSideH2kBridge (I := I) (M := M) g 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq]
  exact chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h (h_twice_identities α)

/-- **Manifold-level `MemWkpChart g 4 2` for `u_h ∈ laplacianDomainPow g 2`.**

Combining `chartSideH2kBridge_two_of_twice_diff_identities` with
`laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge`, the canonical
function representative of `u_h ∈ laplacianDomainPow g 2` lies in
`MemWkpChart g 4 2` with a finite chart-based norm, given the family of
twice-differentiated chart-bilinear variational identities. -/
theorem laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_twice_identities :
      ∀ α : M, ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
        ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
          (∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN))
          + (∫ y in chartTargetEuclid (I := I) (M := M) α,
              densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
            ∂(volume : Measure EuclN)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_bridge := chartSideH2kBridge_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h h_twice_identities
  have h := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 2 hu_h h_bridge
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq] at h
  exact h

end ChartPushedMemWkpFourSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
