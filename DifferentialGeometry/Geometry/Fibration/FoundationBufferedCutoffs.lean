import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualStageCutoffs
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# FC30, the buffered ambient cutoffs, on the final closed family (E-free form)

Blueprint `master207B.tex`, FC30 (`found:fibration-ambient-cutoffs`, B:2779–2806): for the three
clouds, smooth `ψ_j` on an OPEN neighbourhood of the relevant image, with values in `[0, 1]`; on
`𝓔^{j−1}(M)`, `‖dψ_j‖ ≤ C_j/ρ(p)` at the point indexed by `p`; plateaux equal to one on the
coordinate thresholds `6`, `6Δ`, `6·10⁵Δ` (edge: with the weak-edge height restriction), vanishing
outside `7`, `7Δ`, `7·10⁵Δ`; "the cutoff is constructed using the previous adjusted image and its
quantitative closeness to `𝓔⁰`".

`fc30_row_FCF` states these clauses on `P : LocalChartPacketsC14Z` (the final closed family; the
cutoffs read only the ancestor `P.toLocalChartPackets`) for the ACTUAL cutoffs of the tree, with
`C_j = b_cut = gafCutoffConstant`:

* stage one, `ψ₁` = CFS31's source cutoff (`gaf02_stageOne_sourceCutoff`) on `𝓔⁰(M)`
  (`𝓔⁰ = cgpGlobalMap`), smooth on the whole block space;
* stages two and three, `ψ₂` = CFS23's buffered edge cutoff (`gaf02_stageTwo_cutoff`), smooth on the
  OPEN set `{x_ρ > 0}` which contains the whole segment `[𝓔⁰ p, f p]`, and `ψ₃` = CFS22's slim
  cutoff (`gaf02_stageThree_cutoff`), smooth everywhere, for EVERY previous image `f` with the
  quantitative closeness to `𝓔⁰` of CFS31's boxed contract (`‖f − 𝓔⁰‖ ≤ (4κ/5)ρ` and (ZM) for the
  stage family); the derivative bound holds along the whole segment `[𝓔⁰ p, f p]`, in particular
  at `f p ∈ 𝓔^{j−1}(M)`.

"Vanishing outside threshold 7" is stated in its closed-support form: the image point lies in the
closed support only if the ORIGINAL point lies in the threshold-`7` core (stage one gives `13/2`).

Not in this file (needs the GAF02 chain object `Gaf02Chain`, lane C14-GAF8): the instantiation
`f = g₁, g₂` (the chain's stage outputs) and the clause "closed support inside the open domain of
`P_jπ_j`" (`P_j` is the chain's slot map; `Gaf02Chain.stage_input_mem_tube`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **FC30, the buffered ambient cutoffs** (E-free form, on the final closed family): the three
actual cutoffs `ψ₁` (CFS31 source), `ψ₂` (CFS23 edge), `ψ₃` (CFS22 slim) are smooth on an open
neighbourhood of the relevant image, `[0, 1]`-valued, equal to one on the thresholds `6`, `6Δ`
(with height `< 6Δ`), `6·10⁵Δ`, have closed support only over the threshold-`7`, `7Δ`, `7·10⁵Δ`
cores, and satisfy `‖dψ_j‖ ≤ b_cut/ρ(p)` on the previous image (stage one: on `𝓔⁰(M)`; stages two
and three: along `[𝓔⁰ p, f p]` for every previous image `f` quantitatively close to `𝓔⁰` in the
sense of CFS31's contract). -/
theorem fc30_row_FCF
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) :
    (ContDiff ℝ ∞ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)) ∧
      (∀ z, markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets) z ∈
          Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) →
        markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
          (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
          (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1) ∧
      (∀ p, cgpGlobalMap P.toLocalChartFamily P.zero p ∈
          tsupport (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
            (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)) →
        ∃ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 7) ∧
      ∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
          (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets))
          (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ ≤ gafCutoffConstant / ρ p) ∧
    (∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 4 * gafKappa / 5 * ρ p) →
      (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
        |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) →
      IsOpen {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      ContDiffOn ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      (∀ p, 0 < gafScaleMarker P.toLocalChartFamily P.zero (f p)) ∧
      (∀ z, gafStageTwoCutoff P.toLocalChartFamily P.zero z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
        gafStageTwoCutoff P.toLocalChartFamily P.zero (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < gafScaleMarker P.toLocalChartFamily P.zero
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p) ∧
        ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p)‖ ≤
            gafCutoffConstant / ρ p) ∧
    (∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 4 * gafKappa / 5 * ρ p) →
      (∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
        |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) →
      ContDiff ℝ ∞ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
      (∀ z, gafStageThreeCutoff P.toLocalChartFamily P.zero z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
            6 * (10 ^ 5 * Δ)) →
        gafStageThreeCutoff P.toLocalChartFamily P.zero (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
            7 * (10 ^ 5 * Δ)) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p)‖ ≤
            gafCutoffConstant / ρ p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := gaf02_stageOne_sourceCutoff P.toLocalChartPackets hΛ hΔ hμ hτ
    hLΛ hLmax he hT hσs hσs1
  refine ⟨⟨h1, h2, h3, fun p hp => ?_, h5⟩, fun f hpert hZM => ?_, fun f hpert hZM => ?_⟩
  · obtain ⟨j, hj, hη⟩ := h4 p hp
    exact ⟨j, hj, hη.trans_lt (by norm_num)⟩
  · obtain ⟨k1, k2, k3, k4, k5⟩ := gaf02_stageTwo_cutoff P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ
      hLmax he hT hσs hσs1 f hpert hZM
    refine ⟨isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous,
      k1, fun p => ?_, k2, k3, k4, k5⟩
    have h := (k5 p 1 ⟨zero_le_one, le_rfl⟩).1
    simpa using h
  · exact gaf02_stageThree_cutoff P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f
      hpert hZM

end DifferentialGeometry.Geometry.Collapse
