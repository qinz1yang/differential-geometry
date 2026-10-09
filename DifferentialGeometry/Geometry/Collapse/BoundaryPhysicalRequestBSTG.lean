import DifferentialGeometry.Geometry.Collapse.BoundaryStagedRequestsBSTG
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspPhysical

/-!
# The named request instance for `r∂` (BRegPhysical) in the boundary staged adapter (lane BSTG)

Dispositions of task 61, D61-11 (draft §7.2–7.3): in the per-sequence order
`early ≺ S ≺ V, δ_local ≺ L_max ≺ β∂, ε_N ≺ r∂ ≺ n₀`, the physical scale is chosen last, below
`min{1/(1000L), 10⁻⁴, 1/(100H∂), ϑ²/(4·10⁸(12L+1000)), 10⁻⁶/(20(c₃+1))}`
(BRegPhysical, B:10476–10481) and the BCP02 product bound at the buffer `H∂`. Lane BCUSP-1's
`cuspPhysicalScale_BCUSP1 β∂ L H ϑ c₃` is half of that minimum; this file makes it a NAMED
request instance of the staged adapter `C14BdryStagedRequestsBSTG` (lane BSTG G1), with `L = 10⁶Δ`,
`ϑ = min_j ϑ_j` and the stage constant
`c₃` early inputs (fixed before the record) and `β∂`, `H∂` the adapter's own values read after `V`.

* `C14BdryStagedRequestsBSTG.withPhysical_BSTG Rq ϑ c₃`: `Rq` with its `r∂` request intersected
  with `cuspPhysicalScale_BCUSP1 β∂ (10⁶Δ) H∂ ϑ c₃` (applied LAST, after every `inf`, so that `β∂`,
  `H∂` are the final ones: it changes neither `β∂, ε_N` nor `H`).
* `bdryRd_withPhysical_bounds_BSTG`: at every prefix and every `V`, the adapter's `r∂` satisfies all
  five BRegPhysical entries strictly, `20c₃r∂ < 10⁻⁶`, and the product bound
  `r∂ < β∂³/(2000(1+H∂))`.
* consumer `exists_bdry_staged_physical_BSTG`: the staged boundary assignment at the instance — ONE
  prefix; on every boundary sequence the outputs `V, δ`, then `L_max, β∂, ε_N`, then `H∂, r∂` with
  BRegPhysical, and ONE tail carrying T3B_IDX2's per-member conclusion at the member ratio
  `boundaryCounterexampleRatio δ₀ (n+1)` and the certificate premise at `r∂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The BRegPhysical request instance**: the `r∂` request of `Rq` intersected with the late
physical cusp scale `cuspPhysicalScale_BCUSP1 β∂ (10⁶Δ) H∂ ϑ c₃` at the adapter's `β∂, H∂`. -/
def C14BdryStagedRequestsBSTG.withPhysical_BSTG (Rq : C14BdryStagedRequestsBSTG) (ϑ c₃ : ℝ)
    (hϑ : 0 < ϑ) (hc₃ : 0 ≤ c₃) : C14BdryStagedRequestsBSTG :=
  { Rq with
    rd := fun P V a e => min (Rq.rd P V a e)
      (cuspPhysicalScale_BCUSP1 (bdryβd_BSTG Rq P V) (1000000 * P.Δ) (bdryH_BSTG Rq P V) ϑ c₃)
    rd_pos := fun P V a e => lt_min (Rq.rd_pos P V a e)
      (cuspPhysicalScale_pos_BCUSP1 (bdryβd_pos_BSTG Rq P V) (by linarith [P.Δ_gt6])
        (one_pos.trans_le (one_le_bdryH_BSTG Rq P V)) hϑ hc₃) }

/-- The instance's `r∂` lies below the late physical cusp scale. -/
theorem bdryRd_withPhysical_le_BSTG (Rq : C14BdryStagedRequestsBSTG) {ϑ c₃ : ℝ} (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) (P : C14PreFinal) (V : ℝ) :
    bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V ≤
      cuspPhysicalScale_BCUSP1 (bdryβd_BSTG Rq P V) (1000000 * P.Δ) (bdryH_BSTG Rq P V) ϑ c₃ :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- **BRegPhysical for the instance's `r∂`** (B:10476–10484), with `L = 10⁶Δ`: the five entries
strictly, `ε∂ = 20c₃r∂ < 10⁻⁶`, and BCP02's product bound at `H∂`. -/
theorem bdryRd_withPhysical_bounds_BSTG (Rq : C14BdryStagedRequestsBSTG) {ϑ c₃ : ℝ} (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) (P : C14PreFinal) (V : ℝ) :
    bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / (1000 * (1000000 * P.Δ)) ∧
      bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / 10000 ∧
      100 * bdryH_BSTG Rq P V * bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 ∧
      bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V <
        ϑ ^ 2 / (4 * 10 ^ 8 * (12 * (1000000 * P.Δ) + 1000)) ∧
      bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / 1000000 / (20 * (c₃ + 1)) ∧
      20 * c₃ * bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / 1000000 ∧
      bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V <
        bdryβd_BSTG Rq P V ^ 3 / (2000 * (1 + bdryH_BSTG Rq P V)) := by
  have hβ := bdryβd_pos_BSTG Rq P V
  have hL : 0 < 1000000 * P.Δ := by linarith [P.Δ_gt6]
  have hH : 0 < bdryH_BSTG Rq P V := one_pos.trans_le (one_le_bdryH_BSTG Rq P V)
  have hs := cuspPhysicalScale_pos_BCUSP1 hβ hL hH hϑ hc₃
  have hle := bdryRd_withPhysical_le_BSTG Rq hϑ hc₃ P V
  have hr := bdryRd_pos_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := two_mul_cuspPhysicalScale_le_BCUSP1 (bdryβd_BSTG Rq P V)
    (1000000 * P.Δ) (bdryH_BSTG Rq P V) ϑ c₃
  have heps := cuspPhysicalScale_eps_BCUSP1 hβ hL hH hϑ hc₃
  refine ⟨by linarith, by linarith,
    bdryH_mul_bdryRd_lt_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V, by linarith, by linarith,
    ?_, by linarith⟩
  calc 20 * c₃ * bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V
      ≤ 20 * c₃ * cuspPhysicalScale_BCUSP1 (bdryβd_BSTG Rq P V) (1000000 * P.Δ)
          (bdryH_BSTG Rq P V) ϑ c₃ := mul_le_mul_of_nonneg_left hle (by positivity)
    _ < 1 / 1000000 := heps

/-- **Consumer: the staged boundary assignment at the BRegPhysical instance** (D61-11's order
`early ≺ S ≺ V, δ ≺ L_max ≺ β∂, ε_N ≺ r∂ ≺ n₀`): for the early tolerances `t`, the boundary
tolerances `ϑ₃, ϑ > 0`, the stage constant `c₃ ≥ 0` and every boundary request record `Rq`, ONE
admissible prefix such that on every boundary sequence at the member ratios
`boundaryCounterexampleRatio δ₀ (n+1)`, with the producer's outputs `V ≥ T`, `δ < δ'`, the adapter's
`L_max, β∂, ε_N, H∂` and the instance's `r∂`: `r∂` satisfies BRegPhysical with `L = 10⁶Δ` and the
product bound at `H∂`, and ONE tail carries T3B_IDX2's per-member conclusion and the certificate
premise at `r∂`. -/
theorem exists_bdry_staged_physical_BSTG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧ ∀ (t : C14Tol) (ϑ₃ ϑ c₃ : ℝ), 0 < ϑ₃ → ∀ (hϑ : 0 < ϑ)
      (hc₃ : 0 ≤ c₃) (Rq : C14BdryStagedRequestsBSTG),
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toSTG.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
      P.w < boundaryVolumeCap ∧ P.vs < ϑ₃ / 4 ∧
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        400 * V < c14Lmax Rq.toSTG.toC14 P V ∧ bdryβd_BSTG Rq P V < P.β 1 ∧
        bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / (1000 * (1000000 * P.Δ)) ∧
        bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / 10000 ∧
        100 * bdryH_BSTG Rq P V * bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 ∧
        bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V <
          ϑ ^ 2 / (4 * 10 ^ 8 * (12 * (1000000 * P.Δ) + 1000)) ∧
        bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V < 1 / 1000000 / (20 * (c₃ + 1)) ∧
        bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V <
          bdryβd_BSTG Rq P V ^ 3 / (2000 * (1 + bdryH_BSTG Rq P V)) ∧
        ∀ᶠ n in atTop,
          BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
            ((n + 1 : ℕ) : ℝ) P.Λ P.w P.β P.Δ P.σs P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc
            (c14Lmax Rq.toSTG.toC14 P V) P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz
            (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V) ∧
          1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
            P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3) *
              min (1 / 2) (bdryRd_BSTG (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃) P V / 4) ^ 2 := by
  obtain ⟨δStar, hδStar, h⟩ := exists_bdry_staged_assignment_BSTG K hK A hA
  refine ⟨δStar, hδStar, fun t ϑ₃ ϑ c₃ hϑ₃ hϑ hc₃ Rq => ?_⟩
  obtain ⟨P, hPt, hM, h3, hw, hvs, hP⟩ := h t ϑ₃ hϑ₃ (Rq.withPhysical_BSTG ϑ c₃ hϑ hc₃)
  refine ⟨P, hPt, hM, h3, hw, hvs, ?_⟩
  intro δ₀ hδ₀ hδ₀S W _ g B hcoll hder
  obtain ⟨V, hTV, δ, hδ, hδδ', h400, -, -, hβd, -, -, -, hev⟩ := hP δ₀ hδ₀ hδ₀S W g B hcoll hder
  obtain ⟨b1, b2, b3, b4, b5, -, b7⟩ := bdryRd_withPhysical_bounds_BSTG Rq hϑ hc₃ P V
  exact ⟨V, hTV, δ, hδ, hδδ', h400, hβd, b1, b2, b3, b4, b5, b7, hev⟩

end DifferentialGeometry.Geometry.Collapse
