import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBinding
import DifferentialGeometry.Geometry.Collapse.StrongEdgeRiemannian

/-!
# LFR44 item 2 on the completed interiors, regional tail form (lane BFAM-ZD)

External review 53 §4.2 (A-D, (BD)): the boundary analogue of `exists_strong_edge_density_tail_FAM3`
(the closed template, `LocalChartPacketsC14DensityProducer`). `exists_strong_edge_density_riemannian`
holds on any complete σ-compact Riemannian manifold; its collapsed-model hypothesis is discharged on
the completed interior `(W°, d_ĝ)` by the regional LC09 `model_completion_BDRY5` (G15 + first-hit
witness + BSA06's normalized buffer) at every point with `D > 5`, at the model tolerance
`σ = min a₀ (1/2)` chosen from `Δ, β₂, s` only.

`exists_strong_edge_density_boundary_BFZD`: for `Δ, β₂, s` there are a rank-one threshold
`bD βE` (a function of the strong quality), a volume threshold `wD` and a length `LD` such that for
every completion `ĝ` (complete, `= g°` on `{D ≥ 4}`, `≥ g°`), every original scale `ρ` with BCP04.a
at `n`, `8 LD ≤ n`, `16 ≤ n`, the LC02 lower bound at `w < wD`, BSA06's normalized buffer of radius
`n/4`, a `Λ`-Lipschitz bound for `g` with `Λ < (10⁶Δ)⁻¹`, every strong quality `βE < 1/100`, every
`β` with `β 2 = β₂`, `β 1 < bD βE`, and every nonslim one-stratum point `p` of `(W°, ρ ∘ val)` with
`D(p) > 5`: every weak edge `q` (qualities `< 10⁻⁸`) with `d(q, p) < 10Δρ(p)` has a strong edge `a`
(quality `βE, s`) with `d(q, a) < ρ(a)`. In the boundary producer `wD` is folded into the volume
threshold `w₀` (before `b`), `bD b` into the rank-one threshold `b₀` (after `b`), `8 LD ≤ n` into
the tail.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **LFR44 item 2 on the completed interiors** (regional tail form of (BD); lane BFAM-ZD). The
density thresholds of `exists_strong_edge_density_riemannian` with the collapsed model of
`model_completion_BDRY5` at the points with `D > 5`. See the module docstring. -/
theorem exists_strong_edge_density_boundary_BFZD {Δ β₂ s : ℝ} (hβ₂ : 0 < β₂)
    (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ) (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ bD : ℝ → ℝ, (∀ βE : ℝ, 0 < βE → βE < 1 / 100 → 0 < bD βE) ∧
      ∃ wD : ℝ, 0 < wD ∧ ∃ LD : ℝ, 4 ≤ LD ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
        ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
        (∀ p, 0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / ρ p) →
        8 * LD ≤ n → 16 ≤ n → ∀ {w : ℝ}, 0 < w → w < wD →
        (∀ p, firstVolumeScale g p w / 2 < ρ p) →
        (∀ p : W.Carrier,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
              (-((n / 4) ^ 2)⁻¹)) →
        ∀ {Λ : ℝ}, (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤
          ENNReal.ofReal Λ * riemannianEDistOf g x y) → Λ < 1 / (1000000 * Δ) →
        ∀ βE : ℝ, 0 < βE → βE < 1 / 100 → ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < bD βE →
        ∀ p : W.pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary W g p →
        @scaledSplittingStratum.{0, 0} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
          (fun x => ρ x) (fun x => hρ x) β 1 p →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) (WithLp 2 (ℝ × Z))
            ((inducedMetricSpace ĝ).rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
            (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
        ∀ (b' s' : ℝ) (q : W.pieceInterior ⊤), b' < 1 / 100000000 → s' < 1 / 100000000 →
          @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s' →
          @dist (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toDist q p < 10 * Δ * ρ p →
          ∃ a : W.pieceInterior ⊤, @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
              ((inducedMetricSpace ĝ).rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ βE s ∧
            @dist (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toDist q a < ρ a := by
  obtain ⟨a₀, ha₀, hpar⟩ := exists_strong_edge_density_riemannian.{0, 0, 0, 0}
    (I := 𝓘(ℝ, E3)) hβ₂ hβ₂small hΔ hs hssmall
  choose! bD hbD hdata using hpar
  obtain ⟨wD, hwD, -, LD, hLD, hmodel⟩ := model_completion_BDRY5.{0} (σ := min a₀ (1 / 2))
    (lt_min ha₀ (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
  refine ⟨bD, hbD, wD, hwD, LD, hLD, ?_⟩
  intro W _ g ĝ hcomp heq hle ρ hρ n hbcp hnL hn16 w hw hww hfirst hsecN Λ hlip hΛ βE hβE hβE' β
    hβ2 hβ1 p hp5 hp hns b' s' q hb' hs' hq hqp
  let _ := inducedMetricSpace ĝ
  have _ : CompleteSpace (W.pieceInterior ⊤) := completeSpace_completion_BDRY2 W ĝ hcomp
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / (1000000 * Δ) := by
    rw [Real.coe_toNNReal']
    exact max_lt hΛ (by positivity)
  obtain ⟨C, mC, c, hcC, -, hdimC, hcompC, hsegC, hf⟩ :=
    hmodel W g ĝ hcomp heq ρ hρ hbcp hnL hn16 hw hww hfirst hsecN p hp5
  let _ := mC
  have _ := hcC
  exact (hdata βE hβE hβE' (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (Real.toNNReal Λ)
    (fun x => ρ x) (fun x => hρ x) (lipschitzWith_comp_val_completion_BDRY5 W g ĝ hle hlip) hΛc β
    hβ2 hβ1 p hp (fun Z _ z hbdd hdiam hne => hns ⟨Z, _, z, hbdd, hdiam, hne⟩) C c
    (min a₀ (1 / 2)) hsegC hdimC hcompC (min_le_left _ _) hf).2 b' s' q hb' hs' hq hqp

end DifferentialGeometry.Geometry.Collapse
