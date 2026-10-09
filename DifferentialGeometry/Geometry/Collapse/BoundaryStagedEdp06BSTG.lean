import DifferentialGeometry.Geometry.Collapse.BoundaryStagedRequestsBSTG
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarBFR
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConorm

/-!
# EDP06's collar step through the staged boundary assignment (lane BSTG, consumer)

Consumer of `exists_bdry_staged_assignment_BSTG` (pattern: lane C14-STG's
`exists_c14d_staged_edp06_STG`). EDP06's collar → circle step on the boundary family needs the
parameter facts `3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1` (its no-three input is the field `rank_le_two`
of `LocalPacketsOnBFR`, lane BCG-5); the staged boundary assignment provides them at its ONE prefix,
and on the same tail every member carries T3B_IDX2's per-member conclusion
`BoundaryPacketsOutBFR_BQ`, whose family `F : LocalPacketsOnBFR … P.Λ P.β P.Δ …` is an instance of
the universally quantified family below.

* `exists_bdry_staged_edp06_BSTG`: for every boundary request record, ONE admissible prefix with
  `3βc ≤ β 2`, `w < ω₃/4`, `vs < ϑ₃/4` such that on every boundary sequence every late member
  satisfies `BoundaryPacketsOutBFR_BQ` at the prefix's parameters and EVERY family
  `LocalPacketsOnBFR` at these parameters (on `(W n)°` with T3B_IDX2's level sets) has: every point
  of EDP06's band at a revised edge centre (`d(x, j) < 100Δρ(j)`, `|η_j(x)| < 4.01Δ`,
  `|F_s(x)/ρ(x) − 4Δ| < h ≤ 1/1000`) is two-stratum, lies in `{D > 10}` and in a circle chart with
  `‖η_a(x)‖ < 2(1 + γ)`.
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **EDP06's collar → circle step through ONE staged boundary assignment** (lane BSTG): there is
`δStar > 0` such that for the early tolerances `t`, every `ϑ₃ > 0` and every boundary request
record `Rq` there is ONE admissible prefix `P` meeting `Rq`'s interior requests with `3βc ≤ β 2`,
`w < ω₃/4`, `vs < ϑ₃/4` such that on every boundary sequence (BBR03's ratios, `δ₀ ≤ δStar`), with
the outputs `V ≥ T`, `δ < δ'`, every late member satisfies T3B_IDX2's per-member conclusion at the
prefix's parameters, and every family `LocalPacketsOnBFR` at these parameters (in particular the
member's own family) has EDP06's collar step at every revised edge centre. -/
theorem exists_bdry_staged_edp06_BSTG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧ ∀ (t : C14Tol) (ϑ₃ : ℝ), 0 < ϑ₃ → ∀ Rq : C14BdryStagedRequestsBSTG,
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toSTG.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
      P.w < boundaryVolumeCap ∧ P.vs < ϑ₃ / 4 ∧
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        ∀ᶠ n in atTop,
          BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
            ((n + 1 : ℕ) : ℝ) P.Λ P.w P.β P.Δ P.σs P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc
            (c14Lmax Rq.toSTG.toC14 P V) P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz
            (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V) ∧
          letI := interiorChartedT_BDRY1 (W n)
          haveI := interiorManifoldT_BDRY1 (W n)
          ∀ (ρ : (W n).Carrier → ℝ) (hρpos : ∀ p, 0 < ρ p)
            (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤)),
          letI := inducedMetricSpace ĝ
          ∀ (hXc : CompleteSpace ((W n).pieceInterior ⊤))
            (F : LocalPacketsOnBFR ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
              (fun x => ρ x) (fun x => hρpos x) P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s' P.ε
              P.γc P.βc (c14Lmax Rq.toSTG.toC14 P V) P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz
              {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
              {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x}
              {x | ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x}
              {x | ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x})
            (h : ℝ), h ≤ 1 / 1000 →
          ∀ (j : (W n).pieceInterior ⊤) (hj : j ∈ F.edgeB.centres) (x : (W n).pieceInterior ⊤),
            dist x j < 100 * P.Δ * ρ j →
            (let c := F.edgeB.chart j hj;
              let hMc : CompleteSpace ((W n).pieceInterior ⊤) := hXc;
              letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
              letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
              letI : IsContinuousRiemannianBundle E3
                  (fun x : (W n).pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
                radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
              letI : IsRiemannianManifold 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) :=
                radialScaledManifold (m := inducedMetricSpace ĝ) ĝ
                  (inducedMetricSpace_hmetric ĝ) (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
              letI : CompleteSpace ((W n).pieceInterior ⊤) :=
                ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹
                  (inv_pos.mpr (hρpos j))).mpr hMc;
              |c.coord x| < 401 / 100 * P.Δ) →
            |F.edgeB.smoothing x / ρ x - 4 * P.Δ| < h →
            x ∈ scaledSplittingStratum.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                (fun y => hρpos y) P.β 2 ∧
              ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x ∧
              ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
                dist x a < 2 * ρ a ∧
                (let c := F.circle.chart a ha;
                  letI := (inducedMetricSpace ĝ).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a));
                  ‖c.coord x‖ < 2 * (1 + P.γ)) := by
  obtain ⟨δStar, hδStar, hall⟩ := exists_bdry_staged_assignment_BSTG K hK A hA
  refine ⟨δStar, hδStar, fun t ϑ₃ hϑ₃ Rq => ?_⟩
  obtain ⟨P, hPt, hM, h3, hw, hvs, hP⟩ := hall t ϑ₃ hϑ₃ Rq
  refine ⟨P, hPt, hM, h3, hw, hvs, ?_⟩
  intro δ₀ hδ₀ hδ₀S W _ g B hcoll hder
  obtain ⟨V, hTV, δ, hδ, hδδ', -, -, -, -, -, -, -, hev⟩ := hP δ₀ hδ₀ hδ₀S W g B hcoll hder
  have hβ2 : P.β 2 < 1 := by
    rw [P.β_two]
    exact P.β₂_lt.trans (by norm_num)
  have hΔ : 1 ≤ P.Δ := by linarith [P.Δ_gt6]
  refine ⟨V, hTV, δ, hδ, hδδ', hev.mono fun n hn => ⟨hn.1, ?_⟩⟩
  intro ρ hρpos ĝ hXc F h hh j hj x hx hη ht
  let instM_BSTG : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace ĝ
  obtain ⟨hη', hF1, hF2⟩ := edp06_band_mem_band_EDP6 hΔ hh hη ht
  exact F.edgeB_collar_circle_IDX2 h3 hβ2 P.γ_pos.le hΔ hj hx hη' hF1 hF2

end DifferentialGeometry.Geometry.Collapse
