import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentBSTD1

/-!
# BCP04 and BCP05 on the per-sequence boundary assignment (lane B-BBR-BSA)

Blueprint 207B, BCP04 (B:8443–8615, restricted interior packets and the actual remaining cover)
and BCP05 (B:8617–8676, actual zero balls are disjoint from the cusp collars). Both rows are read
off ONE member output of the per-sequence assignment `exists_boundarySequenceAssignment_BSTD1`
(T3B on the final boundary family `LocalPacketsOnBFRZ`, lane BFAM-ZD; per member at
`δ_{n+1} = boundaryCounterexampleRatio δ₀ (n+1)` and the BCP04.a index `n + 1`).

`bcp04_bcp05_row_BBS`: for every early choice `E` and every standing sequence `S` (BBR03's
sequence below `δStar`) there are ONE zero scale `V`, ONE register `R` over `(E, V)` and ONE tail
`n₀` such that every member `n ≥ n₀` has, on its SAME carrier and labelled boundary (`P.cusp = B`):

* BCP04.a: `(n + 1)·d/(d + 3) < d/ρ(p)` at every point with `d = d(p, ∂M) > 0`;
* the completed interior `(W°, ĝ)` (`ĝ = g` on an open set containing `{d ≥ 4}`, `g ≤ ĝ`) and, for
  every orientation, ONE family `F : LocalPacketsOnBFRZ` on the regions `{d > 10}` (circle, slim,
  strong-edge and zero centres; their eligible covers), `{d ≥ 20}` (the actual four-family cover
  `F.exhaustion`), `{d > 20}`, `{d ≥ 35}` (revised edges) — with its SAME packets, compact supports,
  enclosures, zero witnesses, multiplicity bounds, tenth-radius zero cover of the eligible zero
  stratum, and zero balls that MEET the stratum (centres need not be zero points);
* BCP04's rank region: the splitting ranks of `(W°, ĝ)` and of `(W, g)` agree on `{d > 5}`;
* every per-centre consumer domain of radius `4(2010000 + 2·10⁶Δ + 400V + β₁⁻¹ + b⁻¹)ρ_j` at
  `d(j) > 10` is an actual `g`-ball with the distances of `W`; every zero ball is a `g`-ball;
* BCP05 on the SAME zero family: EITHER the labelled product `T² × [0,1]` (BCP03's exception) OR the
  collection of all `B_i⁺ = e_i{z < 92}` and all selected open zero balls `B_g(z, R_z⁰)` is pairwise
  disjoint (collar–collar, zero–zero, zero–collar), including selected centres that are not zero
  points themselves.

The zero–zero clause is new here (from `F.zero.disjoint` through the `g`-ball identity); everything
else is a projection of the member output.
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

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **BCP04 and BCP05 on the standing tail** (B:8443–8676): ONE zero scale, ONE register and ONE
tail for every early choice and every standing sequence; on each late member, BCP04.a, the
restricted interior family `F : LocalPacketsOnBFRZ` on `{d > 10}`, `{d ≥ 20}` (ranks on `{d > 5}`,
actual `g`-ball domains and zero balls) and, on the SAME zero family, BCP05: the labelled product
OR the pairwise disjointness of all `B_i⁺ = e_i{z < 92}` and all selected zero balls. -/
theorem bcp04_bcp05_row_BBS {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∃ P : BoundaryExportPacket (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
      (cuspTolerance_BCUSP1 (E.β 1) R.βd R.εN),
    P.cusp = S.B n ∧
    ∃ ρ : (S.W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
      -- BCP04.a at the member's index `n + 1`
      (∀ p, 0 < distanceToBoundary (S.W n) (S.g n) p →
        ((n + 1 : ℕ) : ℝ) * (distanceToBoundary (S.W n) (S.g n) p).toReal /
            ((distanceToBoundary (S.W n) (S.g n) p).toReal + 3) <
          (distanceToBoundary (S.W n) (S.g n) p).toReal / ρ p) ∧
      letI := interiorChartedT_BDRY1 (S.W n)
      haveI := interiorManifoldT_BDRY1 (S.W n)
      ∃ _ : ConnectedSpace ((S.W n).pieceInterior ⊤),
      ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤),
      ∃ O : Set ((S.W n).pieceInterior ⊤), IsOpen O ∧
        {x : (S.W n).pieceInterior ⊤ |
          ENNReal.ofReal 4 ≤ distanceToBoundary (S.W n) (S.g n) x} ⊆ O ∧
        (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x) ∧
        (∀ (x : (S.W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
          (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
        letI := inducedMetricSpace ĝ
        ∃ _ : CompleteSpace ((S.W n).pieceInterior ⊤),
        ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤) 3,
        ∃ F : LocalPacketsOnBFRZ ((S.W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
            (fun x => ρ x) (fun x => hρpos x) E.Λ E.β E.Δ E.σs K E.σc E.μ E.b E.s E.b' E.s' E.ε
            E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz
            {x | ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 20 < distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 35 ≤ distanceToBoundary (S.W n) (S.g n) x} oM,
          -- BCP04: the ranks on `{d > 5}`
          (∀ x : (S.W n).pieceInterior ⊤,
            ENNReal.ofReal 5 < distanceToBoundary (S.W n) (S.g n) x →
            scaledSplittingRank.{0, 0} (fun y : (S.W n).pieceInterior ⊤ => ρ y)
                (fun y => hρpos y) E.β x =
              @scaledSplittingRank.{0, 0} (S.W n).Carrier (inducedMetricSpace (S.g n)) ρ hρpos
                E.β x) ∧
          -- BCP04: every per-centre consumer domain is an actual `g`-ball with the distances of `W`
          (∀ j : (S.W n).pieceInterior ⊤,
            ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) j →
            Subtype.val '' Metric.ball j
                (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) =
              riemannianBallOf (S.g n) j.val
                (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) ∧
            ∀ y ∈ Metric.ball j ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
              ∀ z ∈ Metric.ball j
                  ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
                riemannianEDistOf (S.g n) y.val z.val = edist y z) ∧
          (letI := F.instMetricN
          letI := F.instChartedN
          letI := F.instMetricC
          -- BCP04: the zero balls are actual `g`-balls of `W`
          (∀ z (hz : z ∈ F.zero.centres),
            Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
              riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius) ∧
          -- BCP05 (on the SAME zero family): labelled product OR pairwise disjointness
          ((∃ (i j : Fin P.cusp.count), i ≠ j ∧
            ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (S.W n).model (Torus × Icc (0 : ℝ) 1)
              (S.W n).Carrier ∞,
              (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
                ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
          ((∀ i j : Fin P.cusp.count, i ≠ j →
            Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
              ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
          (∀ z (hz : z ∈ F.zero.centres) z' (hz' : z' ∈ F.zero.centres), z ≠ z' →
            Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
              (riemannianBallOf (S.g n) z'.val (F.zero.zero z' hz').radius)) ∧
          ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
            Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
              ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})))) := by
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignment_BSTD1 E S
  refine ⟨V, R, n₀, fun n hn => ?_⟩
  obtain ⟨⟨P, hPB, -, ρ, hρpos, -, -, -, -, -, -, -, -, -, ha, hconn, ĝ, O, hO, hOsub, hOeq, hle,
    hcomp, hF⟩, -⟩ := hR n hn
  refine ⟨P, hPB, ρ, hρpos, ha, hconn, ĝ, O, hO, hOsub, hOeq, hle, hcomp, fun oM => ?_⟩
  obtain ⟨F, hrank, hdom, hzb, -, -, -, hT3⟩ := hF oM
  refine ⟨F, hrank, hdom, hzb, ?_⟩
  rcases hT3 with hprod | ⟨hcoll, hzc, -⟩
  · exact Or.inl hprod
  · refine Or.inr ⟨fun i j hij => (hcoll i j hij).1, fun z hz z' hz' hne => ?_, hzc⟩
    rw [← hzb z hz, ← hzb z' hz']
    let instM : MetricSpace ((S.W n).pieceInterior ⊤) := inducedMetricSpace ĝ
    let instN := F.instMetricN
    let instCh := F.instChartedN
    let instC := F.instMetricC
    exact Set.disjoint_image_of_injective Subtype.val_injective
      (F.zero.disjoint z hz z' hz' hne)

end DifferentialGeometry.Geometry.Collapse
