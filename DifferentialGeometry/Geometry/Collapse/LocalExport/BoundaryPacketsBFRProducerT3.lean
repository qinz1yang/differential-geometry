import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRProducerV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspSplitting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspTaylor
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspPhysical

/-!
# T3B on the extended final boundary family (lane BCG-5)

`lc88_boundary_packets_BFR_BCG5` is lane BCG-3's T3B (`lc88_boundary_packets_BF_BCG3`; same
statement, same tail, same packet, same proof) re-run on the output of T2B v2 on the extended family
(`eventually_nonempty_boundaryPacketsBFR_BCG5`): the ONE family is `F : LocalPacketsOnBFR …`, whose
new field `rank_le_two` gives rank `≤ 2` of the scale on `U₁ = {D > 10}` (producer gap found by lane
BCG-4: no 3-splitting at the collar points of the revised edge charts). No conjunction of two
existence statements: the rank bound is a field of the same `F`. Every other clause is verbatim.
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

/-- **T3B on the extended final boundary family** (lane BCG-5): BCG-3's T3B with
`F : LocalPacketsOnBFR …` (new field `rank_le_two` on `{D > 10}`). Text of BCG-3:
(reviews 51/52;
ONE producer, ONE family). T2B v2's prefix with the cusp requests `β∂, εN` at T3's tolerance
slot. On one tail: the export packet `P` at the requested tolerance with the supplied labels,
`δ_n ≤ β∂²/1000`, ONE scale `ρ` (T2B's clauses, collar smallness on `P.cusp`, BCUSP-1's late
certificate and cusp certificates B3–B5 for the same `P` and `ρ`), BCP04.a at `n`, ONE completion
`ĝ`, ONE `F : LocalPacketsOnBF …` with every clause of T2B v2, and T3's product alternative OR
separation. -/
theorem lc88_boundary_packets_BFR_BCG5
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → ∀ᶠ n in atTop,
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n)
          (cuspTolerance_BCUSP1 (β 1) βd εN),
        P.cusp = B n ∧ boundaryCounterexampleRatio δ₀ n ≤ βd ^ 2 / 1000 ∧
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          -- BCUSP-1: the late `ρ` certificate and the cusp certificates B3–B5 on the SAME `P`, `ρ`
          (∀ r : ℝ, 0 < r →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
            ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
              ρ ((P.cusp.collar i).toFun q) < r) ∧
          (∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 →
            ∀ (i : Fin P.cusp.count) (q₀ : CuspHalfSpace), 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
              5 ≤ P.height i ((P.cusp.collar i).toFun q₀) →
              P.height i ((P.cusp.collar i).toFun q₀) ≤ 95 →
              letI := (inducedMetricSpace (g n)).rescale (ρ ((P.cusp.collar i).toFun q₀))⁻¹
                (inv_pos.mpr (hρpos _));
              letI := (inducedMetricSpace (P.cusp.collar i).cusp.torusMetric).rescale
                ((ρ ((P.cusp.collar i).toFun q₀))⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
                (mul_pos (inv_pos.mpr (hρpos _)) (Real.exp_pos _));
              ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((P.cusp.collar i).toFun q₀)
                  (WithLp.toLp 2 ((0 : ℝ), t₀)) βd,
                (∀ x, (f.toFun x).fst = (P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) /
                  ρ ((P.cusp.collar i).toFun q₀)) ∧
                ∀ x, (ρ ((P.cusp.collar i).toFun q₀))⁻¹ *
                    (riemannianEDistOf (g n) x ((P.cusp.collar i).toFun q₀)).toReal ≤ βd⁻¹ + βd →
                  (f.toFun x).snd = (invFunOn (P.cusp.collar i).toFun cuspDomain x).1) ∧
          (∀ (i : Fin P.cusp.count) (p : CuspHalfSpace), p ∈ cuspDomain → 2 ≤ p.2.val 0 →
            p.2.val 0 ≤ 98 →
            (∀ u : TangentSpace (W n).model ((P.cusp.collar i).toFun p),
              |mvfderiv (W n).model (P.height i) ((P.cusp.collar i).toFun p) u| ≤
                (1 + 2 * (εN + βd ^ 2 / 1000)) *
                  Real.sqrt ((g n).inner ((P.cusp.collar i).toFun p) u u)) ∧
            ∀ (R : ℝ), 0 < R → ∀ u w : TangentSpace (W n).model ((P.cusp.collar i).toFun p),
              R⁻¹ * |(CovariantDerivative.trivial (W n).model (W n).Carrier ℝ).hessian
                  (LeviCivita (g n)) (P.height i) ((P.cusp.collar i).toFun p) u w| ≤
                2 * R * (R⁻¹ * Real.sqrt ((g n).inner ((P.cusp.collar i).toFun p) u u)) *
                  (R⁻¹ * Real.sqrt ((g n).inner ((P.cusp.collar i).toFun p) w w))) ∧
          (∀ H : ℝ, 0 < H →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (H⁻¹ / 4) ^ 2 →
          ∀ (i : Fin P.cusp.count) (pa p : CuspHalfSpace), pa.2.val 0 ≤ 96 → 19 ≤ p.2.val 0 →
            p.2.val 0 ≤ 91 →
          ∀ (a : ℝ) (c : ℝ → (W n).Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ H →
            (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) (W n).model 2 c t) →
            (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt (g n) c t) →
            (∀ t ∈ Icc x₀ (x₀ + ℓ), (g n).inner (c t)
              (mfderiv 𝓘(ℝ, ℝ) (W n).model c t ((NormedSpace.fromTangentSpace t).symm 1))
              (mfderiv 𝓘(ℝ, ℝ) (W n).model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤
                ρ ((P.cusp.collar i).toFun pa) ^ 2) →
            (P.cusp.collar i).toFun p = c x₀ →
            (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, (P.cusp.collar i).toFun q = c t ∧
              2 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 98) ∧
            |deriv (fun t => (P.height i (c t) - a) / ρ ((P.cusp.collar i).toFun pa)) x₀ -
              ((P.height i (c (x₀ + ℓ)) - a) / ρ ((P.cusp.collar i).toFun pa) -
                (P.height i (c x₀) - a) / ρ ((P.cusp.collar i).toFun pa)) / ℓ| ≤
              ρ ((P.cusp.collar i).toFun pa) * ℓ) ∧
          (∀ L H ϑ c₃ : ℝ, 0 < L → 0 < H → 0 < ϑ → 0 ≤ c₃ →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
                min (1 / 2) (cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ / 4) ^ 2 →
            (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
              ρ ((P.cusp.collar i).toFun q) < cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
              ρ ((P.cusp.collar i).toFun q) ≤ βd ^ 3 / (2000 * (1 + H)) ∧
              ρ ((P.cusp.collar i).toFun q) * H < 1 / 100 ∧
              2 * ρ ((P.cusp.collar i).toFun q) * (12 * L + 1000) < ϑ ^ 2 / 10 ^ 8 ∧
              20 * c₃ * ρ ((P.cusp.collar i).toFun q) < 1 / 1000000) ∧
            ∀ (C : ℝ) (p : (W n).Carrier) (b : Fin P.cusp.count), C ≤ 95 / 100 * L →
              Λ * C ≤ 1 / 2 →
              (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block b),
                riemannianEDistOf (g n) p x < ENNReal.ofReal (C * ρ p)) →
              ρ p < 2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
              ∀ y, riemannianEDistOf (g n) p y < ENNReal.ofReal (C * ρ p) →
                ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧
                  q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91) ∧
          (∀ p, 0 < distanceToBoundary (W n) (g n) p →
            (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
                ((distanceToBoundary (W n) (g n) p).toReal + 3) <
              (distanceToBoundary (W n) (g n) p).toReal / ρ p) ∧
          letI := interiorChartedT_BDRY1 (W n)
          haveI := interiorManifoldT_BDRY1 (W n)
          ∃ _ : ConnectedSpace ((W n).pieceInterior ⊤),
          ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤),
          ∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
            {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x} ⊆ O ∧
            (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) ∧
            (∀ (x : (W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
              (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
            letI := inducedMetricSpace ĝ
            ∃ _ : CompleteSpace ((W n).pieceInterior ⊤),
            ∃ F : LocalPacketsOnBFR ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V vs ζ Λ' {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x},
              -- ranks on U₀ = {D > 5}
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x →
                scaledSplittingRank.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                    (fun y => hρpos y) β x =
                  @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
                    x) ∧
              -- every per-centre consumer domain is an actual g-ball with the distances of W
              (∀ j : (W n).pieceInterior ⊤,
                ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) j →
                Subtype.val '' Metric.ball j
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) =
                  riemannianBallOf (g n) j.val
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) ∧
                ∀ y ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                  ∀ z ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                    riemannianEDistOf (g n) y.val z.val = edist y z) ∧
              -- the zero balls are actual g-balls of W
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              ∀ z (hz : z ∈ F.zero.centres),
                Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius) ∧
              -- weak-edge distance locality on the active edge domains
              (∀ j ∈ F.edge.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
                Metric.infDist x (closure {y : (W n).pieceInterior ⊤ |
                    @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                      (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
                  @Metric.infDist (W n).Carrier (inducedMetricSpace (g n)).toPseudoMetricSpace
                    x.val (@closure (W n).Carrier _ {y : (W n).Carrier |
                      @isEdgePoint.{0, 0} _ ((inducedMetricSpace (g n)).rescale (ρ y)⁻¹
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
              -- weak-edge distance locality on the revised (active) edge domains
              (∀ j ∈ F.edgeB.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
                Metric.infDist x (closure {y : (W n).pieceInterior ⊤ |
                    @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                      (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
                  @Metric.infDist (W n).Carrier (inducedMetricSpace (g n)).toPseudoMetricSpace
                    x.val (@closure (W n).Carrier _ {y : (W n).Carrier |
                      @isEdgePoint.{0, 0} _ ((inducedMetricSpace (g n)).rescale (ρ y)⁻¹
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
              -- BZ-1: the original-metric zero certificates of the producer v2 on `F.zero`
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              -- (A6') enlarged zero curvature of the ORIGINAL metric
              (∀ c (hc : c ∈ F.zero.centres),
                ∀ y ∈ riemannianBallOf (g n) c.val (400 * (F.zero.zero c hc).radius),
                SectionalBoundedBelowAt (g n) y
                  (-((1 / 60) ^ 2 * ((F.zero.zero c hc).radius)⁻¹ ^ 2))) ∧
              -- (I) `ĝ` is `g` on the enlarged zero balls
              (∀ c (hc : c ∈ F.zero.centres),
                Subtype.val '' Metric.ball c (400 * (F.zero.zero c hc).radius) =
                  riemannianBallOf (g n) c.val (400 * (F.zero.zero c hc).radius) ∧
                ∀ y ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
                  ∀ z ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
                    riemannianEDistOf (g n) y.val z.val = edist y z) ∧
              -- (TD) test domains inside `B(c, 11 r_c)`
              (∀ c (hc : c ∈ F.zero.centres), ∀ q, (F.zero.zero c hc).radius / 10 ≤ dist c q →
                dist c q ≤ 10 * (F.zero.zero c hc).radius →
                (∀ x ∈ @Metric.ball _ ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹
                    (inv_pos.mpr (hρpos q))).toPseudoMetricSpace q (β 1)⁻¹,
                  x ∈ Metric.ball c (11 * (F.zero.zero c hc).radius)) ∧
                ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
                  ∀ x ∈ @Metric.ball _ (((inducedMetricSpace ĝ).rescale
                      ((F.zero.zero c hc).radius)⁻¹
                      (inv_pos.mpr (F.zero.zero c hc).radius_pos)).rescale lam
                      hlam).toPseudoMetricSpace q ζ⁻¹,
                    x ∈ Metric.ball c (11 * (F.zero.zero c hc).radius)) ∧
              -- (A3') LC62 for the points of `W`
              ∀ c (hc : c ∈ F.zero.centres), ∀ q : (W n).Carrier,
                riemannianEDistOf (g n) c.val q ≤
                  ENNReal.ofReal (10 * (F.zero.zero c hc).radius) →
                T / 20 ≤ (F.zero.zero c hc).radius / ρ q) ∧
              -- T3: the labelled product alternative OR the separation of zero balls and collars
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              (∃ (i j : Fin P.cusp.count), i ≠ j ∧
                ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (W n).model (Torus × Icc (0 : ℝ) 1)
                  (W n).Carrier ∞,
                  (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
                    ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
              ((∀ i j : Fin P.cusp.count, i ≠ j →
                Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
                  ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
                Disjoint {x | P.level i x ≤ 90} {y | P.level j y ≤ 90} ∧
                ∀ x y, P.level i x ≤ 90 → P.level j y ≤ 90 →
                  ENNReal.ofReal 1 ≤ riemannianEDistOf (g n) x y) ∧
              (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
                Disjoint (riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
                  ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
              Disjoint (⋃ z, ⋃ hz : z ∈ F.zero.centres,
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
                (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)))) := by
  -- every supplier is destructured by `Exists.elim` and projections (no `obtain`/`rintro` on the
  -- large goal: each `cases` motive would re-check it)
  refine (eventually_nonempty_boundaryPacketsBFR_BCG5 K hK A hA).elim fun δ2 t1 => ?_
  refine (bsa04_row.{0}).elim fun δC hC => ?_
  refine t1.2.elim fun a₂ t2 => ?_
  refine ⟨min δ2 δC, lt_min t1.1 hC.1, a₂, t2.1, fun γ hγ hγ1 => ?_⟩
  refine (t2.2 γ hγ hγ1).elim fun β₀ t3 => ?_
  refine ⟨β₀, t3.1, t3.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine (t3.2.2 βc γc hβc hβγ hγc hγc1).elim fun σ₀ t4 => ?_
  refine t4.2.elim fun Δ₀ t5 => ?_
  refine ⟨σ₀, t4.1, Δ₀, t5.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  refine (t5.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ).elim fun τ₀ t6 => ?_
  refine t6.2.elim fun bc₀ t7 => ?_
  refine ⟨τ₀, t6.1, bc₀, t7.1, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8 => ?_⟩
  refine (t7.2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3 i4 i5 i6 i7
    i8).elim fun a₀ t8 => ?_
  refine t8.elim fun b₁ t9 => ?_
  refine ⟨a₀, b₁, t9.1, t9.2.1, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  refine (t9.2.2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6).elim fun w₀ t10 => ?_
  refine ⟨w₀, t10.1, fun w hw hww hwc => ?_⟩
  refine (t10.2 w hw hww hwc).elim fun bd₀ t11 => ?_
  refine ⟨bd₀, t11.1, fun b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3 => ?_⟩
  refine (t11.2 b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3).elim fun b₀ t12 => ?_
  refine ⟨b₀, t12.1, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap βd εN hβd hεN => ?_⟩
  refine (t12.2 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap).elim fun εr t13 => ?_
  refine t13.elim fun δ' t14 => ?_
  refine t14.elim fun Λ' t15 => ?_
  refine ⟨εr, δ', Λ', t15.1, t15.2.1, t15.2.2.1, t15.2.2.2.1, t15.2.2.2.2.1,
    fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  refine (t15.2.2.2.2.2 T hT hTΛ e he he1 δ₀ hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll
    hder).elim fun V t16 => ?_
  refine t16.2.elim fun δ t17 => ?_
  refine ⟨V, t16.1, δ, t17.1, t17.2.1, fun Lmax hLmax => ?_⟩
  have hV0 : 0 ≤ V := hT.le.trans t16.1
  have hw' : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (lpa01_volume_bounds_BDRY5 hΛ hw hwc).1
  have hβsq : 0 < β 1 ^ 2 / 1000 := by positivity
  have hβd2 : 0 < βd ^ 2 / 1000 := by positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `filter_upwards` would `dsimp` the (large) goal: combine the tail facts by hand instead
  have hev := (t17.2.2 Lmax hLmax).and ((hnR.eventually_ge_atTop 7).and
    ((hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹).and
    ((hnR.eventually_ge_atTop (300 * V + 1)).and
    ((hnR.eventually_ge_atTop (1 / (16 * (β 1 ^ 2 / 1000)))).and
    ((hnR.eventually_ge_atTop (1 / (16 * (βd ^ 2 / 1000)))).and
    (hnR.eventually_ge_atTop (6408 / 16)))))))
  refine hev.mono fun n hn => ?_
  have hn7 := hn.2.1
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith only [hn7])
  have hn0 : (0 : ℝ) < n := by linarith only [hn7]
  have hn3 : (3 : ℝ) ≤ n := by linarith only [hn7]
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hδβ : boundaryCounterexampleRatio δ₀ n ≤ β 1 ^ 2 / 1000 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hβsq hn1
      (one_le_sixteen_mul_of_ge_BDRY5 hβsq hn.2.2.2.2.1)
  have hratio : boundaryCounterexampleRatio δ₀ n ≤ βd ^ 2 / 1000 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hβd2 hn1
      (one_le_sixteen_mul_of_ge_BDRY5 hβd2 hn.2.2.2.2.2.1)
  have hδ6408 : boundaryCounterexampleRatio δ₀ n ≤ 1 / 6408 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ (by norm_num) hn1 (by linarith only [hn.2.2.2.2.2.2])
  have h100 : boundaryCounterexampleRatio δ₀ n ≤ 1 / 100 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ (by norm_num) hn1 (by linarith only [hn7])
  have h300 : 300 * V < n := by linarith only [hn.2.2.2.1]
  have hratio0 : 0 ≤ boundaryCounterexampleRatio δ₀ n :=
    (boundaryCounterexampleRatio_pos hδ₀ hn1).le
  have hnw' : (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (inv_le_comm₀ hn0 hw').mpr hn.2.2.1
  have h1000 := cuspTolerance_le_thousandth_BCUSP1 (β 1) βd εN
  -- T2B v2's data at `n`
  refine Exists.elim hn.1 fun ρ u1 => ?_
  refine Exists.elim u1 fun hρpos u2 => ?_
  have hsm := u2.1
  have hlip := u2.2.1
  have hlc := u2.2.2.1
  have hcol := u2.2.2.2.1
  have hbcp := u2.2.2.2.2.1
  refine Exists.elim u2.2.2.2.2.2 fun hconn u4 => ?_
  refine Exists.elim u4 fun ĝ u5 => ?_
  refine Exists.elim u5 fun O u6 => ?_
  refine Exists.elim u6.2.2.2.2 fun hcN u7 => ?_
  refine Exists.elim u7 fun F u8 => ?_
  -- the export packet at the REQUESTED tolerance, with the supplied labels
  refine (exists_boundaryExportPacket_req_BCUSP1 (B n) (hcoll n) (hder n) hK2 hδ6408 hβ1 hβd hεN
    (A := A)).elim fun P hP => ?_
  -- the curvature scale at every point (the original scale `ρ < 2 r(w')`)
  have hscale : ∀ p : (W n).Carrier,
      ENNReal.ofReal ((n : ℝ) * ρ p) < curvatureRadius (g n) p := by
    intro p
    have hst := (hC.2 (W n) (g n) K _ hK2 hratio0
      ((boundaryCounterexampleRatio_le δ₀ n).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hn3 (boundaryCounterexampleRatio_mul_le δ₀ hn1) p).1
    exact ofReal_mul_lt_of_scale_BDRY5 hst
      (firstVolumeScale_anti_of_le (g n) p (inv_pos.mpr hn0) hnw') (hlc p).2 hn0
  -- the collar smallness for `P`
  have hcolP : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000 := by
    rw [hP]
    exact hcol
  have hsmall : ∀ (i : Fin P.cusp.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / (2000 * (1 + 0)) := by
    intro i q _ hq
    have h := hcolP i q hq
    rwa [add_zero, mul_one]
  -- BCUSP-1's late certificate for the same `ρ`
  have hcert : ∀ r : ℝ, 0 < r →
      1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
      ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) < r := by
    rw [hP]
    intro r hr hcond i q hq
    exact (B n).lt_of_le_two_mul_firstVolumeScale h100 hw' hr hcond (fun p => (hlc p).2.le) i hq
  let instM_BDRY5 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace ĝ
  let _ := F.instMetricN
  let _ := F.instChartedN
  let _ := F.instMetricC
  -- every actual zero ball misses every full enlarged collar (T3's separation, same `F`)
  have hsep : ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
      Disjoint (riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
        ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) := by
    intro z hz i
    have hz10 : ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) z := F.zero.centres_subset hz
    have hR : (F.zero.zero z hz).radius ≤ V * ρ z := (F.zero.radius_mem z hz).2
    have hRpos : 0 < (F.zero.zero z hz).radius := (F.zero.zero z hz).radius_pos
    have hR5 := ofReal_radius_add_five_le_BDRY5 (W n) (g n) ρ hρpos hbcp h300 z.val hz10 hR
    obtain ⟨y, hyball, hy0⟩ := F.zero.meets_stratum z hz
    have hyg : y.val ∈ riemannianBallOf (g n) z.val (F.zero.zero z hz).radius := by
      rw [← u8.2.2.1 z hz]
      exact ⟨y, hyball, rfl⟩
    have hy5 : ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) y :=
      ofReal_five_lt_distanceToBoundary_BDRY1 (W n) (g n) hRpos.le hR5 hyg
    have hyW : @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
        y.val = 0 := by
      rw [← u8.1 y hy5]
      exact hy0
    exact P.zeroBall_disjoint_enlargedCollar_96 i ρ hρpos β ζ 0 hβ1 hζ1 hζ2 le_rfl hδβ
      (cuspTolerance_le_beta_BCUSP1 _ _ _) (hsmall i) z.val _ V n hV0 h300 hR (hscale z.val) hz10
      ⟨y.val, hyg, hyW⟩
  refine ⟨P, hP, hratio, ρ, hρpos, hsm, hlip, hlc, hcolP, hcert, ?_, ?_, ?_, ?_, hbcp, hconn, ĝ, O,
    u6.1, u6.2.1, u6.2.2.1, u6.2.2.2.1, hcN, F, u8.1, u8.2.1, u8.2.2.1, u8.2.2.2.1, u8.2.2.2.2.1,
    u8.2.2.2.2.2, ?_⟩
  · -- B3
    intro L γd hL hβγ hγ1 hcond i q₀ hz2 hz98 h5 h95
    have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
    have hz96 : q₀.2.val 0 ≤ 96 := by
      have h := abs_lt.mp (P.height_contract i q₀ hq₀ hz2 hz98).1
      linarith
    have hrL : 0 < βd ^ 3 / (2000 * (1 + L)) := div_pos (pow_pos hβd 3) (by linarith)
    have hρL : ρ ((P.cusp.collar i).toFun q₀) ≤ βd ^ 3 / (2000 * (1 + L)) :=
      (hcert _ hrL hcond i q₀ hz96).le
    exact (P.cusp_splitting_BCUSP1 hK1 h1000 i βd γd L (ρ ((P.cusp.collar i).toFun q₀)) q₀
      (hρpos _) hβd hβγ hγ1 hL hratio (cuspTolerance_le_request_BCUSP1 _ _ _) hρL hz2 hz98 h5
      h95).1
  · -- B4, norm and Hessian
    intro i p hp h2 h98
    have hNH := P.cusp_norm_hessian_BCUSP1 hK1 h1000 i hp h2 h98
    refine ⟨fun u => ?_, hNH.2.2⟩
    have hN := cuspTolerance_le_norm_BCUSP1 (β 1) βd εN
    have hg := Real.sqrt_nonneg ((g n).inner ((P.cusp.collar i).toFun p) u u)
    refine (hNH.2.1 u).trans (mul_le_mul_of_nonneg_right ?_ hg)
    linarith
  · -- B4, Taylor
    intro H hH hcond i pa p hpa h19 h91 a c x₀ ℓ hℓ hℓH hc hgeo hspeed hpc
    have hR := hρpos ((P.cusp.collar i).toFun pa)
    have hRH : ρ ((P.cusp.collar i).toFun pa) < H⁻¹ := hcert H⁻¹ (inv_pos.mpr hH) hcond i pa hpa
    have hRℓ : ρ ((P.cusp.collar i).toFun pa) * ℓ < 1 := by
      calc ρ ((P.cusp.collar i).toFun pa) * ℓ ≤ ρ ((P.cusp.collar i).toFun pa) * H :=
            mul_le_mul_of_nonneg_left hℓH hR.le
        _ < H⁻¹ * H := mul_lt_mul_of_pos_right hRH hH
        _ = 1 := inv_mul_cancel₀ hH.ne'
    exact P.cusp_taylor_BCUSP1 hK1 h1000 i hR c x₀ ℓ hℓ hc hgeo hspeed hpc (by linarith)
      (by linarith)
  · -- B5
    intro L H ϑ c₃ hL hH hϑ hc₃ hcond
    have hr0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
    have hsm5 := hcert _ hr0 hcond
    refine ⟨fun i q hq => ?_, fun C p bb hC hΛC hmeet =>
      P.toBoundaryCollarPacket.bcg01_reference_domain (by linarith) hρpos hΛ.le hlip hsm5 hL hC
        hΛC (cuspPhysicalScale_mul_L_BCUSP1 hβd hL hH hϑ hc₃) hmeet⟩
    have h := hsm5 i q hq
    have hrH := cuspPhysicalScale_mul_H_BCUSP1 hβd hL hH hϑ hc₃
    have hrT := cuspPhysicalScale_taylor_BCUSP1 hβd hL hH hϑ hc₃
    have hrE := cuspPhysicalScale_eps_BCUSP1 hβd hL hH hϑ hc₃
    have hA12 : 0 < 12 * L + 1000 := by linarith
    have hh1 : ρ ((P.cusp.collar i).toFun q) * H ≤ cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * H :=
      mul_le_mul_of_nonneg_right h.le hH.le
    have hh2 : 2 * ρ ((P.cusp.collar i).toFun q) * (12 * L + 1000) ≤
        2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * (12 * L + 1000) :=
      mul_le_mul_of_nonneg_right (by linarith only [h]) hA12.le
    have hh3 : 20 * c₃ * ρ ((P.cusp.collar i).toFun q) ≤
        20 * c₃ * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ :=
      mul_le_mul_of_nonneg_left h.le (by linarith only [hc₃])
    exact ⟨h, h.le.trans (cuspPhysicalScale_le_bcp02_BCUSP1 hβd hL hH hϑ hc₃),
      by linarith only [hh1, hrH], by linarith only [hh2, hrT], by linarith only [hh3, hrE]⟩
  · -- T3's product alternative OR separation
    rcases P.alternative with hprod | hdisj
    · exact Or.inl hprod
    · refine Or.inr ⟨hdisj, hsep, ?_⟩
      apply Set.disjoint_left.mpr
      intro x hx hb
      obtain ⟨z, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hz, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      obtain ⟨q, hq, hqx⟩ := P.toBoundaryCollarPacket.tsupport_block_subset i hi
      have hq92 : q.2.val 0 < 92 := by
        have hh : q.2.val 0 ≤ 90 + cuspTolerance_BCUSP1 (β 1) βd εN := hq.2
        linarith only [hh, h1000]
      exact Set.disjoint_left.mp (hsep z hz i) hx ⟨q, hq92, hqx⟩

end DifferentialGeometry.Geometry.Collapse
