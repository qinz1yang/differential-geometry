import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRZSeqBSTD1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySupply

/-!
# The joint (BA) producer per member, at the member's index (lane BSTD2, G2-pre)

Review 69 (D69-3) / text v1 H1: a tail member must carry a `BoundarySupply` (with BCG02's joint (BA)
certificates `ba_spec`) at the register's parameters and the member's index `n + 1`. The (BA)
certificates come only from the joint producer `lc88_boundary_packets_BFRZ_BA_BIND` (lane
BCG2-BIND), whose per-member conclusion is T3B-BFRZ's (the same `P, ρ, ĝ, O, F`) with the (BA) block
appended on `F.forgetBFR_BFZD`. As lane BSTG-D1 did for T3B-BFRZ (`BoundaryPacketsOutBFRZ_BSTD1`):

* `BoundaryPacketsOutBA_BSTD2`: that per-member conclusion as ONE definition, verbatim (generator
  `build-logs/scratch/BSTD2/gen_ba.py`), member `(W, g, B)`, ratio `δn`, BCP04.a index `idx`, error
  `θ` as parameters; `lc88_boundary_packets_BA_out_BSTD2` (verbatim check, index `n`).
* `BoundaryPacketsOutBA_BSTD2.toBFRZ_BSTD2`: it contains T3B-BFRZ's per-member conclusion (drop the
  (BA) block; the SAME `P, ρ, ĝ, O, F`).
* `BoundaryPacketsOutBA_BSTD2.supply_BSTD2`: for every orientation, ONE `BoundarySupply` at index
  `m` (BAUG-A's packaging of the same data, `lc88_boundarySupply_BAUGA`'s proof per member).
* `BoundaryPacketsOutBA_BSTD2.mono_index_BSTD2`, `lc88_boundary_packets_BA_out_succ_BSTD2`: the
  BCP04.a index raised to the member's counterexample index `n + 1` (BSA06 pair kernel per member,
  as `lc88_boundary_packets_BFRZ_out_succ_BSTD1`).
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

/-- **T3B-BFRZ's per-member conclusion with BCG02's joint (BA) block on the SAME family**
(`lc88_boundary_packets_BFRZ_BA_BIND`, verbatim after `∀ᶠ n`) for ONE member `(W, g, B)` at the
ratio `δn`, with the BCP04.a index `idx`, the prefix values and the (BA) error `θ`. -/
def BoundaryPacketsOutBA_BSTD2 (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (δn : ℝ)
    (B : NearlyCuspidalBoundary W g K δn) (idx : ℝ) (Λ w : ℝ) (β : ℕ → ℝ)
    (Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' βd εN θ : ℝ) : Prop :=
  ∃ P : BoundaryExportPacket W g K A δn
    (cuspTolerance_BCUSP1 (β 1) βd εN),
  P.cusp = B ∧ δn ≤ βd ^ 2 / 1000 ∧
  ∃ ρ : W.Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧
    (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
    (∀ p, firstVolumeScale g p w / 2 < ρ p ∧
      ρ p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
    (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
    -- BCUSP-1: the late `ρ` certificate and the cusp certificates B3–B5 on the SAME `P`, `ρ`
    (∀ r : ℝ, 0 < r →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
      ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) < r) ∧
    (∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 →
      ∀ (i : Fin P.cusp.count) (q₀ : CuspHalfSpace), 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
        5 ≤ P.height i ((P.cusp.collar i).toFun q₀) →
        P.height i ((P.cusp.collar i).toFun q₀) ≤ 95 →
        letI := (inducedMetricSpace g).rescale (ρ ((P.cusp.collar i).toFun q₀))⁻¹
          (inv_pos.mpr (hρpos _));
        letI := (inducedMetricSpace (P.cusp.collar i).cusp.torusMetric).rescale
          ((ρ ((P.cusp.collar i).toFun q₀))⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
          (mul_pos (inv_pos.mpr (hρpos _)) (Real.exp_pos _));
        ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((P.cusp.collar i).toFun q₀)
            (WithLp.toLp 2 ((0 : ℝ), t₀)) βd,
          (∀ x, (f.toFun x).fst = (P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) /
            ρ ((P.cusp.collar i).toFun q₀)) ∧
          ∀ x, (ρ ((P.cusp.collar i).toFun q₀))⁻¹ *
              (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal ≤ βd⁻¹ + βd →
            (f.toFun x).snd = (invFunOn (P.cusp.collar i).toFun cuspDomain x).1) ∧
    (∀ (i : Fin P.cusp.count) (p : CuspHalfSpace), p ∈ cuspDomain → 2 ≤ p.2.val 0 →
      p.2.val 0 ≤ 98 →
      (∀ u : TangentSpace W.model ((P.cusp.collar i).toFun p),
        |mvfderiv W.model (P.height i) ((P.cusp.collar i).toFun p) u| ≤
          (1 + 2 * (εN + βd ^ 2 / 1000)) *
            Real.sqrt (g.inner ((P.cusp.collar i).toFun p) u u)) ∧
      ∀ (R : ℝ), 0 < R → ∀ u w : TangentSpace W.model ((P.cusp.collar i).toFun p),
        R⁻¹ * |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian
            (LeviCivita g) (P.height i) ((P.cusp.collar i).toFun p) u w| ≤
          2 * R * (R⁻¹ * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) u u)) *
            (R⁻¹ * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) w w))) ∧
    (∀ H : ℝ, 0 < H →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (H⁻¹ / 4) ^ 2 →
    ∀ (i : Fin P.cusp.count) (pa p : CuspHalfSpace), pa.2.val 0 ≤ 96 → 19 ≤ p.2.val 0 →
      p.2.val 0 ≤ 91 →
    ∀ (a : ℝ) (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ H →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
        (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
        (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤
          ρ ((P.cusp.collar i).toFun pa) ^ 2) →
      (P.cusp.collar i).toFun p = c x₀ →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, (P.cusp.collar i).toFun q = c t ∧
        2 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 98) ∧
      |deriv (fun t => (P.height i (c t) - a) / ρ ((P.cusp.collar i).toFun pa)) x₀ -
        ((P.height i (c (x₀ + ℓ)) - a) / ρ ((P.cusp.collar i).toFun pa) -
          (P.height i (c x₀) - a) / ρ ((P.cusp.collar i).toFun pa)) / ℓ| ≤
        ρ ((P.cusp.collar i).toFun pa) * ℓ) ∧
    (∀ L H ϑ c₃ : ℝ, 0 < L → 0 < H → 0 < ϑ → 0 ≤ c₃ →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
          min (1 / 2) (cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ / 4) ^ 2 →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) < cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
        ρ ((P.cusp.collar i).toFun q) ≤ βd ^ 3 / (2000 * (1 + H)) ∧
        ρ ((P.cusp.collar i).toFun q) * H < 1 / 100 ∧
        2 * ρ ((P.cusp.collar i).toFun q) * (12 * L + 1000) < ϑ ^ 2 / 10 ^ 8 ∧
        20 * c₃ * ρ ((P.cusp.collar i).toFun q) < 1 / 1000000) ∧
      ∀ (C : ℝ) (p : W.Carrier) (b : Fin P.cusp.count), C ≤ 95 / 100 * L →
        Λ * C ≤ 1 / 2 →
        (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block b),
          riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p)) →
        ρ p < 2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
        ∀ y, riemannianEDistOf g p y < ENNReal.ofReal (C * ρ p) →
          ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧
            q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91) ∧
    (∀ p, 0 < distanceToBoundary W g p →
      idx * (distanceToBoundary W g p).toReal /
          ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p) ∧
    letI := interiorChartedT_BDRY1 W
    haveI := interiorManifoldT_BDRY1 W
    ∃ _ : ConnectedSpace (W.pieceInterior ⊤),
    ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤),
    ∃ O : Set (W.pieceInterior ⊤), IsOpen O ∧
      {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary W g x} ⊆ O ∧
      (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) ∧
      letI := inducedMetricSpace ĝ
      ∃ _ : CompleteSpace (W.pieceInterior ⊤),
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3,
      ∃ F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
          (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
          T V vs ζ Λ' {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM,
        -- ranks on U₀ = {D > 5}
        (∀ x : W.pieceInterior ⊤,
          ENNReal.ofReal 5 < distanceToBoundary W g x →
          scaledSplittingRank.{0, 0} (fun y : W.pieceInterior ⊤ => ρ y)
              (fun y => hρpos y) β x =
            @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) ρ hρpos β
              x) ∧
        -- every per-centre consumer domain is an actual g-ball with the distances of W
        (∀ j : W.pieceInterior ⊤,
          ENNReal.ofReal 10 < distanceToBoundary W g j →
          Subtype.val '' Metric.ball j
              (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) =
            riemannianBallOf g j.val
              (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) ∧
          ∀ y ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
            ∀ z ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
              riemannianEDistOf g y.val z.val = edist y z) ∧
        -- the zero balls are actual g-balls of W
        (letI := F.instMetricN
        letI := F.instChartedN
        letI := F.instMetricC
        ∀ z (hz : z ∈ F.zero.centres),
          Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
            riemannianBallOf g z.val (F.zero.zero z hz).radius) ∧
        -- weak-edge distance locality on the active edge domains
        (∀ j ∈ F.edge.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
          Metric.infDist x (closure {y : W.pieceInterior ⊤ |
              @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
            @Metric.infDist W.Carrier (inducedMetricSpace g).toPseudoMetricSpace
              x.val (@closure W.Carrier _ {y : W.Carrier |
                @isEdgePoint.{0, 0} _ ((inducedMetricSpace g).rescale (ρ y)⁻¹
                  (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
        -- weak-edge distance locality on the revised (active) edge domains
        (∀ j ∈ F.edgeB.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
          Metric.infDist x (closure {y : W.pieceInterior ⊤ |
              @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
            @Metric.infDist W.Carrier (inducedMetricSpace g).toPseudoMetricSpace
              x.val (@closure W.Carrier _ {y : W.Carrier |
                @isEdgePoint.{0, 0} _ ((inducedMetricSpace g).rescale (ρ y)⁻¹
                  (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
        -- BZ-1: the original-metric zero certificates of the producer v2 on `F.zero`
        (letI := F.instMetricN
        letI := F.instChartedN
        letI := F.instMetricC
        -- (A6') enlarged zero curvature of the ORIGINAL metric
        (∀ c (hc : c ∈ F.zero.centres),
          ∀ y ∈ riemannianBallOf g c.val (400 * (F.zero.zero c hc).radius),
          SectionalBoundedBelowAt g y
            (-((1 / 60) ^ 2 * ((F.zero.zero c hc).radius)⁻¹ ^ 2))) ∧
        -- (I) `ĝ` is `g` on the enlarged zero balls
        (∀ c (hc : c ∈ F.zero.centres),
          Subtype.val '' Metric.ball c (400 * (F.zero.zero c hc).radius) =
            riemannianBallOf g c.val (400 * (F.zero.zero c hc).radius) ∧
          ∀ y ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
            ∀ z ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
              riemannianEDistOf g y.val z.val = edist y z) ∧
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
        ∀ c (hc : c ∈ F.zero.centres), ∀ q : W.Carrier,
          riemannianEDistOf g c.val q ≤
            ENNReal.ofReal (10 * (F.zero.zero c hc).radius) →
          T / 20 ≤ (F.zero.zero c hc).radius / ρ q) ∧
        -- T3: the labelled product alternative OR the separation of zero balls and collars
        (letI := F.instMetricN
        letI := F.instChartedN
        letI := F.instMetricC
        (∃ (i j : Fin P.cusp.count), i ≠ j ∧
          ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1)
            W.Carrier ∞,
            (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
              ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
        ((∀ i j : Fin P.cusp.count, i ≠ j →
          Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
            ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
          Disjoint {x | P.level i x ≤ 90} {y | P.level j y ≤ 90} ∧
          ∀ x y, P.level i x ≤ 90 → P.level j y ≤ 90 →
            ENNReal.ofReal 1 ≤ riemannianEDistOf g x y) ∧
        (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
          Disjoint (riemannianBallOf g z.val (F.zero.zero z hz).radius)
            ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
        Disjoint (⋃ z, ⋃ hz : z ∈ F.zero.centres,
            riemannianBallOf g z.val (F.zero.zero z hz).radius)
          (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)))) ∧
        -- BCG2-BIND: BCG02 (BA) on the projection `F.forgetBFR_BFZD` of the SAME `F`
        -- BCG02 at the circle references: value AND differential with ONE unit row (BCG-7 G6)
        (∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.circle.centres)
          (bb : Fin P.cusp.count),
          (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
            riemannianEDistOf g j.val x < ENNReal.ofReal (10 * ρ j)) →
          ∃ Ab : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1),
            Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
            (∀ y : W.pieceInterior ⊤, dist y j < 10 * ρ j →
              ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
                Ab ((let c := F.forgetBFR_BFZD.circle.chart j hj;
                    letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                    c.coord y) -
                  (let c := F.forgetBFR_BFZD.circle.chart j hj;
                    letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                    c.coord j))‖ < θ) ∧
            ∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j → ∃ θ' < θ,
              ∀ u : TangentSpace 𝓘(ℝ, E3) x,
              |mvfderiv 𝓘(ℝ, E3)
                  (fun y : W.pieceInterior ⊤ =>
                    (P.height bb y - P.height bb j) / ρ j) x u -
                Ab (mvfderiv 𝓘(ℝ, E3) (let c := F.forgetBFR_BFZD.circle.chart j hj;
                    letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                    c.coord) x u) 0| ≤
                θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u)) ∧
        -- BCG02 at the REVISED (active) edge references `F.edgeB`: value AND differential
        -- with ONE sign (BCG-7/BCG-8 G8)
        (∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.edgeB.centres)
          (bb : Fin P.cusp.count),
          (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
            riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * ρ j)) →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            (∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
              |(P.height bb y - P.height bb j) / ρ j -
                a * (F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj y -
                  F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj j)| < θ) ∧
            ∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * ρ j → ∃ θ' < θ,
              ∀ u : TangentSpace 𝓘(ℝ, E3) x,
              |mvfderiv 𝓘(ℝ, E3)
                  (fun y : W.pieceInterior ⊤ =>
                    (P.height bb y - P.height bb j) / ρ j) x u -
                a * mvfderiv 𝓘(ℝ, E3) (F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj) x u| ≤
                θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u)) ∧
        -- BCG02 at the slim references: value AND differential with ONE sign (BCG-8 G9)
        ∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.slim.centres)
          (bb : Fin P.cusp.count),
          (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
            riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
              |(P.height bb y - P.height bb j) / ρ j -
                a * ((F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 y -
                  (F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 j)| < θ) ∧
            ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
              ∀ u : TangentSpace 𝓘(ℝ, E3) x,
              |mvfderiv 𝓘(ℝ, E3)
                  (fun y : W.pieceInterior ⊤ =>
                    (P.height bb y - P.height bb j) / ρ j) x u -
                a * mvfderiv 𝓘(ℝ, E3) (F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2
                  x u| ≤
                θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u)

/-- **Verbatim check**: the joint (BA) producer with its per-member conclusion written as
`BoundaryPacketsOutBA_BSTD2` (BCP04.a index `idx = n`, as in the producer). -/
theorem lc88_boundary_packets_BA_out_BSTD2
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) :
    ∃ σC : ℝ, 0 < σC ∧ ∃ ηC : ℝ, 0 < ηC ∧
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → γ ≤ θ ^ 2 / 10000000 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      3 * β₂ ≤ σC → β₂ ≤ θ ^ 2 / 10000000 → ∃ σE : ℝ, 0 < σE ∧ ∃ ηE : ℝ, 0 < ηE ∧
      ∃ σS : ℝ, 0 < σS ∧ ∃ ηS : ℝ, 0 < ηS ∧
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
        μ * Δ ≤ θ / 4 → σc ≤ θ ^ 2 / 10000000 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ → 3 * b ≤ σE →
        b * (2 * (421 * Δ + 1)) ≤ 1 → b ≤ θ ^ 2 / 10000000 →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → vs ≤ θ / 4 → σs ≤ θ ^ 2 / 10000000 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
        3 * ν ≤ β 3 → 2 * β 1 ≤ ηC → 2 * β 1 ≤ ηE → 2 * β 1 ≤ ηS →
        1000000 * Δ * β 1 ^ 3 < 1 → 3 * β 1 ≤ σS → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
        β 1 ≤ θ ^ 2 / 10000000 →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → σC⁻¹ ≤ Lmax →
      σE⁻¹ ≤ Lmax → σS⁻¹ ≤ Lmax → ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 →
      ∀ᶠ n in atTop,
        BoundaryPacketsOutBA_BSTD2 (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
          (n : ℝ) Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' βd εN θ :=
  lc88_boundary_packets_BFRZ_BA_BIND K hK A hA hθ hθ1 hν hν1

variable {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {δn : ℝ}
  {B : NearlyCuspidalBoundary W g K δn} {Λ w : ℝ} {β : ℕ → ℝ}
  {Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' βd εN θ : ℝ}

/-- **The joint per-member conclusion contains T3B-BFRZ's** (the SAME `P, ρ, ĝ, O`, and for every
orientation the SAME `F`; the (BA) block is dropped). -/
theorem BoundaryPacketsOutBA_BSTD2.toBFRZ_BSTD2 {idx : ℝ}
    (h : BoundaryPacketsOutBA_BSTD2 W g K A δn B idx Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ
      δ εr e T V vs ζ Λ' βd εN θ) :
    BoundaryPacketsOutBFRZ_BSTD1 W g K A δn B idx Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
      εr e T V vs ζ Λ' βd εN := by
  obtain ⟨P, hcusp, hratio, ρ, hρpos, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hconn, ĝ, O, hO,
    hOsub, hOeq, hle, hcomp, hF⟩ := h
  refine ⟨P, hcusp, hratio, ρ, hρpos, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hconn, ĝ, O, hO,
    hOsub, hOeq, hle, hcomp, fun oM => ?_⟩
  obtain ⟨F, r1, r2, r3, r4, r5, r6, r7, -⟩ := hF oM
  exact ⟨F, r1, r2, r3, r4, r5, r6, r7⟩

/-- **ONE `BoundarySupply` per orientation from the joint per-member conclusion** at a natural
index `m` (BAUG-A's packaging, `lc88_boundarySupply_BAUGA`, per member: the SAME
`P, ρ, ĝ, O, F`). -/
theorem BoundaryPacketsOutBA_BSTD2.supply_BSTD2 {m : ℕ}
    (h : BoundaryPacketsOutBA_BSTD2 W g K A δn B (m : ℝ) Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax
      τ γ δ εr e T V vs ζ Λ' βd εN θ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    Nonempty (BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λ' θ W g δn m B oM) := by
  obtain ⟨P, hcusp, hratio, ρ, hρpos, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hconn, ĝ, O, hO,
    hOsub, hOeq, hle, hcomp, hF⟩ := h
  obtain ⟨F, r1, r2, r3, -, r5, r6, r7, ba⟩ := hF oM
  exact ⟨{
    packet := P
    rho := ρ
    rho_pos := hρpos
    completion := {
      metric := ĝ
      agree := O
      isOpen_agree := hO
      far_subset_agree := hOsub
      inner_eq_on_agree := hOeq
      inner_le := hle
      complete := hcomp }
    family := F
    cusp_eq := hcusp
    scale_spec := ⟨c1, c2, c3, c4, c10⟩
    cusp_spec := ⟨hratio, c5, c6, c7, c8, c9⟩
    transport_spec := ⟨r1, r2, r3, r5, r6⟩
    geometric_cases := r7
    ba_spec := ba }⟩

/-- **Raising the BCP04.a index of the joint per-member conclusion** (only the BCP04.a clause reads
`idx`). -/
theorem BoundaryPacketsOutBA_BSTD2.mono_index_BSTD2 {idx idx' : ℝ}
    (hup : ∀ ρ : W.Carrier → ℝ, (∀ p, 0 < ρ p) →
      (∀ p, ρ p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∀ p, 0 < distanceToBoundary W g p →
        idx' * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p)
    (h : BoundaryPacketsOutBA_BSTD2 W g K A δn B idx Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ
      δ εr e T V vs ζ Λ' βd εN θ) :
    BoundaryPacketsOutBA_BSTD2 W g K A δn B idx' Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
      εr e T V vs ζ Λ' βd εN θ := by
  obtain ⟨P, hP, hδn, ρ, hρpos, hsm, hlip, hlc, hcol, h1, h2, h3, h4, h5, -, hrest⟩ := h
  exact ⟨P, hP, hδn, ρ, hρpos, hsm, hlip, hlc, hcol, h1, h2, h3, h4, h5,
    hup ρ hρpos (fun p => (hlc p).2), hrest⟩

/-- **The joint (BA) producer per member at the member's counterexample index** `n + 1` (the
accepted IDX4 member form; per member from the BSA06 pair kernel `bsa06_pair_BDRY2`, as
`lc88_boundary_packets_BFRZ_out_succ_BSTD1`). -/
theorem lc88_boundary_packets_BA_out_succ_BSTD2
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) :
    ∃ σC : ℝ, 0 < σC ∧ ∃ ηC : ℝ, 0 < ηC ∧
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → γ ≤ θ ^ 2 / 10000000 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      3 * β₂ ≤ σC → β₂ ≤ θ ^ 2 / 10000000 → ∃ σE : ℝ, 0 < σE ∧ ∃ ηE : ℝ, 0 < ηE ∧
      ∃ σS : ℝ, 0 < σS ∧ ∃ ηS : ℝ, 0 < ηS ∧
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
        μ * Δ ≤ θ / 4 → σc ≤ θ ^ 2 / 10000000 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ → 3 * b ≤ σE →
        b * (2 * (421 * Δ + 1)) ≤ 1 → b ≤ θ ^ 2 / 10000000 →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → vs ≤ θ / 4 → σs ≤ θ ^ 2 / 10000000 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
        3 * ν ≤ β 3 → 2 * β 1 ≤ ηC → 2 * β 1 ≤ ηE → 2 * β 1 ≤ ηS →
        1000000 * Δ * β 1 ^ 3 < 1 → 3 * β 1 ≤ σS → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
        β 1 ≤ θ ^ 2 / 10000000 →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → σC⁻¹ ≤ Lmax →
      σE⁻¹ ≤ Lmax → σS⁻¹ ≤ Lmax → ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 →
      ∀ᶠ n in atTop,
        BoundaryPacketsOutBA_BSTD2 (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
          ((n + 1 : ℕ) : ℝ) Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' βd εN
          θ := by
  obtain ⟨σC, hσC, ηC, hηC, δ3, hδ3, a₂, ha₂, hT3⟩ :=
    lc88_boundary_packets_BA_out_BSTD2 K hK A hA hθ hθ1 hν hν1
  obtain ⟨δP, hδP, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨σC, hσC, ηC, hηC, min δ3 δP, lt_min hδ3 hδP, a₂, ha₂, fun γ hγ hγ1 hγθ => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hT3⟩ := hT3 γ hγ hγ1 hγθ
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hT3⟩ := hT3 βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hσC' hβθ => ?_⟩
  obtain ⟨σE, hσE, ηE, hηE, σS, hσS, ηS, hηS, τ₀, hτ₀, bc₀, hbc₀, hT3⟩ :=
    hT3 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hσC' hβθ
  refine ⟨σE, hσE, ηE, hηE, σS, hσS, ηS, hηS, τ₀, hτ₀, bc₀, hbc₀,
    fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 s b' s' i1 i2 i3 i4 i5 i6 i7 i8 =>
      ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hT3⟩ := hT3 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    s b' s' i1 i2 i3 i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  obtain ⟨w₀, hw₀, hT3⟩ := hT3 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, hT3⟩ := hT3 w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb l1 l2 l3 l4 l5 l6 l7 l8 σs vs m1 m2 m3 m4 m5 => ?_⟩
  obtain ⟨b₀, hb₀, hT3⟩ := hT3 b hb l1 l2 l3 l4 l5 l6 l7 l8 σs vs m1 m2 m3 m4 m5
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 q1 q2 q3 q4 q5 q6 q7 q8 ζ cap hζ1 hζ2 hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hεrcap, hδ', hΛ', hT3⟩ :=
    hT3 β hβ2 hβ1 hβ1b hβ11 hβ3 q1 q2 q3 q4 q5 q6 q7 q8 ζ cap hζ1 hζ2 hcap
  refine ⟨εr, δ', Λ', hεr, hεr1, hεrcap, hδ', hΛ', fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B
    hcoll hder => ?_⟩
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ :=
    hT3 T hT hTΛ e he he1 δ₀ hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder
  refine ⟨V, hTV, δ, hδ, hδδ', fun Lmax hLmax o1 o2 o3 βd εN hβd hεN hεNθ => ?_⟩
  obtain ⟨hw', hw'c⟩ := lpa01_volume_bounds_BDRY5 hΛ hw hwc
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ((hev Lmax hLmax o1 o2 o3 βd εN hβd hεN hεNθ).and ((hnR.eventually_ge_atTop 3).and
    (hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹))).mono fun n hn => ?_
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hn3 : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by rw [hcast]; linarith only [hn.2.1]
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith only [hn3]
  have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by
    refine (inv_le_comm₀ hn0 hw').mpr ?_
    rw [hcast]
    linarith only [hn.2.2]
  exact BoundaryPacketsOutBA_BSTD2.mono_index_BSTD2 (idx := (n : ℝ))
    (fun ρ hρ hρw p hp => (hpair (W n) (g n) K _ hK2
      (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_mul_le δ₀ (Nat.le_add_left 1 n))
      hinv hw'c p (hρ p) (hρw p).le).2.2.2 hp) hn.1

end DifferentialGeometry.Geometry.Collapse
