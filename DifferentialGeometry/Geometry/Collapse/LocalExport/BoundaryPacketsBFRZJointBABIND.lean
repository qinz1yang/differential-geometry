import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZProducerT3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZForget
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryValuesBFRDifferentialIdx
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryJointBAOfDataBIND

/-!
# T3B on the complete final boundary family with BCG02's joint (BA) clauses on the projection of
the SAME family (lane BCG2-BIND, G2; review 64 D64-6)

`(∃ F_Z : BFRZ, Good F_Z) ∧ (∃ F : BFR, BA F)` does not give `∃ F_Z, Good F_Z ∧ BA F_Z.toBFR`
(review 64 §6.2). `lc88_boundary_packets_BFRZ_BA_BIND` closes this: it is the statement of
`lc88_boundary_values_differential_BFR_BCG8` (BCG02 complete: BCG8's requests at their binders,
three joint value/differential clauses) whose family binder is that of
`lc88_boundary_packets_BFRZ_BFZD` — for every orientation `oM`, ONE `F : LocalPacketsOnBFRZ … oM`
with every clause of T2B and T3's product alternative OR separation — and whose three joint (BA)
clauses are about `F.forgetBFR_BFZD`, the forgetful projection of that SAME `F`. Equivalently: the
statement of `lc88_boundary_packets_BFRZ_BFZD` verbatim (same prefix, tail, `P`, `ρ`, `ĝ`, `O`, `F`)
with BCG8's requests inserted at their binders and the (BA) block appended (generator
`build-logs/scratch/BCG2-BIND/gen_g2.py`, which checks that T3B_IDX2 and T3B_BFRZ differ only in
the family binder).

Proof: BCG8's chain run on `lc88_boundary_packets_BFRZ_BFZD`; at the tail point `n`, for the
orientation `oM` and T3B's ONE `F`, the consumer lemma `bcg02_joint_BA_of_data_BIND` (G1) applied to
the data `P.toBoundaryCollarPacket, ρ, ĝ, F.forgetBFR_BFZD` and their certificates from the same
member (Lipschitz scale, collar smallness, `ĝ = g°` on `{D ≥ 4}`, BCP04.a at `n`, B5's
physical-scale bound at `(10⁶Δ, 1, θ, 0)` after its late condition, completeness). This is the
version that `BoundarySupply` (lane BAUG-A, D61-2) wraps.
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

/-- **T3B on BFRZ with BCG02's joint (BA) clauses on the projection of the SAME family** (lane
BCG2-BIND, review 64 D64-6; see the module docstring): BCG8's statement whose ONE family is, for
every orientation `oM`, `F : LocalPacketsOnBFRZ … oM` (T3B on BFRZ's family, every clause of T2B,
T3's product alternative OR separation), and whose circle / revised edge / slim joint
value-and-differential clauses are about `F.forgetBFR_BFZD`. -/
theorem lc88_boundary_packets_BFRZ_BA_BIND
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
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))
          (cuspTolerance_BCUSP1 (β 1) βd εN),
        P.cusp = B n ∧ boundaryCounterexampleRatio δ₀ (n + 1) ≤ βd ^ 2 / 1000 ∧
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          -- BCUSP-1: the late `ρ` certificate and the cusp certificates B3–B5 on the SAME `P`, `ρ`
          (∀ r : ℝ, 0 < r →
            1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
            ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
              ρ ((P.cusp.collar i).toFun q) < r) ∧
          (∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
            1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
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
            1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
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
            1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
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
            ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) 3,
            ∃ F : LocalPacketsOnBFRZ ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V vs ζ Λ' {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x} oM,
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
                (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)))) ∧
              -- BCG2-BIND: BCG02 (BA) on the projection `F.forgetBFR_BFZD` of the SAME `F`
              -- BCG02 at the circle references: value AND differential with ONE unit row (BCG-7 G6)
              (∀ (j : (W n).pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.circle.centres)
                (bb : Fin P.cusp.count),
                (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
                  riemannianEDistOf (g n) j.val x < ENNReal.ofReal (10 * ρ j)) →
                ∃ Ab : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1),
                  Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
                  (∀ y : (W n).pieceInterior ⊤, dist y j < 10 * ρ j →
                    ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
                      Ab ((let c := F.forgetBFR_BFZD.circle.chart j hj;
                          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                          c.coord y) -
                        (let c := F.forgetBFR_BFZD.circle.chart j hj;
                          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                          c.coord j))‖ < θ) ∧
                  ∀ x : (W n).pieceInterior ⊤, dist x j < 10 * ρ j → ∃ θ' < θ,
                    ∀ u : TangentSpace 𝓘(ℝ, E3) x,
                    |mvfderiv 𝓘(ℝ, E3)
                        (fun y : (W n).pieceInterior ⊤ =>
                          (P.height bb y - P.height bb j) / ρ j) x u -
                      Ab (mvfderiv 𝓘(ℝ, E3) (let c := F.forgetBFR_BFZD.circle.chart j hj;
                          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
                          c.coord) x u) 0| ≤
                      θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                        (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u)) ∧
              -- BCG02 at the REVISED (active) edge references `F.edgeB`: value AND differential
              -- with ONE sign (BCG-7/BCG-8 G8)
              (∀ (j : (W n).pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.edgeB.centres)
                (bb : Fin P.cusp.count),
                (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
                  riemannianEDistOf (g n) j.val x < ENNReal.ofReal (20 * Δ * ρ j)) →
                ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
                  (∀ y : (W n).pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
                    |(P.height bb y - P.height bb j) / ρ j -
                      a * (F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj y -
                        F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj j)| < θ) ∧
                  ∀ x : (W n).pieceInterior ⊤, dist x j < 20 * Δ * ρ j → ∃ θ' < θ,
                    ∀ u : TangentSpace 𝓘(ℝ, E3) x,
                    |mvfderiv 𝓘(ℝ, E3)
                        (fun y : (W n).pieceInterior ⊤ =>
                          (P.height bb y - P.height bb j) / ρ j) x u -
                      a * mvfderiv 𝓘(ℝ, E3) (F.forgetBFR_BFZD.edgeB.coord_BCG1 j hj) x u| ≤
                      θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                        (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u)) ∧
              -- BCG02 at the slim references: value AND differential with ONE sign (BCG-8 G9)
              ∀ (j : (W n).pieceInterior ⊤) (hj : j ∈ F.forgetBFR_BFZD.slim.centres)
                (bb : Fin P.cusp.count),
                (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
                  riemannianEDistOf (g n) j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
                ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
                  (∀ y : (W n).pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
                    |(P.height bb y - P.height bb j) / ρ j -
                      a * ((F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 y -
                        (F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 j)| < θ) ∧
                  ∀ x : (W n).pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
                    ∀ u : TangentSpace 𝓘(ℝ, E3) x,
                    |mvfderiv 𝓘(ℝ, E3)
                        (fun y : (W n).pieceInterior ⊤ =>
                          (P.height bb y - P.height bb j) / ρ j) x u -
                      a * mvfderiv 𝓘(ℝ, E3) (F.forgetBFR_BFZD.slim.centre j hj).coord_BCG2
                        x u| ≤
                      θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                        (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ).inner x u u) := by
  -- every supplier is destructured by `Exists.elim` and projections (BCG-3's pitfall: no
  -- `obtain`/`rintro`/`filter_upwards` on the large goal)
  refine (bcg02_joint_BA_of_data_BIND hθ hθ1 hν hν1).elim fun σC c1 => ?_
  refine c1.2.elim fun ηC c2 => ?_
  refine (lc88_boundary_packets_BFRZ_BFZD K hK A hA).elim fun δStar t0 => ?_
  refine t0.2.elim fun a₂ t2 => ?_
  refine ⟨σC, c1.1, ηC, c2.1, δStar, t0.1, a₂, t2.1, fun γ hγ hγ1 hγθ => ?_⟩
  refine (t2.2 γ hγ hγ1).elim fun β₀ t3 => ?_
  refine ⟨β₀, t3.1, t3.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine (t3.2.2 βc γc hβc hβγ hγc hγc1).elim fun σ₀ t4 => ?_
  refine t4.2.elim fun Δ₀ t5 => ?_
  refine ⟨σ₀, t4.1, Δ₀, t5.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hβ₂σ hβ₂θ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 1 < 100 / β₂ := by
      rw [lt_div_iff₀ hβ₂]
      linarith
    linarith
  have hΔ0 : 0 < Δ := by linarith
  refine (c2.2 Δ (β₂ / 3) hΔ1 (by positivity) (by linarith)).elim fun σE e1 => ?_
  refine e1.2.elim fun ηE e2 => ?_
  refine e2.2.elim fun σS s1 => ?_
  refine s1.2.elim fun ηS s2 => ?_
  refine (t5.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ).elim fun τ₀ t6 => ?_
  refine t6.2.elim fun bc₀ t7 => ?_
  refine ⟨σE, e1.1, ηE, e2.1, σS, s1.1, ηS, s2.1, τ₀, t6.1, bc₀, t7.1, fun σc ε μ τ h1 h2 h3 h4
    h5 h6 h7 h8 h9 h10 h11 h12 hμθ hσcθ s b' s' i1 i2 i3 i4 i5 i6 i7 i8 => ?_⟩
  refine (t7.2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3 i4 i5 i6 i7
    i8).elim fun a₀ t8 => ?_
  refine t8.elim fun b₁ t9 => ?_
  refine ⟨a₀, b₁, t9.1, t9.2.1, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  refine (t9.2.2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6).elim fun w₀ t10 => ?_
  refine ⟨w₀, t10.1, fun w hw hww hwc => ?_⟩
  refine (t10.2 w hw hww hwc).elim fun bd₀ t11 => ?_
  refine ⟨bd₀, t11.1, fun b hb l1 l2 l3 l4 l5 l6 hbH hbθ σs vs m1 m2 m3 hvs hσsθ => ?_⟩
  refine (t11.2 b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3).elim fun b₀ t12 => ?_
  refine ⟨b₀, t12.1, fun β hβ2 hβ1 hβ1b hβ11 hβ3 hνβ hβηC hβηE hβηS hβL h3βS hβH hβθ ζ cap
    hζ1 hζ2 hcap => ?_⟩
  refine (t12.2 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap).elim fun εr t13 => ?_
  refine t13.elim fun δ' t14 => ?_
  refine t14.elim fun Λ' t15 => ?_
  refine ⟨εr, δ', Λ', t15.1, t15.2.1, t15.2.2.1, t15.2.2.2.1, t15.2.2.2.2.1,
    fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  refine (t15.2.2.2.2.2 T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W g B hcoll hder).elim fun V t16 => ?_
  refine t16.2.elim fun δ t17 => ?_
  refine ⟨V, t16.1, δ, t17.1, t17.2.1, fun Lmax hLmax hσCL hσEL hσSL βd εN hβd hεN hεNθ => ?_⟩
  -- the parameter facts used by the consumer lemma
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hβsq : 0 < β 1 ^ 2 / 1000 := by positivity
  have hθsq : 0 < θ ^ 2 / 40000000 := by positivity
  have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ.le hΔ1
  have hΛC : 950000 * Δ * Λ ≤ 1 / 2 := by linarith
  have hβ31 : β 3 < 1 :=
    lt_of_le_of_lt hβ3 (threeSplittingExclusionThreshold_lt.{0, 0}.trans (by norm_num))
  have hβ₂3 : 3 * β 2 ≤ σC := by rw [hβ2]; exact hβ₂σ
  have hβ2θ : β 2 ≤ θ ^ 2 / 10000000 := by rw [hβ2]; exact hβ₂θ
  have hν2 : 3 * (β₂ / 3) ≤ β 2 := by rw [hβ2]; linarith
  have hb'6 : 1 / (1000000 * Δ) ≤ 1 / 1000000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs6 : s < 1 / 1000000 := by linarith
  have hεB := cuspTolerance_le_beta_BCUSP1 (β 1) βd εN
  have hεBθ : cuspTolerance_BCUSP1 (β 1) βd εN ≤ θ ^ 2 / 40000000 :=
    (cuspTolerance_le_norm_BCUSP1 (β 1) βd εN).trans hεNθ
  have hL0 : 0 < 1000000 * Δ := by positivity
  -- the late condition of B5 at `(L, H, ϑ, c₃) = (10⁶Δ, 1, θ, 0)`
  have hRHS : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
      min (1 / 2) (cuspPhysicalScale_BCUSP1 βd (1000000 * Δ) 1 θ 0 / 4) ^ 2 := by
    have hsc := cuspPhysicalScale_pos_BCUSP1 hβd hL0 one_pos hθ le_rfl
    have hm : 0 < min (1 / 2) (cuspPhysicalScale_BCUSP1 βd (1000000 * Δ) 1 θ 0 / 4) :=
      lt_min (by norm_num) (by positivity)
    have hw' := (lpa01_volume_bounds_BDRY5 hΛ hw hwc).1
    positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `filter_upwards` would `dsimp` the (large) goal: combine the tail facts by hand instead
  have hev := (t17.2.2 Lmax hLmax βd εN hβd hεN).and ((hnR.eventually_ge_atTop (32 * ηC⁻¹)).and
    ((hnR.eventually_ge_atTop (32 * ηE⁻¹)).and ((hnR.eventually_ge_atTop (32 * ηS⁻¹)).and
    ((eventually_ratio_succ_le_BCG8 δ₀ hβsq).and ((eventually_ratio_succ_le_BCG8 δ₀ hθsq).and
    ((hnR.eventually_ge_atTop (32 * (1000000 * Δ))).and
    (eventually_ratio_sq_lt_BCG8 hδ₀ hRHS)))))))
  refine hev.mono fun n hn => ?_
  -- T3B on BFRZ: its data at `n`
  refine Exists.elim hn.1 fun P v1 => ?_
  refine Exists.elim v1.2.2 fun ρ v2 => ?_
  refine Exists.elim v2 fun hρpos v3 => ?_
  refine Exists.elim v3.2.2.2.2.2.2.2.2.2.2 fun hconn v4 => ?_
  refine Exists.elim v4 fun ĝ v5 => ?_
  refine Exists.elim v5 fun O v6 => ?_
  refine Exists.elim v6.2.2.2.2 fun hcN v7 => ?_
  let instM_BIND : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace ĝ
  have heq : ∀ x : (W n).pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
      ĝ.inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x := fun x hx =>
    v6.2.2.1 x (v6.2.1 hx)
  have hU₁ : ∀ x ∈ {x : (W n).pieceInterior ⊤ |
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x},
      ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x := fun _ hx =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hx
  -- B5's physical-scale clause at `L = 10⁶Δ`, `ϑ = θ` (T3B's late condition holds at `n`)
  have hB5 : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      2 * ρ ((P.cusp.collar i).toFun q) * (12 * (1000000 * Δ) + 1000) < θ ^ 2 / 10 ^ 8 :=
    fun i q hq => ((v3.2.2.2.2.2.2.2.2.1 (1000000 * Δ) 1 θ 0 hL0 one_pos hθ le_rfl
      hn.2.2.2.2.2.2.2).1 i q hq).2.2.2.1
  refine ⟨P, v1.1, v1.2.1, ρ, hρpos, v3.1, v3.2.1, v3.2.2.1, v3.2.2.2.1, v3.2.2.2.2.1,
    v3.2.2.2.2.2.1, v3.2.2.2.2.2.2.1, v3.2.2.2.2.2.2.2.1, v3.2.2.2.2.2.2.2.2.1,
    v3.2.2.2.2.2.2.2.2.2.1, hconn, ĝ, O, v6.1, v6.2.1, v6.2.2.1, v6.2.2.2.1, hcN, fun oM => ?_⟩
  -- the ONE family of T3B on BFRZ for `oM`; (BA) on its projection by the consumer lemma (G1)
  refine Exists.elim (v7 oM) fun F v8 => ?_
  exact ⟨F, v8.1, v8.2.1, v8.2.2.1, v8.2.2.2.1, v8.2.2.2.2.1, v8.2.2.2.2.2.1, v8.2.2.2.2.2.2,
    s2.2 (W n) (g n) P.toBoundaryCollarPacket ρ hρpos ĝ hK1 hΛ.le v3.2.1 v3.2.2.2.1 heq
      v3.2.2.2.2.2.2.2.2.2.1 hB5 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.2.2.1 hn.2.2.2.2.1 hεB
      hεBθ hn.2.2.2.2.2.1 hΛC hβ1 hβηC hβηE hβηS hβL h3βS hβH hβθ hβ₂3 hβ2θ hν2 hνβ hβ31 hσCL
      hσEL hσSL hγθ l6 hbH hbθ hs6 hμθ h1.le hσcθ m1 hσsθ hvs hcN _ _ _ _ hU₁
      F.forgetBFR_BFZD⟩

end DifferentialGeometry.Geometry.Collapse
