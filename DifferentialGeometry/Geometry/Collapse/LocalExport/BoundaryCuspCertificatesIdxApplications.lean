import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCertificatesIdx
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# The requested T3 with the cusp certificates at BBR03's counterexample sequence (lane BDRY-IDX2)

Non-vacuous use of `lc88_boundary_collapse_packet_cusp_BCUSP1_IDX2`: its sequence hypothesis (ratio
`boundaryCounterexampleRatio δ₀ (n + 1)`) is the TYPE produced by BBR03's framework
`exists_boundary_counterexample_sequence_of_no_threshold` (universe `0`).
`lc88_boundary_collapse_packet_cusp_of_no_threshold_IDX2` instantiates it there: under the same
prefix, for every `δ₀ ≤ δ_*`, every certificate `Good` without a nonempty-boundary threshold yields
BBR03's counterexample sequence (no member satisfies `Good`) carrying the whole requested-T3 tail
with the cusp certificates B3–B5 on ONE packet.
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
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The requested T3 with the cusp certificates at BBR03's sequence** (lane BDRY-IDX2): the
statement of `lc88_boundary_collapse_packet_cusp_BCUSP1_IDX2` with the sequence replaced by the one
BBR03 produces for a certificate `Good` without a nonempty-boundary threshold. -/
theorem lc88_boundary_collapse_packet_cusp_of_no_threshold_IDX2
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop),
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
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
            ∃ F : LocalPacketsOn ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x →
                scaledSplittingRank.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                    (fun y => hρpos y) β x =
                  @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
                    x) ∧
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              (∀ z (hz : z ∈ F.zero.centres),
                Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius) ∧
              ((∃ (i j : Fin P.cusp.count), i ≠ j ∧
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
                (⋃ i, tsupport (P.toBoundaryCollarPacket.block i))))) := by
  obtain ⟨δS, hδS, a₂, ha₂, hR⟩ :=
    lc88_boundary_collapse_packet_cusp_BCUSP1_IDX2 hσs hσs1 K hK A hA
  refine ⟨δS, hδS, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hR⟩ := hR γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hR⟩ := hR βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hR⟩ := hR β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hR⟩ := hR σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hR⟩ := hR σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hR⟩ := hR w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 βd εN hβd hεN => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hR⟩ := hR β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 βd εN hβd
    hεN
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S
    Good h => ?_⟩
  -- BBR03's counterexample sequence (universe `0`) at the ratios `δ_{n+1}` for THIS `δ₀`
  refine (exists_boundary_counterexample_sequence_of_no_threshold.{0} K A hδ₀ Good h).elim
    fun W x1 => ?_
  refine x1.elim fun hW x2 => ?_
  refine x2.elim fun g x3 => ?_
  refine x3.elim fun B hB => ?_
  let _ : ∀ n, ConnectedSpace (W n).Carrier := hW
  exact ⟨W, hW, g, B, fun n => (hB n).1, fun n => (hB n).2.1, fun n => (hB n).2.2,
    hR T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W g B (fun n => (hB n).1) (fun n => (hB n).2.1)⟩

end DifferentialGeometry.Geometry.Collapse
