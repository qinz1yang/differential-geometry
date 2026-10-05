import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZJointBABIND

/-!
# `BoundarySupply`: ONE stored T3B joint supply on the complete boundary family (lane BAUG-A, G4)

Draft 61 §1.1–§1.2, dispositions D61-1 and D61-2. The boundary chain starts from ONE object that
stores the per-member joint conclusion of the boundary producer `lc88_boundary_packets_BFRZ_BFZD`
(index-corrected T3B on the complete final family `LocalPacketsOnBFRZ`): the same export packet
`P`, the same original scale `ρ`, the same interior completion `ĝ` (with `O` and completeness) and
the same family `F`, together with every clause of the producer about them. It is ONE structure,
not four existence statements; nothing downstream re-chooses `P`, `ρ`, `ĝ` or `F`.

* `BoundaryCompletionData W g`: DATA `ĝ`, `O` with the comparison proofs and completeness of
  `(W°, d_ĝ)`;
* `BoundarySupplyCore … W g δn n B oM`: DATA `packet`, `rho`, `completion`, `family`
  (`LocalPacketsOnBFRZ … oM` on `(W°, d_ĝ)` with scale `ρ ∘ ι`, regions `{D > 10}`, `{D ≥ 20}`,
  `{D > 20}`, `{D ≥ 35}`); PROPS `cusp_eq`, `scale_spec` (smooth, `Λ`-Lipschitz, LC02 bounds,
  collar smallness, BCP04.a at the index `n`), `cusp_spec` (`δ_n ≤ β∂²/1000`, BCUSP-1's late
  certificate, B3 splitting, B4 norm/Hessian, B5 first exit, physical scale), `transport_spec`
  (ranks on `{D > 5}`, per-centre consumer balls are `g`-balls, zero balls are `g`-balls, the
  weak-edge distance locality on the `edgeB` domains, BZ-1's original-metric zero certificates),
  `geometric_cases` (labelled whole product OR separation of zero balls and collars);
* `BoundarySupply … θ … W g δn n B oM extends BoundarySupplyCore`: PROP `ba_spec` — BCG02's joint
  (BA) certificates (value AND differential, ONE row / ONE sign, error `θ`) at the circle, `edgeB`
  and slim references on `family.forgetBFR_BFZD` (D64-6: bound to the SAME family; source
  `lc88_boundary_packets_BFRZ_BA_BIND`);
* the ACTIVE VIEW (definitions, never a new choice): `activeCircle`, `activeSlim`, `activeZero`,
  `activeEdge := family.edgeB`, `edgeHeightRaw := edgeB.smoothing / ρ` (pointwise), and the
  forgetful projection `familyBFR := family.forgetBFR_BFZD`; the inherited old `edge` is never
  read (its locality clause is not stored) and the smoothing is never re-chosen.

The zero sublevel types and the weak-edge density are fields of the SAME `family` (no second
producer, no separate Spec structure); BCG03–BCG06 do not read them.
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

/-- **The interior completion of a carrier with boundary** (T3B's `ĝ, O`): a smooth metric `ĝ`
on `W°` (interior atlas), an open set `O ⊇ {D ≥ 4}` on which `ĝ = g°`, `g° ≤ ĝ` everywhere, and
`(W°, d_ĝ)` complete. DATA with proofs of its fields. -/
structure BoundaryCompletionData (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) where
  /-- The completed metric `ĝ` on `W°`. -/
  metric : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)
  /-- The open agreement set `O`. -/
  agree : Set (W.pieceInterior ⊤)
  isOpen_agree : IsOpen agree
  far_subset_agree :
    {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary W g x} ⊆ agree
  inner_eq_on_agree : ∀ x ∈ agree, metric.inner x = (pieceInteriorMetric W g ⊤).inner x
  inner_le : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
    (pieceInteriorMetric W g ⊤).inner x v v ≤ metric.inner x v v
  /-- `(W°, d_ĝ)` is complete. -/
  complete : @CompleteSpace (W.pieceInterior ⊤) (inducedMetricSpace metric).toUniformSpace

/-- **`BoundarySupplyCore`** (D61-2 without the BCG02 clauses): ONE stored T3B joint supply at
one member — the export packet, the original scale, the interior completion and the complete
final family `F : LocalPacketsOnBFRZ` (orientation `oM` of `W°`), with every clause of
`lc88_boundary_packets_BFRZ_BFZD` about them (except the locality clause of the inherited old
`edge`, which no boundary construction reads). `δn` is the member's ratio
(`boundaryCounterexampleRatio δ₀ (n + 1)` on BBR03's sequence) and `n` the BCP04.a index. -/
structure BoundarySupplyCore (K : ℕ) (A : ℝ → ℝ) (β : ℕ → ℝ)
    (βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (δn : ℝ) (n : ℕ)
    (B : NearlyCuspidalBoundary W g K δn)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) where
  /-- The export packet `P` at the requested cusp tolerance. -/
  packet : BoundaryExportPacket W g K A δn (cuspTolerance_BCUSP1 (β 1) βd εN)
  /-- The ONE original scale `ρ`. -/
  rho : W.Carrier → ℝ
  rho_pos : ∀ p, 0 < rho p
  /-- The ONE interior completion `ĝ, O`. -/
  completion : BoundaryCompletionData W g
  /-- The ONE complete final family on `(W°, d_ĝ)` with the scale `ρ ∘ ι`. -/
  family :
    letI := inducedMetricSpace completion.metric
    letI := completion.complete
    LocalPacketsOnBFRZ (W.pieceInterior ⊤) completion.metric
      (inducedMetricSpace_hmetric completion.metric) (fun x => rho x) (fun x => rho_pos x) Λ β Δ
      σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM
  /-- The packet carries the supplied boundary labels. -/
  cusp_eq : packet.cusp = B
  /-- The scale: smooth, `Λ`-Lipschitz for `g`, LC02's bounds, collar smallness, BCP04.a. -/
  scale_spec :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ rho ∧
    (∀ x y, ENNReal.ofReal |rho x - rho y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
    (∀ p, firstVolumeScale g p w / 2 < rho p ∧
      rho p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
    (∀ (i : Fin packet.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      rho ((packet.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
    (∀ p, 0 < distanceToBoundary W g p →
      (n : ℝ) * (distanceToBoundary W g p).toReal /
          ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / rho p)
  /-- The cusp certificates on the SAME `P`, `ρ`: the ratio request, BCUSP-1's late certificate,
  B3 (splitting with the height coordinate), B4 (norm and Hessian), B5 (first exit), the physical
  scale and the support window of the actual collar blocks. -/
  cusp_spec :
    δn ≤ βd ^ 2 / 1000 ∧
    (∀ r : ℝ, 0 < r →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
      ∀ (i : Fin packet.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        rho ((packet.cusp.collar i).toFun q) < r) ∧
    (∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 →
      ∀ (i : Fin packet.cusp.count) (q₀ : CuspHalfSpace), 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
        5 ≤ packet.height i ((packet.cusp.collar i).toFun q₀) →
        packet.height i ((packet.cusp.collar i).toFun q₀) ≤ 95 →
        letI := (inducedMetricSpace g).rescale (rho ((packet.cusp.collar i).toFun q₀))⁻¹
          (inv_pos.mpr (rho_pos _));
        letI := (inducedMetricSpace (packet.cusp.collar i).cusp.torusMetric).rescale
          ((rho ((packet.cusp.collar i).toFun q₀))⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
          (mul_pos (inv_pos.mpr (rho_pos _)) (Real.exp_pos _));
        ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((packet.cusp.collar i).toFun q₀)
            (WithLp.toLp 2 ((0 : ℝ), t₀)) βd,
          (∀ x, (f.toFun x).fst =
            (packet.height i x - packet.height i ((packet.cusp.collar i).toFun q₀)) /
              rho ((packet.cusp.collar i).toFun q₀)) ∧
          ∀ x, (rho ((packet.cusp.collar i).toFun q₀))⁻¹ *
              (riemannianEDistOf g x ((packet.cusp.collar i).toFun q₀)).toReal ≤ βd⁻¹ + βd →
            (f.toFun x).snd = (invFunOn (packet.cusp.collar i).toFun cuspDomain x).1) ∧
    (∀ (i : Fin packet.cusp.count) (p : CuspHalfSpace), p ∈ cuspDomain → 2 ≤ p.2.val 0 →
      p.2.val 0 ≤ 98 →
      (∀ u : TangentSpace W.model ((packet.cusp.collar i).toFun p),
        |mvfderiv W.model (packet.height i) ((packet.cusp.collar i).toFun p) u| ≤
          (1 + 2 * (εN + βd ^ 2 / 1000)) *
            Real.sqrt (g.inner ((packet.cusp.collar i).toFun p) u u)) ∧
      ∀ (R : ℝ), 0 < R → ∀ u w : TangentSpace W.model ((packet.cusp.collar i).toFun p),
        R⁻¹ * |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian
            (LeviCivita g) (packet.height i) ((packet.cusp.collar i).toFun p) u w| ≤
          2 * R * (R⁻¹ * Real.sqrt (g.inner ((packet.cusp.collar i).toFun p) u u)) *
            (R⁻¹ * Real.sqrt (g.inner ((packet.cusp.collar i).toFun p) w w))) ∧
    (∀ H : ℝ, 0 < H →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (H⁻¹ / 4) ^ 2 →
    ∀ (i : Fin packet.cusp.count) (pa p : CuspHalfSpace), pa.2.val 0 ≤ 96 → 19 ≤ p.2.val 0 →
      p.2.val 0 ≤ 91 →
    ∀ (a : ℝ) (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ H →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
        (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
        (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤
          rho ((packet.cusp.collar i).toFun pa) ^ 2) →
      (packet.cusp.collar i).toFun p = c x₀ →
      (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, (packet.cusp.collar i).toFun q = c t ∧
        2 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 98) ∧
      |deriv (fun t => (packet.height i (c t) - a) / rho ((packet.cusp.collar i).toFun pa)) x₀ -
        ((packet.height i (c (x₀ + ℓ)) - a) / rho ((packet.cusp.collar i).toFun pa) -
          (packet.height i (c x₀) - a) / rho ((packet.cusp.collar i).toFun pa)) / ℓ| ≤
        rho ((packet.cusp.collar i).toFun pa) * ℓ) ∧
    (∀ L H ϑ c₃ : ℝ, 0 < L → 0 < H → 0 < ϑ → 0 ≤ c₃ →
      1000 * δn ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
          min (1 / 2) (cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ / 4) ^ 2 →
      (∀ (i : Fin packet.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        rho ((packet.cusp.collar i).toFun q) < cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
        rho ((packet.cusp.collar i).toFun q) ≤ βd ^ 3 / (2000 * (1 + H)) ∧
        rho ((packet.cusp.collar i).toFun q) * H < 1 / 100 ∧
        2 * rho ((packet.cusp.collar i).toFun q) * (12 * L + 1000) < ϑ ^ 2 / 10 ^ 8 ∧
        20 * c₃ * rho ((packet.cusp.collar i).toFun q) < 1 / 1000000) ∧
      ∀ (C : ℝ) (p : W.Carrier) (b : Fin packet.cusp.count), C ≤ 95 / 100 * L →
        Λ * C ≤ 1 / 2 →
        (∃ x ∈ tsupport (packet.toBoundaryCollarPacket.block b),
          riemannianEDistOf g p x < ENNReal.ofReal (C * rho p)) →
        rho p < 2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
        ∀ y, riemannianEDistOf g p y < ENNReal.ofReal (C * rho p) →
          ∃ q ∈ cuspDomain, (packet.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧
            q.2.val 0 < 91 ∧ 19 < packet.height b y ∧ packet.height b y < 91)
  /-- The original-metric transport of the family: ranks, consumer balls, zero balls, the weak-edge
  distance on the `edgeB` domains and BZ-1's zero certificates. -/
  transport_spec :
    letI := inducedMetricSpace completion.metric
    letI := completion.complete
    (∀ x : W.pieceInterior ⊤,
      ENNReal.ofReal 5 < distanceToBoundary W g x →
      scaledSplittingRank.{0, 0} (fun y : W.pieceInterior ⊤ => rho y)
          (fun y => rho_pos y) β x =
        @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) rho rho_pos β
          x) ∧
    (∀ j : W.pieceInterior ⊤,
      ENNReal.ofReal 10 < distanceToBoundary W g j →
      Subtype.val '' Metric.ball j
          (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * rho j) =
        riemannianBallOf g j.val
          (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * rho j) ∧
      ∀ y ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * rho j),
        ∀ z ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * rho j),
          riemannianEDistOf g y.val z.val = edist y z) ∧
    (letI := family.instMetricN
    letI := family.instChartedN
    letI := family.instMetricC
    ∀ z (hz : z ∈ family.zero.centres),
      Subtype.val '' Metric.ball z (family.zero.zero z hz).radius =
        riemannianBallOf g z.val (family.zero.zero z hz).radius) ∧
    (∀ j ∈ family.edgeB.centres, ∀ x ∈ Metric.ball j (200 * Δ * rho j),
      Metric.infDist x (closure {y : W.pieceInterior ⊤ |
          @isEdgePoint.{0, 0} _ ((inducedMetricSpace completion.metric).rescale (rho y)⁻¹
            (inv_pos.mpr (rho_pos y))) y Δ b' s'}) =
        @Metric.infDist W.Carrier (inducedMetricSpace g).toPseudoMetricSpace
          x.val (@closure W.Carrier _ {y : W.Carrier |
            @isEdgePoint.{0, 0} _ ((inducedMetricSpace g).rescale (rho y)⁻¹
              (inv_pos.mpr (rho_pos y))) y Δ b' s'})) ∧
    (letI := family.instMetricN
    letI := family.instChartedN
    letI := family.instMetricC
    (∀ c (hc : c ∈ family.zero.centres),
      ∀ y ∈ riemannianBallOf g c.val (400 * (family.zero.zero c hc).radius),
      SectionalBoundedBelowAt g y
        (-((1 / 60) ^ 2 * ((family.zero.zero c hc).radius)⁻¹ ^ 2))) ∧
    (∀ c (hc : c ∈ family.zero.centres),
      Subtype.val '' Metric.ball c (400 * (family.zero.zero c hc).radius) =
        riemannianBallOf g c.val (400 * (family.zero.zero c hc).radius) ∧
      ∀ y ∈ Metric.ball c (400 * (family.zero.zero c hc).radius),
        ∀ z ∈ Metric.ball c (400 * (family.zero.zero c hc).radius),
          riemannianEDistOf g y.val z.val = edist y z) ∧
    (∀ c (hc : c ∈ family.zero.centres), ∀ q, (family.zero.zero c hc).radius / 10 ≤ dist c q →
      dist c q ≤ 10 * (family.zero.zero c hc).radius →
      (∀ x ∈ @Metric.ball _ ((inducedMetricSpace completion.metric).rescale (rho q)⁻¹
          (inv_pos.mpr (rho_pos q))).toPseudoMetricSpace q (β 1)⁻¹,
        x ∈ Metric.ball c (11 * (family.zero.zero c hc).radius)) ∧
      ∀ (lam : ℝ) (hlam : 0 < lam), Λz ≤ lam →
        ∀ x ∈ @Metric.ball _ (((inducedMetricSpace completion.metric).rescale
            ((family.zero.zero c hc).radius)⁻¹
            (inv_pos.mpr (family.zero.zero c hc).radius_pos)).rescale lam
            hlam).toPseudoMetricSpace q ζ⁻¹,
          x ∈ Metric.ball c (11 * (family.zero.zero c hc).radius)) ∧
    ∀ c (hc : c ∈ family.zero.centres), ∀ q : W.Carrier,
      riemannianEDistOf g c.val q ≤
        ENNReal.ofReal (10 * (family.zero.zero c hc).radius) →
      T / 20 ≤ (family.zero.zero c hc).radius / rho q)
  /-- T3: the labelled whole product OR the separation of zero balls and collars. -/
  geometric_cases :
    letI := inducedMetricSpace completion.metric
    letI := completion.complete
    letI := family.instMetricN
    letI := family.instChartedN
    letI := family.instMetricC
    (∃ (i j : Fin packet.cusp.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1)
        W.Carrier ∞,
        (∀ p, D p ∈ packet.cusp.component i ↔ p.2.1 = 0) ∧
          ∀ p, D p ∈ packet.cusp.component j ↔ p.2.1 = 1) ∨
    ((∀ i j : Fin packet.cusp.count, i ≠ j →
      Disjoint ((packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((packet.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      Disjoint {x | packet.level i x ≤ 90} {y | packet.level j y ≤ 90} ∧
      ∀ x y, packet.level i x ≤ 90 → packet.level j y ≤ 90 →
        ENNReal.ofReal 1 ≤ riemannianEDistOf g x y) ∧
    (∀ z (hz : z ∈ family.zero.centres) (i : Fin packet.cusp.count),
      Disjoint (riemannianBallOf g z.val (family.zero.zero z hz).radius)
        ((packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
    Disjoint (⋃ z, ⋃ hz : z ∈ family.zero.centres,
        riemannianBallOf g z.val (family.zero.zero z hz).radius)
      (⋃ i, tsupport (packet.toBoundaryCollarPacket.block i)))

/-- **`BoundarySupply`** (D61-2 with D64-6): the core supply together with BCG02's joint (BA)
certificates — value AND differential with ONE row (circle) / ONE sign (`edgeB`, slim), error
`θ` — on the projection `family.forgetBFR_BFZD` of the SAME stored family, for every boundary
component whose actual collar block meets the reference ball (`10ρ(j)`, `20Δρ(j)`,
`950000Δρ(j)`). The source is the joint producer `lc88_boundary_packets_BFRZ_BA_BIND`. -/
structure BoundarySupply (K : ℕ) (A : ℝ → ℝ) (β : ℕ → ℝ)
    (βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ)
    (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (δn : ℝ) (n : ℕ)
    (B : NearlyCuspidalBoundary W g K δn)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3)
    extends BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz W g δn n B oM where
  /-- BCG02 (BA) at the circle, `edgeB` and slim references of the SAME family. -/
  ba_spec :
    letI := inducedMetricSpace completion.metric
    letI := completion.complete
    (∀ (j : W.pieceInterior ⊤) (hj : j ∈ family.forgetBFR_BFZD.circle.centres)
      (bb : Fin packet.cusp.count),
      (∃ x ∈ tsupport (packet.toBoundaryCollarPacket.block bb),
        riemannianEDistOf g j.val x < ENNReal.ofReal (10 * rho j)) →
      ∃ Ab : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1),
        Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 10 * rho j →
          ‖EuclideanSpace.single 0 ((packet.height bb y - packet.height bb j) / rho j) -
            Ab ((let c := family.forgetBFR_BFZD.circle.chart j hj;
                letI := (inducedMetricSpace completion.metric).rescale (rho j)⁻¹
                    (inv_pos.mpr (rho_pos j));
                c.coord y) -
              (let c := family.forgetBFR_BFZD.circle.chart j hj;
                letI := (inducedMetricSpace completion.metric).rescale (rho j)⁻¹
                    (inv_pos.mpr (rho_pos j));
                c.coord j))‖ < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 10 * rho j → ∃ θ' < θ,
          ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ =>
                (packet.height bb y - packet.height bb j) / rho j) x u -
            Ab (mvfderiv 𝓘(ℝ, E3) (let c := family.forgetBFR_BFZD.circle.chart j hj;
                letI := (inducedMetricSpace completion.metric).rescale (rho j)⁻¹
                    (inv_pos.mpr (rho_pos j));
                c.coord) x u) 0| ≤
            θ' * Real.sqrt ((scaleMetric ((rho j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (rho_pos j)) 2) completion.metric).inner x u u)) ∧
    (∀ (j : W.pieceInterior ⊤) (hj : j ∈ family.forgetBFR_BFZD.edgeB.centres)
      (bb : Fin packet.cusp.count),
      (∃ x ∈ tsupport (packet.toBoundaryCollarPacket.block bb),
        riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * rho j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * rho j →
          |(packet.height bb y - packet.height bb j) / rho j -
            a * (family.forgetBFR_BFZD.edgeB.coord_BCG1 j hj y -
              family.forgetBFR_BFZD.edgeB.coord_BCG1 j hj j)| < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * rho j → ∃ θ' < θ,
          ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ =>
                (packet.height bb y - packet.height bb j) / rho j) x u -
            a * mvfderiv 𝓘(ℝ, E3) (family.forgetBFR_BFZD.edgeB.coord_BCG1 j hj) x u| ≤
            θ' * Real.sqrt ((scaleMetric ((rho j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (rho_pos j)) 2) completion.metric).inner x u u)) ∧
    ∀ (j : W.pieceInterior ⊤) (hj : j ∈ family.forgetBFR_BFZD.slim.centres)
      (bb : Fin packet.cusp.count),
      (∃ x ∈ tsupport (packet.toBoundaryCollarPacket.block bb),
        riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * rho j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * rho j →
          |(packet.height bb y - packet.height bb j) / rho j -
            a * ((family.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 y -
              (family.forgetBFR_BFZD.slim.centre j hj).coord_BCG2 j)| < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * rho j → ∃ θ' < θ,
          ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ =>
                (packet.height bb y - packet.height bb j) / rho j) x u -
            a * mvfderiv 𝓘(ℝ, E3) (family.forgetBFR_BFZD.slim.centre j hj).coord_BCG2
              x u| ≤
            θ' * Real.sqrt ((scaleMetric ((rho j)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (rho_pos j)) 2) completion.metric).inner x u u)

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

/-- The forgetful projection of the stored family to `LocalPacketsOnBFR` (a definition). -/
def familyBFR :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    LocalPacketsOnBFR (W.pieceInterior ⊤) S.completion.metric
      (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x)
      Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.forgetBFR_BFZD

/-- **Active edge family** = the REVISED edge family `edgeB` of the stored family (a definition;
the inherited old `edge` is never read). -/
def activeEdge :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    EdgeFamilyOn (W.pieceInterior ⊤) S.completion.metric
      (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x)
      β Δ σc μ b s b' s' ε γc βc
      {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.edgeB

/-- Active circle family = the stored family's circle family. -/
def activeCircle :
    letI := inducedMetricSpace S.completion.metric
    CircleFamilyOn 𝓘(ℝ, E3) (W.pieceInterior ⊤) (fun x => S.rho x) (fun x => S.rho_pos x) β
      {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x} :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.circle

/-- Active slim family = the stored family's slim family. -/
def activeSlim :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    SlimFamilyOn (W.pieceInterior ⊤) S.completion.metric
      (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x)
      β Δ σs K {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
      {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x} :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.slim

/-- The raw normalized weak-edge height `edgeB.smoothing / ρ` on `W°` (pointwise; the smoothing of
the stored `edgeB`, never re-chosen). -/
def edgeHeightRaw (x : W.pieceInterior ⊤) : ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.activeEdge.smoothing x / S.rho x

theorem familyBFR_edgeB :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    S.familyBFR.edgeB = S.activeEdge :=
  rfl

theorem activeEdge_eq :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    S.activeEdge = S.family.edgeB :=
  rfl

theorem edgeHeightRaw_apply (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    S.edgeHeightRaw x = S.family.edgeB.smoothing x / S.rho x :=
  rfl

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
