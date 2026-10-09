import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsB
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Producer

/-!
# The FINAL boundary family `LocalPacketsOnBF` (lane BCG-3, review 51 P0-B)

Review 51 (dispositions `docs/geometrization/chapter14/out/dispositions-task51-boundary-family-
enrichment.md`, binding): "Final boundary family" is reserved for the object that carries P0-B (the
same-chart certificates, bound to the same family) and P0-C (requests at the right construction
time). `LocalPacketsOnBF … vs ζ Λz U₁ U₂ Ue₁ Ue₂` extends the enriched base family
`LocalPacketsOnB` by the P0-B certificates as FIELDS (the conjuncts of BCG-2's T2B and of BZ-1's
certified zero producer):
* `circle_residual` (A2, LFR07's residual enclosure on the circle charts);
* `edgeDiskB` (A1, LC84 disk packets of the REVISED edge charts `edgeB`, height on
  `edgeB.smoothing`);
* `edgeB_section` (A7, EGP05's inner sections of the revised edge charts on `(−8.5Δ, 8.5Δ)`);
* `zero_local_comparison` (A3, LC62), `zero_shell_split` and `zero_adapted` (A5, X82 and LC73 of
  quality `ζ`, ratios `λ ≥ Λz`), `zero_curvature` (A6, enlarged zero curvature on
  `B(c, 400 r_c)`).
The texts are those of the closed layers (`LocalChartPacketsD/R/Z/C14`) with the closed
completeness proof replaced by the carrier's `CompleteSpace` and the edge clauses on `edgeB`
(P0-A: every boundary construction consumes `edgeB`). P0-C is carried by the producers (requested
zero cap before `V`, cusp requests before the height; modules `BoundaryPacketsBProducerV2`, `…T3`).

* `LocalPacketsOnBF` (structure);
* `LocalPacketsOnBF.ofClosedC14`: every closed `LocalChartPacketsC14` is a final boundary family
  with all four regions `univ` (`edgeB = edge`);
* `eventually_nonempty_localPacketsOnBF_closed_BCG3`: the closed producer
  `eventually_nonempty_localChartPacketsC14` composed with the specialization (non-vacuous use: the
  structure is inhabited on a tail of every closed standing sequence).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The final boundary family** (review 51 P0-B): the enriched base family `LocalPacketsOnB`
with the same-chart certificates as fields — LFR07's residual on the circle charts, LC84 disk
packets and EGP05 sections on the revised edge charts `edgeB`, and on the zero family LC62, X82,
LC73 (quality `ζ`, ratios `λ ≥ Λz`) and the enlarged zero curvature. -/
structure LocalPacketsOnBF (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [hXc : CompleteSpace X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
    extends LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs U₁ U₂ Ue₁ Ue₂ where
  /-- LFR07's residual enclosure of the circle chart at `j` (A2; TCP01: `|η_j| ≤ 8 ⊂ D_j`). -/
  circle_residual : ∀ j (hj : j ∈ circle.centres),
    let c := circle.chart j hj
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10
  /-- LC84's disk packet over every REVISED edge chart, height on `edgeB.smoothing` (A1). -/
  edgeDiskB : ∀ j (hj : j ∈ edgeB.centres),
    let c := edgeB.chart j hj
    let Fs := edgeB.smoothing
    let A : Set X := closure
      {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := hXc
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
        (fun x => Fs x / ρ j), P.toEdgeChart = c
  /-- EGP05's inner section of every REVISED edge chart, normalized there (A7). -/
  edgeB_section : ∀ j (hj : j ∈ edgeB.centres),
    let c := edgeB.chart j hj
    let Fs := edgeB.smoothing
    let hMc : CompleteSpace X := hXc
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
      ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
        Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ
  /-- LC62's neighbouring-scale bound at every zero centre (A3). -/
  zero_local_comparison : ∀ c (hc : c ∈ zero.centres), ∀ q,
    dist c q ≤ 10 * (zero.zero c hc).radius → T / 20 ≤ (zero.zero c hc).radius / ρ q
  /-- X82 (LC70) at every point of the closed shell of every selected zero ball (A5). -/
  zero_shell_split : ∀ c (hc : c ∈ zero.centres), ∀ q, (zero.zero c hc).radius / 10 ≤ dist c q →
    dist c q ≤ 10 * (zero.zero c hc).radius →
    ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
      ∃ (z : Zf) (F : @KleinerLottApprox X
        (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
        (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
        q (WithLp.toLp 2 (0, z)) (β 1)),
        ∀ x : X, (@KleinerLottApprox.toFun X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
          (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
          q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
          (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))
  /-- LC73 at every point of the closed shell of every selected zero ball, every ratio `λ ≥ Λz`
  (A5). -/
  zero_adapted : ∀ c (hc : c ∈ zero.centres), ∀ q, (zero.zero c hc).radius / 10 ≤ dist c q →
    dist c q ≤ 10 * (zero.zero c hc).radius →
    ∀ (lam : ℝ) (hlam : 0 < lam), Λz ≤ lam →
    let R := (zero.zero c hc).radius
    let hR : 0 < R := (zero.zero c hc).radius_pos
    let η := (zero.zero c hc).radial
    let mr := mX.rescale R⁻¹ (inv_pos.mpr hR)
    let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX) g
      hmetric hR
    let := mr.rescale lam hlam
    letI := (mr.rescale_completeSpace_iff lam hlam).mpr
      ((mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hXc)
    letI := radialScaledBundle gr lam hlam
    letI := radialScaledContinuous gr lam hlam
    letI := radialScaledManifold (m := mr) gr hmr lam hlam
    let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
    let ψ := fun x => lam * (η x - η q)
    ∃ hEnorm : IsMetricNorm h,
      ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
        ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
        (∀ x, (κ.toFun x).fst = lam *
          (@dist X mr.toDist c x - @dist X mr.toDist c q)) ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
        (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
        (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
        ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
          ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
          intrinsicGeodesic h hEnorm x u (dist x y) = y →
          |mvfderiv (I := I3) ψ x u -
            ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ
  /-- The enlarged zero-ball curvature at every selected zero centre (A6). -/
  zero_curvature : ∀ c (hc : c ∈ zero.centres), ∀ y ∈ ball c (400 * (zero.zero c hc).radius),
    SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((zero.zero c hc).radius)⁻¹ ^ 2))

section Closed

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The closed specialization of the final boundary family**: every closed
`LocalChartPacketsC14` is a `LocalPacketsOnBF` with all four regions `univ`; the revised edge
family is the closed edge family, and every certificate is the closed field of the same name
(`edgeDiskB` = `edgeDisk`, `edgeB_section` = `edge_section`). -/
def LocalPacketsOnBF.ofClosedC14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) :
    LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      univ univ univ univ where
  toLocalPacketsOnB := LocalPacketsOnB.ofClosedRV P.toLocalChartPacketsRV
  circle_residual := P.circle_residual
  edgeDiskB := P.edgeDisk
  edgeB_section := P.edge_section
  zero_local_comparison := P.zero_local_comparison
  zero_shell_split := P.zero_shell_split
  zero_adapted := P.zero_adapted
  zero_curvature := P.zero_curvature

end Closed

/-- **Non-vacuous use: the final boundary family on closed standing sequences.** The closed
producer `eventually_nonempty_localChartPacketsC14` composed with `LocalPacketsOnBF.ofClosedC14`:
on one tail of every closed standing sequence the final boundary family with regions `univ` exists
on the same scale `ρ` with LC02's bounds, for every slim value tolerance `vs > 0`, every adapted
quality `β₁ < ζ < 1` (ratios `λ ≥ Λ'`) and every requested zero cap. -/
theorem eventually_nonempty_localPacketsOnBF_closed_BCG3 (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ → ℝ) (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
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
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalPacketsOnBF (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' univ univ univ univ) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ',
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax => ?_⟩
  filter_upwards [h Lmax hLmax] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨P⟩⟩ := hi
  exact ⟨ρ, hρpos, hρb, ⟨LocalPacketsOnBF.ofClosedC14 P⟩⟩

end DifferentialGeometry.Geometry.Collapse
