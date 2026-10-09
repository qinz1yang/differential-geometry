import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketFamilySection

/-!
# Review 51, A1 + A7 + P2: the regional edge kernel with disk packets and sections (lane BE-1)

External review 51 (P0-B, items A1 and A7; P2): the boundary base family must carry, for the
ACTIVE edge family, the closed route's same-chart certificates — LC84's `EdgeDiskPacket` over the
family's own chart with the height on the family's own smoothing (`LocalChartPacketsD.edgeDisk`)
and EGP05's section over `(−8.5Δ, 8.5Δ)` (`LocalChartPacketsC14.edge_section`, blueprint 207B,
B:5042–5053), both produced by the SAME construction; the regional edge kernel is unfolded ONCE and
called at the carrier/region level for each region (old `{D > 10}`, new `{D > 20}`).

* `normalized_volume_and_derivatives_BE1`: LPA01's normalized analytic data at a point in the form
  of the disk kernel's hypotheses (`ρ(p)⁻² g`, volume of the unit ball, derivative bounds on balls of
  radius `< b⁻¹`); `normalized_volume_and_derivatives_LC87` without `[CompactSpace X]` and with the
  radius bound `R < b⁻¹` itself.
* `exists_regional_edgeDiskFamily_BE1`: the regional edge kernel. Threshold chain = the chain of
  `exists_regional_edgeFamily_BDRY4` with the disk/section kernel's smallness folded in (`σ₀ ≤ 10⁻¹⁰`,
  `τ₀ ≤ 10⁻³⁰` by `min`; `ε, μ ≤ 10⁻⁸` and `100ΔΛ ≤ 10⁻⁸` as hypotheses, as in the closed producer
  `eventually_nonempty_localChartFamilyEADS`) and the disk threshold `bd₀` after `(K, v, A)` and before
  `b`; every threshold is chosen before the carrier and the regions. On a complete, proper,
  σ-compact, connected, oriented carrier, for regions `U₂ ⊆ U₁ ⊆ Kc`: ONE `EdgeFamilyOn … U₁ U₂`
  (the family of `exists_regional_edgeFamily_BDRY4`: LFR44 witnesses, BDRY3's selection, ONE global
  smoothing) together with, for THAT family, at every centre `j`:
  (coarse) the recorded coarse-border composite,
  (disk) an `EdgeDiskPacket P` (normalized at `j`, height on the family's smoothing) with
  `P.toEdgeChart = F.chart j hj`,
  (section) a continuous `s : (−8.5Δ, 8.5Δ) → X` with `η_j(s a) = a`, `t(s a) < Δ/100` and
  normalized distance `d(s a, j) < 10Δ` (i.e. `< 10Δρ(j)`).
  The disk packet and the section come from ONE call of
  `exists_edgeDiskPackets_sections_of_strong_edge_family` on the selected centres (the same call
  that produces the smoothing and the charts).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- LPA01's normalized analytic data at a point in the form of the disk kernel's threshold
hypotheses (`ρ(p)⁻² g`, derivative bounds on balls of radius `< b⁻¹`); no compactness. -/
theorem normalized_volume_and_derivatives_BE1 {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [SigmaCompactSpace X]
    [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) X]
    [IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x)]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g) {p : X} {r v b : ℝ} (hr : 0 < r) {K : ℕ}
    (Acurv : ℝ → ℝ)
    (hvol0 : v ≤ (ballVolume (normalizedCenterMetric g r hr) p 1).toReal)
    (hder0 : ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤ Acurv R) :
    have hmetric' := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
    letI := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric' r⁻¹ (inv_pos.mpr hr)
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
    ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) X gR (ball p 1) ∧
      ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k gR y ≤ Acurv R := by
  intro hmetric'
  let mR : MetricSpace X := mX.rescale r⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric' r⁻¹ (inv_pos.mpr hr)
  intro gR
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hmeq : normalizedCenterMetric g r hr = gR := by
    have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
        scaleMetric c hc g = scaleMetric d hd g := by
      rintro c d hc hd rfl
      rfl
    exact key _ _ _ _ (inv_pow r 2).symm
  have hball : ∀ ρ', riemannianBallOf gR p ρ' = ball p ρ' := fun ρ' =>
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR p ρ'
  refine ⟨?_, ?_⟩
  · rw [hmeq] at hvol0
    rw [← hball 1]
    exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
  · intro R hR hRb k hk y hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R := by
      rw [hmeq, hball]
      exact hy
    have hd := hder0 R hR hRb k hk y hy'
    rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
    exact hd

/-- **The regional edge kernel with LC84 disk packets and EGP05 sections on the SAME family.** See
the module docstring. Parameter order: the prefix of `exists_regional_edgeFamily_BDRY4` (edge-chart
constants `βc, γc → σ₀, Δ₀`; `Δ → τ₀, κ₀, bc₀`; `σc, ε, μ, τ, s, b', s' → a₀, b₁`; `Λ`) with
`ε, μ ≤ 10⁻⁸` and `100ΔΛ ≤ 10⁻⁸`; then the analytic data `v, A → bd₀`; the strong quality `b`
(`b < bd₀`); LFR44's `b₀`; then the carrier, the scale, `β`, `σ` and the regions. -/
theorem exists_regional_edgeDiskFamily_BE1 {βc γc : ℝ} (hβc : 0 < βc) (hβγ : βc < γc / 1000)
    (hγc : 0 < γc) (hγc1 : γc < 1 / 100) (K : ℕ) (hK : 5 ≤ K) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∀ v : ℝ, 0 < v → ∀ Aprof : ℝ → ℝ, ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] [ProperSpace X] [ConnectedSpace X]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ManifoldOrientation (𝓡 3) X 3 →
        ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p), ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ →
        LipschitzWith (Real.toNNReal Λ) ρ →
      ∀ (β : ℕ → ℝ), β 2 = β₂ → β 1 < b₀ → ∀ {σ : ℝ}, σ ≤ a₀ →
      ∀ (U₁ U₂ Kc : Set X), IsCompact Kc → U₁ ⊆ Kc → U₂ ⊆ U₁ →
      (∀ p ∈ U₂, ∀ a, dist a p < Δ * ρ a → a ∈ U₁) →
      (∀ p ∈ U₂, ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
      (∀ p ∈ U₁, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ₀ / ρ p) ^ 2)) →
      (∀ p ∈ U₁, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      (∀ p ∈ U₁, ∀ y ∈ ball p (4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ p),
        SectionalBoundedBelowAt g y (-((4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ p) ^ 2)⁻¹)) →
      (∀ p ∈ U₁, v ≤ (DifferentialGeometry.Geometry.Collapse.ballVolume
        (normalizedCenterMetric g (ρ p) (hρpos p)) p 1).toReal) →
      (∀ p ∈ U₁, ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R) →
      ∃ F : EdgeFamilyOn X g hmetric ρ hρpos β Δ σc μ b s b' s' ε γc βc U₁ U₂,
        (∀ j (hj : j ∈ F.centres),
          let c := F.chart j hj
          let A : Set X := closure
            {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
          let hMc : CompleteSpace X := ‹CompleteSpace X›
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          (c.Qn j = 0 ∧
            (∀ x ∈ ball j (200 * Δ), ∀ y ∈ ball j (200 * Δ),
              (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
            (∀ x ∈ ball j (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
            (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
              ∃ x ∈ ball j (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
            (∀ a ∈ A ∩ ball j (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
            (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball j (190 * Δ),
              dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))) ∧
        (∀ j (hj : j ∈ F.centres),
          let c := F.chart j hj
          let Fs := F.smoothing
          let A : Set X := closure
            {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
          let hMc : CompleteSpace X := ‹CompleteSpace X›
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
            scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
          have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
          ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
            (fun x => Fs x / ρ j), P.toEdgeChart = c) ∧
        ∀ j (hj : j ∈ F.centres),
          let c := F.chart j hj
          let Fs := F.smoothing
          let hMc : CompleteSpace X := ‹CompleteSpace X›
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
            ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
              Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ := by
  classical
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hE⟩ :=
    exists_edgeDiskPackets_sections_of_strong_edge_family hβc hβγ hγc hγc1
  refine ⟨min σ₀ (1 / 10 ^ 10), lt_min hσ₀ (by norm_num), Δ₀, hΔ₀,
    fun β₂ Δ hβ₂ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, hE⟩ := hE Δ hΔ₀Δ hΔ1
  refine ⟨min τ₀ (1 / 10 ^ 30), lt_min hτ₀ (by norm_num), κ₀, hκ₀, bc₀, hbc₀,
    fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s' hs hssmall hsb' hss' hb'd
      hs'd hb'e hs'e => ?_⟩
  obtain ⟨b₁, hb₁, hE⟩ := hE σc ε μ τ κ₀ s b' s' hσc (hσcσ₀.trans (min_le_left _ _))
    (hσcσ₀.trans (min_le_right _ _)) hε hε1 hε8 hμ hμ1 hμ8 hτ (hττ₀.trans (min_le_left _ _))
    (hττ₀.trans (min_le_right _ _)) hθ hκ₀.le le_rfl hb'd hs'd hb'e hs'e hsb' hss'
  obtain ⟨a₀, ha₀, hdens⟩ := exists_strong_edge_density_riemannian.{0, 0, 0, 0}
    (I := 𝓘(ℝ, E3)) hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, b₁, ha₀, hb₁, fun Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 v hv Aprof => ?_⟩
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  obtain ⟨bd₀, hbd₀, hE⟩ := hE (Real.toNNReal Λ) (by rw [hΛc]; exact hlam)
    (by rw [hΛc]; exact hbudget) (by rw [hΛc]; exact hΛ44) (by rw [hΛc]; exact hend)
    (by rw [hΛc]; exact hΛ8) K hK 1 v one_pos hv Aprof
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd => ?_⟩
  have hb100 : b < 1 / 100 := by
    have h1 : 100 < b⁻¹ := lt_of_le_of_lt (by linarith) hsource
    have h2 := (lt_inv_comm₀ (by norm_num) hb).mp h1
    linarith
  have hE := hE b hb hbc hbb₁ hbd hb100 hsource hbs
  obtain ⟨b₀, hb₀, hdens⟩ := hdens b hb hb100
  refine ⟨b₀, hb₀, fun X mX _ _ _ _ _ _ g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1 σ hσa₀ U₁ U₂ Kc
    hKc hU₁ hU₂ hmargin hmodel hsecκ hsecb hsecM hvol0 hder0 => ?_⟩
  -- the Riemannian instances of the aligned metric
  let instRB : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have instCRB : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have instRM : IsRiemannianManifold 𝓘(ℝ, E3) X := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  have instM1 : IsManifold 𝓘(ℝ, E3) 1 X := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have instT2 : T2Space (TangentBundle 𝓘(ℝ, E3) X) := inferInstance
  have hsmall : ((Real.toNNReal Λ : NNReal) : ℝ) * Δ ≤ 1 / 100 := by
    rw [hΛc]
    linarith [mul_pos hΔpos hΛ]
  -- LFR44's strong-edge selection: candidates the strong edges of `U₁`
  let Es : Set X := {a | a ∈ U₁ ∧
    @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b s}
  let N : Set X := {p | p ∈ U₂ ∧ p ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 1 ∧
    ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))}
  have hN : ∀ p ∈ N, ∃ q ∈ Es, dist p q < Δ * ρ q := by
    rintro p ⟨hpU, hpS, hns⟩
    obtain ⟨C, mC, c, hCc, -, hCdim, hCcomp, hCseg, hf⟩ := hmodel p hpU
    have hnonslim : letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        ∀ (A : Type) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
          diam (univ : Set A) < 1000 * Δ →
          ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)) := by
      intro A mA a hbdd hdiam hne
      exact hns ⟨A, mA, a, hbdd, hdiam, hne⟩
    obtain ⟨a, ha, hd⟩ := (hdens X g hmetric (Real.toNNReal Λ) ρ hρpos hρlip
      (by rw [hΛc]; exact hΛ44) β hβ2 hβ1 p hpS hnonslim C c σ hCseg hCdim hCcomp hσa₀ hf).1
    exact ⟨a, ⟨hmargin p hpU a hd, ha⟩, by rwa [dist_comm]⟩
  obtain ⟨Je, hJeE, hJefin, hJedisj, hcov, hcovE⟩ :=
    exists_finite_strong_edge_selection_of_compact_BDRY3 hKc (E := Es) (N := N) (W := ∅)
      (fun a ha => hU₁ ha.1) hρlip hρpos hΔ1 hsmall hN (fun p hp => absurd hp (notMem_empty p))
  have hJeU : ∀ j ∈ Je, j ∈ U₁ := fun j hj => (hJeE hj).1
  have hJeS : ∀ j ∈ Je,
      @isEdgePoint.{0, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s :=
    fun j hj => (hJeE hj).2
  -- the multiplicity
  have hbudgetM : ((Real.toNNReal Λ : NNReal) : ℝ) * (2000000 * Δ) ≤ 1 / 4 := by
    rw [hΛc]
    linarith [mul_pos hΔpos hΛ]
  -- ONE call of the disk/section kernel: ONE smoothing, the charts, the coarse-border composite,
  -- the disk packets over the charts and the sections, at every selected centre
  obtain ⟨F, hF0, hFL, hF⟩ : ∃ F : X → ℝ, (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      ∀ p ∈ Je, (∀ x, |F x - infDist x (closure {y | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'})| < μ * (Δ * ρ p)) ∧
      (let A : Set X := closure
        {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      ∃ c : EdgeChart gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ p) (fun x => F x / ρ p),
        c.center = p ∧
        (c.Qn p = 0 ∧
          (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
            (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
          (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
          (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
            ∃ x ∈ ball p (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
          (∀ a ∈ A ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
          (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball p (190 * Δ),
            dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)) ∧
        ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ p) (fun x => F x / ρ p),
          P.toEdgeChart = c ∧
          ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
            ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
              F (sec a) / ρ p / (ρ (sec a) / ρ p) < Δ / 100 ∧ dist (sec a) p < 10 * Δ) := by
    rcases Je.eq_empty_or_nonempty with hJe | hJne
    · refine ⟨fun _ => 0, fun _ => le_rfl, (LipschitzWith.const (0 : ℝ)).weaken bot_le,
        fun p hp => ?_⟩
      rw [hJe] at hp
      exact absurd hp (notMem_empty p)
    have hcentre := fun p (hp : p ∈ hJefin.toFinset) =>
      normalized_volume_and_derivatives_BE1 g hEnorm (p := p) (b := b) (hρpos p) (K := K) Aprof
        (hvol0 p (hJeU p (hJefin.mem_toFinset.mp hp)))
        (hder0 p (hJeU p (hJefin.mem_toFinset.mp hp)))
    obtain ⟨F, hF0, hFL, hFc⟩ := hE X g hEnorm o ρ hρpos hJefin.toFinset
      (by rw [Set.Finite.toFinset_nonempty]; exact hJne)
      (fun p hp => hJeS p (hJefin.mem_toFinset.mp hp))
      (fun p hp => hsecκ p (hJeU p (hJefin.mem_toFinset.mp hp)))
      (fun p hp => hsecb p (hJeU p (hJefin.mem_toFinset.mp hp))) hρlip hρsm hcentre
    exact ⟨F, hF0, hFL, fun p hp => hFc p (hJefin.mem_toFinset.mpr hp)⟩
  have hecent := fun j (hj : j ∈ Je) => (hF j hj).2
  choose ec hec using hecent
  refine ⟨{ centres := Je
            finite_centres := hJefin
            centres_subset := hJeU
            strong := hJeS
            disjoint_centres := hJedisj
            covers_strong := fun a ha hE => hcovE a ⟨ha, hE⟩
            covers_nonslim := fun p hp hns => hcov p (Or.inl ⟨hp.1, hp.2, hns⟩)
            multiplicity := fun x => ncard_disjoint_family_balls_le_proper_BDRY3 g hEnorm
              finrank_euclideanSpace_fin hρlip hρpos hΔpos hbudgetM hJefin hJedisj
              (fun j hj => hsecM j (hJeU j hj)) x
            smoothing := F
            smoothing_nonneg := hF0
            lipschitz_smoothing := hFL
            smoothing_value := fun p hp => (hF p hp).1
            chart := ec
            chart_center := fun j hj => (hec j hj).1 },
    fun j hj => (hec j hj).2.1, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨P, hP, -⟩ := (hec j hj).2.2
    exact ⟨P, hP⟩
  · obtain ⟨-, -, sec, hsc, hsec⟩ := (hec j hj).2.2
    exact ⟨sec, hsc, hsec⟩

end DifferentialGeometry.Geometry.Collapse
