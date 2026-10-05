import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalEdgeDisk
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDiskApplications

/-!
# Consumers of the regional edge kernel with disk packets and sections (lane BE-1)

* `EdgeFamilyOn.zeroFibre_disk_section_BE1`: at a centre `j` of a regional edge family, the
  disk clause and the section clause of `exists_regional_edgeDiskFamily_BE1` (for the family's own
  chart, normalized at `j`) give together: the whole zero fibre
  `{y ∈ B(j, 100Δ) : η_j y = 0, H y ≤ 4Δ}` of the chart is homeomorphic to the closed disk, compact
  and connected (LFR33's fibre, from the disk packet), and every value `a ∈ (−8.5Δ, 8.5Δ)` of `η_j` is
  taken in `B(j, 10Δ)` at a point of height `H ≤ 4Δ` (from the section: `t < Δ/100 ≤ 4Δ`); in
  particular the zero fibre contains the section point over `0`.
* `exists_two_regional_edgeDiskFamilies_BE1` (review 51, P2): the regional edge kernel's threshold
  chain unfolded ONCE and the kernel called TWICE at the carrier/region level, for two region pairs
  `(U₁, U₂)` and `(V₁, V₂)` on the same carrier with the same scale (the boundary instances are
  `U₁ = {D > 10}`, `U₂ = {D ≥ 20}` and `V₁ = {D > 20}`, `V₂ = {D ≥ 35}`, lane BCG-2): two edge
  families, and on EACH returned family the consequence above at every centre.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The disk fibre and the section of the same chart.** At a centre `j` of a regional edge
family, the disk clause and the section clause of `exists_regional_edgeDiskFamily_BE1` give: the zero
fibre of the family's chart (normalized at `j`, height on the family's smoothing) is a closed disk,
compact and connected, and every value `a ∈ (−8.5Δ, 8.5Δ)` of the chart coordinate is taken in
`B(j, 10Δ)` at a point of height `≤ 4Δ`. -/
theorem EdgeFamilyOn.zeroFibre_disk_section_BE1 {X : Type} [mX : MetricSpace X]
    [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρpos : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
    {U₁ U₂ : Set X} (F : EdgeFamilyOn X g hmetric ρ hρpos β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ F.centres)
    (hdisk : let c := F.chart j hj
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
        (fun x => Fs x / ρ j), P.toEdgeChart = c)
    (hsec : let c := F.chart j hj
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
          Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ) :
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
    (Nonempty ({y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ∧
      ConnectedSpace {y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ}) ∧
    ∀ a ∈ Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), ∃ x ∈ ball j (10 * Δ), c.coord x = a ∧
      edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) x ≤ 4 * Δ := by
  have hc := F.chart_center j hj
  intro c Fs hMc
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
  have hc' : c.center = j := hc
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP⟩ := hdisk
    have h := P.fibre_closedCell_of_eq hP hΔ
    rw [hc'] at h
    exact h
  · intro a ha
    obtain ⟨sec, -, hs⟩ := hsec
    obtain ⟨h1, h2, h3⟩ := hs ⟨a, ha⟩
    refine ⟨sec ⟨a, ha⟩, h3, h1, ?_⟩
    rw [edgeRowHeight_le_iff hΔ]
    exact h2.le.trans (by linarith)

/-- **Review 51, P2: the regional edge kernel unfolded once, called twice.** One threshold chain
(that of `exists_regional_edgeDiskFamily_BE1`), then the carrier, the scale, `β`, `σ`, and TWO
region pairs `(U₁, U₂)`, `(V₁, V₂)` with their own hypotheses: two regional edge families, and on
each returned family, at every centre, the disk fibre and the section of the family's own chart
(`EdgeFamilyOn.zeroFibre_disk_section_BE1`). -/
theorem exists_two_regional_edgeDiskFamilies_BE1 {βc γc : ℝ} (hβc : 0 < βc)
    (hβγ : βc < γc / 1000) (hγc : 0 < γc) (hγc1 : γc < 1 / 100) (K : ℕ) (hK : 5 ≤ K) :
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
      ∀ (V₁ V₂ Kv : Set X), IsCompact Kv → V₁ ⊆ Kv → V₂ ⊆ V₁ →
      (∀ p ∈ V₂, ∀ a, dist a p < Δ * ρ a → a ∈ V₁) →
      (∀ p ∈ V₂, ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
      (∀ p ∈ V₁, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ₀ / ρ p) ^ 2)) →
      (∀ p ∈ V₁, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      (∀ p ∈ V₁, ∀ y ∈ ball p (4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ p),
        SectionalBoundedBelowAt g y (-((4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ p) ^ 2)⁻¹)) →
      (∀ p ∈ V₁, v ≤ (DifferentialGeometry.Geometry.Collapse.ballVolume
        (normalizedCenterMetric g (ρ p) (hρpos p)) p 1).toReal) →
      (∀ p ∈ V₁, ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R) →
      ∃ F : EdgeFamilyOn X g hmetric ρ hρpos β Δ σc μ b s b' s' ε γc βc U₁ U₂,
      ∃ Fe : EdgeFamilyOn X g hmetric ρ hρpos β Δ σc μ b s b' s' ε γc βc V₁ V₂,
        (∀ j (hj : j ∈ F.centres),
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
          Nonempty ({y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
              edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ≃ₜ
                ClosedCell 2) ∧
          ∀ a ∈ Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), ∃ x ∈ ball j (10 * Δ), c.coord x = a ∧
            edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) x ≤ 4 * Δ) ∧
        ∀ j (hj : j ∈ Fe.centres),
          let c := Fe.chart j hj
          let Fs := Fe.smoothing
          let hMc : CompleteSpace X := ‹CompleteSpace X›
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          Nonempty ({y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
              edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ≃ₜ
                ClosedCell 2) ∧
          ∀ a ∈ Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), ∃ x ∈ ball j (10 * Δ), c.coord x = a ∧
            edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) x ≤ 4 * Δ := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := exists_regional_edgeDiskFamily_BE1 hβc hβγ hγc hγc1 K hK
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8
    s b' s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 v hv Aprof => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 v hv Aprof
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd
  refine ⟨b₀, hb₀, fun X mX _ _ _ _ _ _ g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1 σ hσa₀
    U₁ U₂ Kc hKc hU₁ hU₂ hmargin hmodel hsecκ hsecb hsecM hvol hder
    V₁ V₂ Kv hKv hV₁ hV₂ hmarginV hmodelV hsecκV hsecbV hsecMV hvolV hderV => ?_⟩
  -- first call: the region pair `(U₁, U₂)`
  obtain ⟨F, -, hdisk, hsec⟩ := h X g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1 hσa₀ U₁ U₂ Kc hKc
    hU₁ hU₂ hmargin hmodel hsecκ hsecb hsecM hvol hder
  -- second call: the region pair `(V₁, V₂)`, same thresholds, same carrier and scale
  obtain ⟨Fe, -, hdiskV, hsecV⟩ := h X g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1 hσa₀ V₁ V₂ Kv hKv
    hV₁ hV₂ hmarginV hmodelV hsecκV hsecbV hsecMV hvolV hderV
  refine ⟨F, Fe, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨⟨hfib, -, -⟩, hval⟩ :=
      F.zeroFibre_disk_section_BE1 hΔpos hj (hdisk j hj) (hsec j hj)
    exact ⟨hfib, hval⟩
  · obtain ⟨⟨hfib, -, -⟩, hval⟩ :=
      Fe.zeroFibre_disk_section_BE1 hΔpos hj (hdiskV j hj) (hsecV j hj)
    exact ⟨hfib, hval⟩

end DifferentialGeometry.Geometry.Collapse
