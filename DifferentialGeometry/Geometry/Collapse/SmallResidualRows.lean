import DifferentialGeometry.Geometry.Collapse.SmallZeroRows
import DifferentialGeometry.Geometry.Collapse.SmallRadial
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualProducer

/-!
The residual packet is produced on one small model, with its scale returned to the actual source.
The metric and orientation squares retain the original carrier and the same selected data.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
open Set Filter

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

theorem eventually_nonempty_localChartPacketsR_smallSources
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
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
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type u) [_mX : ∀ i, MetricSpace (X i)] [_cX : ∀ i, ChartedSpace E3 (X i)]
        [_sX : ∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [_cptX : ∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (_hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∀ oX : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
      ∃ S : ∀ i, SmallManifoldModel (I := I3) (X i),
      let Y := fun i => (S i).Carrier
      let mY := fun i => (S i).metricSpace
      letI _smallMetrics := mY
      letI _smallCharts := fun i => (S i).charts
      letI _smallSmooth := fun i => (S i).smooth
      letI _smallCompact : ∀ i, CompactSpace (Y i) :=
        fun i => (S i).diffeo.toHomeomorph.symm.compactSpace
      ∃ oY : ∀ i, ManifoldOrientation I3 (Y i) 3,
        (∀ i, (S i).diffeo.symm.preservesOrientation (oX i) (oY i)) ∧
      let gY := fun i => (S i).metric (g i)
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsR (Y i) (gY i)
          ((S i).metric_aligned (g i) (_hmetric i))
          (ρ ∘ (S i).diffeo) (fun x => hρpos ((S i).diffeo x)) Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
 := by
  classical
  obtain ⟨a₂, ha₂, hγ⟩ := eventually_nonempty_localChartPacketsR hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, ?_⟩
  intro γ hγpos hγone
  obtain ⟨β₀, hβ₀, hβ₀a, hβc⟩ := hγ γ hγpos hγone
  refine ⟨β₀, hβ₀, hβ₀a, ?_⟩
  intro βc γc hβcpos hβcγc hγcpos hγcone
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hΔ⟩ := hβc βc γc hβcpos hβcγc hγcpos hγcone
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, ?_⟩
  intro β₂ Δ hβ₂ hβ₂β₀ hβ₂one hΔβ hΔΔ₀
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hσc⟩ := hΔ β₂ Δ hβ₂ hβ₂β₀ hβ₂one hΔβ hΔΔ₀
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, ?_⟩
  intro σc ε μ τ hσcpos hσcσ₀ hσcone hεpos hεone hμpos hμone hτpos hττ₀
    hτε hεsmall hμsmall s b' s' hs hsone hsb' hss' hb'Δ hs'Δ hb'τ hs'τ
  obtain ⟨a₀, b₁, ha₀, hb₁, hσ⟩ :=
    hσc σc ε μ τ hσcpos hσcσ₀ hσcone hεpos hεone hμpos hμone hτpos hττ₀
      hτε hεsmall hμsmall s b' s' hs hsone hsb' hss' hb'Δ hs'Δ hb'τ hs'τ
  refine ⟨a₀, b₁, ha₀, hb₁, ?_⟩
  intro σ hσpos hσa₂ hσspl hσa₀ Λ hΛpos hΔΛ hΛΔ hΔΛsmall hquality hΛs' hΔΛtiny
  obtain ⟨w₀, hw₀, hw⟩ :=
    hσ σ hσpos hσa₂ hσspl hσa₀ Λ hΛpos hΔΛ hΛΔ hΔΛsmall hquality hΛs' hΔΛtiny
  refine ⟨w₀, hw₀, ?_⟩
  intro w hwpos hww₀ hwp
  obtain ⟨bd₀, hbd₀, hb⟩ := hw w hwpos hww₀ hwp
  refine ⟨bd₀, hbd₀, ?_⟩
  intro b hbpos hbs hbbc₀ hbb₁ hΔb hbbd₀
  obtain ⟨b₀, hb₀, hβ⟩ := hb b hbpos hbs hbbc₀ hbb₁ hΔb hbbd₀
  refine ⟨b₀, hb₀, ?_⟩
  intro β hβtwo hβonepos hβoneb₀ hβoneone hβthree ζ hβζ hζone
  obtain ⟨εr, δ', Λ', hεr, hεrone, hδ', hΛ', hfinal⟩ :=
    hβ β hβtwo hβonepos hβoneb₀ hβoneone hβthree ζ hβζ hζone
  refine ⟨εr, δ', Λ', hεr, hεrone, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he heone Lmax hLmax X mX cX sX cptX g hmetric α hα hstand hder oX
  let S := fun i => smallCompactThreeModel (X i)
  let Y := fun i => (S i).Carrier
  let mY := fun i => (S i).metricSpace
  let smallMetrics := mY
  let smallCharts := fun i => (S i).charts
  let smallSmooth := fun i => (S i).smooth
  let smallCompact : ∀ i, CompactSpace (Y i) :=
    fun i => (S i).diffeo.toHomeomorph.symm.compactSpace
  let oY := fun i => Classical.choose ((S i).exists_orientation (oX i))
  have hO : ∀ i, (S i).diffeo.symm.preservesOrientation (oX i) (oY i) :=
    fun i => Classical.choose_spec ((S i).exists_orientation (oX i))
  refine ⟨S, oY, hO, ?_⟩
  let gY := fun i => (S i).metric (g i)
  have hm : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b) :=
    fun i => (S i).metric_aligned (g i) (hmetric i)
  have hsY : ∀ i (p : Y i),
      ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p := by
    intro i p
    rw [smallModel_firstVolumeScale, smallModel_curvatureRadius]
    exact hstand i ((S i).diffeo p)
  have hd : ∀ i (p : Y i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gY i) p (C * firstVolumeScale (gY i) p v),
        curvatureDerivativeNorm (gY i) k y ≤
          A C v * (firstVolumeScale (gY i) p v ^ (k + 2))⁻¹ := by
    intro i p v hv hvc hav C hC hCa k hk y hy
    rw [smallModel_curvatureDerivativeNorm, smallModel_firstVolumeScale]
    apply hder i ((S i).diffeo p) v hv hvc hav C hC hCa k hk ((S i).diffeo y)
    rw [smallModel_ball_preimage, smallModel_firstVolumeScale] at hy
    exact hy
  obtain ⟨V, hTV, δ, hδ, hδδ', hpackets⟩ :=
    hfinal T hT hTΛ e he heone Lmax hLmax Y gY hm α hα hsY hd oY
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  filter_upwards [hpackets] with i hi
  rcases hi with ⟨ρY, hρY, hρbounds, hP⟩
  let ρ : X i → ℝ := ρY ∘ (S i).diffeo.symm
  have hρpos : ∀ p, 0 < ρ p := fun p => hρY ((S i).diffeo.symm p)
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · intro p
    have hh := hρbounds ((S i).diffeo.symm p)
    rw [smallModel_firstVolumeScale, smallModel_firstVolumeScale,
      Diffeomorph.apply_symm_apply] at hh
    exact hh
  · have hρsquare : ρ ∘ (S i).diffeo = ρY := by
      funext x
      exact congrArg ρY ((S i).diffeo.symm_apply_apply x)
    simpa only [hρsquare] using hP

section OriginalFields

variable {M : Type u} [mM : MetricSpace M] [cM : ChartedSpace E3 M]
  [sM : IsManifold I3 ∞ M] [compactM : CompactSpace M]
  (S : SmallManifoldModel (I := I3) M)

local instance smallMetricResidual : MetricSpace S.Carrier := S.metricSpace
local instance smallCompactResidual : CompactSpace S.Carrier :=
  S.diffeo.toHomeomorph.symm.compactSpace

variable (g : SmoothRiemannianMetric I3 M)
  (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
  (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
  (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
  (P : LocalChartPacketsR S.Carrier (S.metric g) (S.metric_aligned g hmetric)
    (ρ ∘ S.diffeo) (fun p => hρ (S.diffeo p)) Λ β Δ σs K
    σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)

theorem smallModel_circle_residual_original (j : S.Carrier) (hj : j ∈ P.circle.centres) :
    let c := P.circle.chart j hj
    letI _smallRescaled := (smallMetricResidual (mM := mM) S).rescale ((ρ ∘ S.diffeo) j)⁻¹
      (inv_pos.mpr (hρ (S.diffeo j)))
    letI _sourceRescaled := mM.rescale (ρ (S.diffeo j))⁻¹ (inv_pos.mpr (hρ (S.diffeo j)))
    ∀ x ∈ Metric.ball (S.diffeo j) 200,
      ‖c.coord (S.diffeo.symm x)‖ ≤ 8 → x ∈ Metric.ball (S.diffeo j) 10 := by
  let c := P.circle.chart j hj
  have hnative := P.circle_residual j hj
  let eR := S.isometryEquiv.rescale (ρ (S.diffeo j))⁻¹
    (inv_pos.mpr (hρ (S.diffeo j)))
  let sourceRescaled := mM.rescale (ρ (S.diffeo j))⁻¹
    (inv_pos.mpr (hρ (S.diffeo j)))
  let smallRescaled := (smallMetricResidual (mM := mM) S).rescale ((ρ ∘ S.diffeo) j)⁻¹
    (inv_pos.mpr (hρ (S.diffeo j)))
  change ∀ x ∈ Metric.ball (S.diffeo j) 200,
    ‖c.coord (S.diffeo.symm x)‖ ≤ 8 → x ∈ Metric.ball (S.diffeo j) 10
  intro x hx hcoord
  have hd : dist (S.diffeo.symm x) j = dist x (S.diffeo j) := by
    have h := eR.symm.dist_eq x (S.diffeo j)
    change dist (S.diffeo.symm x) (S.diffeo.symm (S.diffeo j)) =
      dist x (S.diffeo j) at h
    simpa only [Diffeomorph.symm_apply_apply] using h
  have hsmall := hnative (S.diffeo.symm x)
    (by simpa only [Metric.mem_ball, hd] using hx) hcoord
  simpa only [Metric.mem_ball, hd] using hsmall

theorem smallModel_zero_local_comparison_original :
    letI _modelMetrics := P.instMetricN
    letI _modelCharts := P.instChartedN
    letI _coneMetrics := P.instMetricC
    ∀ (c : S.Carrier) (hc : c ∈ P.zero.centres) (q : M),
      dist (S.diffeo c) q ≤ 10 * (P.zero.zero c hc).radius →
      T / 20 ≤ (P.zero.zero c hc).radius / ρ q := by
  let modelMetrics := P.instMetricN
  let modelCharts := P.instChartedN
  let coneMetrics := P.instMetricC
  intro c hc q hq
  have hd : dist c (S.diffeo.symm q) = dist (S.diffeo c) q := by
    have h := S.isometryEquiv.dist_eq c (S.diffeo.symm q)
    change dist (S.diffeo c) (S.diffeo (S.diffeo.symm q)) =
      dist c (S.diffeo.symm q) at h
    rw [S.diffeo.apply_symm_apply] at h
    exact h.symm
  have ht := P.zero_local_comparison c hc (S.diffeo.symm q) (by rwa [hd])
  simpa only [Function.comp_apply, Diffeomorph.apply_symm_apply] using ht

end OriginalFields

end DifferentialGeometry.Geometry.Collapse
