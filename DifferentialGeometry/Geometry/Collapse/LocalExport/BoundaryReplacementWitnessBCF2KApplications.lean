import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementWitnessBCF2K

/-!
# Consumer: BCF02's strict replacement, steps one to three, on the final boundary family

`LocalPacketsOnBFRZ.bcf02_steps_one_three_BCF2K` composes the two groups of lane BCF2-K on ONE final
boundary family over `(W°, d_ĝ)` (regions `{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}`), with
BCP04.a at the index `n`: for a revised edge centre `i` and `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`,
`t(q) ≤ 4.01Δ`, `D(q) ≥ 35`, outside every selected zero ball `B(z, .38R_z)` and every selected slim
region `{d(q, k) < 9Δρ_k, |η_k(q)| < 10Δ}` (the original-coordinate consequences of `q ∈ M₂`):
EDP03's enclosure gives `d(q, i) < 6Δρ_i`; step one makes `p_i` a nonslim one-stratum point; steps
two and three give the weak witness `q'`, the strong witness `a` with `D(a) > 70/3`, and a centre
`j` of the SAME `edgeB` with `d(a, j) < Δρ_j`. No membership of `q` in the open edge base is
assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2


/-- **BCF02's strict replacement, steps one to three, on the final boundary family** (see the
module docstring). -/
theorem LocalPacketsOnBFRZ.bcf02_steps_one_three_BCF2K (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hn : 1140 * Δ ≤ 35 * n) (hT : 1000 * Δ ≤ T)
    (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hβ2 : β 2 < 1 / 1000000)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      (i : W.pieceInterior ⊤), i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        i ∈ scaledSplittingStratum.{0, 0} (fun x : W.pieceInterior ⊤ => ρ x) (fun x => hρ x) β 1 ∧
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) (WithLp 2 (ℝ × Z))
            ((inducedMetricSpace ĝ).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i
            (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) ∧
        ∃ q' a : W.pieceInterior ⊤, @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
          dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
          |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100 ∧
          F.edgeB.smoothing q' / ρ q' < Δ / 100 ∧
          @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
          dist q' a < ρ a ∧ ENNReal.ofReal (70 / 3) < distanceToBoundary W g a ∧
          ∃ j ∈ F.edgeB.centres, dist a j < Δ * ρ j := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F i hi q hq hηq htq hq35 hZ hS
  have hΔ0 : 0 < Δ := by linarith
  have hlam' : 100 * Δ * Λ ≤ 1 / 100 := hlam.trans (by norm_num)
  have hqi : dist q i < 6 * Δ * ρ i :=
    (F.toLocalPacketsOnB.edgeB_enclosure_BCF2K hΔ0 hμ hτ hlam hi (by norm_num) (by norm_num)
      (mem_ball.mpr hq) hηq htq).2 (by norm_num)
  obtain ⟨h1, hns⟩ := F.toLocalPacketsOnBFR.bcf02_centre_decision_BCF2K hΔ0 hΛ hlam' hT hσs
    hσs1 hb hs hβ2 hi hqi hZ hS
  exact ⟨h1, hns, F.bcf02_strong_witness_BCF2K W g ĝ hle ρ hρ hbcp hΔ hΛ hμ hτ hlam hn oM i hi
    h1 hns q hq hηq htq hq35⟩

end DifferentialGeometry.Geometry.Collapse
