import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBValueBEC

/-!
# BCF02, strict replacement (Repl_∂) with EGP04's (EC) instantiated on the same final family

Review 68, A4 (D68-5): the EC-conditional exit
`LocalPacketsOnBFRZ.bcf02_strict_replacement_of_comparison_BCF2K` carries EGP04's value clause as
data; here it is instantiated by lane B-EGP04-EC's `egp04_edgeB_value_BFRZ` on the SAME
`LocalPacketsOnBFRZ F` through `F.edgeB` (value clause only, which is all BCF02 needs; the
derivative clause is Codex X140's). The parameter order of the supplier is
kept: its early constants `σ, η` depend only on `θ = 1/100`, the exclusion quality `ν = 10⁻⁷` and
`Δ`, and are fixed BEFORE every family parameter; the requests `σ⁻¹ ≤ Lmax`, `b ≤ η`, `3b ≤ σ`,
`b(2(20Δ + 1)) ≤ 1`, `μΔ < 10⁻⁴` are tail requests on the register's later universally quantified
parameters `b, μ, Lmax` (never chosen after `q`, `j` or `E`).

* `bcf02_ec_value_edgeB_BCF2K`: EGP04 (EC), value clause, in the vocabulary of BCF02 step four
  (`coord_BAUGA`): for `i, j ∈ I_e^B` and a point `q' ∈ D_i` with `ζ_j(q') = 1` (so `j ∈ J_e(i)`),
  a sign `a` and a constant `c` with `|s_j η_j − (aη_i + c)| < 1/100` on `D_i`;
* `LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K`: (Repl_∂) on the final boundary family over
  `(W°, d_ĝ)` with NO comparison data left: `∃ j ∈ I_e^B, |η_j(q)| < 2Δ, ζ_j(q) = 1,
  v_j(π₂E q) = ρ_j, |u_j(π₂E q)|/ρ_j < 3Δ`;
* `bcf02_register_lipschitz_BCF2K`: the T3B register's clauses `Λ < s'/(10⁸Δ²)`, `s' < 1/(10⁶Δ)`
  give the supplier's `10⁶ΔΛ < 10⁻⁵`.
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

/-- **The register supplies the supplier's Lipschitz bound**: `Δ ≥ 1`, `0 ≤ Λ`, the T3B register's
`Λ < s'/(10⁸Δ²)` and `s' < 1/(10⁶Δ)` give `10⁶ΔΛ < 10⁻⁵`. -/
theorem bcf02_register_lipschitz_BCF2K {Δ Λ s' : ℝ} (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛs : Λ < s' / (100000000 * Δ ^ 2)) (hs' : s' < 1 / (1000000 * Δ)) :
    1000000 * Δ * Λ < 1 / 100000 := by
  have hΔ0 : 0 < Δ := by linarith
  have h1 : Λ * (100000000 * Δ ^ 2) < s' := (lt_div_iff₀ (by positivity)).mp hΛs
  have h2 : s' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hs'
  have h3 : Λ * (100000000 * Δ ^ 2) * (1000000 * Δ) < 1 := by
    have := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < 1000000 * Δ)
    linarith
  have h4 : Δ * Λ ≤ Δ ^ 3 * Λ := by
    have hΔ3 : Δ ≤ Δ ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right hΔ3 hΛ
  nlinarith

/-- **EGP04 (EC), value clause, in BCF02's vocabulary** (wrapper of `egp04_edgeB_value_BFRZ` with
`θ = 1/100`, `ν = 10⁻⁷`): early constants `σ, η` (depending on `Δ` only); then on every final
boundary family with `σ⁻¹ ≤ Lmax`, `b ≤ η`, `3b ≤ σ`, `b(2(20Δ + 1)) ≤ 1`, `b, s < 10⁻⁶`,
`10⁶ΔΛ < 10⁻⁵`, `μ, τ ≤ 1/100`, `μΔ < 10⁻⁴`: for revised edge centres `i, j` and `q' ∈ D_i`
with `ζ_j(q') = 1` there are a sign `a` and a constant `c` with
`|s_j η_j(x) − (aη_i(x) + c)| < 1/100` on `D_i`. -/
theorem bcf02_ec_value_edgeB_BCF2K {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
      (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM),
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
      μ * Δ < 1 / 10000 →
      ∀ i ∈ F.edgeB.centres, ∀ j ∈ F.edgeB.centres, ∀ q' ∈ ball i (20 * Δ * ρ i),
        F.edgeB.cutoff_BAUGA j q' = 1 →
        ∃ a c : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
          |ρ j / ρ i * F.edgeB.coord_BAUGA j x - (a * F.edgeB.coord_BAUGA i x + c)| < 1 / 100 := by
  obtain ⟨σ, hσ, hσ1, η, hη, hEC⟩ :=
    egp04_edgeB_value_BFRZ (θ := 1 / 100) (ν := 1 / 10 ^ 7) (by norm_num) (by norm_num)
      (by norm_num) hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    U₁ U₂ Ue₁ Ue₂ oM F hσL hbη h3b hbH hb hs hΛ hLΛ hμ hτ hμΔ i hi j hj q' hq'D hζq'
  have hsupp : (tsupport (F.edgeB.cutoff_BAUGA j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
    refine ⟨q', subset_tsupport _ ?_, hq'D⟩
    rw [Function.mem_support, hζq']
    norm_num
  obtain ⟨a, ha, hlin⟩ := hEC F hσL hbη h3b hbH hb hs hΛ hLΛ hμ hτ (by linarith) i hi j hj hsupp
  refine ⟨a, ρ j / ρ i * F.edgeB.coord_BCG1 j hj i, ha, fun x hx => ?_⟩
  rw [F.edgeB.coord_BAUGA_of_mem hj, F.edgeB.coord_BAUGA_of_mem hi]
  exact hlin x hx

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The strict replacement contract (Repl_∂) on the final boundary family, EC instantiated**
(review 68, A4): for `Δ ≥ 2`, early constants `σ, η` (EGP04's, depending on `Δ` only); then over
every completion `(W°, d_ĝ)` with BCP04.a at `n` and every final boundary family on the regions
`{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}` whose parameters satisfy the step-one–three bounds,
`c₃ ≤ Δ/2` and EGP04's tail requests (`σ⁻¹ ≤ Lmax`, `b ≤ η`, `3b ≤ σ`, `b(2(20Δ + 1)) ≤ 1`,
`10⁶ΔΛ < 10⁻⁵`, `μΔ < 10⁻⁴`), for every map `E` with (ERR) and (FM): a point `q` with `D(q) ≥ 35`,
outside every selected zero ball `B(z, .38R_z)` and every selected slim region, `q ∈ U_i`,
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` has a revised centre `j` with `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`,
`v_j(π₂E q) = ρ_j` and `|u_j(π₂E q)|/ρ_j < 3Δ`. No `q ∈ X₂`, no `π₂E(q) ∈ B₂`. -/
theorem LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
    ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
    ∀ {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz c₃ : ℝ},
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 → c₃ ≤ Δ / 2 →
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 →
      1000000 * Δ * Λ < 1 / 100000 → μ * Δ < 1 / 10000 →
    ∀ (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3),
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      {Y : Type} (E : W.pieceInterior ⊤ → Y) (π₂ : Y → Y) (u v : W.pieceInterior ⊤ → Y → ℝ),
      (∀ j ∈ F.edgeB.centres, ∀ x, |u j (π₂ (E x)) -
        ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x) →
      (∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 100 * Δ * ρ j →
        |F.edgeB.coord_BAUGA j x| < 6 * Δ → F.edgeB.smoothing x / ρ x < 6 * Δ →
          v j (π₂ (E x)) = ρ j) →
      ∀ i : W.pieceInterior ⊤, i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        ∃ j ∈ F.edgeB.centres, |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧
          F.edgeB.cutoff_BAUGA j q = 1 ∧ v j (π₂ (E q)) = ρ j ∧
          |u j (π₂ (E q))| / ρ j < 3 * Δ := by
  obtain ⟨σ, hσ, hσ1, η, hη, hEC⟩ := bcf02_ec_value_edgeB_BCF2K (by linarith : (1 : ℝ) ≤ Δ)
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro W _ g ĝ hle ρ hρ n hbcp Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz c₃
    hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hc₃ hσL hbη h3b hbH hLΛ hμΔ oM
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F Y E π₂ u v hERR hFM i hi q hq hηq htq hq35 hZ hS
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  obtain ⟨j, hj, q', hζq', hq'D, hrep⟩ :=
    F.bcf02_strict_replacement_of_comparison_BCF2K W g ĝ hle ρ hρ hbcp hΔ hΛ hμ hτ hlam hσc hn
      hT hσs hσs1 hb hs hβ2 hc₃ oM E π₂ u v hERR hFM i hi q hq hηq htq hq35 hZ hS
  obtain ⟨a, c, ha, hlin⟩ := hEC F hσL hbη h3b hbH hb hs hΛ hLΛ (by linarith) (by linarith)
    hμΔ i hi j hj q' hq'D hζq'
  exact ⟨j, hj, hrep a (1 / 100) c ha le_rfl hlin⟩

end Carrier

end DifferentialGeometry.Geometry.Collapse
