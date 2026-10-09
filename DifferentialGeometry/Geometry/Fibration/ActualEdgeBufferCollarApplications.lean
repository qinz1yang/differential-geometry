import DifferentialGeometry.Geometry.Fibration.ActualEdgeBufferCollar
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Staged

/-!
# EDP03's clauses free of the final map, assembled on the final family

Lane C14-EDP3. Blueprint `master207B.tex`, EDP03 (`lem:fibration-edge-original-buffer-and-height`,
B:6837–6947), external review 53 §2.3 / §5 (derived lemmas on existing fields, no new field).

* `edp03_efree_C14` (on `LocalChartPacketsC14`, at an edge centre `j`, physical units,
  `η = η_j`, `t = Fs/ρ`, `H₀ = Δψ(t/Δ)`, `Y = {p ∈ B(j, 100Δρ(j)) : |η| < 5Δ, t < 5Δ}`):
  `Y ⊆ B(j, 8Δρ(j))`; `η`, `H₀` smooth on `Y`; `t` smooth at the points of `Y` with `t ≥ Δ/10`;
  `dη > .99` on a `ρ(j)⁻²g`-unit vector; a compact `Q ⊆ Y` with (EBuf) in its interior; the
  constant-core identities `t ≤ 2Δ ⇒ H₀ ≤ 2Δ`, `t ≥ 2Δ ⇒ H₀ = t`; and on the collar
  `3.9Δ < t < 4.1Δ`: the scale ratio, `H₀ =ᶠ t`, `D(η, H₀) = D(η, t)`, `D(η, t)` onto, and the
  co-norm `> (1 − (γc + βc))/(ρ(p)/ρ(j)) > .9` for `ρ(j)⁻²g`.
* `c14_edp03_params_EDP3`: every numerical condition of `edp03_efree_C14` is a built-in guarantee
  of the staged prefix `C14PreSplit`, each at its own stage (no new request).
* `edp03_efree_staged_EDP3`: the same conclusion for a family with the parameters of an admissible
  staged prefix `P : C14PreFinal` (the prefix of `exists_c14d_staged_assignment`), with NO numerical
  hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The staged prefix carries every numerical condition of EDP03's E-free clauses**: `1 ≤ Δ`
(stage 4), `μ, τ ≤ 10⁻⁸`, `σc ≤ 1/1000` (stage 5), `100ΔΛ ≤ 10⁻⁸` (stage 6),
`b · 1000Δ ≤ 1` (stage 8 from `b < s/10⁵`, `s < b'/10⁵`, `b' < 1/(10⁶Δ)`), and the collar
qualities `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵` (stage 2). -/
theorem c14_edp03_params_EDP3 (P : C14PreSplit) :
    1 ≤ P.Δ ∧ P.μ ≤ 1 / 10 ^ 8 ∧ P.τ ≤ 1 / 10 ^ 8 ∧ 100 * P.Δ * P.Λ ≤ 1 / 10 ^ 8 ∧
      P.σc ≤ 1 / 1000 ∧ P.b * (1000 * P.Δ) ≤ 1 ∧ 0 < P.γc ∧ P.γc ≤ 1 / 100 ∧
      P.βc ≤ 1 / 100000 := by
  have hΔ := P.Δ_gt6
  have hΔ0 : 0 < P.Δ := by linarith
  have hb' : P.b' * (1000000 * P.Δ) < 1 := by
    have h := P.b'_lt
    rwa [lt_div_iff₀ (by positivity)] at h
  have hs := P.s_pos
  have hsb := P.s_lt_b'
  have hbs := P.b_lt_s
  have hb0 := P.b_pos
  have hbb' : P.b ≤ P.b' := by linarith
  have hσ := P.σc_le10
  have hγ := P.γc_lt
  have hβ := P.βc_lt
  refine ⟨by linarith, P.μ_le8, by linarith [P.τ_lt8], P.Λ_c6, by linarith, ?_, P.γc_pos,
    hγ.le, ?_⟩
  · have h1 : P.b * (1000 * P.Δ) ≤ P.b' * (1000000 * P.Δ) := by
      have h2 : P.b * (1000 * P.Δ) ≤ P.b' * (1000 * P.Δ) :=
        mul_le_mul_of_nonneg_right hbb' (by positivity)
      have h3 : P.b' * (1000 * P.Δ) ≤ P.b' * (1000000 * P.Δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      linarith
    linarith
  · have : P.γc / 1000 ≤ 1 / 100000 := by linarith
    linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **EDP03's E-free clauses on the final family** (B:6837–6947): see the module docstring. -/
theorem edp03_efree_C14
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ L.edge.centres) :
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight Δ L.edge.smoothing ρ
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| < 5 * Δ ∧ t p < 5 * Δ}
    Y ⊆ ball j (8 * Δ * ρ j) ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ η Y ∧ ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H₀ Y ∧
    (∀ p ∈ Y, Δ / 10 ≤ t p → ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t p) ∧
    (∀ p ∈ Y, ∃ w : TangentSpace 𝓘(ℝ, E3) p, g.inner p w w = ρ j ^ 2 ∧
      99 / 100 < mvfderiv 𝓘(ℝ, E3) η p w) ∧
    (∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| ≤ 41 / 10 * Δ ∧ t p ≤ 41 / 10 * Δ} ⊆
        interior Q) ∧
    (∀ p, t p ≤ 2 * Δ → H₀ p ≤ 2 * Δ) ∧ (∀ p, 2 * Δ ≤ t p → H₀ p = t p) ∧
    ∀ p ∈ Y, 39 / 10 * Δ < t p → t p < 41 / 10 * Δ →
      (99 / 100 ≤ ρ p / ρ j ∧ ρ p / ρ j ≤ 101 / 100) ∧ H₀ =ᶠ[𝓝 p] t ∧
      mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, H₀]) p =
        mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p ∧
      Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p) ∧
      ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W : TangentSpace 𝓘(ℝ, E3) p,
        g.inner p W W = ρ j ^ 2 ∧
        (1 - (γc + βc)) / (ρ p / ρ j) <
          inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ ∧
        9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ := by
  intro η t H₀ Y
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hY8, hηs, hHs, hder, hQ⟩ := edp03_buffer L.toLocalChartFamilyE hΔ hμ hτ hlam hσc hb hj
  refine ⟨hY8, hηs, hHs, fun p hp ht => ?_, hder, hQ, fun p hp => edgeRowHeight_le_two_EDP3 hΔ0 hp,
    fun p hp => edgeRowHeight_eq_self_EDP3 hΔ0 hp, fun p hp ht1 ht2 => ?_⟩
  · exact L.edge.contMDiffAt_height_of_collar hj hp.1 (by linarith [hp.2.1]) ht
      (by linarith [hp.2.2])
  · obtain ⟨hratio, hco⟩ := L.edge.collar_conorm_phys_EDP3 hγc hγc1 hβc1 hΔ0 hj hp.1 hp.2.1 ht1 ht2
    obtain ⟨hev, hD, -, -⟩ := L.edge.collar_height_conorm_EDP3 hγc hγc1 hβc1 hΔ0 hj hp.1 hp.2.1 ht1
      ht2
    refine ⟨hratio, hev, hD, ?_, hco⟩
    refine surjective_of_conorm_pos_EDP6
      (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p).toLinearMap (fun ξ hξ => ?_)
    obtain ⟨W, -, -, h9⟩ := hco ξ hξ
    exact ⟨W, by
      change 0 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ
      linarith⟩

/-- **EDP03's E-free clauses for an admissible staged prefix** (no numerical hypothesis): for a
family with the parameters of `P : C14PreFinal` (as produced by `exists_c14d_staged_assignment`),
the conclusion of `edp03_efree_C14` holds at every edge centre. -/
theorem edp03_efree_staged_EDP3 (P : C14PreFinal)
    (L : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ β P.Δ σs K P.σc P.μ P.b s b' s' ε P.γc P.βc
      Lmax P.τ γ δ εr e T V vs ζ Λz)
    {j : X} (hj : j ∈ L.edge.centres) :
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight P.Δ L.edge.smoothing ρ
    let Y : Set X := {p | p ∈ ball j (100 * P.Δ * ρ j) ∧ |η p| < 5 * P.Δ ∧ t p < 5 * P.Δ}
    Y ⊆ ball j (8 * P.Δ * ρ j) ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ η Y ∧ ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H₀ Y ∧
    (∀ p ∈ Y, P.Δ / 10 ≤ t p → ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t p) ∧
    (∀ p ∈ Y, ∃ w : TangentSpace 𝓘(ℝ, E3) p, g.inner p w w = ρ j ^ 2 ∧
      99 / 100 < mvfderiv 𝓘(ℝ, E3) η p w) ∧
    (∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * P.Δ * ρ j) ∧ |η p| ≤ 41 / 10 * P.Δ ∧ t p ≤ 41 / 10 * P.Δ} ⊆
        interior Q) ∧
    (∀ p, t p ≤ 2 * P.Δ → H₀ p ≤ 2 * P.Δ) ∧ (∀ p, 2 * P.Δ ≤ t p → H₀ p = t p) ∧
    ∀ p ∈ Y, 39 / 10 * P.Δ < t p → t p < 41 / 10 * P.Δ →
      (99 / 100 ≤ ρ p / ρ j ∧ ρ p / ρ j ≤ 101 / 100) ∧ H₀ =ᶠ[𝓝 p] t ∧
      mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, H₀]) p =
        mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p ∧
      Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p) ∧
      ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W : TangentSpace 𝓘(ℝ, E3) p,
        g.inner p W W = ρ j ^ 2 ∧
        (1 - (P.γc + P.βc)) / (ρ p / ρ j) <
          inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ ∧
        9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ := by
  obtain ⟨hΔ, hμ, hτ, hlam, hσc, hb, hγc, hγc1, hβc1⟩ := c14_edp03_params_EDP3 P.toC14PreSplit
  exact edp03_efree_C14 L hΔ hμ hτ hlam hσc hb hγc hγc1 hβc1 hj

end DifferentialGeometry.Geometry.Collapse
