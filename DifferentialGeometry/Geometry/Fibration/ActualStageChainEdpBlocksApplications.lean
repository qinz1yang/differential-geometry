import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# EDP02–EDP03's final-map clauses on EDP03's domain `Y_j`, on the final family

Lane C14-EDP-E. Blueprint `master207B.tex`, EDP03 (B:6837–6947: `g_i`, `T` smooth on `Y_i`,
(ETan), the normalized (AE) of the proof) and EDP02 (B:6748–6835: the interior inclusion's height
and coordinate bounds, the vertical-set equality), for a chain
`C : Gaf02Chain L.toLocalChartPackets …` on `L : LocalChartPacketsC14` (a projection of the final
closed family `LocalChartPacketsC14Z`).
With `η = η_j`, `t = P/ρ`, `P = edge.smoothing`, `A = u_{E'}(E)`, `s = C.scale`, `T = A/s`,
`g = u_j(E)/R_j`, `Y = {p ∈ B(j, 100Δρ(j)) : |η| < 5Δ, t < 5Δ}`:

* `edp03_final_clauses_C14_EDPE`: `A`, `T`, `g` smooth on `Y` (indeed on `X`) and `s > 0`;
  (ETan) `|g − η| < 5c₃/4` and `|dg(W) − dη(W)| ≤ H √(R_j⁻²g(W, W))` on `Y`; (AE) `|A − P| < c₃ρ`
  on `Y ∩ {.3Δ ≤ t}` and `|dA(W) − dP(W)| ≤ H|W|_g` on `Y ∩ {.3Δ < t}`, with ONE `H < c₃`.
* `edp02_final_clauses_C14_EDPE` (with `c₃ < 10⁻⁵`): on the original smaller set
  `{p ∈ B(j, 100Δρ(j)) : |η| ≤ 3.5Δ, t ≤ 3.5Δ}`, `|g| < 4Δ` and `T < 4Δ`; `T < .31Δ` wherever
  `t < .3Δ`; and `{t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ} = {T ≤ 4Δ}` (globally).
* `edp03_final_clauses_C14Z_EDPE`: the same on the final closed family (projection).
* `Gaf02Chain.final_eq_original_of_empty_EDPE` (the inactive branch, `E = 𝓔⁰`): with empty circle,
  edge and slim families every stage is the identity, `E = 𝓔⁰`, `s = ρ`, `A = z₀P`, `T = z₀t`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_EDPEa
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_EDPEa
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_EDPEa
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP03's final-map clauses on `Y_j`** (B:6845–6860 and the proof's (AE)): see the module
docstring. -/
theorem edp03_final_clauses_C14_EDPE
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) {j : X} (hj : j ∈ L.edge.centres) :
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| < 5 * Δ ∧ t p < 5 * Δ}
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ A Y ∧ ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ Tq Y ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ gq Y ∧ (∀ p, 0 < C.scale p) ∧
    (∀ p ∈ Y, |gq p - η p| < 5 / 4 * c 2) ∧
    (∀ p ∈ Y, 3 / 10 * Δ ≤ t p → |A p - L.edge.smoothing p| < c 2 * ρ p) ∧
    ∃ Hd : ℝ, Hd < c 2 ∧
      (∀ p ∈ Y, ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) gq p W - mvfderiv 𝓘(ℝ, E3) η p W| ≤
          Hd * Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner p W W)) ∧
      ∀ p ∈ Y, 3 / 10 * Δ < t p → ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) A p W - mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W| ≤
          Hd * Real.sqrt (g.inner p W W) := by
  intro jF η t A Tq gq Y
  obtain ⟨-, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hA, -, hs, hT, hg⟩ := C.final_smooth_EDPE
  obtain ⟨Hd, hHd, -, -, hband, hedge⟩ := C.final_derivative_EDPE
  refine ⟨hA.contMDiffOn, hT.contMDiffOn, (hg jF).contMDiffOn, hs, fun p hp => ?_,
    fun p hp ht => ?_, Hd, hHd, fun p hp W => ?_, fun p hp ht W => ?_⟩
  · exact ((C.edgeAxis_value_EDPE jF p).2 hp.1 (by linarith [hp.2.1]) (by linarith [hp.2.2])).2
  · have hz := edgeMarker_eq_one_EDPE L.toLocalChartPackets hΔ0 hj hp.1 (by linarith [hp.2.1])
      ht (by linarith [hp.2.2])
    have h := (C.heightAxis_value_EDPE p).1
    rw [hz, one_mul] at h
    exact h
  · exact hedge jF p hp.1 (by linarith [hp.2.1]) (by linarith [hp.2.2]) W
  · exact hband jF p hp.1 (by linarith [hp.2.1]) ht (by linarith [hp.2.2]) W

/-- **EDP02's final-map clauses** (B:6773–6782, B:6824–6834; `c₃ < 10⁻⁵`): see the module
docstring. -/
theorem edp02_final_clauses_C14_EDPE
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 100000) {j : X}
    (hj : j ∈ L.edge.centres) :
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    (∀ p ∈ ball j (100 * Δ * ρ j), |η p| ≤ 7 / 2 * Δ → t p ≤ 7 / 2 * Δ →
      |gq p| < 4 * Δ ∧ Tq p < 4 * Δ) ∧
    (∀ p, t p < 3 / 10 * Δ → Tq p < 31 / 100 * Δ) ∧
    {p | t p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧ Tq p ≤ 4 * Δ} = {p | Tq p ≤ 4 * Δ} := by
  intro jF η t A Tq gq
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨h35, h03, hV⟩ := C.low_branch_EDPE hc
  refine ⟨fun p hp hη ht => ⟨?_, h35 p ht⟩, h03, hV⟩
  have h := ((C.edgeAxis_value_EDPE jF p).2 hp (by linarith) (by linarith)).2
  have h1 := abs_sub_abs_le_abs_sub (gq p) (η p)
  have h2 : |gq p| - |η p| ≤ |gq p - η p| := h1
  have h3 : 5 / 4 * c 2 < 1 / 2 * Δ := by linarith
  change |gq p| < 4 * Δ
  linarith

/-- **EDP03's final-map clauses on the final closed family** (projection of
`edp03_final_clauses_C14_EDPE`). -/
theorem edp03_final_clauses_C14Z_EDPE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (L : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) {j : X} (hj : j ∈ L.edge.centres)
    {p : X} (hp : p ∈ ball j (100 * Δ * ρ j)) (hη : |L.edge.coord j p| < 5 * Δ)
    (ht : L.edge.smoothing p / ρ p < 5 * Δ) :
    |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero
        ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (C.E p)) / ρ j - L.edge.coord j p| <
      5 / 4 * c 2 := by
  have h := edp03_final_clauses_C14_EDPE L.toLocalChartPacketsC14D.toLocalChartPacketsC14 C hj
  exact h.2.2.2.2.1 p ⟨hp, hη, ht⟩

/-- **The inactive branch** (draft 59 §3.5, `E = 𝓔⁰`): if the circle, edge and slim families are
empty, every stage of the chain is the identity, so `E = 𝓔⁰`, `s = ρ`, the final `E'` coordinate
is the original weak-edge vector `A = z₀P`, and `T = z₀t`. -/
theorem Gaf02Chain.final_eq_original_of_empty_EDPE
    {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
    (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (h0 : P.circle.centres = ∅) (h1 : P.edge.centres = ∅)
    (h2 : P.slim.centres = ∅) :
    C.E = cgpGlobalMap P.toLocalChartFamily P.zero ∧ C.scale = ρ ∧
    (∀ p, EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) =
      cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p) ∧
    ∀ p, EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
      C.scale p = cgpEdgeMarker P.toLocalChartFamily p * (P.edge.smoothing p / ρ p) := by
  obtain ⟨k0, k1, k2⟩ := C.empty_family_stage_id
  have hE : C.E = cgpGlobalMap P.toLocalChartFamily P.zero := by
    funext p
    simp only [Gaf02Chain.E, Gaf02Chain.g₂, Gaf02Chain.g₁, Function.comp_apply, k0 h0, k1 h1,
      k2 h2, id]
  have hs : C.scale = ρ := by
    funext p
    simp only [Gaf02Chain.scale, hE]
    exact gafScaleMarker_globalMap_GAF2 P.toLocalChartFamily P.zero p
  have hA : ∀ p, EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) =
      cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p := fun p => by
    rw [hE]
    exact globalMap_heightAxis_EDPE P p
  refine ⟨hE, hs, hA, fun p => ?_⟩
  rw [hA p, hs, mul_div_assoc]

end DifferentialGeometry.Geometry.Collapse
