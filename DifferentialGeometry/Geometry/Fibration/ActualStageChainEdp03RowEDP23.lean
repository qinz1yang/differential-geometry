import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp03ItemBEDP23
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBufferCollarApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocksApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeight

/-!
# EDP03 as ONE row on the actual chain, and its consumers

Blueprint `master207B.tex`, EDP03 (B:6837–6947). On an enhanced chain `Ĉ : Gaf02ChainE L …` of a
family `L : LocalChartPacketsC14` (group G3 of lane S-EDP02-03) the whole lemma at every edge
centre `k`:

* the E-free clauses (`edp03_efree_C14`: `Y_k ⊆ B(k, 8Δρ_k)`, smoothness of `η_k`, `H₀`,
  `dη_k > .99`, the compact `Q_k` with (EBuf), `H₀` versus `t`, the collar's least singular
  value);
* the final-map clauses (`edp03_final_clauses_C14_EDPE`: `g_k`, `T` smooth, `s > 0`, (ETan), (AE));
* (EH) (`Gaf02Chain.edge_height_EH_EDPE`) and the EDP02 inequalities that hold on all of `X`
  (`edp02_final_clauses_C14_EDPE`: `T < .31Δ` for `t < .3Δ`, `|g_k| < 4Δ`, `T < 4Δ` on the smaller
  sets);
* item 5 (B) (`edp03_itemB_row_EDP23`: the base coordinate, GAF05 uniqueness, the third stage).

`Gaf02ChainE.edp03_row_EDP23` states the conjunction (each conjunct is the instance of the named
theorem, written `type_of% (…)`; no named `Prop`). The numeric premises are PARAMETERS ONLY, the
same as lane S-EDP-FDC's `edgeBase_fibre_disk_EDP23` / `edp04_fibre_disk_EFE`:
`Δ ≥ 2`, `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`, `0 ≤ ε < 1`, `μ τ ≤ 10⁻⁸`, `σc ≤ 1/1000`,
`b·1000Δ ≤ 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵` (`0 ≤ c_w(1)` and `Σ₁ ≤ Ξ₁/10⁴` come from the
rough data `Ĉ.rough`, `1 ≤ Δ` and `100ΔΛ ≤ 10⁻⁸` from the chain's standing numbers).
The consumer on the final family is `edp03_row_C14Z_EDP23`; the numbers `μ τ ≤ 10⁻⁸`,
`σc ≤ 1/1000`, `b·1000Δ ≤ 1` are the staged prefix's built-in guarantees
(`c14_edp03_params_EDP3`), the others at the register are `ClosedRegisterV4.edpE_numerics_RGC`;
their joint discharge at the closed rows' source is NOT claimed here (the item-B row has the
register and dihedral consumers: `eventually_edp03_itemB_rowsSourceZ_EDP23`).
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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}

/-- The chain's standing numbers give `100ΔΛ ≤ 10⁻⁸` (EDP03's `hlam`). -/
theorem hlam_EDP23 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  nlinarith

end Gaf02Chain

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **EDP03 as ONE row on the chain** (see the module header): at every edge centre `k`, the
E-free clauses, the final-map clauses, (EH), the EDP02 inequalities on `X`, and item 5 (B). -/
theorem edp03_row_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    (∀ k : L.edge.finite_centres.toFinset,
      type_of% (edp03_efree_C14 L Ĉ.toChain.std.2.1 hμ hτ Ĉ.toChain.hlam_EDP23 hσc hb hγc hγc1 hβc1
        ((Set.Finite.mem_toFinset _).mp k.2)) ∧
      type_of% (edp03_final_clauses_C14_EDPE L Ĉ.toChain ((Set.Finite.mem_toFinset _).mp k.2)) ∧
      type_of% (Ĉ.toChain.edge_height_EH_EDPE (Ĉ.rough.cw_nonneg 0) (Ĉ.rough.sigma_le 0).le hc hϑ
        hε0 hε ((Set.Finite.mem_toFinset _).mp k.2)) ∧
      type_of% (edp02_final_clauses_C14_EDPE L Ĉ.toChain hc ((Set.Finite.mem_toFinset _).mp k.2))) ∧
    type_of% (Ĉ.edp03_itemB_row_EDP23 hΔ2) :=
  ⟨fun k => ⟨edp03_efree_C14 L Ĉ.toChain.std.2.1 hμ hτ Ĉ.toChain.hlam_EDP23 hσc hb hγc hγc1 hβc1
      ((Set.Finite.mem_toFinset _).mp k.2),
    edp03_final_clauses_C14_EDPE L Ĉ.toChain ((Set.Finite.mem_toFinset _).mp k.2),
    Ĉ.toChain.edge_height_EH_EDPE (Ĉ.rough.cw_nonneg 0) (Ĉ.rough.sigma_le 0).le hc hϑ hε0 hε
      ((Set.Finite.mem_toFinset _).mp k.2),
    edp02_final_clauses_C14_EDPE L Ĉ.toChain hc ((Set.Finite.mem_toFinset _).mp k.2)⟩,
    Ĉ.edp03_itemB_row_EDP23 hΔ2⟩

end Gaf02ChainE

/-- **EDP03's row on the final closed family** (D71-3: the chain lives on the
`LocalChartPacketsC14` projection of the final-family packet). -/
theorem edp03_row_C14Z_EDP23
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    type_of% (Ĉ.edp03_row_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1) :=
  Ĉ.edp03_row_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1

end DifferentialGeometry.Geometry.Collapse
