import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainIsotopySupported
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomains

/-!
# ZSP02 on `Gaf02ChainE`, strengthened: the isotopy is supported in a compact annulus

Lane C14-ZSP35c. Blueprint `master207B.tex`, ZSP02 (B:6374–6479), the clause the boundary carrier
version needs (B:9532–9544 and B:10537: the isotopy is extended by the identity near `∂M`; review
72 D72-2: the flow fixes every original zero ball), bound to the chain `Ĉ : Gaf02ChainE` with
`E = Ĉ.E` (inputs `Gaf02ChainE.zsp02_inputs_ZSP35`, radial bound `εr < 1/2` as in the ZSP02 row).

* `Gaf02ChainE.zsp02_supported_isotopy_ZSP35`: for every zero index `k`, a jointly smooth family
  `Φ : ℝ → X ≃ₘ X`, `Φ 0 = id`, the identity off a compact `K' ⊆ {.39 < η_k < .41}` — in metric
  form the identity on `B̄(c_k, (.39 − e)R_k)` and outside `B(c_k, (.41 + e)R_k)` — with
  `Φ 1 {η_k ≤ .4} = Z_k` and `Φ 1 {η_k = .4} = ∂Z_k` (ZF).

Consumer: `zsp02_supported_isotopy_C14Z_ZSP35` (final family, chain on its `C14` projection;
`Φ 1` carries the original face onto `frontier Z_k` and fixes the inner ball `B̄(c_k, .36R_k)` and
everything outside `B(c_k, .44R_k)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **ZSP02's supported isotopy on `Gaf02ChainE`** (B:6449–6473 with the support clause of
B:9532–9544 / B:10537, D72-2): for every zero index `k` there are a compact `K'` inside the thin
annulus `{.39 < η_k < .41}` and a jointly smooth family `Φ : ℝ → X ≃ₘ X` with `Φ 0 = id`,
`Φ t = id` off `K'` (in particular on `B̄(c_k, (.39 − e)R_k)` and outside
`B(c_k, (.41 + e)R_k)`), `Φ 1 {η_k ≤ .4} = Z_k` and `Φ 1 {η_k = .4} = ∂Z_k`. -/
theorem Gaf02ChainE.zsp02_supported_isotopy_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) :
    ∃ (K' : Set X) (Φ : ℝ → X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X),
      IsCompact K' ∧
      (∀ x ∈ K', 39 / 100 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) ∞ (fun q : ℝ × X => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      (∀ t x, dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ≤
          (39 / 100 - e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ∨
        (41 / 100 + e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center →
        Φ t x = x) ∧
      Φ 1 '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      Φ 1 '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := by
  obtain ⟨hf, hF, hδ₀, hZE, ⟨Hd, hHd, hder⟩, he⟩ := Ĉ.zsp02_inputs_ZSP35
  obtain ⟨K', Φ, hK', hK'η, hΦs, hΦ0, hΦid, h1, h2⟩ :=
    zsp02_supported_isotopy_kernel_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hf hF hδ₀ (hZE k)
      hHd hder hεr he
  obtain ⟨-, hcl, -, -, -⟩ := zsp_radial_facts_ZSP35 P.zero k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hfr := (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1
  refine ⟨K', Φ, hK', hK'η, hΦs, hΦ0, hΦid, fun t x hx => hΦid t x fun hxK => ?_, h1,
    hfr ▸ h2⟩
  obtain ⟨hlo, hhi⟩ := hK'η x hxK
  obtain ⟨hc1, hc2⟩ := abs_lt.mp (hcl x)
  rcases hx with hx | hx
  · have : (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius⁻¹ *
        dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ≤ 39 / 100 - e := by
      rw [inv_mul_le_iff₀ hR]
      linarith
    linarith
  · have : 41 / 100 + e ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius⁻¹ *
        dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center := by
      rw [le_inv_mul_iff₀ hR]
      linarith
    linarith

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **Consumer: the supported zero-domain isotopy on the final family** (chain on the `C14`
projection of `LocalChartPacketsC14Z`): for every zero index `k`, an isotopy `Φ` from the identity,
fixing `B̄(c_k, .36R_k)` and the complement of `B(c_k, .44R_k)` pointwise at all times, whose time
one carries `{η_k ≤ .4}` onto `Z_k` and the original face `{η_k = .4}` onto `∂Z_k`. -/
theorem zsp02_supported_isotopy_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) :
    ∃ Φ : ℝ → X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) ∞ (fun q : ℝ × X => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t x, dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ≤
          36 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ∨
        44 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          dist x (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center →
        Φ t x = x) ∧
      Φ 1 '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      Φ 1 '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := by
  obtain ⟨-, Φ, -, -, hΦs, hΦ0, -, hmet, h1, h2⟩ := Ĉ.zsp02_supported_isotopy_ZSP35 hεr k
  obtain ⟨-, -, -, -, -, -, he, -⟩ := Ĉ.toChain.std
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  refine ⟨Φ, hΦs, hΦ0, fun t x hx => hmet t x ?_, h1, h2⟩
  rcases hx with hx | hx
  · exact Or.inl (hx.trans (mul_le_mul_of_nonneg_right (by linarith) hR.le))
  · exact Or.inr ((mul_le_mul_of_nonneg_right (by linarith) hR.le).trans hx)

end Final

end DifferentialGeometry.Geometry.Collapse
