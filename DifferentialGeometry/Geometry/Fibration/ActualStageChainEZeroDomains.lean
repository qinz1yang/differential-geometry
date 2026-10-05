import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainIsotopy
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroBlock
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroFaces

/-!
# ZSP02 on `Gaf02ChainE`: the actual compact zero domains (the whole row)

Lane C14-ZSP35. Blueprint `master207B.tex`, ZSP02 (`thm:fibration-actual-zero-domains`,
B:6374–6479), bound to the chain on the enhanced planes `Ĉ : Gaf02ChainE …` (lane C14-GAF8b) with
`E = Ĉ.E`: ZSP01's (ZE) is `Gaf02ChainE.zsp01_ZE_GAF8` (`δ₀ = 200c₃/T`), the derivative budget is
the chain's `stage_derivative_lt` (`H < c₃ ≤ 1/512`), `𝓔⁰` is smooth by `globalMap_smooth_EDPE`,
`e < 1/40` is the chain's `std`. The only additional input is the radial parameter bound
`εr < 1/2` (LC29's gradient bound `1 − εr`; the producer outputs `εr < 1/4`, R4).

* `Gaf02ChainE.zsp02_inputs_ZSP35`: the kernel's inputs on the chain.
* `Gaf02ChainE.zsp02_domain_ZSP35` (family `LocalChartPacketsC14`): compactness, the ambient
  diffeomorphism of (ZH), `∂Z_k =` (ZF), (ZB) with radii `.381 − e` / `.402 + e`, the face in
  `|η_k − .4| < 1/500`, the defining function `u_k/v_k − .4` near the face.
* `Gaf02ChainE.zsp02_ZB_ZSP35`: (ZB) verbatim (`.38`, `.42`) when `e ≤ 1/1000`.
* `Gaf02ChainE.zsp02_disjoint_ZSP35`: pairwise disjoint domains.
* `Gaf02ChainE.zsp02_types_ZSP35` (final family `LocalChartPacketsC14Z`): `Z_k ≃ₜ {η_k ≤ .4}` with
  its LPA05/LFR54 type; `∂Z_k` empty with `Z_k = M`, or `≃ₜ S²`, or `≃ₜ T²` (homeomorphism types,
  as G1's `zero_face_type_ZSP35`), compact and connected when nonempty.
* `Gaf02ChainE.zsp02_row_ZSP35`: the whole row (all of the above, every `k`).

Consumer: `zsp02_removed_region_C14Z_ZSP35` (ZSP03's `Z = ⋃ Z_k` and `M₁ = M ∖ int Z` compact,
`B̄(c_k, (.381 − e)R_k) ⊆ int Z`, distinct faces disjoint).
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

/-- **The chain's inputs to ZSP02's kernel** (Gaf02ChainE): `E` is smooth, `𝓔⁰` is smooth, ZSP01's
(ZE) holds with `δ₀ = 200c₃/T < 1/1000`, and the derivative budget `H < c₃ ≤ 1/512 < 1/100`. -/
theorem Gaf02ChainE.zsp02_inputs_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ Ĉ.E ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (cgpGlobalMap P.toLocalChartFamily P.zero) ∧
    200 * c 2 / T < 1 / 1000 ∧
    (∀ (k : P.zero.finite_centres.toFinset) p, ‖Ĉ.E p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))‖ <
      200 * c 2 / T * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
    (∃ Hd : ℝ, Hd < 1 / 100 ∧ ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) Ĉ.E p W -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W)) ∧
    e < 1 / 40 := by
  obtain ⟨-, hΔ, -, -, -, -, he, hT, -⟩ := Ĉ.toChain.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := Ĉ.toChain.numbers
  obtain ⟨Hd, hHd, hder⟩ := Ĉ.toChain.stage_derivative_lt.2.2
  have hT0 : 0 < T := by nlinarith
  refine ⟨Ĉ.toChain.stage_smooth.2.2, Ĉ.toChain.globalMap_smooth_EDPE, ?_,
    fun k p => (Ĉ.zsp01_ZE_GAF8 k p).2.2.1, ⟨Hd, by linarith, hder⟩, he⟩
  rw [div_lt_iff₀ hT0]
  nlinarith

/-- **ZSP02 on `Gaf02ChainE`, the domain clauses** (B:6374–6396; unconditional up to the radial
parameter bound `εr < 1/2`): for every zero index `k`, with `E = Ĉ.E`: `Z_k` is compact; a
diffeomorphism of `M` (FC34b along (ZH)) carries `{η_k ≤ .4}` onto `Z_k` and `{η_k = .4}` onto
(ZF); `∂Z_k =` (ZF); `B̄(c_k, (.381 − e)R_k) ⊆ int Z_k` and `Z_k ⊆ B(c_k, (.402 + e)R_k)`; the face
lies in `|η_k − .4| < 1/500`; on an open neighbourhood of the face `v_k > .99R_k`,
`u_k/v_k − .4` is smooth and defines `Z_k`, with nonzero differential on the face. -/
theorem Gaf02ChainE.zsp02_domain_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) :
    IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    (∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
      Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) =
      zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
    closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((381 / 1000 - e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
      interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
      ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((402 / 1000 + e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
    (∀ z ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E,
      |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z - 2 / 5| < 1 / 500) ∧
    ∃ O : Set X, IsOpen O ∧ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ O ∧
      (∀ z ∈ O, 99 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
          (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd ∧
        ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
          (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ∧
        (z ∈ zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ↔
          ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
            (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 ≤ 0)) ∧
      ∀ z ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
        (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ≠ 0 := by
  obtain ⟨hf, hF, hδ₀, hZE, ⟨Hd, hHd, hder⟩, he⟩ := Ĉ.zsp02_inputs_ZSP35
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := zsp02_kernel_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hf hF
    hδ₀ (hZE k) hHd hder hεr he
  exact ⟨h1, h2, h3, h4, h5, h6, zsp_defining_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hf hF hδ₀
    (hZE k) hHd hder hεr he⟩

/-- **ZSP02 (ZB) verbatim** under LC30's tolerance `e ≤ 1/1000` (the blueprint's
`.32 ≤ d ≤ .38 ⟹ .319 < η < .381`): `B̄(c_k, .38R_k) ⊆ int Z_k` and `Z_k ⊆ B(c_k, .42R_k)`. -/
theorem Gaf02ChainE.zsp02_ZB_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    (k : P.zero.finite_centres.toFinset) :
    closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        (38 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
      interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
      ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        (42 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) := by
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, -, -, h4, h5, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  exact ⟨(closedBall_subset_closedBall (by nlinarith)).trans h4,
    h5.trans (ball_subset_ball (by nlinarith))⟩

/-- **ZSP02, the domains are pairwise disjoint** (B:6421–6423): `Z_k ⊆ B(c_k, R_k)` and LPA05's
selected zero balls are disjoint. -/
theorem Gaf02ChainE.zsp02_disjoint_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {k k' : P.zero.finite_centres.toFinset} (hkk : k ≠ k') :
    Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
      (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E) := by
  obtain ⟨-, -, -, -, -, -, he, -⟩ := Ĉ.toChain.std
  have hsub : ∀ j : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero j Ĉ.E ⊆
        ball j.1 (P.zero.zero j.1 ((Set.Finite.mem_toFinset _).mp j.2)).radius := fun j => by
    have hR := (P.zero.zero j.1 ((Set.Finite.mem_toFinset _).mp j.2)).radius_pos
    obtain ⟨-, -, -, -, h5, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr j
    intro z hz
    have h6 := h5 hz
    rw [mem_ball] at h6 ⊢
    rw [P.zero.zero_center j.1 ((Set.Finite.mem_toFinset _).mp j.2)] at h6
    nlinarith
  have hne : k.1 ≠ k'.1 := fun h => hkk (Subtype.ext h)
  exact (P.zero.disjoint k.1 _ k'.1 _ hne).mono (hsub k) (hsub k')

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **ZSP02's types on the complete closed family** (B:6386–6395): for a chain `Ĉ` on the final
family, every adjusted zero domain `Z_k` is homeomorphic (by the ambient diffeomorphism of (ZH)) to
the SAME original sublevel `{η_k ≤ .4}`, which has its LPA05/LFR54 type; its boundary (ZF) is empty
with `Z_k = M` (compact model), or homeomorphic to `S²`, or to `T²`; a nonempty boundary is compact
and connected. -/
theorem Gaf02ChainE.zsp02_types_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) :
    (CompactModelSublevel oM (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
      PointSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
      CircleSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
      ProjectiveSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
      KleinSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
    Nonempty (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
      {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
    ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
      Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
    ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E).Nonempty →
      IsCompact (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      IsConnected (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) := by
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have ha : (2 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  obtain ⟨-, ⟨Ψ, hΨ1, hΨ2⟩, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  have hface : ∀ s : Set X, Nonempty (s ≃ₜ Ψ '' s) := fun s => ⟨Ψ.toHomeomorph.image s⟩
  refine ⟨P.zero_sublevel_types k.1 hk (2 / 5) ha, ?_, ?_, fun hne => ?_⟩
  · obtain ⟨h⟩ := hface {x | (P.zero.zero k.1 hk).radial x ≤ 2 / 5}
    exact ⟨((Homeomorph.setCongr hΨ1).symm.trans h.symm)⟩
  · obtain ⟨h⟩ := hface {x | (P.zero.zero k.1 hk).radial x = 2 / 5}
    have h' := (Homeomorph.setCongr hΨ2).symm.trans h.symm
    rcases P.zero_face_type_ZSP35 hk ha with ⟨hu, he⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← hΨ2, he, image_empty]
      · rw [← hΨ1, hu]
        exact image_univ_of_surjective (f := (Ψ : X → X)) Ψ.surjective
    · exact Or.inr (Or.inl ⟨h'.trans e1⟩)
    · exact Or.inr (Or.inr ⟨h'.trans e1⟩)
  · have hne' : {x | (P.zero.zero k.1 hk).radial x = 2 / 5}.Nonempty := by
      rw [← hΨ2] at hne
      exact hne.of_image
    obtain ⟨hc, hcon, -⟩ := P.zero_face_connected_ZSP35 hk ha hne'
    rw [← hΨ2]
    exact ⟨hc.image Ψ.continuous, hcon.image _ Ψ.continuous.continuousOn⟩

/-- **ZSP02, the whole row on `Gaf02ChainE` over the complete closed family** (B:6374–6396), with
the radial parameter bound `εr < 1/2` (producer output `εr < 1/4`): for every zero index `k` the
domain `Z_k = B(c_k, .35R_k) ∪ E⁻¹{v_k ≥ .9R_k, u_k ≤ .4v_k}` is compact; an ambient diffeomorphism
(FC34b along (ZH)) carries the SAME original sublevel `{η_k ≤ .4}` onto `Z_k` and `{η_k = .4}` onto
(ZF); `∂Z_k = E⁻¹{v_k ≥ .9R_k, u_k = .4v_k}`; (ZB) with radii `.381 − e`, `.402 + e` (and verbatim
`.38`, `.42` when `e ≤ 1/1000`); near `∂Z_k`, `v_k > .99R_k` and `u_k/v_k − .4` is a smooth defining
function with nonzero differential on `∂Z_k`; `Z_k ≃ₜ {η_k ≤ .4}` (LPA05/LFR54 type); `∂Z_k` is
empty with `Z_k = M`, or `≃ₜ S²`, or `≃ₜ T²`, compact and connected when nonempty; and the domains
are pairwise disjoint. -/
theorem Gaf02ChainE.zsp02_row_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    (∀ k : P.zero.finite_centres.toFinset,
      IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
          zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) =
        zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          ((381 / 1000 - e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          ((402 / 1000 + e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
      (∃ O : Set X, IsOpen O ∧ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ O ∧
        (∀ z ∈ O, 99 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
            (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd ∧
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
            (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
              (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ∧
          (z ∈ zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ↔
            ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
              (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 ≤ 0)) ∧
        ∀ z ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
            (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ≠ 0) ∧
      (CompactModelSublevel oM (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        PointSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        CircleSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        ProjectiveSoulCoreSublevel
          (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        KleinSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
      Nonempty (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
      ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
        Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
          (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E).Nonempty →
        IsCompact (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
        IsConnected (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))) ∧
    (∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E)) ∧
    (e ≤ 1 / 1000 → ∀ k : P.zero.finite_centres.toFinset,
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (38 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (42 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)) := by
  refine ⟨fun k => ?_, fun k k' hkk => Ĉ.zsp02_disjoint_ZSP35 hεr hkk,
    fun he k => Ĉ.zsp02_ZB_ZSP35 hεr he k⟩
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  exact ⟨h1, h2, h3, h4, h5, h7, Ĉ.zsp02_types_ZSP35 hεr k⟩

/-- **Consumer: the removed zero region and the first carrier** (ZSP03's `Z = ⋃_k Z_k`,
`M₁ = M ∖ int Z`, B:6483): for a chain on the final family, `Z` is compact, `M₁` is compact, `Z`
contains every `B̄(c_k, (.381 − e)R_k)` in its interior, and distinct zero faces are disjoint. -/
theorem zsp02_removed_region_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    IsCompact (⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    IsCompact ((⋃ k : P.zero.finite_centres.toFinset,
      interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ) ∧
    (∀ k : P.zero.finite_centres.toFinset,
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          ((381 / 1000 - e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
    ∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspFace_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E) := by
  obtain ⟨hrow, hdisj, -⟩ := Ĉ.zsp02_row_ZSP35 hεr
  refine ⟨isCompact_iUnion fun k => (hrow k).1,
    (isOpen_iUnion fun k => isOpen_interior).isClosed_compl.isCompact, fun k => ?_,
    fun k k' hkk => ?_⟩
  · exact (hrow k).2.2.2.1.trans (interior_mono (subset_iUnion (fun k =>
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) k))
  · rw [← (hrow k).2.2.1, ← (hrow k').2.2.1]
    exact (hdisj k k' hkk).mono ((hrow k).1.isClosed.frontier_subset)
      ((hrow k').1.isClosed.frontier_subset)

end Final

end DifferentialGeometry.Geometry.Collapse
