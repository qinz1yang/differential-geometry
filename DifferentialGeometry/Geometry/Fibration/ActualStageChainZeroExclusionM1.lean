import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomains
import DifferentialGeometry.Geometry.Fibration.ActualReplacementExclusionsApplications
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# FDC01–FDC04: the zero exclusion of `M₂` from the ACTUAL zero domains of ZSP02

Blueprint `master207B.tex`, FDC01 (B:7175–7185: "ZSP02 puts this ball in `int Z`, contradicting
`q ∈ M₂ ⊂ M \ int Z`"), with ZSP03's `M₁ = M \ int_M Z`, `Z = ⋃_k Z_k` (B:6483) and ZSP05's
`M₂ = M₁ \ int_{M₁} M^slim` (B:6601). Here `Z_k = zspDomain_ZSP35 … Ĉ.E` are ZSP02's actual zero
domains of the enhanced chain `Ĉ : Gaf02ChainE` (lane C14-ZSP35b).

* `Gaf02ChainE.zero_far_of_mem_M1_EFC`: a point of the actual `M₁` has `d(q, z) > (.381 − e)R_z`
  from every selected zero centre (ZSP02's (ZB), unconditional radius).
* `Gaf02ChainE.zero_far_verbatim_of_mem_M1_EFC`: under LC30's tolerance `e ≤ 1/1000`,
  `d(q, z) ≥ .38R_z` — exactly the hypothesis `hZ` of lane C14-FDCb's FDC01–FDC04 consumers.
* `isClosed_relative_removal_EFC`: `M₁ \ int_{M₁} S` is closed for a closed `M₁` and EVERY `S`
  (so the actual `M₂` is closed whatever the slim piece is).
* `fdc01_zero_exclusion_sharp_EFC`, `Gaf02ChainE.fdc01_not_zero_of_mem_M1_EFC`: the sharp form of
  FDC01's zero step — `d(q, z) < .107R_z` for the covering zero ball of a zero-stratum centre, so a
  point of the actual `M₁` near an edge centre `p_i` forces `p_i` out of the zero stratum with only
  the chain's `e < 1/40` (no `e ≤ 1/1000`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

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

/-- **The relative removal is closed** (ZSP05's (RC) shape): for a closed `M₁` and EVERY `S`,
`M₁ \ int_{M₁} S` (relative interior, subtype topology) is closed. -/
theorem isClosed_relative_removal_EFC {M : Type*} [TopologicalSpace M] {M₁ : Set M} (S : Set M)
    (hM₁ : IsClosed M₁) :
    IsClosed (M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxM : x ∈ M₁
  · have hrel : x ∈ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁) := by
      by_contra h
      exact hx ⟨hxM, h⟩
    obtain ⟨-, O, hO, hxO, hOA⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hrel
    exact ⟨O, fun y hyO hy => hy.2
      (DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mpr
        ⟨hy.1, O, hO, hyO, hOA⟩), hO, hxO⟩
  · exact ⟨M₁ᶜ, fun y hy hy2 => hy hy2.1, hM₁.isOpen_compl, hxM⟩

/-- **A point of the actual `M₁` is outside every `(.381 − e)`-zero ball** (ZSP02's (ZB),
unconditional radius): if `q ∉ int ⋃_k Z_k`, then `d(q, z) > (.381 − e)R_z` for every selected
zero centre `z`. -/
theorem Gaf02ChainE.zero_far_of_mem_M1_EFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) {q : X}
    (hq : q ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ)
    (z : X) (hz : z ∈ P.zero.centres) :
    (381 / 1000 - e) * (P.zero.zero z hz).radius < dist q z := by
  by_contra hlt
  push Not at hlt
  have h4 := (Ĉ.zsp02_domain_ZSP35 hεr ⟨z, (Set.Finite.mem_toFinset _).mpr hz⟩).2.2.2.1
  have hc : (P.zero.zero z hz).center = z := P.zero.zero_center z hz
  have hmem : q ∈ closedBall (P.zero.zero z hz).center
      ((381 / 1000 - e) * (P.zero.zero z hz).radius) := by
    rw [mem_closedBall, hc]
    exact hlt
  exact hq (interior_mono (subset_iUnion (fun k : P.zero.finite_centres.toFinset =>
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ⟨z, (Set.Finite.mem_toFinset _).mpr hz⟩)
    (h4 hmem))

/-- **FDC01's `hZ` from the actual `M₁`** (ZSP02 (ZB) verbatim, LC30's tolerance `e ≤ 1/1000`): a
point `q ∉ int ⋃_k Z_k` lies outside every selected `.38`-zero ball, `.38R_z ≤ d(q, z)`. -/
theorem Gaf02ChainE.zero_far_verbatim_of_mem_M1_EFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {q : X} (hq : q ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ) :
    ∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z := by
  intro z hz
  have h := Ĉ.zero_far_of_mem_M1_EFC hεr hq z hz
  have hR := (P.zero.zero z hz).radius_pos
  have h1 : 38 / 100 * (P.zero.zero z hz).radius ≤ (381 / 1000 - e) * (P.zero.zero z hz).radius :=
    mul_le_mul_of_nonneg_right (by linarith) hR.le
  linarith

/-- **The actual `M₂` is closed and avoids the `.38`-zero balls** (ZSP03 / ZSP05 shapes): with
`Z = ⋃_k Z_k` (ZSP02's actual domains), `M₁ = M \ int Z` and `M₂ = M₁ \ int_{M₁} Sl` for ANY slim
set `Sl`, the set `M₂` is closed and every `q ∈ M₂` has `.38R_z ≤ d(q, z)` (`e ≤ 1/1000`). These
are the hypotheses `IsClosed M₂`, `hZ` of lane C14-FDCb's FDC02 / FDC04 consumers. -/
theorem Gaf02ChainE.relative_removal_zero_far_EFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {Z Sl M₁ M₂ : Set X}
    (hZ : Z = ⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
    (hM₁ : M₁ = (interior Z)ᶜ)
    (hM₂ : M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set M₁)) :
    IsClosed M₂ ∧
      ∀ q ∈ M₂, ∀ z (hz : z ∈ P.zero.centres),
        38 / 100 * (P.zero.zero z hz).radius ≤ dist q z := by
  have hM₁c : IsClosed M₁ := by
    rw [hM₁]
    exact isOpen_interior.isClosed_compl
  refine ⟨by rw [hM₂]; exact isClosed_relative_removal_EFC Sl hM₁c, fun q hq => ?_⟩
  have hq1 : q ∈ M₁ := by
    rw [hM₂] at hq
    exact hq.1
  rw [hM₁, hZ] at hq1
  exact Ĉ.zero_far_verbatim_of_mem_M1_EFC hεr he hq1

/-- **FDC01's zero step, sharp metric form**: a zero-stratum point `p` and `q` with
`d(q, p) < 6Δρ(p)` give a selected zero centre `z` with `p ∈ B(z, R_z/10)` and
`d(q, z) < .107R_z` (`T ≥ 1000Δ`, `100ΔΛ ≤ 1/100`; LPA05's tenth-radius cover). -/
theorem fdc01_zero_exclusion_sharp_EFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hT : 1000 * Δ ≤ T) {p q : X}
    (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0) (hqp : dist q p < 6 * Δ * ρ p) :
    ∃ z, ∃ hz : z ∈ P.zero.centres, dist p z < (P.zero.zero z hz).radius / 10 ∧
      dist q z < 107 / 1000 * (P.zero.zero z hz).radius := by
  have hcov := P.zero.covers_stratum hp
  simp only [mem_iUnion] at hcov
  obtain ⟨z, hz, hpz⟩ := hcov
  refine ⟨z, hz, hpz, ?_⟩
  set R := (P.zero.zero z hz).radius with hRdef
  have hrz := hρ z
  have hT0 : 0 < T := by nlinarith
  have hTR : T * ρ z ≤ R := (P.zero.radius_mem z hz).1
  have hR : 0 < R := lt_of_lt_of_le (mul_pos hT0 hrz) hTR
  have hpz' : dist p z < R / 10 := hpz
  have hρp : ρ p ≤ ρ z + Λ * (R / 10) := by
    have h1 := P.lipschitz_scale.dist_le_mul p z
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist p z ≤ Λ * (R / 10) := mul_le_mul_of_nonneg_left hpz'.le hΛ
    linarith [(abs_le.mp h1).2]
  have h6 : 6 * Δ * ρ p ≤ 6 * Δ * ρ z + 6 * Δ * Λ * (R / 10) := by
    have := mul_le_mul_of_nonneg_left hρp (by positivity : (0 : ℝ) ≤ 6 * Δ)
    linarith
  have hz1 : 6 * Δ * ρ z ≤ 6 / 1000 * R := by
    have h1 : 1000 * Δ * ρ z ≤ T * ρ z := mul_le_mul_of_nonneg_right hT hrz.le
    linarith
  have hz2 : 6 * Δ * Λ * (R / 10) ≤ 6 / 100000 * R := by
    have h1 : Δ * Λ ≤ 1 / 10000 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hR.le
    nlinarith
  have h3 := dist_triangle q p z
  linarith

/-- **FDC01's zero step from the actual `M₁`, without `e ≤ 1/1000`**: for `q ∈ U_i` with
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` and `q ∉ int ⋃_k Z_k`, the selected edge centre `p_i` is not
zero-stratum. Uses only the chain's `e < 1/40` (`(.381 − e)R > .356R > .107R`). -/
theorem Gaf02ChainE.fdc01_not_zero_of_mem_M1_EFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    {i : X} (hi : i ∈ P.edge.centres) {q : X} (hq : q ∈ ball i (100 * Δ * ρ i))
    (hηq : |P.edge.coord i q| ≤ 401 / 100 * Δ) (htq : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ)
    (hM₁ : q ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ) :
    i ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 := by
  obtain ⟨hΛ, hΔ1, -, -, hLΛ, -, he, hT, hσs, hσs1, -⟩ := Ĉ.toChain.std
  have hΔ : 0 < Δ := by linarith
  have hT' : 1000 * Δ ≤ T := by nlinarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := hlam.trans (by norm_num)
  have hqi := (fdc01_exclusion_inputs_C14 P hΔ hΛ hμ hτ hlam hT' hσs hσs1 hi hq hηq htq).1
  intro h0
  obtain ⟨z, hz, -, hqz⟩ := fdc01_zero_exclusion_sharp_EFC P.toLocalChartPackets hΔ hΛ hΔΛ hT' h0
    hqi
  have hfar := Ĉ.zero_far_of_mem_M1_EFC hεr hM₁ z hz
  have hR := (P.zero.zero z hz).radius_pos
  have h1 : 107 / 1000 * (P.zero.zero z hz).radius ≤
      (381 / 1000 - e) * (P.zero.zero z hz).radius :=
    mul_le_mul_of_nonneg_right (by linarith) hR.le
  linarith

end DifferentialGeometry.Geometry.Collapse
