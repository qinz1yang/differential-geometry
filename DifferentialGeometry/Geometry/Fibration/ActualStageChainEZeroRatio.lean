import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesRegular
import DifferentialGeometry.Topology.Manifold.RatioCompatibleDefiner

/-!
# ZSP02's GLOBAL ratio: a defining function equal to `u_k/v_k − .4` near the whole face

Lane C14-ZSP35d. Review 74 D74-7 (package Z0, closed instance `a = v/R`); blueprint ZSP02
(B:6390–6393: "on a neighborhood of this entire boundary `v_i > .99R_i` and `u_i/v_i − .4` is a
smooth defining function with nonzero differential"), made GLOBAL for the rows producer's
`ZeroDomains.ratio` / `ratio_smooth` / `ratio_regular` / `range_eq` / `boundary_eq` fields.

The linearized global function `H_k = ψ(η_k) + χ(η_k)(q − η_k)` (`q = ℓ_k ∘ E + .4`,
`zsp02_defining_global_ZSP35`) satisfies `H_k − .4 = (v_k/R_k)(u_k/v_k − .4)` on the thin annulus
`{.39 < η_k < .41}` — NOT `u_k/v_k − .4` itself unless `v_k = R_k`. The generic kernel
`exists_ratioCompatible_global_definer_ZSP35` (factor `a = v_k/R_k`, positive on the annulus by
ZSP01's (ZE)) divides the factor out near the face only.

* `zspDefiner_ZSP35` (the name of `H_k`), `zspDefiner_sub_eq_ZSP35` (the factorization).
* `Gaf02ChainE.zsp02_global_ratio_ZSP35` (Ĉ : Gaf02ChainE, `εr < 1/2`): a smooth `F` on `M` and an
  open `N ⊇ ∂Z_k` with `closure N ⊆ {.39 < η_k < .41}`, `v_k > .99R_k` on `closure N`,
  `F = u_k/v_k − .4` on `N`, `Z_k = {F ≤ 0}`, `(ZF) = {F = 0}`, `dF ≠ 0` on `{F = 0}`.

Consumer: `zsp02_global_ratio_C14Z_ZSP35` (final family; `∂Z_k = {F = 0}` with `frontier`).
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

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- ZSP02's global linearized defining function `H_k = ψ(η_k) + χ(η_k)(ℓ_k ∘ f + .4 − η_k)` (the
function of (ZH) at `τ = 1`). -/
def zspDefiner_ZSP35 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) : X → ℝ :=
  fun z => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
    zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
      (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)

/-- **The factorization on the thin annulus**: where `.39 < η_k < .41` and `v_k ≠ 0`,
`H_k − .4 = (v_k/R_k)(u_k/v_k − .4)`. -/
theorem zspDefiner_sub_eq_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {z : X}
    (h1 : 39 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)
    (h2 : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100)
    (hv : (f z (.inr (.inr (.inr (.inl k))))).snd ≠ 0) :
    zspDefiner_ZSP35 L Z k f z - 2 / 5 =
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          (f z (.inr (.inr (.inr (.inl k))))).snd *
        (((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  rw [zspDefiner_ZSP35, zspPsi_eq_self_ZSP35 (by linarith) (by linarith),
    zspChi_eq_one_ZSP35 (by linarith) (by linarith), zspQCLM_apply_ZSP35]
  field_simp
  ring

end Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **ZSP02's global ratio on `Gaf02ChainE`** (D74-7, package Z0, closed instance `a = v/R`): for
every zero index `k` there are a smooth `F : M → ℝ` and an open `N ⊇ ∂Z_k` (ZF) with
`closure N ⊆ {.39 < η_k < .41}` and `v_k(E) > .99R_k` on `closure N`, such that
`F = u_k(E)/v_k(E) − .4` on `N`, `Z_k = {F ≤ 0}`, `(ZF) = {F = 0}`, and `dF ≠ 0` at every zero. -/
theorem Gaf02ChainE.zsp02_global_ratio_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) :
    ∃ (F : X → ℝ) (N : Set X), IsOpen N ∧
      zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ N ∧
      (∀ z ∈ closure N,
        39 / 100 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100 ∧
        99 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
          (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd) ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ z ∈ N, F z = ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) ∧
      {z | F z ≤ 0} = zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      {z | F z = 0} = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      ∀ x, F x = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 := by
  obtain ⟨hH, hreg, hsub, hlev, -, -⟩ := Ĉ.zsp02_defining_global_ZSP35 hεr k
  obtain ⟨-, -, -, -, -, hface, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  obtain ⟨hf, -, hδ₀, hZE, -, -⟩ := Ĉ.zsp02_inputs_ZSP35
  obtain ⟨hηc, -, -, -, -⟩ := zsp_radial_facts_ZSP35 P.zero k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hH' : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := hH
  have hG : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun z => zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E z - 2 / 5) :=
    hH'.sub contMDiff_const
  have hGeq : ∀ z, zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E z - 2 / 5 = 0 ↔
      z ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := fun z => by
    rw [sub_eq_zero, ← hlev]
    rfl
  have hGle : ∀ z, zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E z - 2 / 5 ≤ 0 ↔
      z ∈ zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := fun z => by
    rw [sub_nonpos, ← hsub]
    rfl
  have hregG : ∀ x, zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E x - 2 / 5 = 0 →
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
        (fun z => zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E z - 2 / 5) x ≠ 0 := by
    intro x hx h0
    have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
        (zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) x :=
      (hH' x).mdifferentiableAt (by simp)
    have hm := (hd.hasMFDerivAt.sub (hasMFDerivAt_const (I := 𝓘(ℝ, E3)) (I' := 𝓘(ℝ, ℝ))
      (2 / 5 : ℝ) x)).mfderiv
    have heq : (fun z => zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E z - 2 / 5) =
        zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E - fun _ => (2 / 5 : ℝ) := rfl
    rw [heq, hm] at h0
    obtain ⟨v, hv⟩ := hreg x (by rw [sub_eq_zero] at hx; exact hx) 1
    have h1 := DFunLike.congr_fun h0 v
    have h2 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) x v =
        0 := (sub_zero _).symm.trans h1
    have h0' : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
        zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) x v = 0 := h2
    rw [h0'] at hv
    exact absurd (show (0 : ℝ) = 1 from hv) zero_ne_one
  -- the positive factor `v_k/R_k` on the thin annulus
  have hband : ∀ z, 39 / 100 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z →
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100 →
      99 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd := by
    intro z h1 h2
    have hvz := zsp_band_marker_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E (hZE k) (z := z)
      ⟨by linarith, by linarith⟩
    nlinarith
  have hv : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd) :=
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inr (.inl k))))).contDiff.comp_contMDiff hf
  set O : Set X := {z | 39 / 100 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const)
  have hzero : {x | zspDefiner_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E x - 2 / 5 = 0} ⊆ O := by
    intro z hz
    obtain ⟨h1, h2⟩ := abs_lt.mp (hface z ((hGeq z).mp hz))
    exact ⟨by linarith, by linarith⟩
  obtain ⟨F, N, hNo, hZN, hNO, hFs, hFr, hFle, hF0, hFreg⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_ratioCompatible_global_definer_ZSP35
      hG hregG hO hzero
      (r := fun z => ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5)
      (contMDiff_const.mul hv).contMDiffOn
      (fun z hz => mul_pos (inv_pos.mpr hR) (by nlinarith [hband z hz.1 hz.2]))
      (fun z hz => zspDefiner_sub_eq_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hz.1 hz.2
        (by nlinarith [hband z hz.1 hz.2]))
  refine ⟨F, N, hNo, fun z hz => hZN ((hGeq z).mpr hz), fun z hz => ?_, hFs, hFr, ?_, ?_, hFreg⟩
  · obtain ⟨h1, h2⟩ := hNO hz
    exact ⟨h1, h2, hband z h1 h2⟩
  · rw [hFle]
    ext z
    exact hGle z
  · rw [hF0]
    ext z
    exact hGeq z

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **Consumer: the global ratio on the final family** (chain on the `C14` projection of
`LocalChartPacketsC14Z`): a smooth `F` on `M`, equal to `u_k/v_k − .4` on an open neighbourhood
of the whole frontier of `Z_k`, with `Z_k = {F ≤ 0}`, `frontier Z_k = {F = 0}` and `dF ≠ 0`
there. -/
theorem zsp02_global_ratio_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) :
    ∃ (F : X → ℝ) (N : Set X), IsOpen N ∧
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ⊆ N ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ z ∈ N, F z = ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) ∧
      {z | F z ≤ 0} = zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      {z | F z = 0} = frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      ∀ x, F x = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 := by
  obtain ⟨F, N, hNo, hZN, -, hFs, hFr, hFle, hF0, hFreg⟩ := Ĉ.zsp02_global_ratio_ZSP35 hεr k
  have hfr := (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1
  exact ⟨F, N, hNo, hfr ▸ hZN, hFs, hFr, hFle, hfr ▸ hF0, hFreg⟩

end Final

end DifferentialGeometry.Geometry.Collapse
