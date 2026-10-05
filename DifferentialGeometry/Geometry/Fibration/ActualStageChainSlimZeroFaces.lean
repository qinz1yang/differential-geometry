import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimAtlas
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroSaturation
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# ZSP03 for `j = 3`: whole zero faces are whole slim fibres, `∂C₃` is finite, `C₃` is regular

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP03 (B:6481–6529), slim stage, on the chain with
(JA) `Ĉ : Gaf02ChainEJA` and the closed slim base `Bs = W₃ ∩ R₃` of G10 (`f = π₃ ∘ E`,
`U = f⁻¹(Bs)`, chart `ψ_i ∘ g_i = f` on `Y_i`). `Z = ⋃_k Z_k` (ZSP02), `M₁ = M ∖ int Z`.

* generic: `deriv_ne_zero_of_eventuallyEq_comp_ZSP35` (a function factoring through `g` with
  nonzero differential has a nonzero one-variable derivative), `exists_isolated_zero_ZSP35`,
  `exists_pos_near_ZSP35` (sign change at a simple zero).
* `zspBaseFun_ZSP35` (`b_k(w) = u_k(w)/v_k(w) − .4` on the block space);
  `Gaf02ChainEJA.slim_face_chart_ZSP35`: at a face point `q ∈ U`, `b_k ∘ ψ_i` has a simple zero
  at `g_i(q)` (the descended defining function has nonzero differential on `B₃`).
* `Gaf02ChainEJA.zsp03_slim_face_fibre_ZSP35` (final family): if `∂Z_k` meets `U`, the ENTIRE
  connected face `∂Z_k` is ONE whole fibre `f⁻¹(f p)` (B:6491–6493, 6516–6523).
* `Gaf02ChainEJA.zsp03_slim_face_points_ZSP35`: the base face set
  `F₃ = ⋃_k f(∂Z_k ∩ U)` is finite (one point per face meeting `U`).
* `Gaf02ChainEJA.zsp03_slim_fibre_ZSP35` (whole fibres over `Bs` lie in `int Z` or in `M₁`);
  `zsp03_slim_saturated_ZSP35` (`M₁ ∩ U = U ∩ f⁻¹(C₃)`, `C₃ = f(M₁ ∩ U) ⊆ Bs` relatively closed,
  `Bs ∖ f(Z) ⊆ relint C₃`, `C₃ ∖ relint C₃ ⊆ F₃`).
* `Gaf02ChainEJA.zsp03_slim_regular_ZSP35` (final family): `C₃ ⊆ closure (relint C₃)` — the
  kernel's input (I3) on the closed side.

Consumer: `zsp03_slim_C14Z_ZSP35` (all of the above for a chain on the final family).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Descent of a nonzero differential to one variable**: if `r = h ∘ g` near `p`, `g` is
differentiable at `p`, `h` at `g p`, and `dr(p) ≠ 0`, then `h'(g p) ≠ 0`. -/
theorem deriv_ne_zero_of_eventuallyEq_comp_ZSP35 {r g : M → ℝ} {h : ℝ → ℝ} {p : M}
    (hr : r =ᶠ[𝓝 p] h ∘ g) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g p)
    (hh : DifferentiableAt ℝ h (g p)) (hne : mfderiv I 𝓘(ℝ, ℝ) r p ≠ 0) :
    deriv h (g p) ≠ 0 := by
  intro h0
  have hf0 : fderiv ℝ h (g p) = 0 :=
    ContinuousLinearMap.ext_ring (by rw [zero_apply]; exact h0)
  have hh' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h (g p) 0 := by
    have := hh.hasFDerivAt.hasMFDerivAt
    rw [hf0] at this
    exact this
  have hc := (hh'.comp p hg.hasMFDerivAt).congr_of_eventuallyEq hr
  apply hne
  rw [hc.mfderiv]
  ext v
  rfl

/-- **A simple zero is isolated**: if `h'(t₀) ≠ 0`, some open `O ∋ t₀` meets the level
`{h = h t₀}` only at `t₀`. -/
theorem exists_isolated_zero_ZSP35 {h : ℝ → ℝ} {t₀ : ℝ} (hh : DifferentiableAt ℝ h t₀)
    (hne : deriv h t₀ ≠ 0) :
    ∃ O : Set ℝ, IsOpen O ∧ t₀ ∈ O ∧ ∀ t ∈ O, h t = h t₀ → t = t₀ := by
  have hev := hh.hasDerivAt.eventually_ne (c := h t₀) hne
  obtain ⟨O, hO, ho, hsub⟩ := mem_nhdsWithin.mp hev
  refine ⟨O, hO, ho, fun t ht hht => ?_⟩
  by_contra hne'
  exact hsub ⟨ht, hne'⟩ hht

/-- **Sign change at a simple zero**: if `h(t₀) = 0` and `h'(t₀) ≠ 0`, every neighbourhood of
`t₀` contains a point where `h > 0`. -/
theorem exists_pos_near_ZSP35 {h : ℝ → ℝ} {t₀ : ℝ} (hh : DifferentiableAt ℝ h t₀)
    (hne : deriv h t₀ ≠ 0) (h0 : h t₀ = 0) {T : Set ℝ} (hT : T ∈ 𝓝 t₀) :
    ∃ t ∈ T, 0 < h t := by
  have hs := hh.hasDerivAt.tendsto_slope
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hev : ∀ᶠ t in 𝓝[≠] t₀, slope h t₀ t < 0 := hs (gt_mem_nhds hneg)
    have hev2 : ∀ᶠ t in 𝓝[<] t₀, slope h t₀ t < 0 ∧ t ∈ T :=
      (hev.filter_mono (nhdsLT_le_nhdsNE t₀)).and (nhdsWithin_le_nhds hT)
    obtain ⟨t, ⟨hsl, htT⟩, htlt⟩ := (hev2.and self_mem_nhdsWithin).exists
    refine ⟨t, htT, ?_⟩
    rw [slope_def_field, h0, sub_zero] at hsl
    have hd : t - t₀ < 0 := by linarith [show t < t₀ from htlt]
    exact (div_neg_iff.mp hsl).elim (fun h1 => h1.1) (fun h1 => absurd h1.2 (not_lt.mpr hd.le))
  · have hev : ∀ᶠ t in 𝓝[≠] t₀, 0 < slope h t₀ t := hs (lt_mem_nhds hpos)
    have hev2 : ∀ᶠ t in 𝓝[>] t₀, 0 < slope h t₀ t ∧ t ∈ T :=
      (hev.filter_mono (nhdsGT_le_nhdsNE t₀)).and (nhdsWithin_le_nhds hT)
    obtain ⟨t, ⟨hsl, htT⟩, htgt⟩ := (hev2.and self_mem_nhdsWithin).exists
    refine ⟨t, htT, ?_⟩
    rw [slope_def_field, h0, sub_zero] at hsl
    have hd : 0 < t - t₀ := by linarith [show t₀ < t from htgt]
    exact (div_pos_iff.mp hsl).elim (fun h1 => h1.1) (fun h1 => absurd h1.2 (not_lt.mpr hd.le))

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- ZSP03's base function `b_k(w) = u_k(w)/v_k(w) − .4` on the block space (the descended
defining function of the zero face). -/
def zspBaseFun_ZSP35
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (k : P.zero.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ :=
  fun y => ((y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 / (y (.inr (.inr (.inr (.inl k))))).snd -
    2 / 5

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The slim stage map `f = π₃ ∘ E`. -/
def slimMap_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)

/-- ZSP03's removed zero region `Z = ⋃_k Z_k`. -/
def zeroUnion_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Set X :=
  ⋃ k : P.zero.finite_centres.toFinset, zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E

/-- The base face set `F₃ = ⋃_k f(∂Z_k ∩ U)`. -/
def slimFacePoints_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  ⋃ k : P.zero.finite_centres.toFinset, C.slimMap_ZSP35 ''
    (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
      C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35)

/-- ZSP03's slim base domain `C₃ = f(M₁ ∩ U)`, `M₁ = M ∖ int Z`. -/
def slimC3_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.slimMap_ZSP35 '' ((interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35)

theorem continuous_slimMap_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    Continuous C.slimMap_ZSP35 :=
  (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.continuous.comp
    C.toChain.stage_smooth.2.2.continuous

/-- `b_k ∘ f` is ZSP02's defining quantity `r_k = u_k(E)/v_k(E) − .4` (the zero block is
retained by `π₃`). -/
theorem baseFun_slimMap_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (k : P.zero.finite_centres.toFinset) (y : X) :
    zspBaseFun_ZSP35 P k (C.slimMap_ZSP35 y) =
      ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 :=
  (C.toChain.zero_base_function_ZSP35 2 k).1 y

/-- The zero region is compact. -/
theorem isCompact_zeroUnion_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) :
    IsCompact C.zeroUnion_ZSP35 :=
  isCompact_iUnion fun k => (C.zsp02_domain_ZSP35 hεr k).1

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {cadj : ℝ}

/-- **The descended defining function has a simple zero in the chart** (B:6510–6515): at a face
point `q ∈ ∂Z_k ∩ U` there is a slim chart `i` with `q ∈ Y_i`, `ψ_i ∘ g_i = f` on `Y_i`, and the
one-variable function `b_k ∘ ψ_i` is differentiable at `g_i(q)`, vanishes there and has nonzero
derivative there. -/
theorem slim_face_chart_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) {q : X}
    (hqF : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E)
    (hqU : C.slimMap_ZSP35 q ∈ C.slimBs_ZSP35) :
    ∃ i : P.slim.finite_centres.toFinset, q ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
      (∀ y ∈ gaf07SlimY_GAFC P.toLocalChartPackets i,
        C.toChain.gaf07SlimCoord_GAFC i y ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
        C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i y) = C.slimMap_ZSP35 y) ∧
      DifferentiableAt ℝ (fun t => zspBaseFun_ZSP35 P k (C.slimParam_ZSP35 i t))
        (C.toChain.gaf07SlimCoord_GAFC i q) ∧
      deriv (fun t => zspBaseFun_ZSP35 P k (C.slimParam_ZSP35 i t))
        (C.toChain.gaf07SlimCoord_GAFC i q) ≠ 0 ∧
      zspBaseFun_ZSP35 P k (C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q)) = 0 := by
  obtain ⟨i, hY, -, hloc⟩ := C.slim_chart_local_ZSP35 hqU
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, hdne⟩ := C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hvq : 0 < (C.E q (.inr (.inr (.inr (.inl k))))).snd := by
    have := (hOprop q (hFO hqF)).1
    nlinarith
  have hfq : C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q) = C.slimMap_ZSP35 q :=
    (hloc q hY).2
  have hzero : zspBaseFun_ZSP35 P k (C.slimMap_ZSP35 q) = 0 := by
    rw [C.baseFun_slimMap_ZSP35 k q, hqF.2, mul_div_assoc, div_self hvq.ne', mul_one, sub_self]
  have hbk : ContDiffAt ℝ ∞ (zspBaseFun_ZSP35 P k) (C.slimMap_ZSP35 q) := by
    refine zero_base_function_smooth_ZSP35 _ _ ?_
    change ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q)
      (.inr (.inr (.inr (.inl k))))).snd ≠ 0
    rw [gafStageQ_starProjection_zeroTag_GAF8 P 2 k]
    exact hvq.ne'
  have hψ : DifferentiableAt ℝ (C.slimParam_ZSP35 i) (C.toChain.gaf07SlimCoord_GAFC i q) :=
    ((C.slimParam_spec_ZSP35 i).1.contDiffAt (isOpen_ball.mem_nhds (hloc q hY).1)).differentiableAt
      (by simp)
  have hh : DifferentiableAt ℝ (fun t => zspBaseFun_ZSP35 P k (C.slimParam_ZSP35 i t))
      (C.toChain.gaf07SlimCoord_GAFC i q) := by
    have hb' : DifferentiableAt ℝ (zspBaseFun_ZSP35 P k)
        (C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q)) := by
      rw [hfq]
      exact hbk.differentiableAt (by simp)
    exact hb'.comp _ hψ
  have heq : (fun y => ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) =ᶠ[𝓝 q]
      (fun t => zspBaseFun_ZSP35 P k (C.slimParam_ZSP35 i t)) ∘
        C.toChain.gaf07SlimCoord_GAFC i := by
    filter_upwards [(isOpen_gaf07SlimY_GAFC P.toLocalChartPackets i).mem_nhds hY] with y hy
    exact ((congrArg (zspBaseFun_ZSP35 P k) (hloc y hy).2).trans
      (C.baseFun_slimMap_ZSP35 k y)).symm
  have hg : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.toChain.gaf07SlimCoord_GAFC i) q :=
    ((C.contMDiff_slimCoord_ZSP35 i) q).mdifferentiableAt (by simp)
  refine ⟨i, hY, hloc, hh, deriv_ne_zero_of_eventuallyEq_comp_ZSP35 heq hg hh (hdne q hqF), ?_⟩
  rw [hfq]
  exact hzero

/-- **Whole fibres over `Bs` do not cross the zero region** (B:6503–6507, slim stage): for
`w ∈ Bs` the WHOLE fibre `f⁻¹(w)` (connected, C14-GAF-C) lies in `int Z` or in `M₁`. -/
theorem zsp03_slim_fibre_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hεr : εr < 1 / 2)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.slimBs_ZSP35) :
    C.slimMap_ZSP35 ⁻¹' {w} ⊆ interior C.zeroUnion_ZSP35 ∨
      C.slimMap_ZSP35 ⁻¹' {w} ⊆ (interior C.zeroUnion_ZSP35)ᶜ := by
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, hfrU⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hw.2
  have hcon : IsConnected (C.slimMap_ZSP35 ⁻¹' {w}) :=
    (C.toGaf02ChainE.gaf07_slim_whole_fibre_GAFC C.c_two_lt w hw.1 i hi.1 hi.2).2.2.2
  by_cases hmeet : ∃ k : P.zero.finite_centres.toFinset,
      (C.slimMap_ZSP35 ⁻¹' {w} ∩
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)).Nonempty
  · obtain ⟨k, p, hpF, hp⟩ := hmeet
    refine Or.inr fun q hq => hfrk k ?_
    have hpq : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q) :=
      (show _ = w from hpF).trans (show _ = w from hq).symm
    exact (Gaf02ChainE.zsp03_face_saturated_ZSP35 (Ĉ := C.toGaf02ChainE) (k := k) hεr 2
      hpq).mp hp
  · push Not at hmeet
    have hF : C.slimMap_ZSP35 ⁻¹' {w} ⊆ interior C.zeroUnion_ZSP35 ∪
        (closure C.zeroUnion_ZSP35)ᶜ := by
      intro x hx
      by_cases hxi : x ∈ interior C.zeroUnion_ZSP35
      · exact Or.inl hxi
      · refine Or.inr fun hxc => ?_
        have hxf : x ∈ frontier C.zeroUnion_ZSP35 := ⟨hxc, hxi⟩
        rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU] at hxf
        obtain ⟨k, hk⟩ := mem_iUnion.mp hxf
        have hne := hmeet k
        rw [Set.eq_empty_iff_forall_notMem] at hne
        exact hne x ⟨hx, hk⟩
    rcases IsPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
        (disjoint_compl_right_iff_subset.mpr interior_subset_closure) hF hcon.isPreconnected with
      h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (compl_subset_compl.mpr interior_subset_closure))

/-- **ZSP03, slim stage: saturation and the base domain `C₃`** (B:6486–6489, 6503–6509): with
`M₁ = M ∖ int Z`, `U = f⁻¹(Bs)`, `C₃ = f(M₁ ∩ U)`: `M₁ ∩ U = U ∩ f⁻¹(C₃)`; `C₃ ⊆ Bs` is relatively
closed; every point of `Bs ∖ f(Z)` is a relative interior point of `C₃`; and a point of `C₃` that
is not a relative interior point lies in the base face set `F₃`. -/
theorem zsp03_slim_saturated_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 ∧
      C.slimC3_ZSP35 ⊆ C.slimBs_ZSP35 ∧
      IsClosed (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
      C.slimBs_ZSP35 \ C.slimMap_ZSP35 '' C.zeroUnion_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
      C.slimC3_ZSP35 \
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ⊆
        C.slimFacePoints_ZSP35 := by
  have hsat : ∀ p q : X, C.slimMap_ZSP35 p ∈ C.slimBs_ZSP35 →
      C.slimMap_ZSP35 p = C.slimMap_ZSP35 q →
      (p ∈ (interior C.zeroUnion_ZSP35)ᶜ ↔ q ∈ (interior C.zeroUnion_ZSP35)ᶜ) := by
    intro p q hp hpq
    have hpF : p ∈ C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} := rfl
    have hqF : q ∈ C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} := hpq.symm
    rcases C.zsp03_slim_fibre_ZSP35 hεr hp with h | h
    · exact ⟨fun h' => absurd (h hpF) h', fun h' => absurd (h hqF) h'⟩
    · exact ⟨fun _ => h hqF, fun _ => h hpF⟩
  have hZc : IsClosed (C.slimMap_ZSP35 '' C.zeroUnion_ZSP35) :=
    ((C.isCompact_zeroUnion_ZSP35 hεr).image C.continuous_slimMap_ZSP35).isClosed
  have hC3B : C.slimC3_ZSP35 ⊆ C.slimBs_ZSP35 := by
    rintro _ ⟨p, ⟨-, hp⟩, rfl⟩
    exact hp
  -- `Bs ∖ f(Z) ⊆ C₃` (every point of `W₃` is in the image)
  have hBZ : C.slimBs_ZSP35 \ C.slimMap_ZSP35 '' C.zeroUnion_ZSP35 ⊆ C.slimC3_ZSP35 := by
    rintro w ⟨hw, hwZ⟩
    obtain ⟨p, hp⟩ := C.toGaf02ChainE.gaf07_slim_onto_GAFC w hw.1
    have hpw : C.slimMap_ZSP35 p = w := hp
    refine ⟨p, ⟨fun hpi => hwZ ⟨p, interior_subset hpi, hpw⟩, ?_⟩, hpw⟩
    rw [mem_preimage, hpw]
    exact hw
  have hrel : C.slimBs_ZSP35 \ C.slimMap_ZSP35 '' C.zeroUnion_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) := by
    intro w hw
    exact DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mpr
      ⟨hw.1, (C.slimMap_ZSP35 '' C.zeroUnion_ZSP35)ᶜ, hZc.isOpen_compl, hw.2,
        fun y hy => hBZ ⟨hy.2, hy.1⟩⟩
  refine ⟨?_, hC3B, ?_, hrel, ?_⟩
  · ext p
    constructor
    · rintro ⟨hp, hpU⟩
      exact ⟨hpU, p, ⟨hp, hpU⟩, rfl⟩
    · rintro ⟨hpU, q, ⟨hq, hqU⟩, hqp⟩
      exact ⟨(hsat q p hqU hqp).mp hq, hpU⟩
  · -- properness of the whole restriction
    have hprop := (C.toChain.gaf07_proper_G47 2 C.slimBs_ZSP35).1
    have hcl : IsClosed {x : (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.E p)) ⁻¹' C.slimBs_ZSP35 | (x : X) ∈ (interior C.zeroUnion_ZSP35)ᶜ} :=
      isOpen_interior.isClosed_compl.preimage continuous_subtype_val
    convert hprop.isClosedMap _ hcl using 1
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨p, ⟨hp, hpX⟩, hpw⟩
      exact ⟨⟨p, hpX⟩, hp, Subtype.ext hpw⟩
    · rintro ⟨⟨p, hpX⟩, hp, hpw⟩
      exact ⟨p, ⟨hp, hpX⟩, congrArg Subtype.val hpw⟩
  · rintro w ⟨hw3, hwrel⟩
    have hwZ : w ∈ C.slimMap_ZSP35 '' C.zeroUnion_ZSP35 := by
      by_contra h
      exact hwrel (hrel ⟨hC3B hw3, h⟩)
    obtain ⟨q₁, ⟨hq₁, hq₁U⟩, rfl⟩ := hw3
    obtain ⟨q₂, hq₂, hq₂w⟩ := hwZ
    obtain ⟨k, hk⟩ := mem_iUnion.mp hq₂
    have hq₂c : q₂ ∈ (interior C.zeroUnion_ZSP35)ᶜ := (hsat q₁ q₂ hq₁U hq₂w.symm).mp hq₁
    have hq₂F : q₂ ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
      rw [(C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed.frontier_eq]
      exact ⟨hk, fun hint => hq₂c (interior_mono (subset_iUnion
        (fun k : P.zero.finite_centres.toFinset =>
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) k) hint)⟩
    refine mem_iUnion.mpr ⟨k, q₂, ⟨hq₂F, ?_⟩, hq₂w⟩
    rw [mem_preimage, hq₂w]
    exact hq₁U

end Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz oM}

/-- **ZSP03, `j = 3`: a zero face meeting `U` is ONE whole slim fibre** (B:6491–6493, 6516–6523):
if `p ∈ ∂Z_k` and `f(p) ∈ Bs`, then `f⁻¹(f p) = ∂Z_k` (the fibre is open in the connected face —
the descended `b_k` has an isolated simple zero in the base chart — and closed). -/
theorem zsp03_slim_face_fibre_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) {p : X}
    (hpF : p ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))
    (hpU : C.slimMap_ZSP35 p ∈ C.slimBs_ZSP35) :
    C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} =
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
  have hfr := (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1
  have hsub : C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} ⊆
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) :=
    C.toGaf02ChainE.zsp03_whole_fibre_ZSP35 hεr 2 k hpF
  refine Subset.antisymm hsub ?_
  rw [hfr] at hpF hsub ⊢
  have hcon : IsConnected (zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E) :=
    ((C.toGaf02ChainE.zsp02_types_ZSP35 hεr k).2.2.2 ⟨p, hpF⟩).2
  have : ConnectedSpace (zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E) :=
    isConnected_iff_connectedSpace.mp hcon
  set A : Set (zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E) :=
    Subtype.val ⁻¹' (C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p}) with hA
  have hAcl : IsClosed A :=
    (isClosed_singleton.preimage C.continuous_slimMap_ZSP35).preimage continuous_subtype_val
  have hAop : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    have hxw : C.slimMap_ZSP35 x.1 = C.slimMap_ZSP35 p := hx
    have hxU : C.slimMap_ZSP35 x.1 ∈ C.slimBs_ZSP35 := hxw ▸ hpU
    obtain ⟨i, hY, hloc, hh, hne, -⟩ := C.slim_face_chart_ZSP35 hεr k x.2 hxU
    obtain ⟨O, hO, htO, hiso⟩ := exists_isolated_zero_ZSP35 hh hne
    have hgc : Continuous (C.toChain.gaf07SlimCoord_GAFC i) :=
      (C.contMDiff_slimCoord_ZSP35 i).continuous
    refine ⟨Subtype.val ⁻¹' (gaf07SlimY_GAFC P.toLocalChartPackets i ∩
      C.toChain.gaf07SlimCoord_GAFC i ⁻¹' O), fun y hy => ?_,
      ((isOpen_gaf07SlimY_GAFC P.toLocalChartPackets i).inter (hO.preimage hgc)).preimage
        continuous_subtype_val, ⟨hY, htO⟩⟩
    -- `y` is a face point in the chart neighbourhood: `b_k ∘ ψ_i` vanishes at `g_i y`
    have hvy : 0 < (C.E y.1 (.inr (.inr (.inr (.inl k))))).snd := by
      have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
      have := y.2.1
      nlinarith
    have hy0 : zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
        (C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i y.1)) =
        zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
          (C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i x.1)) := by
      rw [(hloc y.1 hy.1).2, (hloc x.1 hY).2, C.baseFun_slimMap_ZSP35 k y.1,
        C.baseFun_slimMap_ZSP35 k x.1, y.2.2, x.2.2, mul_div_assoc, div_self hvy.ne', mul_div_assoc,
        div_self (by
          have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
          have := x.2.1
          nlinarith : (C.E x.1 (.inr (.inr (.inr (.inl k))))).snd ≠ 0)]
    have ht := hiso _ hy.2 hy0
    change C.slimMap_ZSP35 y.1 = C.slimMap_ZSP35 p
    rw [← (hloc y.1 hy.1).2, ht, (hloc x.1 hY).2, hxw]
  have hpA : (⟨p, hpF⟩ : zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E) ∈ A := rfl
  rcases isClopen_iff.mp ⟨hAcl, hAop⟩ with h | h
  · rw [h] at hpA
    exact absurd hpA (notMem_empty _)
  · intro y hy
    have : (⟨y, hy⟩ : zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E) ∈ A := by
      rw [h]
      exact mem_univ _
    exact this

/-- **ZSP03, `j = 3`: finitely many base face points** (B:6494–6495): each `f(∂Z_k ∩ U)` has at
most one point, so the base face set `F₃ = ⋃_k f(∂Z_k ∩ U)` is finite. -/
theorem zsp03_slim_face_points_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    (∀ k : P.zero.finite_centres.toFinset, (C.slimMap_ZSP35 ''
      (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
        C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35)).Subsingleton) ∧
      C.slimFacePoints_ZSP35.Finite := by
  have hsub : ∀ k : P.zero.finite_centres.toFinset, (C.slimMap_ZSP35 ''
      (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
        C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35)).Subsingleton := by
    rintro k _ ⟨p, ⟨hpF, hpU⟩, rfl⟩ _ ⟨q, ⟨hqF, -⟩, rfl⟩
    have h := C.zsp03_slim_face_fibre_ZSP35 hεr k hpF hpU
    have hq : q ∈ C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} := by
      rw [h]
      exact hqF
    exact hq.symm
  exact ⟨hsub, finite_iUnion fun k => (hsub k).finite⟩

/-- **ZSP03, `j = 3`: `C₃` is regular in `Bs`** (B:6510–6515; the kernel's input (I3)): every
point of `C₃` is a limit of relative interior points of `C₃` — at a face point `w = f(∂Z_k)` the
descended `b_k` changes sign in the base chart, and over its positive side the whole fibres lie
outside `Z` (properness keeps them in the defining neighbourhood of `∂Z_k`). -/
theorem zsp03_slim_regular_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    C.slimC3_ZSP35 ⊆ closure
      (Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) := by
  obtain ⟨-, -, -, hrel, hfront⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  intro w hw
  by_cases hwi : w ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)
  · exact subset_closure hwi
  obtain ⟨k, q, ⟨hqF, hqU⟩, rfl⟩ := mem_iUnion.mp (hfront ⟨hw, hwi⟩)
  have hfr := (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1
  have hqF' : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E := hfr ▸ hqF
  obtain ⟨i, hY, hloc, hh, hne, h0⟩ := C.slim_face_chart_ZSP35 hεr k hqF' hqU
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, -⟩ := C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k
  -- the defining neighbourhood of the face, away from the other zero domains
  set Vn : Set X := O ∩ ⋂ l ∈ ({k}ᶜ : Set P.zero.finite_centres.toFinset),
    (zspDomain_ZSP35 P.toLocalChartFamily P.zero l C.E)ᶜ with hVn
  have hVo : IsOpen Vn := hO.inter ((toFinite _).isOpen_biInter fun l _ =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr l).1.isClosed.isOpen_compl)
  have hfib : C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 q} ⊆ Vn := by
    rw [C.zsp03_slim_face_fibre_ZSP35 hεr k hqF hqU, hfr]
    intro y hy
    refine ⟨hFO hy, mem_iInter₂.mpr fun l hl => ?_⟩
    have hyk : y ∈ zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E :=
      (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed.frontier_subset (hfr ▸ hy)
    exact Set.disjoint_left.mp (C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr
      (Ne.symm (show l ≠ k from hl))) hyk
  -- fibres over a neighbourhood of `f q` stay in `Vn`
  have hGc : IsClosed (C.slimMap_ZSP35 '' Vnᶜ) :=
    (hVo.isClosed_compl.isCompact.image C.continuous_slimMap_ZSP35).isClosed
  have hqG : C.slimMap_ZSP35 q ∉ C.slimMap_ZSP35 '' Vnᶜ := by
    rintro ⟨y, hy, hyq⟩
    exact hy (hfib hyq)
  -- the chart parameter domain around `g_i q`
  have hdom : C.toChain.gaf07SlimCoord_GAFC i q ∈ C.slimAtlas_ZSP35.dom i := by
    refine ⟨(hloc q hY).1, ?_⟩
    change C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q) ∈
      gaf07SlimRatio_G47 P.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets
    rw [(hloc q hY).2]
    exact hqU.2
  have hψc : ContinuousAt (C.slimParam_ZSP35 i) (C.toChain.gaf07SlimCoord_GAFC i q) :=
    (C.slimAtlas_ZSP35.continuousOn_param_BCF i).continuousAt
      ((C.slimAtlas_ZSP35.isOpen_dom i).mem_nhds hdom)
  rw [_root_.mem_closure_iff]
  intro N hN hqN
  have hT : C.slimAtlas_ZSP35.dom i ∩ C.slimParam_ZSP35 i ⁻¹' (N ∩ (C.slimMap_ZSP35 '' Vnᶜ)ᶜ) ∈
      𝓝 (C.toChain.gaf07SlimCoord_GAFC i q) := by
    refine Filter.inter_mem ((C.slimAtlas_ZSP35.isOpen_dom i).mem_nhds hdom)
      (hψc.preimage_mem_nhds ?_)
    rw [(hloc q hY).2]
    exact (hN.inter hGc.isOpen_compl).mem_nhds ⟨hqN, hqG⟩
  obtain ⟨t, ⟨htd, htN, htG⟩, hpos⟩ := exists_pos_near_ZSP35 hh hne h0 hT
  have htB : C.slimParam_ZSP35 i t ∈ C.slimBs_ZSP35 := C.slimAtlas_ZSP35.param_mem_BCF htd
  refine ⟨C.slimParam_ZSP35 i t, htN, hrel ⟨htB, ?_⟩⟩
  rintro ⟨y, hyZ, hyt⟩
  have hyV : y ∈ Vn := by
    by_contra hyV
    exact htG ⟨y, hyV, hyt⟩
  obtain ⟨l, hl⟩ := mem_iUnion.mp hyZ
  have hlk : l = k := by
    by_contra hlk
    exact (mem_iInter₂.mp hyV.2 l hlk) hl
  subst hlk
  have hneg := ((hOprop y hyV.1).2.2).mp hl
  rw [← C.baseFun_slimMap_ZSP35 l y] at hneg
  have hyt' : C.slimMap_ZSP35 y = C.slimParam_ZSP35 i t := hyt
  rw [hyt'] at hneg
  linarith

end Gaf02ChainEJA

/-- **Consumer: ZSP03 for `j = 3` on the final family**: for a chain with (JA) on the `C14`
projection, every zero face meeting `U` is one whole slim fibre, the base face set `F₃` is finite,
`M₁ ∩ U = U ∩ f⁻¹(C₃)`, `C₃ ⊆ Bs` is relatively closed and regular, and its relative frontier lies
in `F₃`. -/
theorem zsp03_slim_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    (∀ (k : P.zero.finite_centres.toFinset) (p : X),
      p ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) →
      C.slimMap_ZSP35 p ∈ C.slimBs_ZSP35 →
      C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} =
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)) ∧
    C.slimFacePoints_ZSP35.Finite ∧
    (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 =
      C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 ∧
    C.slimC3_ZSP35 ⊆ C.slimBs_ZSP35 ∧
    IsClosed (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
    C.slimC3_ZSP35 ⊆
      closure (Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∧
    C.slimC3_ZSP35 \
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ⊆
      C.slimFacePoints_ZSP35 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  exact ⟨fun k p hp hpU => C.zsp03_slim_face_fibre_ZSP35 hεr k hp hpU,
    (C.zsp03_slim_face_points_ZSP35 hεr).2, h1, h2, h3, C.zsp03_slim_regular_ZSP35 hεr, h5⟩

end Final

end DifferentialGeometry.Geometry.Collapse
