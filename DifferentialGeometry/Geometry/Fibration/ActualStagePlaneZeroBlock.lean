import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes
import DifferentialGeometry.Geometry.Fibration.ActualZeroBlockIsolation

/-!
# (ZB\*) and the whole-small-block exit on the enhanced stage planes

Blueprint `master207B.tex`, ZSP01 (B:6323–6395) and CGP04 (whole small blocks); draft 59 §1.5
(D59-2). For a zero tag `k` (radius `R_k`), a preimage `p` of `x ∈ S_st` with `ρ(p) > 200R_k/T`,
and a cloud point `y ∈ S_st` in the contributor window of the radius `Σρ ∘ A.rsel x₀`:

  `J_k y = 0` and `A.plane y ≤ ker J_k`                                                  (ZB\*)

(`J_k` = projection onto the WHOLE zero block). Route (draft §1.5): (MCb) and the two-preimage
ratios give `ρ(q) ≥ (27/125)ρ(p)` for the model preimage `q = A.pre y` (`zero_chain_PLN`), the scale
of the reference chart gives `ρ(a) ≥ (4/5)ρ(q)`; a zero support meeting the reference comparison
domain would carry a point with `ρ ≤ 20R_k/T` and `ρ ≥ (3/4)ρ(a)` — impossible; so `k` is absent
from the ACTUAL support list of `Φ_a` and the whole `k`-block of `K_a ∘ Φ_a` vanishes (no new
pruning). The value half is ZSP01's original zero block at `q`.

Whole-small-block exit (draft §1.5, for CGP04): a marker block deleted by `K_a` (stage `0`,
`ρ(c) ≤ ρ(a)/2`) or excluded by the actual lists (stages `1, 2`, `ρ(c) ≤ .99ρ(a)`) vanishes as a
whole in `K_a ∘ Φ_a`, hence `A.plane x ≤ ker J_c`.

* `zero_chain_PLN`, `zero_meet_absurd_PLN`.
* `FirstStagePlanes_PLN.zero_block`, `EdgeStagePlanes_PLN.zero_block`,
  `SlimStagePlanes_PLN.zero_block`.
* `FirstStagePlanes_PLN.small_block_zero`, `.small_block_plane` (and the edge / slim analogues).
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNz {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNz {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNz {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **The scale chain of (ZB\*)**: for a selection `sel` over `S̃_st`, a preimage `p` of
`x ∈ S_st`, a preimage `q` of `y ∈ S_st` and the window
`B̄(y, 80ε⁻¹Σρ(sel y)) ∩ B(x, 8ε⁻¹Σρ(sel x)) ≠ ∅` (`Σ ≤ ε/10000`): `ρ(q) ≥ (27/125)ρ(p)`
((MCb) with `L' = 88ε⁻¹` and CFS26's two-preimage ratio twice). -/
theorem zero_chain_PLN (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) {p q : X}
    {x y : BlockSpace (fun _ : CGPTag L Z => ℝ²)}
    (hpx : cgpProjMap L Z (gafStageTags L Z st) p = x) (hx : x ∈ gafCloud L Z st)
    (hy : y ∈ gafCloud L Z st) (hqy : cgpProjMap L Z (gafStageTags L Z st) q = y)
    (hmeet : (closedBall y (80 * εc⁻¹ * (σ * ρ (sel y))) ∩
      ball x (8 * εc⁻¹ * (σ * ρ (sel x)))).Nonempty) :
    27 / 125 * ρ p ≤ ρ q := by
  classical
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hεi : 0 < εc⁻¹ := inv_pos.mpr hε
  have hrx := hρ (sel x)
  have hry := hρ (sel y)
  have h1 := mem_closedBall.mp hz1
  have h2 := mem_ball.mp hz2
  have hσ : 0 < σ := by
    by_contra h
    push_neg at h
    have h3 : σ * ρ (sel x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hrx.le
    have h4 : 8 * εc⁻¹ * (σ * ρ (sel x)) ≤ 0 := by nlinarith
    linarith [dist_nonneg (x := z) (y := x)]
  have hd : dist y x ≤ 88 * εc⁻¹ * max (σ * ρ (sel y)) (σ * ρ (sel x)) := by
    have h3 : dist y x ≤ dist z y + dist z x := dist_triangle_left y x z
    have hm1 : σ * ρ (sel y) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_left _ _
    have hm2 : σ * ρ (sel x) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_right _ _
    nlinarith
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  have hxT := gafCloud_subset_enlarged L Z hΔ0 st hx
  have hyT := gafCloud_subset_enlarged L Z hΔ0 st hy
  have hLs : 88 * εc⁻¹ * σ ≤ 1 / 5 := by
    have : εc⁻¹ * σ ≤ 1 / 10000 := by
      rw [inv_mul_le_iff₀ hε]
      linarith
    nlinarith
  have hmcb := (gafCloud_mcb_GAF2 L Z hΔ hΛ hsmall st sel hsel hσ.le (by positivity) hLs x hxT y
    hyT hd).1
  have h5 : 3 / 5 * ρ (sel x) ≤ ρ (sel y) := by
    have h6 : σ * (3 / 5 * ρ (sel x)) ≤ σ * ρ (sel y) := by
      have : σ * ρ (sel x) / (5 / 3) = σ * (3 / 5 * ρ (sel x)) := by ring
      linarith
    exact le_of_mul_le_mul_left h6 hσ
  have h7 := gafCloud_preimage_ratio_GAF4 L Z hΔ hΛ hsmall st sel hsel x hx p
    (by rw [gafStageQ_starProjection_globalMap]; exact hpx)
  have hsel' : ∀ w ∈ gafCloudEnlarged L Z st,
      cgpProjMap L Z (gafStageTags L Z st) (Function.update sel y q w) = w := by
    intro w hw
    by_cases hwy : w = y
    · subst hwy
      rw [Function.update_self]
      exact hqy
    · rw [Function.update_of_ne hwy]
      exact hsel w hw
  have h8 := gafCloud_preimage_ratio_GAF4 L Z hΔ hΛ hsmall st (Function.update sel y q) hsel' y hy
    (sel y) (by rw [gafStageQ_starProjection_globalMap]; exact hsel y hyT)
  rw [Function.update_self] at h8
  nlinarith

end Generic

section R

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_PLNz
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_PLNz
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_PLNz
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **No zero support meets a large reference**: if `ρ(a) > (80/3)R_k/T`, no point `z` of the closed
support of the zero cutoff of `k` lies in `B(a, Cρ(a))` with `ΛC ≤ 1/4` (LPA05: `ρ(z) ≤ 20R_k/T`;
slow variation: `ρ(z) ≥ (3/4)ρ(a)`). -/
theorem zero_meet_absurd_PLN
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) {k : X}
    (hk : k ∈ P.zero.centres) {a z : X} {Cr : ℝ}
    (hz : z ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)))
    (hza : dist z a < Cr * ρ a) (hC : Λ * Cr ≤ 1 / 4)
    (hρa : 80 / 3 * ((P.zero.zero k hk).radius / T) < ρ a) : False := by
  have h1 := zero_cutoff_ratio_GAF P hT he hεr hk hz
  have h2 := (scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a) hza hC).1
  have h3 : 20 * (P.zero.zero k hk).radius / T = 20 * ((P.zero.zero k hk).radius / T) := by ring
  linarith

end R

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

open Classical in
/-- **(ZB\*) at the first stage**: for a zero tag `k`, a preimage `p` of `x ∈ S` with
`ρ(p) > 200R_k/T` and `y ∈ S` in the contributor window of the radius `Σρ ∘ A.rsel x₀`
(`Σ ≤ ε_c/10000`): the whole `k`-block of `y` vanishes and `A.plane y ≤ ker J_k`. -/
theorem FirstStagePlanes_PLN.zero_block
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x y :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    blockProjCLM_PLN (V
        := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) y = 0 ∧
      A.plane y ≤ LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have hR := (P.zero.zero k.1 hk).radius_pos
  have hRT : 0 < (P.zero.zero k.1 hk).radius / T := div_pos hR hT
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
      q = y := hqy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hchain := zero_chain_PLN P.toLocalChartFamily P.zero hΔ hΛ hsmall 0 (A.rsel x₀) hsel hε
    hσε hpx hx hy hqy' hmeet
  have hρp' : 200 * ((P.zero.zero k.1 hk).radius / T) < ρ p := by
    have : 200 * (P.zero.zero k.1 hk).radius / T = 200 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    linarith
  have hρq : 20 * (P.zero.zero k.1 hk).radius / T < ρ q := by
    have : 20 * (P.zero.zero k.1 hk).radius / T = 20 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    nlinarith
  have hsa := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a.1) (mem_ball.mp hqa)
    (by nlinarith : Λ * (200) ≤ 1 / 4)
  have hρa : 80 / 3 * ((P.zero.zero k.1 hk).radius / T) < ρ a.1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have hz := zsp01_original_zero_block P.toLocalChartPacketsR hT he hεr k hρq
    rw [blockProjCLM_apply_PLN, ← hqy']
    change blockRestrict _ (cgpGlobalMap P.toLocalChartFamily P.zero q) _ = 0
    rw [blockRestrict_apply]
    split_ifs
    · exact hz
    · rfl
  have habs : (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∉
      tcpListedTags P.toLocalChartFamily P.zero a.1 := by
    intro h
    obtain ⟨z, hz, hza⟩ := (mem_tcpListedTags_KA7 (i := a.1)).mp h
    exact zero_meet_absurd_PLN P.toLocalChartPacketsR hΛ hT he hεr hk hz (mem_ball.mp hza)
      (by nlinarith) hρa
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord a q _ ?_
    (Eventually.of_forall fun u => ?_)
  · refine (A.prune a).differentiableAt.comp _ ?_
    rw [A.model_eq a]
    exact ((contDiff_tcpModelGraph _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _
  · beta_reduce
    rw [A.prune_eq a, A.model_eq a, Function.comp_apply, blockRestrict_apply]
    split_ifs
    · change tcpModelComponent P.toLocalChartFamily P.zero a.1
        (tcpListedTags P.toLocalChartFamily P.zero a.1) (tcpListedEdges P.toLocalChartFamily a.1)
        (A.Ac a) (A.cc a) (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) (.inr (.inr (.inr (.inl k)))) u = 0
      simp only [tcpModelComponent, habs, ite_false]
      rfl
    · rfl

open Classical in
/-- **(ZB\*) at the edge stage**: for a zero tag `k`, a preimage `p` of `x ∈ S₂` with
`ρ(p) > 200R_k/T` and `y ∈ S₂` in the contributor window of the radius `Σρ ∘ A.rsel x₀`
(`Σ ≤ ε_c/10000`): the whole `k`-block of `y` vanishes and `A.plane y ≤ ker J_k`. -/
theorem EdgeStagePlanes_PLN.zero_block
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x y :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inr (.inl k)))) y = 0 ∧
      A.plane y ≤ LinearMap.ker ((blockProjCLM_PLN
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have hR := (P.zero.zero k.1 hk).radius_pos
  have hRT : 0 < (P.zero.zero k.1 hk).radius / T := div_pos hR hT
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, -, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hchain := zero_chain_PLN P.toLocalChartFamily P.zero hΔ hΛ hsmall 1 (A.rsel x₀) hsel hε hσε
    hpx hx hy hqy hmeet
  have hρp' : 200 * ((P.zero.zero k.1 hk).radius / T) < ρ p := by
    have : 200 * (P.zero.zero k.1 hk).radius / T = 200 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    linarith
  have hρq : 20 * (P.zero.zero k.1 hk).radius / T < ρ q := by
    have : 20 * (P.zero.zero k.1 hk).radius / T = 20 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    nlinarith
  have hsa := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a.1) (mem_ball.mp hqa)
    (by nlinarith : Λ * (100 * Δ) ≤ 1 / 4)
  have hρa : 80 / 3 * ((P.zero.zero k.1 hk).radius / T) < ρ a.1 := by nlinarith
  refine ⟨?_, ?_⟩
  · -- ZSP01's original zero block at the model preimage
    have hz := zsp01_original_zero_block P.toLocalChartPacketsR hT he hεr k hρq
    have hqy' : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        q = y := hqy
    rw [blockProjCLM_apply_PLN, ← hqy']
    change blockRestrict _ (cgpGlobalMap P.toLocalChartFamily P.zero q) _ = 0
    rw [blockRestrict_apply]
    split_ifs
    · exact hz
    · rfl
  -- `k` is absent from the actual zero list of `Φ_a`: the whole block vanishes
  have habs : k.1 ∉ zeroMeetingList P.zero a.1 (20 * Δ) := by
    rintro ⟨hk', z, hz, hza⟩
    exact zero_meet_absurd_PLN P.toLocalChartPacketsR hΛ hT he hεr hk' hz (mem_ball.mp hza)
      (by nlinarith) hρa
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord a q _ ?_
    (Eventually.of_forall fun u => ?_)
  · rw [A.prune_eq a, A.model_eq a]
    exact ((ContinuousLinearMap.id ℝ _).contDiff.comp
      (contDiff_egpModelGraph _ _ _ _ _)).differentiable (by simp) _
  · rw [A.prune_eq a, A.model_eq a]
    change egpModelComponent P.toLocalChartFamily P.zero a.1 (A.sgn a) (A.trans a)
      (.inr (.inr (.inr (.inl k)))) u = 0
    simp only [egpModelComponent, habs, ite_false]
    rfl

open Classical in
/-- **(ZB\*) at the slim stage**: for a zero tag `k`, a preimage `p` of `x ∈ S` with
`ρ(p) > 200R_k/T` and `y ∈ S` in the contributor window of the radius `Σρ ∘ A.rsel x₀`
(`Σ ≤ ε_c/10000`): the whole `k`-block of `y` vanishes and `A.plane y ≤ ker J_k`. -/
theorem SlimStagePlanes_PLN.zero_block
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x y :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    blockProjCLM_PLN (V
        := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) y = 0 ∧
      A.plane y ≤ LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have hR := (P.zero.zero k.1 hk).radius_pos
  have hRT : 0 < (P.zero.zero k.1 hk).radius / T := div_pos hR hT
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
      q = y := hqy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hchain := zero_chain_PLN P.toLocalChartFamily P.zero hΔ hΛ hsmall 2 (A.rsel x₀) hsel hε
    hσε hpx hx hy hqy' hmeet
  have hρp' : 200 * ((P.zero.zero k.1 hk).radius / T) < ρ p := by
    have : 200 * (P.zero.zero k.1 hk).radius / T = 200 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    linarith
  have hρq : 20 * (P.zero.zero k.1 hk).radius / T < ρ q := by
    have : 20 * (P.zero.zero k.1 hk).radius / T = 20 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    nlinarith
  have hsa := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a.1) (mem_ball.mp hqa)
    (by nlinarith : Λ * (10 ^ 6 * Δ) ≤ 1 / 4)
  have hρa : 80 / 3 * ((P.zero.zero k.1 hk).radius / T) < ρ a.1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have hz := zsp01_original_zero_block P.toLocalChartPacketsR hT he hεr k hρq
    rw [blockProjCLM_apply_PLN, ← hqy']
    change blockRestrict _ (cgpGlobalMap P.toLocalChartFamily P.zero q) _ = 0
    rw [blockRestrict_apply]
    split_ifs
    · exact hz
    · rfl
  have habs : ¬ sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) a.1 k.1
      ((Set.Finite.mem_toFinset _).mp k.2) := by
    rintro ⟨z, hz, hza⟩
    exact zero_meet_absurd_PLN P.toLocalChartPacketsR hΛ hT he hεr hk hz (mem_ball.mp hza)
      (by nlinarith) hρa
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord a q _ ?_
    (Eventually.of_forall fun u => ?_)
  · rw [A.prune_eq a, A.model_eq a]
    exact ((ContinuousLinearMap.id ℝ _).contDiff.comp
      (contDiff_sgpFullGraph _ _ _ _ _ _ _)).differentiable (by simp) _
  · rw [A.prune_eq a, A.model_eq a]
    change sgpZeroModelBlock P.toLocalChartFamily P.zero a (A.zsgn a) (A.ztrans a) k u = 0
    unfold sgpZeroModelBlock
    rw [ite_eq_right habs]

open Classical in
/-- **Whole small block, first stage** (CGP04): a marker block with `ρ(c) ≤ ρ(a)/2` is deleted by
`K_a`, so the WHOLE block of `K_a ∘ Φ_a` vanishes. -/
theorem FirstStagePlanes_PLN.small_block_zero
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg)
    (a : P.toLocalChartFamily.circle.finite_centres.toFinset)
        (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ ρ a.1 / 2) (u : ℝ²) :
    (A.prune a ∘ A.model a) u (cgpMarkerTag P.toLocalChartFamily P.zero c) = 0 := by
  rw [Function.comp_apply, A.prune_eq a, blockRestrict_apply,
    ite_eq_right (firstKeep_marker_GAF5 P.toLocalChartFamily P.zero c hc)]

/-- **Whole small block, first stage, plane form** (CGP04): if `ρ(c) ≤ ρ(a)/2` for the reference
`a = A.ref x`, then `A.plane x ≤ ker J_c` (`J_c` the projection onto the whole block of `c`). -/
theorem FirstStagePlanes_PLN.small_block_plane
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
        (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ ρ (A.ref ⟨x, hx⟩).1 / 2) :
    A.plane x ≤ LinearMap.ker ((blockProjCLM_PLN (V
        := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero c) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
                (ℝ² × ℝ)) :
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                        (ℝ² × ℝ)) := by
  rw [A.toStagePlaneData_PLN.plane_of_mem hx]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord _ _ _ ?_
    (Eventually.of_forall fun u => A.small_block_zero _ c hc u)
  refine (A.prune _).differentiableAt.comp _ ?_
  rw [A.model_eq]
  exact ((contDiff_tcpModelGraph _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _

/-- **Whole small block, edge stage** (CGP04): a marker block with `ρ(c) ≤ .99ρ(a)` is excluded by
EGP06's actual lists (or is a circle block), so the WHOLE block of `Φ_a` vanishes. -/
theorem EdgeStagePlanes_PLN.small_block_zero
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : P.toLocalChartFamily.edge.finite_centres.toFinset)
        (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ 99 / 100 * ρ a.1) (u : ℝ) :
    (A.prune a ∘ A.model a) u (cgpMarkerTag P.toLocalChartFamily P.zero c) = 0 := by
  classical
  have hra := hρ a.1
  rw [Function.comp_apply, A.prune_eq a, A.model_eq a]
  rcases c with j | j | j
  · rfl
  · have hS : j.1 ∉ egpSlimList P.toLocalChartFamily a.1 := by
      intro hS
      have h1 := egpSlimList_ratio_GAF4 P.toLocalChartFamily hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ a.1 at hc
      linarith
    change egpModelComponent P.toLocalChartFamily P.zero a.1 (A.sgn a) (A.trans a)
      (.inr (.inl j)) u = 0
    simp only [egpModelComponent, hS, ite_false]
    rfl
  · have hja : j.1 ≠ a.1 := by
      intro hja
      change ρ j.1 ≤ 99 / 100 * ρ a.1 at hc
      rw [hja] at hc
      linarith
    have hS : j.1 ∉ egpEdgeList P.toLocalChartFamily a.1 := by
      intro hS
      have h1 := egpEdgeList_ratio_GAF4 P.toLocalChartFamily hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ a.1 at hc
      linarith
    change egpModelComponent P.toLocalChartFamily P.zero a.1 (A.sgn a) (A.trans a)
      (.inr (.inr (.inl j))) u = 0
    simp only [egpModelComponent, hja, hS, ite_false]
    rfl

/-- **Whole small block, edge stage, plane form** (CGP04): `ρ(c) ≤ .99ρ(A.ref x)` ⇒
`A.plane x ≤ ker J_c`. -/
theorem EdgeStagePlanes_PLN.small_block_plane
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
        (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ 99 / 100 * ρ (A.ref ⟨x, hx⟩).1) :
    A.plane x ≤ LinearMap.ker ((blockProjCLM_PLN (V
        := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero c) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
                (ℝ² × ℝ)) :
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                        (ℝ² × ℝ)) := by
  rw [A.toStagePlaneData_PLN.plane_of_mem hx]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord _ _ _ ?_
    (Eventually.of_forall fun u => A.small_block_zero hΔ hΛ hLΛ _ c hc u)
  refine (A.prune _).differentiableAt.comp _ ?_
  rw [A.model_eq]
  exact ((contDiff_egpModelGraph _ _ _ _ _).differentiable (by simp)) _

/-- **Whole small block, slim stage** (CGP04): a marker block with `ρ(c) ≤ .99ρ(a)` is excluded by
SGP04's actual slim list (or is a circle / edge block), so the WHOLE block of `Φ_a` vanishes. -/
theorem SlimStagePlanes_PLN.small_block_zero
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : P.toLocalChartFamily.slim.finite_centres.toFinset)
        (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ 99 / 100 * ρ a.1) (u : ℝ) :
    (A.prune a ∘ A.model a) u (cgpMarkerTag P.toLocalChartFamily P.zero c) = 0 := by
  classical
  have hra := hρ a.1
  rw [Function.comp_apply, A.prune_eq a, A.model_eq a]
  rcases c with j | j | j
  · rfl
  · have hja : j ≠ a := by
      rintro rfl
      change ρ j.1 ≤ 99 / 100 * ρ j.1 at hc
      linarith
    have hS : j.1 ∉ sgpSlimList P.slim a.1 := by
      intro hS
      have h1 := (sgpSlimList_bounds P.toLocalChartFamily hΔ hΛ hLΛ hS).2.1
      have h2 := (lt_div_iff₀ hra).mp h1
      change ρ j.1 ≤ 99 / 100 * ρ a.1 at hc
      linarith
    change sgpSlimModelBlock P.toLocalChartFamily a (A.sgn a) (A.trans a) j u = 0
    unfold sgpSlimModelBlock
    rw [ite_eq_right hja, ite_eq_right hS]
  · rfl

/-- **Whole small block, slim stage, plane form** (CGP04): `ρ(c) ≤ .99ρ(A.ref x)` ⇒
`A.plane x ≤ ker J_c`. -/
theorem SlimStagePlanes_PLN.small_block_plane
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
        (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (c : CGPMarkerIndex P.toLocalChartFamily)
    (hc : ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ 99 / 100 * ρ (A.ref ⟨x, hx⟩).1) :
    A.plane x ≤ LinearMap.ker ((blockProjCLM_PLN (V
        := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero c) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
                (ℝ² × ℝ)) :
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                        (ℝ² × ℝ)) := by
  rw [A.toStagePlaneData_PLN.plane_of_mem hx]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord _ _ _ ?_
    (Eventually.of_forall fun u => A.small_block_zero hΔ hΛ hLΛ _ c hc u)
  refine (A.prune _).differentiableAt.comp _ ?_
  rw [A.model_eq]
  exact ((contDiff_sgpFullGraph _ _ _ _ _ _ _).differentiable (by simp)) _

end C14

end DifferentialGeometry.Geometry.Collapse
