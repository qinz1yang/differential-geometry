import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Fibration.ActualSlimCloud

/-!
# FC27's slim test: SGP06's planes inside `Q₃`, in the stage notation of GAF01/GAF02

Blueprint `master207B.tex`, FC27 (`found:fibration-projected-clouds`, B:1658, the slim case
from SGP06, B:4711) in the frozen form of `sheet-C14-GAF2.md` (stage `st = 2`, `k = 1`) with the
amendment `plane x ≤ Q₃` (needed for GAF02's `P_j = π_{Q_j} ∘ p_j`).

* `sgpFullGraph_blockRestrict_GAF3`: SGP04's full model graph `Φ_i` is `Q₃`-valued
  (`π_{Q₃} ∘ Φ_i = Φ_i`: only slim and zero blocks are nonzero).
* `range_fderiv_sgpFullGraph_le_GAF3`: hence every plane `im DΦ_i(a)` lies in `Q₃ = gafStageQ 2`.
* `fc27_slim_test_GAF3`: on `LocalChartPacketsRVZ` under SGP06's hypotheses (verbatim), planes
  over `S₃ = gafCloud 2` with dimension `gafStageDim 2 = 1`, inside `gafStageQ 2`, with the (CS)
  test of CFS15 / FC27 at quality `Γ` and radius `Σρ(sel x)` for EVERY selection over
  `S̃₃ = gafCloudEnlarged 2`, and SGP05's rank conclusion for the same planes (consumed by
  GAF02's normal error).
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

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- SGP04's full model graph is `Q₃`-valued: `π_{Q₃}(Φ_i(u)) = Φ_i(u)`. -/
theorem sgpFullGraph_blockRestrict_GAF3 (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (u : ℝ) :
    blockRestrict (cgpQ3Tags L Z) (sgpFullGraph L Z i sgn c zsgn zc u) =
      sgpFullGraph L Z i sgn c zsgn zc u := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · rw [sgpFullGraph_apply]
    rcases t with j | j | j | j | j
    · rfl
    · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
    · rfl
    · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
    · rfl

/-- Every plane `im DΦ_i(a)` of SGP04's full model graph lies in `Q₃ = gafStageQ 2`. -/
theorem range_fderiv_sgpFullGraph_le_GAF3 (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (a : ℝ) :
    (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a).range ≤ gafStageQ L Z 2 := by
  classical
  exact range_fderiv_le_range_blockRestrict_GAF3 _ _ (sgpFullGraph_blockRestrict_GAF3 L Z i sgn c
    zsgn zc) a

end Model

section Row

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27, the slim test** (stage `2` of GAF01/GAF02; SGP06 with the planes inside `Q₃`). For
`0 < Γ < 1` and (CP) `0 < Σ < min(Γ/200, Γ³/(100C_*))`, `0 < e < min(1/100, ΓΣ/100)` there are
SGP04/SGP05's thresholds such that on every actual RVZ family with their hypotheses there are planes
`plane x` over `S₃ = gafCloud 2` (SGP05's `im DΦ_i(η_i p)` at a core witness) with
(1) `dim plane x = gafStageDim 2` and `plane x ≤ gafStageQ 2 = Q₃`; (2) for ANY selection of
preimages over `S̃₃ = gafCloudEnlarged 2`, the (CS) test at quality `Γ`, radius `r = Σρ(sel x)`:
`hausdorffEDist (S̃₃ ∩ B(x, r/Γ)) ((x + plane x) ∩ B(x, r/Γ)) ≤ Γr`; (3) SGP05's rank conclusion for
`plane x` at every preimage of `x` (as in `sgp06_row`). -/
theorem fc27_slim_test_GAF3 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            Module.finrank ℝ (plane x) = gafStageDim 2 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp05_row hΔ hβ₂ hβ₂1 heg heg1
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hrowP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ2 hβ1 hLmax hΛ hLΛ he hT
    hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hσ1 : σs < 1 / 100 := hσθ.trans hθ2
  have hpt : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (Module.finrank ℝ W = gafStageDim 2 ∧ W ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
              ball x (sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x W :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
        ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          x →
        let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
    intro x hx
    have hx' : x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7 := hx
    obtain ⟨p, ⟨i, hp, hηp⟩, rfl⟩ := hx'
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have hηp' : |(P.slim.centre i.1 hi).coord p| ≤ 7 * (10 ^ 5 * Δ) := by
      rw [← mul_assoc]
      exact hηp
    have hrowi := hrowP i
    obtain ⟨sgn, c, zsgn, zc, hsgn, hzsgn, hSG, hrk⟩ := hrowi
    have hs01 := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs.le hσ1.le hi
    obtain ⟨-, -, -, huniq, hzero01, -⟩ := hs01
    have hs0 : ∀ k (hk : k ∈ P.zero.centres),
        sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk → 1 ≤ (P.zero.zero k hk).radius / ρ i.1 :=
      fun k hk hm => (one_le_div_twenty_SGP4 hΔ hT).trans (hzero01 k hk hm).1
    have hpoint := sgp06_point_SGP5 P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn c zsgn zc hsgn
      hzsgn hs0 huniq hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ (fun y hy hyη => (hSG y hy hyη).1) hp hηp'
    obtain ⟨hfin, hcl⟩ := hpoint
    have hQ := range_fderiv_sgpFullGraph_le_GAF3 P.toLocalChartFamily P.zero i sgn c zsgn zc
      ((P.slim.centre i.1 hi).coord p)
    exact ⟨_, ⟨hfin, hQ⟩, hcl, i, hrk p hp hηp'⟩
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun sel hsel x hx =>
    (hplane x hx).2.1 sel hsel, fun x hx => (hplane x hx).2.2⟩

end Row

end DifferentialGeometry.Geometry.Collapse
