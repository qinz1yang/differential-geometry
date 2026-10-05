import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCenterSplittingExclusion

/-!
# The zero raw alignment at circle and edge reference centres: suppliers of (TR0) and (ER0)

Blueprint `master207B.tex`, TCP02 (TR0) (B:5327–5333: "A meeting zero block has a unit row `A₀`
with `|d(p₀,x) − d(p₀,p_i) − A₀u_i(x)| < E` (`d(p_i,x) < 1000`)"; proof B:5362–5367) and EGP03
(ER0) (edge reference, `B(p_i, 600Δ)`), on `P : LocalChartPacketsZ`:

* `tcp02_zero_supplier_ZERO`: (TR0) at every circle centre `i` whose `D_i = B(i, 10ρ(i))` meets a
  zero support, with C14-KA3's pair kernel `tcp02_pair_KA3` (listed rank one = X82's zero
  splitting AT `p_i`, displacement `0`), the reference raw coordinate `circleRaw_KA3` and the
  threshold order of `tcp02_row` (an early `σ`, the zero quality bound `η₁` independent of `Δ`).
* `egp03_zero_supplier_ZERO`: (ER0) at every edge centre `i` whose `D_i = B(i, 20Δρ(i))` meets a
  zero support, with the generic `zero_raw_alignment_ZERO` (reference = the edge chart's
  `(1, b)`-splitting, raw coordinate `edgeRaw_KA3`, exclusion EGP01), in sign form on
  `B(i, 600Δρ(i))`, in the threshold order of EGP03 (`Lc`, `η₀` first).
* consumer: SGP02's (RA) (`sgp02_row`) and (R0) (`sgp02_zero_supplier_ZERO`) under ONE choice of
  thresholds on the same family (example).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ''_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ''_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ''_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `EuclideanSpace.single 0 t = (t)` in `ℝ¹`. -/
theorem single_zero_eq_toLp_const_ZERO (t : ℝ) :
    EuclideanSpace.single (0 : Fin 1) t = WithLp.toLp 2 (Function.const (Fin 1) t) := by
  ext a
  fin_cases a
  simp

/-- A Kleiner–Lott `ε`-map with real factor at `p` (scale `r`) has `|u(x)| ≤ H + 1` at every
`x` with `r⁻¹ d(x, p) < H`, when `ε (2(H+1)) ≤ 1`. -/
theorem abs_fst_le_of_kla_ZERO {X Y : Type} [mX : MetricSpace X] [MetricSpace Y] {r : ℝ}
    (hr : 0 < r) {p : X} {q : Y} {ε H : ℝ}
    (f : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p
      (WithLp.toLp 2 ((0 : ℝ), q)) ε)
    (hH : 0 ≤ H) (hε : ε * (2 * (H + 1)) ≤ 1) {x : X} (hx : r⁻¹ * dist x p < H) :
    |(@KleinerLottApprox.toFun X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f x).fst| ≤
      H + 1 := by
  have hε0 : 0 < ε := @KleinerLottApprox.error_pos X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f
  have hεinv : 2 * (H + 1) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hε0, ← one_div, le_div_iff₀ (by linarith)]
    linarith
  have hε1 : ε ≤ 1 := by nlinarith
  have hdist := @KleinerLottApprox.distortion X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f x
    (show r⁻¹ * dist x p < ε⁻¹ by linarith) p
    (show r⁻¹ * dist p p < ε⁻¹ by rw [dist_self, mul_zero]; positivity)
  rw [@KleinerLottApprox.basepoint X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f] at hdist
  change |dist (@KleinerLottApprox.toFun X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f x)
    (WithLp.toLp 2 ((0 : ℝ), q)) - r⁻¹ * dist x p| ≤ ε at hdist
  have hfst := WithLp.dist_fst_le
    (@KleinerLottApprox.toFun X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f x)
    (WithLp.toLp 2 ((0 : ℝ), q))
  rw [Real.dist_eq] at hfst
  change |(@KleinerLottApprox.toFun X _ (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ p _ ε f x).fst - 0|
    ≤ _ at hfst
  rw [sub_zero] at hfst
  linarith [(abs_le.mp hdist).2]

/-- **TCP02 (TR0) on the actual packets (supplier).** For a target error `E₀` and the exclusion
quality `ν` (`3ν ≤ β₃ < 1`) there are an early `σ` and a zero quality bound `η₁` (independent of
`Δ`) such that, with `3β₂ ≤ σ`, `β₁ ≤ η₁`, `σ⁻¹ ≤ Lmax` and the zero ranges (`T ≥ 1600L`,
`e < 1/40`, `LΛ < 10⁻⁵`): at every circle centre `i` whose `D_i = B(i, 10ρ(i))` meets the support
of the zero ball at `p₀ = k`, there is a unit row `A₀ : ℝ² → ℝ¹` with
`‖ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − A₀ u_i(x)‖ < E₀` on `B(i, 1000ρ(i))` (`u_i = circleRaw_KA3`). -/
theorem tcp02_zero_supplier_ZERO {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 1 ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] E1, A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x, dist x i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
              A₀ (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i
                x)‖ < E₀ := by
  obtain ⟨σ, hσ, hσ1, h1⟩ := tcp02_pair_KA3 hE hν hν1 (j := 1) le_rfl one_le_two
  obtain ⟨η, hη, hk1⟩ := h1 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ1 hσL i hi k hk hmeet
  have hri := hρ i
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hsec := tcp02_sectional_KA3 P' hσ (by linarith) hσL i
  have hno := circle_no_three_KA3 P.circle hi hν3 hβ3
  have hii : i ∈ ball i (10 * ρ i) := mem_ball_self (by positivity)
  obtain ⟨h1, h2, -⟩ := tcp01_zero_lc73_inputs_ZERO P.toLocalChartPacketsR hΛ hΔ hLΛ he hT
    (Λz := 0) (by linarith) i hk hmeet i hii
  obtain ⟨Zf, mZ, z, F, hF⟩ := P.zero_shell_split k hk i h1 h2
  let Ai := P'.circleAdapted i hi
  have hc12 : (1 / 2 : ℝ) ≤ ρ i / ρ i := by rw [div_self hri.ne']; norm_num
  have hc2 : ρ i / ρ i ≤ 2 := by rw [div_self hri.ne']; norm_num
  have hd : dist i i ≤ 0 * ρ i := by rw [dist_self, zero_mul]
  obtain ⟨A₀, hA₀, hal⟩ := @hk1 X mX _ _ _ g hmetric i i (ρ i) (ρ i) hri hri hc12 hc2 hd hsec
    hno Zf Ai.Y mZ Ai.instY z Ai.a (β 1) (β 2) hβ1 hβ2σ F Ai.split
  refine ⟨A₀, hA₀, fun x hx => ?_⟩
  have hmain := hal x hx
  rw [hF x, hF i, sub_self, mul_zero, div_self hri.ne', one_smul, one_smul] at hmain
  have hz : WithLp.toLp 2 (Function.const (Fin 1) (0 : ℝ)) = (0 : E1) := rfl
  rw [hz, sub_zero] at hmain
  rw [circleRaw_KA3_eq P' hi, single_zero_eq_toLp_const_ZERO]
  exact hmain

/-- **EGP03 (ER0) on the actual packets (supplier).** Fix `Δ ≥ 1`, the edge exclusion quality
`ν < 10⁻⁶` and `E > 0`. There are a curvature radius `Lc` and a raw quality `η₀` such that for
EVERY actual family `P : LocalChartPacketsZ` with `b, β₁ ≤ η₀`, `s < 10⁻⁶`, `Lc ≤ Lmax`,
`LΛ < 10⁻⁵`, `e < 1/40` and `T ≥ 1600L`: at every edge centre `i` whose `D_i = B(i, 20Δρ(i))`
meets the support of the zero ball at `p₀ = k`, there is a sign `a₀` with
`|ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − a₀ u_i(x)| < E` on `B(i, 600Δρ(i))` (`u_i = edgeRaw_KA3`). -/
theorem egp03_zero_supplier_ZERO {Δ ν E : ℝ} (hΔ : 1 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.edge.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (600 * Δ * ρ i),
            |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * edgeRaw_KA3 P.toLocalChartFamily i x| < E := by
  set H : ℝ := 600 * Δ with hH
  set τz : ℝ := min (E / 100) (1 / (2 * (H + 1))) with hτz
  obtain ⟨hτ0, hτ1, ha0, ha, ha2, hτE, hHτ⟩ :=
    zero_alignment_parameters_ZERO (by rw [hH]; linarith) hE hτz
  obtain ⟨σ, η, hσ, hσ1, hη, hsupp⟩ :=
    zero_raw_alignment_ZERO (k := 1) le_rfl (by norm_num) hτ0 hτ1 hν (by linarith) ha0 ha ha2
  have hH1 : 0 < 1 / (2 * (H + 1)) := by positivity
  refine ⟨σ⁻¹, min η (min (σ / 3) (min (1 / (2 * (H + 1))) (1 / 10000000))), inv_pos.mpr hσ,
    lt_min hη (lt_min (by positivity) (lt_min hH1 (by norm_num))), ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hb hs hβ1 hLc hΛ hLΛ he hT i hi k hk hmeet
  have hri := hρ i
  have hbσ : 3 * b ≤ σ := by
    have := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hbH0 : b ≤ 1 / (2 * (H + 1)) :=
    hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbH : b * (2 * (H + 1)) ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hbH0
    linarith
  have hb6 : b < 1 / 1000000 := by
    have := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hβη : β 1 ≤ η := hβ1.trans (min_le_left _ _)
  -- the zero shell at `i` (EGP02's reference ball)
  have hii : i ∈ ball i (20 * Δ * ρ i) := mem_ball_self (by have := hρ i; positivity)
  obtain ⟨h1, h2, -⟩ := egp02_zero_lc73_inputs_ZERO P.toLocalChartPacketsR hΛ hΔ hLΛ he hT
    (Λz := 0) (by linarith) i hk hmeet i hii
  -- EGP01: no normalized `(2, ν)`-splitting at the edge centre
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i 2 ν :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i Δ b s ν (P.edge.strong i hi) hb6 hs hν1
  -- the edge reference splitting, with target `ℝ¹ × Y`
  obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KA3 P.toLocalChartFamily hi
  let ψ := @KleinerLottApprox.mapTargetIsometryAt X (WithLp 2 (ℝ × Y)) (WithLp 2 (E1 × Y))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ i (WithLp.toLp 2 ((0 : ℝ), q)) b f
    (realProdIso_SGP Y) (WithLp.toLp 2 ((0 : E1), q)) (realProdIso_SGP_zero q)
  obtain ⟨A₀, hA₀, hal⟩ := hsupp X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V ζ Λz P hLc hβη i k hk h1 h2 hno Y q hbσ ψ
  obtain ⟨a₀, ha₀, hlin⟩ := coisometry_fin_one_SGP A₀ hA₀
  refine ⟨a₀, ha₀, fun x hx => ?_⟩
  have hxR : (ρ i)⁻¹ * dist x i < H := by
    rw [inv_mul_lt_iff₀ hri]
    have : dist x i < 600 * Δ * ρ i := hx
    rw [hH]
    linarith
  have hui := abs_fst_le_of_kla_ZERO hri f (by rw [hH]; linarith) hbH hxR
  rw [hf x] at hui
  have hψx : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b
      ψ x).fst = realFinOneIso_SGP (edgeRaw_KA3 P.toLocalChartFamily i x) := by
    rw [← hf x]
    rfl
  have hnorm : ‖(@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b
      ψ x).fst‖ ≤ H + 1 := by
    rw [hψx, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hui
  have hmain := hal x (hxR.trans hHτ) hnorm
  rw [hψx, hlin, toLp_const_eq_realFinOneIso_ZERO, ← map_sub, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs] at hmain
  exact hmain.trans_lt hτE

/-- Consumer: SGP02's (RA) (`sgp02_row`) and (R0) (`sgp02_zero_supplier_ZERO`) under ONE choice of
thresholds `Lc`, `η₀`, on the same actual family `P : LocalChartPacketsZ`. -/
example {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.slim.centres,
          (∀ j ∈ sgpSlimList P.slim i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |ρ j / ρ i * sgpRaw P.slim j x - a * sgpRaw P.slim i x -
                ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
          ∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E := by
  obtain ⟨L₁, η₁, hL₁, hη₁, hRA⟩ := sgp02_row hΔ hβ₂ hβ₂1 hE
  obtain ⟨L₂, η₂, hL₂, hη₂, hR0⟩ := sgp02_zero_supplier_ZERO hΔ hβ₂ hβ₂1 hE
  refine ⟨max L₁ L₂, min η₁ η₂, lt_max_of_lt_left hL₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hβ2 hβ1 hLc hΛ hLΛ he hT i hi
  let Q := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets.toLocalChartFamilyE
  refine ⟨hRA X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax Q.toLocalChartFamilyQ
    hβ2 (hβ1.trans (min_le_left _ _)) ((le_max_left _ _).trans hLc) hΛ hLΛ i hi, ?_⟩
  exact hR0 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hβ2
    (hβ1.trans (min_le_right _ _)) ((le_max_right _ _).trans hLc) hΛ hLΛ he hT i hi

end DifferentialGeometry.Geometry.Collapse
