import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsZeroApplications

/-!
# The zero raw alignment on the actual packets: suppliers of (R0), (TR0), (ER0)

Blueprint `master207B.tex`: SGP02 (R0) (B:4428–4432, proof B:4473–4480), TCP02 (TR0)
(B:5327–5333, proof B:5362–5367), EGP03 (ER0): a meeting zero block has a unit row `A₀` with
`|d(p₀, x) − d(p₀, p_i) − A₀ u_i(x)| < E` on a fixed reference ball (distances in `R_i` units).
"LC73/LCP04 give an actual `(1, β₁)`-splitting there whose real coordinate is EXACTLY
`d(p₀,·) − d(p₀,p_i)` in reference units. Apply the same AC76/FC20 argument to it and `u_i`."

On `P : LocalChartPacketsZ` (LC87 with LC73's zero shell clauses, C14-ZERO G2):

* `zero_raw_alignment_ZERO` (generic reference, rank `k ≤ 3`): X125's
  `exists_scaled_raw_coisometry_parameter_riemannian` with listed rank one, applied to X82's zero
  splitting AT the reference point `p` (displacement `0`, ratio `ρ(p)/ρ(p)`) and to ANY reference
  `ε₂`-splitting `ψ` of `(X, ρ(p)⁻¹ d, p)` of rank `k` with no `(k+1, ν)`-splitting at `p`: the
  curvature comes from LPA01's buffer (`σ⁻¹ ≤ Lmax`); the conclusion is one coisometry
  `A₀ : ℝᵏ → ℝ¹` with `‖ρ(p)⁻¹ (d(c, x) − d(c, p)) − A₀ (ψ x).fst‖ ≤ 50τ` on
  `ρ(p)⁻¹ d(x, p) < τ⁻¹`, `‖(ψ x).fst‖ ≤ a`, whenever `p` lies in the closed shell of the zero
  ball at `c`.
* `sgp02_zero_supplier_ZERO`: SGP02's (R0) at every slim centre `i` whose `D_i` meets a zero
  support, in the threshold order of `sgp02_row` (`Lc`, `η₀` first, then every actual family):
  a sign `a₀` with `|ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − a₀ u_i(x)| < E` on `B(i, 30Lρ(i))`
  (`u_i = sgpRaw`).
* `toLp_const_eq_realFinOneIso_ZERO`: `ℝ¹` coordinates of the exact radial coordinate.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ'_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ'_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ'_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The exact radial coordinate as an element of `ℝ¹`. -/
theorem toLp_const_eq_realFinOneIso_ZERO (t : ℝ) :
    WithLp.toLp 2 (Function.const (Fin 1) t) = realFinOneIso_SGP t := by
  ext a
  change t = (OrthonormalBasis.singleton (Fin 1) ℝ).repr t a
  rw [OrthonormalBasis.singleton_repr]

/-- **The zero raw alignment at a reference point (generic reference splitting).** For a
reference rank `1 ≤ k ≤ 3`, an accuracy `τ` and an exclusion quality `ν` there are an early `σ`
(asked of the curvature buffer and of the reference quality) and a raw quality `η` such that on
every actual family `P : LocalChartPacketsZ` with `σ⁻¹ ≤ Lmax` and `β₁ ≤ η`: at a point `p` of the
closed shell of the zero ball at `c`, with no `(k+1, ν)`-splitting at `p` in `ρ(p)⁻¹ d`, every
reference `ε₂`-splitting `ψ` of rank `k` at `p` (`3ε₂ ≤ σ`) has one coisometry `A₀ : ℝᵏ → ℝ¹`
with `‖ρ(p)⁻¹ (d(c, x) − d(c, p)) − A₀ (ψ x).fst‖ ≤ 50τ` on `ρ(p)⁻¹ d(x, p) < τ⁻¹`
where `‖(ψ x).fst‖ ≤ a`. -/
theorem zero_raw_alignment_ZERO {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) {τz ν a : ℝ}
    (hτ : 0 < τz) (hτ1 : τz < 1) (hν : 0 < ν) (hν1 : ν < 1) (ha0 : 0 < a)
    (ha : 20 * τz ≤ a) (ha2 : 2 * a ≤ τz⁻¹) :
    ∃ σ η : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < η ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        σ⁻¹ ≤ Lmax → β 1 ≤ η →
        ∀ (p c : X) (hc : c ∈ P.zero.centres), (P.zero.zero c hc).radius / 10 ≤ dist c p →
          dist c p ≤ 10 * (P.zero.zero c hc).radius →
          ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (k + 1)
            ν →
          ∀ (B : Type) [MetricSpace B] (b₀ : B) {ε₂ : ℝ}, 3 * ε₂ ≤ σ →
          ∀ ψ : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
              (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (0, b₀)) ε₂,
          ∃ A₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] E1,
            A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, (ρ p)⁻¹ * dist x p < τz⁻¹ →
              ‖(@KleinerLottApprox.toFun X _ (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ _ _ _
                ψ x).fst‖ ≤ a →
              ‖WithLp.toLp 2 (Function.const (Fin 1) ((ρ p)⁻¹ * (dist c x - dist c p))) -
                A₀ (@KleinerLottApprox.toFun X _ (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ _ _ _
                  ψ x).fst‖ ≤ 50 * τz := by
  have hkn : k ≤ Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; exact hk3
  obtain ⟨σ, hσ, hσ1, hprop⟩ := exists_scaled_raw_coisometry_parameter_riemannian.{0}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) (j := 1) (k := k) le_rfl hk hkn hτ hτ1 hν hν1
    ha0 (by push_cast; linarith) ha2
  obtain ⟨η, hη, hprop⟩ := hprop 0 le_rfl
  refine ⟨σ, η, hσ, hσ1, hη, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hLc hβ1 p c hc h1 h2 hno B _ b₀ ε₂ hε₂ ψ
  have hrp := hρ p
  -- the reference metric `ρ(p)⁻¹ d` and its tensor `ρ(p)⁻² g`
  have hmR := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hrp
  set gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrp) 2) g with hgR
  have hsecR : ∀ y, (ρ p)⁻¹ * dist y p < σ⁻¹ → SectionalBoundedBelowAt gR y (-σ) := by
    intro y hy
    have hy' : y ∈ ball p (σ⁻¹ * ρ p) := by
      rw [mem_ball]
      rw [inv_mul_lt_iff₀ hrp] at hy
      linarith
    have hbuf := P.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hLc p y hy'
    rw [hgR, sectionalBoundedBelowAt_scaleMetric_iff]
    refine hbuf.mono ?_
    have hσ2 : σ ^ 2 ≤ σ := by nlinarith
    have he : -((σ⁻¹ * ρ p) ^ 2)⁻¹ = -(σ ^ 2 * (ρ p)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rw [he]
    have hr2 : 0 ≤ (ρ p)⁻¹ ^ 2 := by positivity
    nlinarith
  -- X82's zero splitting at `p`, read in the reference metric with ratio `ρ(p)/ρ(p)`
  obtain ⟨Zf, mZ, z, F, hF⟩ := P.zero_shell_split c hc p h1 h2
  have hc1 : 0 < ρ p / ρ p := div_pos hrp hrp
  have hmetq : mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp) =
      (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).rescale (ρ p / ρ p)⁻¹ (inv_pos.mpr hc1) :=
    (MetricSpace.rescale_inv_ratio mX hrp hrp).symm
  obtain ⟨φ, hφ⟩ := exists_kleinerLott_of_metric_eq_SGP hmetq F
  have hcpt :
      @CompactSpace X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).toUniformSpace.toTopologicalSpace :=
    MetricSpace.rescale_compactSpace mX _ _
  have hcomp : @CompleteSpace X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).toUniformSpace :=
    (mX.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hrp)).mpr complete_of_compact
  have hsig : @SigmaCompactSpace X
      (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).toUniformSpace.toTopologicalSpace :=
    @CompactSpace.sigmaCompact X _ hcpt
  have hc12 : (1 / 2 : ℝ) ≤ ρ p / ρ p := by rw [div_self hrp.ne']; norm_num
  have hc2 : ρ p / ρ p ≤ 2 := by rw [div_self hrp.ne']; norm_num
  have hpp : @dist X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).toDist p p ≤ 0 := by
    change (ρ p)⁻¹ * dist p p ≤ 0
    rw [dist_self, mul_zero]
  obtain ⟨A₀, hA₀, hal⟩ := @hprop X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)) _ _ hsig hcomp gR hmR
    p (fun y hy => hsecR y hy) hno Zf B mZ _ z b₀ p (β 1) ε₂ (ρ p / ρ p) hc1 hc12 hc2 hpp hβ1
    hε₂ φ ψ
  refine ⟨A₀, hA₀, fun x hx hxa => ?_⟩
  have hraw : ∀ y, (@KleinerLottApprox.toFun X _
      ((mX.rescale (ρ p)⁻¹ (inv_pos.mpr hrp)).rescale (ρ p / ρ p)⁻¹ (inv_pos.mpr hc1)) _ p _
        (β 1) φ y).fst =
      WithLp.toLp 2 (Function.const (Fin 1) ((ρ p)⁻¹ * (dist c y - dist c p))) := by
    intro y
    rw [hφ]
    exact hF y
  have hmain := hal x hx hxa
  rw [hraw x, hraw p, sub_self, mul_zero, div_self hrp.ne', one_smul, one_smul] at hmain
  have hz : WithLp.toLp 2 (Function.const (Fin 1) (0 : ℝ)) = (0 : E1) := rfl
  rw [hz, sub_zero] at hmain
  exact hmain.trans_eq (by push_cast; ring)

/-- The parameters of a zero alignment on a reference ball of radius `H ≥ 3` (`a = H + 1`): the
accuracy `τ = min (E/100) (1/(2(H+1)))` satisfies X125's constraints and `50τ < E`. -/
theorem zero_alignment_parameters_ZERO {E H τz : ℝ} (hH : 3 ≤ H) (hE : 0 < E)
    (hτ : τz = min (E / 100) (1 / (2 * (H + 1)))) :
    0 < τz ∧ τz < 1 ∧ 0 < H + 1 ∧ 20 * τz ≤ H + 1 ∧ 2 * (H + 1) ≤ τz⁻¹ ∧
      50 * τz < E ∧ H < τz⁻¹ := by
  have hH1 : 0 < 2 * (H + 1) := by linarith
  have hτ0 : 0 < τz := by rw [hτ]; exact lt_min (by positivity) (by positivity)
  have hτ1 : τz ≤ 1 / (2 * (H + 1)) := by rw [hτ]; exact min_le_right _ _
  have hτE : τz ≤ E / 100 := by rw [hτ]; exact min_le_left _ _
  have hinv : 2 * (H + 1) ≤ τz⁻¹ := by
    rw [le_inv_comm₀ hH1 hτ0]
    simpa only [one_div] using hτ1
  have hτ8 : τz * (2 * (H + 1)) ≤ 1 := by
    rw [le_div_iff₀ hH1] at hτ1
    linarith
  refine ⟨hτ0, by nlinarith, by linarith, by nlinarith, hinv, by linarith, by linarith⟩

/-- **SGP02 (R0) on the actual packets (supplier).** Fix `Δ ≥ 1`, the exclusion quality `β₂` and
`E > 0`. There are a curvature radius `Lc` (asked of LPA01's buffer) and a raw quality `η₀` such
that for EVERY actual family `P : LocalChartPacketsZ` with `β 2 = β₂`, `β 1 ≤ η₀`, `Lc ≤ Lmax`,
`10⁶ΔΛ < 10⁻⁵`, `e < 1/40` and `T ≥ 1600L`: at every slim centre `i` whose `D_i = B(i, .95Lρ(i))`
meets the support of the zero ball at `p₀ = k`, there is a sign `a₀` with
`|ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − a₀ u_i(x)| < E` on `B(i, 30Lρ(i))` (`u_i = sgpRaw`). -/
theorem sgp02_zero_supplier_ZERO {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hE : 0 < E) :
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
        ∀ i ∈ P.slim.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
            |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E := by
  set H : ℝ := 30 * (1000000 * Δ) with hH
  set τz : ℝ := min (E / 100) (1 / (2 * (H + 1))) with hτz
  obtain ⟨hτ0, hτ1, ha0, ha, ha2, hτE, hHτ⟩ :=
    zero_alignment_parameters_ZERO (by rw [hH]; nlinarith) hE hτz
  obtain ⟨σ, η, hσ, hσ1, hη, hsupp⟩ :=
    zero_raw_alignment_ZERO (k := 1) le_rfl (by norm_num) hτ0 hτ1 hβ₂ hβ₂1 ha0 ha ha2
  have hH1 : 0 < 1 / (2 * (H + 1)) := by positivity
  refine ⟨σ⁻¹, min η (min (σ / 3) (1 / (2 * (H + 1)))), inv_pos.mpr hσ,
    lt_min hη (lt_min (by positivity) hH1), ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hβ2 hβ1 hLc hΛ hLΛ he hT i hi k hk hmeet
  have hri := hρ i
  have hβη : β 1 ≤ η := hβ1.trans (min_le_left _ _)
  have hβσ : 3 * β 1 ≤ σ := by
    have := hβ1.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hβH : β 1 ≤ 1 / (2 * (H + 1)) :=
    hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- SGP01's zero clause puts `i` in the closed shell of the zero ball at `k`
  have hii : i ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i) :=
    mem_ball_self (by have := hρ i; positivity)
  obtain ⟨-, -, h1, h2, -⟩ :=
    ((sgp01_zero_clauses P.toLocalChartPacketsR hΛ hΔ hLΛ he hT i).2 k hk hmeet).2.1 i hii
  -- the exclusion of the slim stratum
  have hstrat := (P.slim.centres_subset hi).1
  have hrank := (scaledSplittingRank_eq_iff.mp hstrat).2.2 2 (by norm_num) (by norm_num)
  rw [hβ2] at hrank
  -- the reference splitting with target `ℝ¹ × Z_i`
  let Si := P.slim.centre i hi
  let _ := Si.instZ
  let ψ := @KleinerLottApprox.mapTargetIsometryAt X (WithLp 2 (ℝ × Si.Z)) (WithLp 2 (E1 × Si.Z))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ i (WithLp.toLp 2 ((0 : ℝ), Si.z)) (β 1) Si.split
    (realProdIso_SGP Si.Z) (WithLp.toLp 2 ((0 : E1), Si.z)) (realProdIso_SGP_zero Si.z)
  obtain ⟨A₀, hA₀, hal⟩ := hsupp X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V ζ Λz P hLc hβη i k hk h1 h2 hrank Si.Z Si.z hβσ ψ
  obtain ⟨a₀, ha₀, hlin⟩ := coisometry_fin_one_SGP A₀ hA₀
  refine ⟨a₀, ha₀, fun x hx => ?_⟩
  have hxR : (ρ i)⁻¹ * dist x i < H := by
    rw [inv_mul_lt_iff₀ hri]
    have : dist x i < 30 * (1000000 * Δ) * ρ i := hx
    rw [hH]
    linarith
  have hb0 : 0 < β 1 := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Si.Z))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1) Si.split
  have hβinv : 2 * (H + 1) ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hb0]
    simpa only [one_div] using hβH
  -- `|u_i(x)| ≤ H + 1`
  have hui : |sgpRaw P.slim i x| ≤ H + 1 := by
    rw [sgpRaw_of_mem P.slim hi]
    have hdist := @KleinerLottApprox.distortion X (WithLp 2 (ℝ × Si.Z))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1) Si.split x
      (show (ρ i)⁻¹ * dist x i < (β 1)⁻¹ by linarith) i
      (show (ρ i)⁻¹ * dist i i < (β 1)⁻¹ by rw [dist_self, mul_zero]; positivity)
    change |dist (sgpSplitMap Si x) (sgpSplitMap Si i) - (ρ i)⁻¹ * dist x i| ≤ β 1 at hdist
    rw [sgpSplitMap_center] at hdist
    have hfst := WithLp.dist_fst_le (sgpSplitMap Si x) (WithLp.toLp 2 ((0 : ℝ), Si.z))
    rw [Real.dist_eq] at hfst
    change |(sgpSplitMap Si x).fst - 0| ≤ _ at hfst
    rw [sub_zero] at hfst
    have hb1 : β 1 ≤ 1 := by
      have : 1 / (2 * (H + 1)) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    linarith [(abs_le.mp hdist).2]
  have hψx : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1)
      ψ x).fst = realFinOneIso_SGP (sgpRaw P.slim i x) := by
    rw [sgpRaw_of_mem P.slim hi]
    rfl
  have hnorm : ‖(@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ (β 1)
      ψ x).fst‖ ≤ H + 1 := by
    rw [hψx, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hui
  have hmain := hal x (hxR.trans hHτ) hnorm
  rw [hψx, hlin, toLp_const_eq_realFinOneIso_ZERO, ← map_sub, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs] at hmain
  exact hmain.trans_lt hτE

end DifferentialGeometry.Geometry.Collapse
