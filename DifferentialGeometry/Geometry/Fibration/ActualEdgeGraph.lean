import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphPoint

/-!
# EGP06 (EG): the actual edge graph comparison on `LocalChartPacketsRVZ`

Blueprint `master207B.tex`, EGP06 (`thm:fibration-actual-edge-graph`, B:5088–5139): "Fix
`C† = 1000(N† + 2)(P† + 1)` before `Δ`. For `0 < e < 1/100` choose EGP04 with `θ < e/(10C†)`.
Then on `{|η_i| ≤ 8Δ, t ≤ 8Δ}`: `‖R_i⁻¹π₂F − Φ_iη_i‖_{C¹} < e`."

* `egp02ListBound_pos_KC4`, `egpGraphConst_pos_KC4`: `N† > 0`, `C† > 0` (early constants).
* `egp06_row` (frozen statement of sheet-C14-KC3.md, EGP06 G4): for `Δ ≥ 1`,
  `β₂ ∈ (0, 10⁻⁶)` and `0 < eg < 1/100` there are `Lc, η₀ > 0` such that on every actual
  `LocalChartPacketsRVZ` with the hypotheses of `egp04_row_RVZ` at `θ = eg/(20C†)`, at every edge
  centre `i` there are signs `|sgn_t| ≤ 1` and translations `c_t` with: on
  `B(i, 100Δρ_i) ∩ {|η_i| ≤ 8Δ, t ≤ 8Δ}`, `‖ρ_i⁻¹π₂𝓔⁰ − Φ_i(η_i)‖ < eg` and, on `ρ_i⁻²g`-unit
  vectors, `‖ρ_i⁻¹d(π₂𝓔⁰)(w) − DΦ_i(η_i)(dη_i(w))‖ < eg` (`Φ_i = egpModelGraph`).
  Strengthening: the blueprint's `θ < e/(10C†)` is met with `θ = e/(20C†)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- EGP02's list bound `N†` is positive (both multiplicity constants are volume ratios). -/
theorem egp02ListBound_pos_KC4 : 0 < egp02ListBound := by
  have hV : ∀ K r : ℝ, K < 0 → 0 < r → 0 < modelVolume K 3 r := fun K r hK hr =>
    modelVolume_pos (by norm_num) hr ⟨hr.le, fun h => absurd h (not_lt.mpr hK.le)⟩
  unfold egp02ListBound egp02EdgeCount egp02SlimCount
  exact add_pos (div_pos (hV _ _ (by norm_num) (by norm_num)) (hV _ _ (by norm_num) (by norm_num)))
    (div_pos (hV _ _ (by norm_num) (by norm_num)) (hV _ _ (by norm_num) (by norm_num)))

/-- EGP06's early constant `C†` is positive. -/
theorem egpGraphConst_pos_KC4 : 0 < egpGraphConst := by
  have h1 := egp02ListBound_pos_KC4
  have h2 := one_le_egpProfileConst
  unfold egpGraphConst
  have h3 : 0 < egp02ListBound + 2 := by linarith
  have h4 : 0 < egpProfileConst + 1 := by linarith
  positivity

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EGP06 (EG) on the actual family.** For `Δ ≥ 1`, `β₂ ∈ (0, 10⁻⁶)` and `0 < eg < 1/100`
there are ONE curvature radius `Lc` and ONE raw quality `η₀` such that on every actual
`LocalChartPacketsRVZ` with the hypotheses of `egp04_row_RVZ` at `θ = eg/(20C†)`, at every edge
centre `i` there are signs `|sgn_t| ≤ 1` and translations `c_t` such that the model
`Φ_i = egpModelGraph L Z i sgn c` satisfies, at every `x ∈ B(i, 100Δρ_i)` with `|η_i(x)| ≤ 8Δ`
and `t(x) ≤ 8Δ`: `‖ρ_i⁻¹π₂𝓔⁰(x) − Φ_i(η_i(x))‖ < eg` and
`‖ρ_i⁻¹d(π₂𝓔⁰)_x(w) − DΦ_i(η_i(x))(dη_i(w))‖ < eg` for every `ρ_i⁻²g`-unit vector `w`. -/
theorem egp06_row {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres,
          ∃ sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
            ∀ x ∈ ball i (100 * Δ * ρ i), |P.edge.coord i x| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
              ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) x -
                egpModelGraph P.toLocalChartFamily P.zero i sgn c (P.edge.coord i x)‖ < eg ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
                  fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ < eg := by
  have hC := egpGraphConst_pos_KC4
  have hθ0 : 0 < eg / (20 * egpGraphConst) := by positivity
  have hC1 : 1 ≤ egpGraphConst := by
    have h1 := egp02ListBound_pos_KC4
    have h2 := one_le_egpProfileConst
    unfold egpGraphConst
    have h3 : 2 ≤ egp02ListBound + 2 := by linarith
    have h4 : 2 ≤ egpProfileConst + 1 := by linarith
    nlinarith
  have hθ1 : eg / (20 * egpGraphConst) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨Lc, η₀, hLc, hη₀, h4⟩ := egp04_row_RVZ hΔ hβ₂ hβ₂1 hθ0 hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  obtain ⟨hE4, hS4, hZ4⟩ := h4 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz P hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  choose! aE haE using hE4
  choose! aS haS using hS4
  choose! aZ haZ using hZ4
  refine ⟨egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ,
    egpTagShift_KC4 P.toLocalChartFamily P.zero i,
    abs_egpTagSign_le_KC4 P.toLocalChartFamily P.zero aS aE aZ, ?_⟩
  intro x hx hη ht
  have hσc1 : σc ≤ 1 := by
    have h2 : (eg / (20 * egpGraphConst)) ^ 2 < 1 := by
      have := mul_lt_mul'' hθ1 hθ1 hθ0.le hθ0.le
      rw [one_mul] at this
      rwa [sq]
    linarith
  obtain ⟨hv, hd⟩ := egp06_point_KC4 P.toLocalChartPacketsR hΛ hΔ hLΛ hμ hτ he hT hσc1 hθ0
    hθ1.le hi aS aE aZ haE haS haZ hx hη ht
  have hfin : (egp02ListBound + 2) *
      (4 * (50 * (egpProfileConst + 1)) * (eg / (20 * egpGraphConst))) < eg := by
    have hN := egp02ListBound_pos_KC4
    have hP := one_le_egpProfileConst
    have hN2 : egp02ListBound + 2 ≠ 0 := by linarith
    have hP1 : egpProfileConst + 1 ≠ 0 := by linarith
    have he : (egp02ListBound + 2) *
        (4 * (50 * (egpProfileConst + 1)) * (eg / (20 * egpGraphConst))) = eg / 100 := by
      unfold egpGraphConst
      field_simp
      ring
    rw [he]
    linarith
  exact ⟨hv.trans_lt hfin, fun w hw => (hd w hw).trans_lt hfin⟩

end DifferentialGeometry.Geometry.Collapse
