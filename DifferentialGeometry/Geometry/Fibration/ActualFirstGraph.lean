import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphCentre
import DifferentialGeometry.Geometry.Fibration.ActualSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# TCP05: the actual first graph and its early modulus (the row)

Blueprint `master207B.tex`, TCP05 (`thm:fibration-actual-first-graph`, B:5518–5598): with
`C = tcpGraphConst` (fixed before `Δ` and noncollapse), for every early `0 < e < 1/100` the
permitted choices produce a smooth `Φ_i : ℝ² → H` with own block `(a, 1)`,
`‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` and `‖R_i⁻¹F − Φ_iη_i‖_{C¹} < e` on `{|η_i| ≤ 8}` (TG). "Choose
`θ < e/(100C²)` in TCP03–TCP04 and impose `ΔΛ < e/(1000C)` at the later scale choice."

`tcp05_row` is stated on THE chapter-14 family `LocalChartPacketsC14`; its hypotheses are exactly
those of TCP03 (circle / slim / edge / zero) and TCP04 at `θ = e/(100C²)` (one early `σ`, `η₂`,
`γ₀`, `η_c`, `θ`; for every `Δ ≥ 1200` one later `η₁`) and the scale budget `1000CΔΛ < e`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_TCP05_KA7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_TCP05_KA7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_TCP05_KA7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The choice `θ = e/(100C²)` is in `(0, 1)` for `0 < e < 1/100`. -/
theorem tcp05_theta_KA7 {eg : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    0 < eg / (100 * tcpGraphConst ^ 2) ∧ eg / (100 * tcpGraphConst ^ 2) < 1 := by
  have hC := one_le_tcpGraphConst
  have hC2 : 1 ≤ tcpGraphConst ^ 2 := one_le_pow₀ hC
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **TCP05** (`thm:fibration-actual-first-graph`, B:5518) on `LocalChartPacketsC14`: for an early
`0 < e < 1/100` (and the exclusion quality `ν`, `3ν ≤ β₃ < 1`) there are early `σ`, `η₂`, `γ₀`,
`η_c` and `θ < 1` (all before `Δ`) and for every `Δ ≥ 1200` a later `η₁`, such that with FC07's
ranges, TCP03's and TCP04's quality bounds at `θ` and `1000CΔΛ < e`, at every circle centre `i`
there is a smooth `Φ_i : ℝ² → H` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` (`C =
tcpGraphConst`, fixed before `Δ`) and (TG) on `{|η_i| ≤ 8} ∩ B(i, 200R_i)`:
`‖R_i⁻¹F − Φ_iη_i‖ < e` and `‖R_i⁻¹dF(w) − DΦ_i dη_i(w)‖ ≤ e|w|` (`|w|` of `R_i⁻²g`). -/
theorem tcp05_row {eg ν : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∀ i (hi : i ∈ P.circle.centres),
        ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
          ContDiff ℝ ∞ Φ ∧
          (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
            Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
          (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
          ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
            ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
                Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                  fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                    (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨hθ0, hθ1⟩ := tcp05_theta_KA7 heg heg1
  set θ := eg / (100 * tcpGraphConst ^ 2) with hθdef
  have hθ21 : θ ^ 2 / 1000 ≤ 1 := by
    have h1 : θ ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨σ1, hσ1, hσ11, η21, hη21, γ01, hγ01, hcirc⟩ := tcp03_circle_row hθ0 hθ1 hν hν1
  obtain ⟨σ2, hσ2, -, γ02, hγ02, hslim⟩ := tcp03_slim_row hθ0 hθ1 hν hν1
  obtain ⟨σ3, hσ3, -, γ03, hγ03, hedge⟩ := tcp03_edge_row hθ0 hθ1 hν hν1
  obtain ⟨σ4, hσ4, -, η24, hη24, γ04, hγ04, η14, hη14, hzero⟩ := tcp03_zero_row hθ0 hθ1 hν hν1
  obtain ⟨σ5, hσ5, -, η25, hη25, γ05, hγ05, ηc, hηc, hheight⟩ := tcp04_row hθ0 hθ1 hν hν1
  set σ := min σ1 (min σ2 (min σ3 (min σ4 σ5))) with hσdef
  have hσ0 : 0 < σ := lt_min hσ1 (lt_min hσ2 (lt_min hσ3 (lt_min hσ4 hσ5)))
  have hσle1 : σ ≤ σ1 := min_le_left _ _
  have hσle2 : σ ≤ σ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hσle3 : σ ≤ σ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσle4 : σ ≤ σ4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hσle5 : σ ≤ σ5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  set η₂ := min η21 (min η24 η25) with hη₂def
  set γ₀ := min γ01 (min γ02 (min γ03 (min γ04 γ05))) with hγ₀def
  refine ⟨σ, hσ0, hσle1.trans hσ11, η₂, γ₀, ηc, θ, lt_min hη21 (lt_min hη24 hη25),
    lt_min hγ01 (lt_min hγ02 (lt_min hγ03 (lt_min hγ04 hγ05))), hηc, hθ0, hθ1,
    fun Δ hΔ => ?_⟩
  obtain ⟨η12, hη12, hslimΔ⟩ := hslim Δ (by linarith)
  obtain ⟨η13, hη13, hedgeΔ⟩ := hedge Δ (by linarith)
  refine ⟨min η12 (min η13 η14), lt_min hη12 (lt_min hη13 hη14), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hμ hτ hLΛ hLmax he hT hε hε1 hσc0 hσcθ hμΔ hν3 hβ3 h3β2 hβ2 hγ hγc hγcγ hβc hb hβ1 hσs
    hσsθ hvs hζ hζθ hεr hΛz hσL hΔΛ i hi
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans (by norm_num) hΔ
  have hinv : ∀ σ' : ℝ, σ ≤ σ' → σ'⁻¹ ≤ Lmax := fun σ' h => (inv_anti₀ hσ0 h).trans hσL
  have hγ' : ∀ γ' : ℝ, γ₀ ≤ γ' → γ ≤ γ' := fun γ' h => hγ.trans h
  have hCrow := hcirc P.toLocalChartPackets hΛ hΔ1 hμ hτ hLΛ hLmax he hT hν3 hβ3
    (h3β2.trans hσle1) (hβ2.trans (min_le_left _ _))
    (hγ' _ (min_le_left _ _)) (hinv _ hσle1) i hi
  have hSrow := hslimΔ P.toLocalChartPacketsRVZ.toLocalChartPacketsRV hΛ hμ hτ hLΛ hLmax he hT hν3
    hβ3 (h3β2.trans hσle2) (hγ' _ ((min_le_right _ _).trans (min_le_left _ _)))
    (hβ1.trans (min_le_left _ _)) hσs hσsθ hvs (hinv _ hσle2) i hi
  have hErow := hedgeΔ P.toLocalChartPackets hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 (h3β2.trans hσle3)
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) hσcθ hμΔ (hinv _ hσle3) i hi
  have hZrow := hzero P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hΛ hΔ1 hLΛ he hT hν3 hβ3
    (h3β2.trans hσle4) (hβ2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
    (hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))) hζ hζθ hεr hΛz (hinv _ hσle4) i hi
  have hH := hheight P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hε hε1 hσc0
    (hσcθ.trans hθ21) hν3 hβ3 (h3β2.trans hσle5)
    (hβ2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
    hγc (hγcγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))) hβc (hinv _ hσle5) i hi
  exact tcp05_centre_KA7 P.toLocalChartPacketsR hΛ hΔ1
    hμ hτ hLΛ hLmax he hT heg hθ0 hθ1.le le_rfl hΔΛ hi
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hCrow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hSrow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hErow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun k hk hm => by
      obtain ⟨A, hA, -, hTC⟩ := hZrow k hk hm
      exact ⟨A, hA, hTC⟩)
    hH

end DifferentialGeometry.Geometry.Collapse
