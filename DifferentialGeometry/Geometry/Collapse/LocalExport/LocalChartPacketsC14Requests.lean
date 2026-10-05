import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Producer

/-!
# The chapter-14 requests on the chapter-13 parameters, and ONE admissible assignment

Lane C14-FAM, registers R14 / R15 / R20 of external review 48 (design
`build-logs/resume/design-C14-FAM.md` (g)): chapter 14's rows state numerical side conditions on the
parameters of the ONE final family (`vs < θ/100`, `σs < θ²/10⁶`, `εr < θ/(100L)`, `γ + β₂ ≤ γ_T/10`,
`T ≥ 1600L`, `Lmax ≥ 400V`, the scale minima of (RegScale), …). They are satisfiable at once
because each one sits on a FREE binder of `eventually_nonempty_localChartPacketsC14` standing after
everything it depends on (blueprint 207B, PBR01, B:10067–10265: "All parameter requirements …
admit one assignment"; order `β₂ → Δ`, `w → b → β₁`, joint zero output last).

* `C14Requests`: the record of all requests, in the producer's order: upper requests on the early
  binders `γ, γc, β₂` and a lower request on `Δ`; upper requests on `σc ε μ τ s b' s' Λ b σs vs β₁ ζ
  cap e` and a lower request on `T` as functions of the earlier `(β₂, Δ)`; a lower request on `Lmax`
  as a function of `(β₂, Δ, V)` (`V` is the joint zero output, `Lmax` is bound after it).
* `C14Assignment Rq`: one assignment of all free parameters with every request of `Rq` and the
  producer's numerical guarantees.
* `exists_c14_assignment`: for every `Rq` there is ONE assignment `A` such that, for every standing
  sequence, with the joint zero output `V` and `Lmax := max 1 (Rq.Lmax β₂ Δ V)`, every late member
  carries the final family `LocalChartPacketsC14` with exactly these parameters (R20's ONE
  admissibility certificate for the chapter-13 block).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The chapter-14 requests on the chapter-13 parameters** (R14 / R15 / R20), in the order of the
producer `eventually_nonempty_localChartPacketsC14`. Upper requests are positive; lower requests are
arbitrary reals. A request may depend only on what is bound before its binder: the early constants
of chapter 14 (captured in the functions), `β₂` and `Δ` (and `V` for `Lmax`). -/
structure C14Requests where
  /-- Circle quality `γ` (TCP01 Gram `γ ≤ γ_T/20`, TCP03 `γ < θ₂²/10¹²`); before `β₀`. -/
  γ : ℝ
  /-- Collar quality `γc` (TCP04 `γ_h < θ²/10¹²`, EDP03 anchor `1/1000`); before `σ₀, Δ₀`. -/
  γc : ℝ
  /-- `β₂` (`10⁻⁷` for `tcp01_gram`, `γ_T/20`, `10⁻⁵` for EGP01, TCP02 compatibility). -/
  β₂ : ℝ
  /-- Lower request on `Δ` (`10⁶`, the short-buffer lower bounds of TCP01–04, FC22, LFR35–38). -/
  Δ : ℝ
  /-- Edge quality `σc` (EGP04 `min(θ_e²/10⁸, 1/(1000L))`). -/
  σc : ℝ → ℝ → ℝ
  /-- Smoothing Lipschitz error `ε`. -/
  ε : ℝ → ℝ → ℝ
  /-- Edge value error `μ` (`min(θ_e/(100Δ), θ₂/(100Δ))`). -/
  μ : ℝ → ℝ → ℝ
  /-- Coarse-border error `τ` (`4τΔ < β₂`). -/
  τ : ℝ → ℝ → ℝ
  /-- Strong endpoint quality `s`. -/
  s : ℝ → ℝ → ℝ
  /-- Weak-edge splitting quality `b'`. -/
  b' : ℝ → ℝ → ℝ
  /-- Weak-edge endpoint quality `s'`. -/
  s' : ℝ → ℝ → ℝ
  /-- Scale Lipschitz constant `Λ` ((RegScale): `LΛ < 10⁻⁵`, `C_ρΔΛ < 10⁻⁶`, `ΔΛ < e₁/(1000C₁)`). -/
  Λ : ℝ → ℝ → ℝ
  /-- Strong splitting quality `b` (EGP03 / TCP02 raw thresholds). -/
  b : ℝ → ℝ → ℝ
  /-- Slim quality `σs` (SGP03 (SB): `min(1/100, θ_s²/10⁶, 1/(100L), …)`). -/
  σs : ℝ → ℝ → ℝ
  /-- Slim value tolerance `vs` (`½ min(θ_s, θ_e, θ₂)/100`). -/
  vs : ℝ → ℝ → ℝ
  /-- `β₁` (SGP02 / EGP03 / TCP02 remaining bounds; the rows' `β₁`-thresholds). -/
  β₁ : ℝ → ℝ → ℝ
  /-- LC73 quality `ζ` of the zero shell clauses (`ζ₀`). -/
  ζ : ℝ → ℝ → ℝ
  /-- Cap for the zero radial difference-Lipschitz constant (`min(θ/(100L), θ/1000, 1/100)`). -/
  cap : ℝ → ℝ → ℝ
  /-- Zero absolute error `e` (ZSP `e₀ < 10⁻³`). -/
  e : ℝ → ℝ → ℝ
  /-- Lower request on the lower zero scale `T` (`T ≥ 1600L`, shell / normal-flow bounds). -/
  T : ℝ → ℝ → ℝ
  /-- Lower request on `Lmax` after the joint zero output `V` (`Lmax ≥ 400V`, test radii). -/
  Lmax : ℝ → ℝ → ℝ → ℝ
  γ_pos : 0 < γ
  γc_pos : 0 < γc
  β₂_pos : 0 < β₂
  σc_pos : ∀ x y, 0 < σc x y
  ε_pos : ∀ x y, 0 < ε x y
  μ_pos : ∀ x y, 0 < μ x y
  τ_pos : ∀ x y, 0 < τ x y
  s_pos : ∀ x y, 0 < s x y
  b'_pos : ∀ x y, 0 < b' x y
  s'_pos : ∀ x y, 0 < s' x y
  Λ_pos : ∀ x y, 0 < Λ x y
  b_pos : ∀ x y, 0 < b x y
  σs_pos : ∀ x y, 0 < σs x y
  vs_pos : ∀ x y, 0 < vs x y
  β₁_pos : ∀ x y, 0 < β₁ x y
  ζ_pos : ∀ x y, 0 < ζ x y
  cap_pos : ∀ x y, 0 < cap x y
  e_pos : ∀ x y, 0 < e x y

/-- **One admissible assignment** of the free parameters of
`eventually_nonempty_localChartPacketsC14` meeting every request of `Rq`, with the producer's
numerical guarantees that rows use. -/
structure C14Assignment (Rq : C14Requests) where
  γ : ℝ
  βc : ℝ
  γc : ℝ
  β₂ : ℝ
  Δ : ℝ
  σc : ℝ
  ε : ℝ
  μ : ℝ
  τ : ℝ
  s : ℝ
  b' : ℝ
  s' : ℝ
  Λ : ℝ
  w : ℝ
  b : ℝ
  σs : ℝ
  vs : ℝ
  β : ℕ → ℝ
  ζ : ℝ
  cap : ℝ
  εr : ℝ
  Λz : ℝ
  T : ℝ
  e : ℝ
  γ_le : γ ≤ Rq.γ
  γc_le : γc ≤ Rq.γc
  β₂_le : β₂ ≤ Rq.β₂
  Δ_ge : Rq.Δ ≤ Δ
  σc_le : σc ≤ Rq.σc β₂ Δ
  ε_le : ε ≤ Rq.ε β₂ Δ
  μ_le : μ ≤ Rq.μ β₂ Δ
  τ_le : τ ≤ Rq.τ β₂ Δ
  s_le : s ≤ Rq.s β₂ Δ
  b'_le : b' ≤ Rq.b' β₂ Δ
  s'_le : s' ≤ Rq.s' β₂ Δ
  Λ_le : Λ ≤ Rq.Λ β₂ Δ
  b_le : b ≤ Rq.b β₂ Δ
  σs_le : σs ≤ Rq.σs β₂ Δ
  vs_le : vs ≤ Rq.vs β₂ Δ
  β₁_le : β 1 ≤ Rq.β₁ β₂ Δ
  ζ_le : ζ ≤ Rq.ζ β₂ Δ
  cap_eq : cap = Rq.cap β₂ Δ
  εr_lt_cap : εr < cap
  T_ge : Rq.T β₂ Δ ≤ T
  e_le : e ≤ Rq.e β₂ Δ
  γ_pos : 0 < γ
  γ_lt : γ < 1 / 10
  βc_pos : 0 < βc
  βc_lt : βc < γc / 1000
  γc_pos : 0 < γc
  γc_lt : γc < 1 / 100
  β_two : β 2 = β₂
  β₂_pos : 0 < β₂
  β₂_lt : β₂ < 1 / 100
  Δ_gt : 100 / β₂ < Δ
  σc_pos : 0 < σc
  ε_pos : 0 < ε
  ε_le8 : ε ≤ 1 / 10 ^ 8
  μ_pos : 0 < μ
  μ_le8 : μ ≤ 1 / 10 ^ 8
  τ_pos : 0 < τ
  s_pos : 0 < s
  b'_lt : b' < 1 / (1000000 * Δ)
  s'_lt : s' < 1 / (1000000 * Δ)
  s_lt_b' : s < b' / 100000
  s_lt_s' : s < s' / 100000
  Λ_pos : 0 < Λ
  ΔΛ_le : 100 * Δ * Λ ≤ 1 / 10 ^ 8
  w_pos : 0 < w
  b_pos : 0 < b
  b_lt : b < s / 100000
  b_inv : 100 * Δ < b⁻¹
  σs_pos : 0 < σs
  σs_le_one : σs ≤ 1 / 100
  vs_pos : 0 < vs
  β₁_pos : 0 < β 1
  β₁_lt : β 1 < ζ
  ζ_lt : ζ < 1
  β_three : β 3 ≤ threeSplittingExclusionThreshold.{0, 0}
  εr_pos : 0 < εr
  εr_lt : εr < 1 / 4
  Λz_pos : 0 < Λz
  T_Λz : 20 * Λz ≤ T
  e_pos : 0 < e
  e_lt : e < 1 / 40

/-! ### Arithmetic of the assignment (standalone, small contexts) -/

/-- The square-root budget of the edge producer from the split choices. -/
theorem c14_sqrt_budget_FAM {γc ε Δ Λ τ : ℝ} (hγc : 0 < γc) (hε : ε ≤ γc / 16000)
    (hΔpos : 0 < Δ) (hΔ : 1008000 / (γc / 2000) ^ 2 ≤ Δ) (hΛ : 300 * Δ * Λ ≤ γc / 16000)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ (γc / 2000) ^ 2 / 10000) :
    2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 := by
  have hK : 0 < (γc / 2000) ^ 2 := by positivity
  have h1 : 504000 / Δ ≤ (γc / 2000) ^ 2 / 2 := by
    rw [div_le_iff₀ hΔpos]
    have h := (div_le_iff₀ hK).mp hΔ
    nlinarith
  have h2 : 504000 / Δ + 3780 * τ < (γc / 2000) ^ 2 := by nlinarith
  have h3 : Real.sqrt (504000 / Δ + 3780 * τ) < γc / 2000 := by
    rw [show γc / 2000 = Real.sqrt ((γc / 2000) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (by positivity) h2
  linarith

/-- The scale-Lipschitz conditions of the producer from three upper bounds on `Λ`. -/
theorem c14_lambda_FAM {γc Δ Λ s' : ℝ} (hΔ : 0 < Δ)
    (h1 : Λ ≤ 1 / (10 ^ 12 * Δ)) (h2 : Λ ≤ γc / (4800000 * Δ))
    (h3 : Λ ≤ s' / (200000000 * Δ ^ 2)) (hs' : 0 < s') :
    Δ * Λ * 2000000 ≤ 1 / 100 ∧ Λ < 1 / (1000000 * Δ) ∧ 100 * Δ * Λ ≤ 1 / 1000000 ∧
      Λ < s' / (100000000 * Δ ^ 2) ∧ 100 * Δ * Λ ≤ 1 / 10 ^ 8 ∧ 300 * Δ * Λ ≤ γc / 16000 := by
  have hΔΛ : Δ * Λ ≤ 1 / 10 ^ 12 := by
    have := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  refine ⟨by nlinarith, ?_, by nlinarith, ?_, by nlinarith, ?_⟩
  · refine h1.trans_lt ?_
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    nlinarith
  · refine h3.trans_lt ?_
    rw [div_lt_div_iff_of_pos_left hs' (by positivity) (by positivity)]
    nlinarith
  · have := (le_div_iff₀ (by positivity)).mp h2
    nlinarith

/-- `140√τ < ε²/20` once `τ ≤ (ε²/5600)²`. -/
theorem c14_tau_sqrt_FAM {ε τ : ℝ} (hε : 0 < ε) (hτ : τ ≤ (ε ^ 2 / 5600) ^ 2) :
    140 * Real.sqrt τ < ε ^ 2 / 20 := by
  have h : Real.sqrt τ ≤ ε ^ 2 / 5600 := by
    rw [show ε ^ 2 / 5600 = Real.sqrt ((ε ^ 2 / 5600) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hτ
  have hε2 : 0 < ε ^ 2 := by positivity
  linarith

/-- `x ≤ c / (2d)` with `0 < c, d` gives `x < c / d`. -/
theorem c14_half_lt_FAM {x c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : x ≤ c / (2 * d)) :
    x < c / d := by
  refine h.trans_lt ?_
  rw [div_lt_div_iff_of_pos_left hc (by positivity) hd]
  linarith

/-- `b ≤ 1/(200Δ)` with `0 < b, Δ` gives `100Δ < b⁻¹`. -/
theorem c14_b_inv_FAM {b Δ : ℝ} (hb : 0 < b) (hΔ : 0 < Δ) (h : b ≤ 1 / (200 * Δ)) :
    100 * Δ < b⁻¹ := by
  have h' : 200 * Δ ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb]
    rwa [one_div] at h
  linarith

/-- **ONE admissible assignment for all chapter-14 requests** (R20, chapter-13 block): for every
request record `Rq` there is ONE assignment `A` of the free parameters of
`eventually_nonempty_localChartPacketsC14`, meeting every request of `Rq`, such that for every
standing sequence, with the joint zero output `V ≥ T` and `Lmax := max 1 (Rq.Lmax β₂ Δ V)`, every
late member carries the final family `LocalChartPacketsC14` with exactly these parameters. -/
theorem exists_c14_assignment (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (Rq : C14Requests) :
    ∃ P : C14Assignment Rq,
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (max 1 (Rq.Lmax P.β₂ P.Δ V)) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz) := by
  have hthr := threeSplittingExclusionThreshold_pos.{0, 0}
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14 K hK A hA
  -- γ
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = min Rq.γ (1 / 20) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγd]; exact lt_min Rq.γ_pos (by norm_num)
  have hγ1 : γ < 1 / 10 := by rw [hγd]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨β₀, hβ₀, -, h⟩ := h γ hγ hγ1
  -- βc, γc
  obtain ⟨γc, hγcd⟩ : ∃ γc : ℝ, γc = min Rq.γc (1 / 200) := ⟨_, rfl⟩
  have hγc : 0 < γc := by rw [hγcd]; exact lt_min Rq.γc_pos (by norm_num)
  have hγc1 : γc < 1 / 100 := by rw [hγcd]; exact (min_le_right _ _).trans_lt (by norm_num)
  have hβc : 0 < γc / 2000 := by positivity
  have hβcγ : γc / 2000 < γc / 1000 := by linarith
  obtain ⟨σ₀, hσ₀, Δ₀, -, h⟩ := h (γc / 2000) γc hβc hβcγ hγc hγc1
  -- β₂, Δ
  obtain ⟨β₂, hβ₂d⟩ : ∃ β₂ : ℝ, β₂ = min (min β₀ Rq.β₂) (1 / 200) := ⟨_, rfl⟩
  have hβ₂ : 0 < β₂ := by rw [hβ₂d]; exact lt_min (lt_min hβ₀ Rq.β₂_pos) (by norm_num)
  have hβ₂β₀ : β₂ ≤ β₀ := by rw [hβ₂d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hβ₂R : β₂ ≤ Rq.β₂ := by rw [hβ₂d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hβ₂1 : β₂ < 1 / 100 := by rw [hβ₂d]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : ℝ,
      Δ = max (max Δ₀ Rq.Δ) (max (100 / β₂ + 1) (1008000 / (γc / 2000) ^ 2)) := ⟨_, rfl⟩
  have hΔβ₂ : 100 / β₂ < Δ := by
    rw [hΔd]
    exact (lt_add_one _).trans_le ((le_max_left _ _).trans (le_max_right _ _))
  have hΔ₀Δ : Δ₀ ≤ Δ := by rw [hΔd]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hΔR : Rq.Δ ≤ Δ := by rw [hΔd]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hΔK : 1008000 / (γc / 2000) ^ 2 ≤ Δ := by
    rw [hΔd]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hΔpos : 0 < Δ := (by positivity : (0 : ℝ) < 100 / β₂).trans hΔβ₂
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂1 hΔβ₂ hΔ₀Δ
  -- σc, ε, μ, τ
  obtain ⟨σc, hσcd⟩ : ∃ σc : ℝ, σc = min (min σ₀ (Rq.σc β₂ Δ)) (1 / 2) := ⟨_, rfl⟩
  have hσc : 0 < σc := by rw [hσcd]; exact lt_min (lt_min hσ₀ (Rq.σc_pos _ _)) (by norm_num)
  have hσcσ₀ : σc ≤ σ₀ := by rw [hσcd]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hσcR : σc ≤ Rq.σc β₂ Δ := by rw [hσcd]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hσc1 : σc < 1 := by rw [hσcd]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min (Rq.ε β₂ Δ) (min (1 / 10 ^ 8) (γc / 16000)) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεd]; exact lt_min (Rq.ε_pos _ _) (lt_min (by norm_num) (by positivity))
  have hεR : ε ≤ Rq.ε β₂ Δ := by rw [hεd]; exact min_le_left _ _
  have hε8 : ε ≤ 1 / 10 ^ 8 := by rw [hεd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεγ : ε ≤ γc / 16000 := by rw [hεd]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hε1 : ε < 1 / 100 := hε8.trans_lt (by norm_num)
  obtain ⟨μ, hμd⟩ : ∃ μ : ℝ, μ = min (Rq.μ β₂ Δ) (1 / 10 ^ 8) := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμd]; exact lt_min (Rq.μ_pos _ _) (by norm_num)
  have hμR : μ ≤ Rq.μ β₂ Δ := by rw [hμd]; exact min_le_left _ _
  have hμ8 : μ ≤ 1 / 10 ^ 8 := by rw [hμd]; exact min_le_right _ _
  have hμ1 : μ ≤ 1 / 1000000 := hμ8.trans (by norm_num)
  obtain ⟨τ, hτd⟩ : ∃ τ : ℝ, τ = min τ₀ (min (Rq.τ β₂ Δ)
      (min ((ε ^ 2 / 5600) ^ 2) ((γc / 2000) ^ 2 / 10000))) := ⟨_, rfl⟩
  have hτ : 0 < τ := by
    rw [hτd]
    exact lt_min hτ₀ (lt_min (Rq.τ_pos _ _) (lt_min (by positivity) (by positivity)))
  have hττ₀ : τ ≤ τ₀ := by rw [hτd]; exact min_le_left _ _
  have hτR : τ ≤ Rq.τ β₂ Δ := by rw [hτd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hτε : τ ≤ (ε ^ 2 / 5600) ^ 2 := by
    rw [hτd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτK : τ ≤ (γc / 2000) ^ 2 / 10000 := by
    rw [hτd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθ := c14_tau_sqrt_FAM hε hτε
  -- s, b', s'
  obtain ⟨b', hb'd⟩ : ∃ b' : ℝ, b' = min (Rq.b' β₂ Δ)
      (min (1 / (2 * 1000000 * Δ)) (τ * Δ / (2 * 1000000000))) := ⟨_, rfl⟩
  have hb' : 0 < b' := by
    rw [hb'd]; exact lt_min (Rq.b'_pos _ _) (lt_min (by positivity) (by positivity))
  have hb'R : b' ≤ Rq.b' β₂ Δ := by rw [hb'd]; exact min_le_left _ _
  have hb'D : b' < 1 / (1000000 * Δ) := by
    refine c14_half_lt_FAM one_pos (by positivity) ?_
    rw [hb'd, ← mul_assoc]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hb'E : b' < τ * Δ / 1000000000 := by
    refine c14_half_lt_FAM (by positivity) (by norm_num) ?_
    rw [hb'd]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨s', hs'd⟩ : ∃ s' : ℝ, s' = min (Rq.s' β₂ Δ)
      (min (1 / (2 * 1000000 * Δ)) (τ * Δ / (2 * 1000000000))) := ⟨_, rfl⟩
  have hs' : 0 < s' := by
    rw [hs'd]; exact lt_min (Rq.s'_pos _ _) (lt_min (by positivity) (by positivity))
  have hs'R : s' ≤ Rq.s' β₂ Δ := by rw [hs'd]; exact min_le_left _ _
  have hs'D : s' < 1 / (1000000 * Δ) := by
    refine c14_half_lt_FAM one_pos (by positivity) ?_
    rw [hs'd, ← mul_assoc]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs'E : s' < τ * Δ / 1000000000 := by
    refine c14_half_lt_FAM (by positivity) (by norm_num) ?_
    rw [hs'd]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = min (Rq.s β₂ Δ) (min (1 / 200) (min b' s' / (2 * 100000))) :=
    ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hsd]
    exact lt_min (Rq.s_pos _ _) (lt_min (by norm_num) (div_pos (lt_min hb' hs') (by norm_num)))
  have hsR : s ≤ Rq.s β₂ Δ := by rw [hsd]; exact min_le_left _ _
  have hs1 : s < 1 / 100 := by
    rw [hsd]; exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hsm : s ≤ min b' s' / (2 * 100000) := by
    rw [hsd]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hsb' : s < b' / 100000 :=
    c14_half_lt_FAM hb' (by norm_num) (hsm.trans (div_le_div_of_nonneg_right (min_le_left _ _)
      (by norm_num)))
  have hss' : s < s' / 100000 :=
    c14_half_lt_FAM hs' (by norm_num) (hsm.trans (div_le_div_of_nonneg_right (min_le_right _ _)
      (by norm_num)))
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hs1 hsb' hss' hb'D hs'D hb'E hs'E
  -- σ, Λ
  have hσ : 0 < min (min a₂ threeSplittingExclusionThreshold.{0, 0}) a₀ :=
    lt_min (lt_min ha₂ hthr) ha₀
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℝ, Λ = min (Rq.Λ β₂ Δ) (min (1 / (10 ^ 12 * Δ))
      (min (γc / (4800000 * Δ)) (s' / (200000000 * Δ ^ 2)))) := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by
    rw [hΛd]
    exact lt_min (Rq.Λ_pos _ _) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hΛR : Λ ≤ Rq.Λ β₂ Δ := by rw [hΛd]; exact min_le_left _ _
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6⟩ := c14_lambda_FAM (γc := γc) (Λ := Λ) (s' := s') hΔpos
    (by rw [hΛd]; exact (min_le_right _ _).trans (min_le_left _ _))
    (by rw [hΛd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by rw [hΛd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    hs'
  have hbudget := c14_sqrt_budget_FAM hγc hεγ hΔpos hΔK hΛ6 hτ.le hτK
  obtain ⟨w₀, hw₀, h⟩ := h _ hσ ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _) Λ hΛ hΛ1 hΛ2 hΛ3 hbudget hΛ4
    hΛ5
  -- w
  have hw : 0 < min (w₀ / 2) 1 := lt_min (by positivity) one_pos
  have hww : min (w₀ / 2) 1 < w₀ := (min_le_left _ _).trans_lt (by linarith)
  have hwπ : min (w₀ / 2) 1 < 4 * Real.pi / 3 :=
    (min_le_right _ _).trans_lt (by linarith [Real.pi_gt_three])
  obtain ⟨bd₀, hbd₀, h⟩ := h _ hw hww hwπ
  -- b, σs, vs
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = min (Rq.b β₂ Δ) (min (s / (2 * 100000)) (min (bc₀ / 2)
      (min (b₁ / 2) (min (bd₀ / 2) (1 / (200 * Δ)))))) := ⟨_, rfl⟩
  have hb : 0 < b := by
    rw [hbd]
    exact lt_min (Rq.b_pos _ _) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  have hbR : b ≤ Rq.b β₂ Δ := by rw [hbd]; exact min_le_left _ _
  have hbs : b < s / 100000 := by
    refine c14_half_lt_FAM hs (by norm_num) ?_
    rw [hbd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hbc : b < bc₀ := by
    rw [hbd]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt
      (by linarith)
  have hbb₁ : b < b₁ := by
    rw [hbd]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))).trans_lt (by linarith)
  have hbbd : b < bd₀ := by
    rw [hbd]
    exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))).trans_lt (by linarith)
  have hsource : 100 * Δ < b⁻¹ := by
    refine c14_b_inv_FAM hb hΔpos ?_
    rw [hbd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨σs, hσsd⟩ : ∃ σs : ℝ, σs = min (Rq.σs β₂ Δ) (1 / 100) := ⟨_, rfl⟩
  have hσs : 0 < σs := by rw [hσsd]; exact lt_min (Rq.σs_pos _ _) (by norm_num)
  have hσsR : σs ≤ Rq.σs β₂ Δ := by rw [hσsd]; exact min_le_left _ _
  have hσs1 : σs ≤ 1 / 100 := by rw [hσsd]; exact min_le_right _ _
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbbd σs (Rq.vs β₂ Δ) hσs hσs1
    (Rq.vs_pos _ _)
  -- β, ζ, cap
  obtain ⟨ζ, hζd⟩ : ∃ ζ : ℝ, ζ = min (Rq.ζ β₂ Δ) (1 / 2) := ⟨_, rfl⟩
  have hζ : 0 < ζ := by rw [hζd]; exact lt_min (Rq.ζ_pos _ _) (by norm_num)
  have hζR : ζ ≤ Rq.ζ β₂ Δ := by rw [hζd]; exact min_le_left _ _
  have hζ1 : ζ < 1 := by rw [hζd]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨β₁, hβ₁d⟩ : ∃ β₁ : ℝ, β₁ = min (b₀ / 2) (min (ζ / 2) (Rq.β₁ β₂ Δ)) := ⟨_, rfl⟩
  have hβ₁ : 0 < β₁ := by
    rw [hβ₁d]; exact lt_min (by positivity) (lt_min (by positivity) (Rq.β₁_pos _ _))
  have hβ₁b₀ : β₁ < b₀ := by rw [hβ₁d]; exact (min_le_left _ _).trans_lt (by linarith)
  have hβ₁ζ : β₁ < ζ := by
    rw [hβ₁d]; exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hβ₁R : β₁ ≤ Rq.β₁ β₂ Δ := by
    rw [hβ₁d]; exact (min_le_right _ _).trans (min_le_right _ _)
  let β : ℕ → ℝ := fun n =>
    if n = 2 then β₂ else if n = 3 then threeSplittingExclusionThreshold.{0, 0} else β₁
  have hβ2 : β 2 = β₂ := by simp [β]
  have hβ1 : β 1 = β₁ := by simp [β]
  have hβ3 : β 3 = threeSplittingExclusionThreshold.{0, 0} := by simp [β]
  obtain ⟨εr, δ', Λz, hεr, hεr4, hεrcap, -, hΛz, h⟩ := h β hβ2 (hβ1 ▸ hβ₁) (hβ1 ▸ hβ₁b₀)
    (hβ1 ▸ hβ₁ζ.trans hζ1) hβ3.le ζ (Rq.cap β₂ Δ) (hβ1 ▸ hβ₁ζ) hζ1 (Rq.cap_pos _ _)
  -- T, e
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = max (20 * Λz) (Rq.T β₂ Δ) := ⟨_, rfl⟩
  have hTΛ : 20 * Λz ≤ T := by rw [hTd]; exact le_max_left _ _
  have hT : 0 < T := (by positivity : (0 : ℝ) < 20 * Λz).trans_le hTΛ
  have hTR : Rq.T β₂ Δ ≤ T := by rw [hTd]; exact le_max_right _ _
  obtain ⟨e, hed⟩ : ∃ e : ℝ, e = min (Rq.e β₂ Δ) (1 / 80) := ⟨_, rfl⟩
  have he : 0 < e := by rw [hed]; exact lt_min (Rq.e_pos _ _) (by norm_num)
  have heR : e ≤ Rq.e β₂ Δ := by rw [hed]; exact min_le_left _ _
  have he1 : e < 1 / 40 := by rw [hed]; exact (min_le_right _ _).trans_lt (by norm_num)
  have hfin := h T hT hTΛ e he he1
  refine ⟨{
    γ := γ
    βc := γc / 2000
    γc := γc
    β₂ := β₂
    Δ := Δ
    σc := σc
    ε := ε
    μ := μ
    τ := τ
    s := s
    b' := b'
    s' := s'
    Λ := Λ
    w := min (w₀ / 2) 1
    b := b
    σs := σs
    vs := Rq.vs β₂ Δ
    β := β
    ζ := ζ
    cap := Rq.cap β₂ Δ
    εr := εr
    Λz := Λz
    T := T
    e := e
    γ_le := by rw [hγd]; exact min_le_left _ _
    γc_le := by rw [hγcd]; exact min_le_left _ _
    β₂_le := hβ₂R
    Δ_ge := hΔR
    σc_le := hσcR
    ε_le := hεR
    μ_le := hμR
    τ_le := hτR
    s_le := hsR
    b'_le := hb'R
    s'_le := hs'R
    Λ_le := hΛR
    b_le := hbR
    σs_le := hσsR
    vs_le := le_rfl
    β₁_le := hβ1 ▸ hβ₁R
    ζ_le := hζR
    cap_eq := rfl
    εr_lt_cap := hεrcap
    T_ge := hTR
    e_le := heR
    γ_pos := hγ
    γ_lt := hγ1
    βc_pos := hβc
    βc_lt := hβcγ
    γc_pos := hγc
    γc_lt := hγc1
    β_two := hβ2
    β₂_pos := hβ₂
    β₂_lt := hβ₂1
    Δ_gt := hΔβ₂
    σc_pos := hσc
    ε_pos := hε
    ε_le8 := hε8
    μ_pos := hμ
    μ_le8 := hμ8
    τ_pos := hτ
    s_pos := hs
    b'_lt := hb'D
    s'_lt := hs'D
    s_lt_b' := hsb'
    s_lt_s' := hss'
    Λ_pos := hΛ
    ΔΛ_le := hΛ5
    w_pos := hw
    b_pos := hb
    b_lt := hbs
    b_inv := hsource
    σs_pos := hσs
    σs_le_one := hσs1
    vs_pos := Rq.vs_pos _ _
    β₁_pos := hβ1 ▸ hβ₁
    β₁_lt := hβ1 ▸ hβ₁ζ
    ζ_lt := hζ1
    β_three := hβ3.le
    εr_pos := hεr
    εr_lt := hεr4
    Λz_pos := hΛz
    T_Λz := hTΛ
    e_pos := he
    e_lt := he1 }, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, -, hV⟩ := hfin X g hmetric α hα hstand hder hor
  exact ⟨V, hTV, δ, hδ, hV (max 1 (Rq.Lmax β₂ Δ V)) (lt_max_of_lt_left one_pos)⟩

end DifferentialGeometry.Geometry.Collapse
