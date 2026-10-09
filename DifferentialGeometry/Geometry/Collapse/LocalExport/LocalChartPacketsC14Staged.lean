import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Requests

/-!
# The staged prefix requests contract of the final family (`LocalChartPacketsC14`)

Lanes C14-FAM2 / C14-FAM2b, external review 50, blocking item A (A1–A3), lead decision T50-2.
The delivered `C14Requests` / `exists_c14_assignment` (first version, kept unchanged) let every
request depend only on `(β₂, Δ)`; review 50 requires a STAGED contract: stage `n`'s request is a
function of the admissible prefix of everything fixed before it (parameters, the producer's
threshold outputs and their facts), and returns a positive upper bound (or a finite lower bound for
`Δ`, `T`, `Lmax`).

* The thirteen prefixes `C14Tol` (external tolerances `γ_T, θ_s, θ_e, θ_2` and the (RegScale)
  constants `C_ρ, e₁, C₁`, fixed first), `C14PreCirc` (`γ`), `C14PreCollar` (`βc, γc`),
  `C14PreExcl` (`β₂`, the version callable before `Δ`), `C14PreScale` (`Δ`, the root budget
  `Δ > 504000 (4000/γc)²` reserved), `C14PreEdge` (`σc ε μ τ s b' s'`, with C14-KC's `σc ≤ 10⁻¹⁰`,
  `τ ≤ 10⁻³⁰`), `C14PreLip` (`Λ`, each (RegScale) budget separately), `C14PreVol` (`w`),
  `C14PreSplit` (`b`), `C14PreSlim` (`σs, vs`), `C14PreBeta` (`ζ` BEFORE `β₁`, `β 3 = ϑ₃`),
  `C14PreZero` (`cap`, then `εr < cap`) and `C14PreFinal` (`T, e`), each extending the previous one
  and recording the producer's guarantees so far.
* `C14StagedRequests`, `C14StagedRequests.Meets`, `C14StagedRequests.inf` (common minima / maxima
  over all rows), `c14Lmax` (`1 + max(1, max(400V, L_requested))`, strictly above `400V`).
* `c14_stage_*_FAM2b`: one lemma per producer binder group, with an abstract continuation.
* `exists_c14_staged_assignment`: ONE admissible prefix meeting every staged request; for every
  standing sequence, with the joint zero output `V` and `Lmax := c14Lmax Rq P V` (the only request
  seeing `V`), every late member carries `LocalChartPacketsC14` with exactly these parameters.
  No back-dependency: `cap` sees `C14PreBeta`, `Λ` sees `C14PreEdge`; only `Lmax` sees `V`.
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

/-! ### The admissible prefixes -/

/-- **Stage 0: the external tolerances**, fixed before every chapter-13 parameter: the Gram
tolerance `γ_T` (TCP01), the row tolerances `θ_s` (SGP03), `θ_e` (EGP04), `θ_2` (TCP03), and the
(RegScale) constants `C_ρ`, `e₁`, `C₁` of GAF01 / PR10. -/
structure C14Tol where
  /-- TCP01's external Gram tolerance. -/
  γT : ℝ
  /-- SGP03's tolerance. -/
  θs : ℝ
  /-- EGP04's tolerance. -/
  θe : ℝ
  /-- TCP03's tolerance. -/
  θ2 : ℝ
  /-- (RegScale) `C_ρ`. -/
  Cρ : ℝ
  /-- (RegScale) `e₁`. -/
  e₁ : ℝ
  /-- (RegScale) `C₁`. -/
  C₁ : ℝ
  γT_pos : 0 < γT
  γT_le : γT ≤ 1
  θs_pos : 0 < θs
  θs_lt : θs < 1
  θe_pos : 0 < θe
  θe_lt : θe < 1
  θ2_pos : 0 < θ2
  θ2_lt : θ2 < 1
  Cρ_pos : 0 < Cρ
  e₁_pos : 0 < e₁
  C₁_pos : 0 < C₁

/-- **Stage 1** (`γ`, after the producer's `a₂`; the producer's `β₀` after it). The Gram budget
`γ ≤ γ_T/20` is built in. -/
structure C14PreCirc extends C14Tol where
  a₂ : ℝ
  γ : ℝ
  β₀ : ℝ
  a₂_pos : 0 < a₂
  γ_pos : 0 < γ
  γ_lt : γ < 1 / 10
  γ_le_γT : γ ≤ γT / 20
  β₀_pos : 0 < β₀
  β₀_le : β₀ ≤ a₂

/-- **Stage 2** (`βc, γc`; the producer's `σ₀, Δ₀` after them). -/
structure C14PreCollar extends C14PreCirc where
  βc : ℝ
  γc : ℝ
  σ₀ : ℝ
  Δ₀ : ℝ
  βc_pos : 0 < βc
  βc_lt : βc < γc / 1000
  γc_pos : 0 < γc
  γc_lt : γc < 1 / 100
  σ₀_pos : 0 < σ₀
  Δ₀_pos : 0 < Δ₀

/-- **Stage 3** (`β₂`, the version callable before `Δ`): `β₂ ≤ 10⁻⁷` (`tcp01_gram`, R20) and
`β₂ ≤ γ_T/20` (Gram) are built in. -/
structure C14PreExcl extends C14PreCollar where
  β₂ : ℝ
  β₂_pos : 0 < β₂
  β₂_le : β₂ ≤ β₀
  β₂_lt : β₂ < 1 / 100
  β₂_le7 : β₂ ≤ 1 / 10000000
  β₂_le_γT : β₂ ≤ γT / 20

/-- **Stage 4** (`Δ`; the producer's `τ₀, bc₀` after it). The root budget is reserved here:
`Δ > 504000 (4000/γc)²`. -/
structure C14PreScale extends C14PreExcl where
  Δ : ℝ
  τ₀ : ℝ
  bc₀ : ℝ
  Δ_gt : 100 / β₂ < Δ
  Δ₀_le : Δ₀ ≤ Δ
  Δ_gt6 : 1000000 < Δ
  Δ_root : 504000 * (4000 / γc) ^ 2 < Δ
  τ₀_pos : 0 < τ₀
  bc₀_pos : 0 < bc₀

/-- **Stage 5** (`σc ε μ τ`, then `s b' s'`; the producer's `a₀, b₁`; the free `σ`): the
producer's conditions, C14-KC's supplier conditions `σc ≤ 10⁻¹⁰`, `τ ≤ 10⁻³⁰`, the root budget
`ε < γc/8000`, `τ < (γc/4000)²/3780`, `τ < (ε²/2800)²`, and PBR / R20's `μ, τ < 10⁻⁸`,
`4τΔ < β₂`, `b', s' < 10⁻⁸`, `s < 10⁻⁶`. -/
structure C14PreEdge extends C14PreScale where
  σc : ℝ
  ε : ℝ
  μ : ℝ
  τ : ℝ
  s : ℝ
  b' : ℝ
  s' : ℝ
  a₀ : ℝ
  b₁ : ℝ
  σ : ℝ
  σc_pos : 0 < σc
  σc_le : σc ≤ σ₀
  σc_lt : σc < 1
  ε_pos : 0 < ε
  ε_lt : ε < 1 / 100
  μ_pos : 0 < μ
  μ_le : μ ≤ 1 / 1000000
  τ_pos : 0 < τ
  τ_le : τ ≤ τ₀
  τ_sqrt : 140 * Real.sqrt τ < ε ^ 2 / 20
  ε_le8 : ε ≤ 1 / 10 ^ 8
  μ_le8 : μ ≤ 1 / 10 ^ 8
  s_pos : 0 < s
  s_lt : s < 1 / 100
  s_lt_b' : s < b' / 100000
  s_lt_s' : s < s' / 100000
  b'_lt : b' < 1 / (1000000 * Δ)
  s'_lt : s' < 1 / (1000000 * Δ)
  b'_lt_τ : b' < τ * Δ / 1000000000
  s'_lt_τ : s' < τ * Δ / 1000000000
  a₀_pos : 0 < a₀
  b₁_pos : 0 < b₁
  σ_pos : 0 < σ
  σ_le_a₂ : σ ≤ a₂
  σ_le_thr : σ ≤ threeSplittingExclusionThreshold.{0, 0}
  σ_le_a₀ : σ ≤ a₀
  σc_le10 : σc ≤ 1 / 10 ^ 10
  τ_le30 : τ ≤ 1 / 10 ^ 30
  ε_root : ε < γc / 8000
  τ_root : τ < (γc / 4000) ^ 2 / 3780
  τ_ε : τ < (ε ^ 2 / 2800) ^ 2
  μ_lt8 : μ < 1 / 10 ^ 8
  τ_lt8 : τ < 1 / 10 ^ 8
  τΔ_lt : 4 * τ * Δ < β₂
  b'_lt8 : b' < 1 / 10 ^ 8
  s'_lt8 : s' < 1 / 10 ^ 8
  s_lt6 : s < 1 / 10 ^ 6

/-- **Stage 6** (`Λ`; the producer's `w₀` after it): the producer's six conditions, the root
budget `Λ < γc/(1200000Δ)` and each (RegScale) budget separately: `LΛ < 10⁻⁵` (`L = 10⁶Δ`),
`100ΔΛ < 10⁻⁸`, `C_ρΔΛ < 10⁻⁶`, `ΔΛ < e₁/(1000C₁)`, `2·10⁸ΔΛ < 1`. -/
structure C14PreLip extends C14PreEdge where
  Λ : ℝ
  w₀ : ℝ
  Λ_pos : 0 < Λ
  Λ_c1 : Δ * Λ * 2000000 ≤ 1 / 100
  Λ_c2 : Λ < 1 / (1000000 * Δ)
  Λ_c3 : 100 * Δ * Λ ≤ 1 / 1000000
  budget : 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000
  Λ_c5 : Λ < s' / (100000000 * Δ ^ 2)
  Λ_c6 : 100 * Δ * Λ ≤ 1 / 10 ^ 8
  Λ_root : Λ < γc / (1200000 * Δ)
  LΛ_lt : 1000000 * Δ * Λ < 1 / 100000
  ΔΛ_lt8 : 100 * Δ * Λ < 1 / 10 ^ 8
  CρΔΛ_lt : Cρ * Δ * Λ < 1 / 1000000
  ΔΛ_lt_e₁ : Δ * Λ < e₁ / (1000 * C₁)
  ΔΛ_lt_one : 200000000 * Δ * Λ < 1
  w₀_pos : 0 < w₀

/-- **Stage 7** (`w`; the producer's `bd₀` after it). -/
structure C14PreVol extends C14PreLip where
  w : ℝ
  bd₀ : ℝ
  w_pos : 0 < w
  w_lt : w < w₀
  w_lt_pi : w < 4 * Real.pi / 3
  bd₀_pos : 0 < bd₀

/-- **Stage 8** (`b`, with R20's `b < 10⁻⁶`). -/
structure C14PreSplit extends C14PreVol where
  b : ℝ
  b_pos : 0 < b
  b_lt_s : b < s / 100000
  b_lt_bc₀ : b < bc₀
  b_lt_b₁ : b < b₁
  b_inv : 100 * Δ < b⁻¹
  b_lt_bd₀ : b < bd₀
  b_lt6 : b < 1 / 10 ^ 6

/-- **Stage 9** (`σs, vs`; the producer's `b₀` after them). -/
structure C14PreSlim extends C14PreSplit where
  σs : ℝ
  vs : ℝ
  b₀ : ℝ
  σs_pos : 0 < σs
  σs_le : σs ≤ 1 / 100
  vs_pos : 0 < vs
  b₀_pos : 0 < b₀

/-- **Stage 10** (`ζ` BEFORE `β₁`: the producer needs `β₁ < ζ`, so `ζ` is fixed first; then `β`
with `β 2 = β₂`, `β 3 = ϑ₃` (equality, the threshold of `threeSplittingExclusionThreshold`)). -/
structure C14PreBeta extends C14PreSlim where
  ζ : ℝ
  β : ℕ → ℝ
  ζ_lt : ζ < 1
  β_two : β 2 = β₂
  β₁_pos : 0 < β 1
  β₁_lt_b₀ : β 1 < b₀
  β₁_lt : β 1 < 1
  β_three : β 3 = threeSplittingExclusionThreshold.{0, 0}
  β₁_lt_ζ : β 1 < ζ

/-- **Stage 11** (`cap`; the producer's `εr < cap`, `δ'`, `Λz` after it). -/
structure C14PreZero extends C14PreBeta where
  cap : ℝ
  εr : ℝ
  δ' : ℝ
  Λz : ℝ
  cap_pos : 0 < cap
  cap_le : cap ≤ 1 / 100
  εr_pos : 0 < εr
  εr_lt : εr < 1 / 4
  εr_lt_cap : εr < cap
  δ'_pos : 0 < δ'
  Λz_pos : 0 < Λz

/-- **Stage 12** (`T, e`): `20Λz ≤ T`, `1600 · 10⁶Δ ≤ T`, `e < 1/40`, ZSP's `e < 10⁻³`. -/
structure C14PreFinal extends C14PreZero where
  T : ℝ
  e : ℝ
  T_pos : 0 < T
  T_Λz : 20 * Λz ≤ T
  T_Δ : 1600 * (1000000 * Δ) ≤ T
  e_pos : 0 < e
  e_lt : e < 1 / 40
  e_lt3 : e < 1 / 1000

/-! ### The staged requests -/

/-- **The staged requests contract** (review 50, A1–A3): stage `n`'s request is a function of
the admissible prefix BEFORE stage `n` (parameters, producer outputs and their facts so far);
upper requests are positive, `Δ`, `T` and `Lmax` are lower requests. `Lmax` alone sees the joint
zero output `V`. -/
structure C14StagedRequests where
  γ : C14Tol → ℝ
  γc : C14PreCirc → ℝ
  βc : C14PreCirc → ℝ
  β₂ : C14PreCollar → ℝ
  Δ : C14PreExcl → ℝ
  σc : C14PreScale → ℝ
  ε : C14PreScale → ℝ
  μ : C14PreScale → ℝ
  τ : C14PreScale → ℝ
  s : C14PreScale → ℝ
  b' : C14PreScale → ℝ
  s' : C14PreScale → ℝ
  Λ : C14PreEdge → ℝ
  w : C14PreLip → ℝ
  b : C14PreVol → ℝ
  σs : C14PreSplit → ℝ
  vs : C14PreSplit → ℝ
  ζ : C14PreSlim → ℝ
  β₁ : C14PreSlim → ℝ
  cap : C14PreBeta → ℝ
  T : C14PreZero → ℝ
  e : C14PreZero → ℝ
  Lmax : C14PreFinal → ℝ → ℝ
  γ_pos : ∀ p, 0 < γ p
  γc_pos : ∀ p, 0 < γc p
  βc_pos : ∀ p, 0 < βc p
  β₂_pos : ∀ p, 0 < β₂ p
  σc_pos : ∀ p, 0 < σc p
  ε_pos : ∀ p, 0 < ε p
  μ_pos : ∀ p, 0 < μ p
  τ_pos : ∀ p, 0 < τ p
  s_pos : ∀ p, 0 < s p
  b'_pos : ∀ p, 0 < b' p
  s'_pos : ∀ p, 0 < s' p
  Λ_pos : ∀ p, 0 < Λ p
  w_pos : ∀ p, 0 < w p
  b_pos : ∀ p, 0 < b p
  σs_pos : ∀ p, 0 < σs p
  vs_pos : ∀ p, 0 < vs p
  ζ_pos : ∀ p, 0 < ζ p
  β₁_pos : ∀ p, 0 < β₁ p
  cap_pos : ∀ p, 0 < cap p
  e_pos : ∀ p, 0 < e p

/-- `P` meets every request of `Rq`, each at the prefix before its stage. -/
structure C14StagedRequests.Meets (Rq : C14StagedRequests) (P : C14PreFinal) : Prop where
  γ_le : P.γ ≤ Rq.γ P.toC14Tol
  γc_le : P.γc ≤ Rq.γc P.toC14PreCirc
  βc_le : P.βc ≤ Rq.βc P.toC14PreCirc
  β₂_le : P.β₂ ≤ Rq.β₂ P.toC14PreCollar
  Δ_ge : Rq.Δ P.toC14PreExcl ≤ P.Δ
  σc_le : P.σc ≤ Rq.σc P.toC14PreScale
  ε_le : P.ε ≤ Rq.ε P.toC14PreScale
  μ_le : P.μ ≤ Rq.μ P.toC14PreScale
  τ_le : P.τ ≤ Rq.τ P.toC14PreScale
  s_le : P.s ≤ Rq.s P.toC14PreScale
  b'_le : P.b' ≤ Rq.b' P.toC14PreScale
  s'_le : P.s' ≤ Rq.s' P.toC14PreScale
  Λ_le : P.Λ ≤ Rq.Λ P.toC14PreEdge
  w_le : P.w ≤ Rq.w P.toC14PreLip
  b_le : P.b ≤ Rq.b P.toC14PreVol
  σs_le : P.σs ≤ Rq.σs P.toC14PreSplit
  vs_le : P.vs ≤ Rq.vs P.toC14PreSplit
  ζ_le : P.ζ ≤ Rq.ζ P.toC14PreSlim
  β₁_le : P.β 1 ≤ Rq.β₁ P.toC14PreSlim
  cap_le : P.cap ≤ Rq.cap P.toC14PreBeta
  T_ge : Rq.T P.toC14PreZero ≤ P.T
  e_le : P.e ≤ Rq.e P.toC14PreZero

/-- The trivial requests (every upper request `1`, every lower request `0`). -/
def C14StagedRequests.trivial : C14StagedRequests where
  γ _ := 1
  γc _ := 1
  βc _ := 1
  β₂ _ := 1
  Δ _ := 0
  σc _ := 1
  ε _ := 1
  μ _ := 1
  τ _ := 1
  s _ := 1
  b' _ := 1
  s' _ := 1
  Λ _ := 1
  w _ := 1
  b _ := 1
  σs _ := 1
  vs _ := 1
  ζ _ := 1
  β₁ _ := 1
  cap _ := 1
  T _ := 0
  e _ := 1
  Lmax _ _ := 0
  γ_pos _ := one_pos
  γc_pos _ := one_pos
  βc_pos _ := one_pos
  β₂_pos _ := one_pos
  σc_pos _ := one_pos
  ε_pos _ := one_pos
  μ_pos _ := one_pos
  τ_pos _ := one_pos
  s_pos _ := one_pos
  b'_pos _ := one_pos
  s'_pos _ := one_pos
  Λ_pos _ := one_pos
  w_pos _ := one_pos
  b_pos _ := one_pos
  σs_pos _ := one_pos
  vs_pos _ := one_pos
  ζ_pos _ := one_pos
  β₁_pos _ := one_pos
  cap_pos _ := one_pos
  e_pos _ := one_pos

/-- **The common requests of two request records**: the minimum of every upper request and the
maximum of every lower request (`σs, vs, ζ, cap, …` as common minima over all rows, A3). -/
def C14StagedRequests.inf (R₁ R₂ : C14StagedRequests) : C14StagedRequests where
  γ p := min (R₁.γ p) (R₂.γ p)
  γc p := min (R₁.γc p) (R₂.γc p)
  βc p := min (R₁.βc p) (R₂.βc p)
  β₂ p := min (R₁.β₂ p) (R₂.β₂ p)
  Δ p := max (R₁.Δ p) (R₂.Δ p)
  σc p := min (R₁.σc p) (R₂.σc p)
  ε p := min (R₁.ε p) (R₂.ε p)
  μ p := min (R₁.μ p) (R₂.μ p)
  τ p := min (R₁.τ p) (R₂.τ p)
  s p := min (R₁.s p) (R₂.s p)
  b' p := min (R₁.b' p) (R₂.b' p)
  s' p := min (R₁.s' p) (R₂.s' p)
  Λ p := min (R₁.Λ p) (R₂.Λ p)
  w p := min (R₁.w p) (R₂.w p)
  b p := min (R₁.b p) (R₂.b p)
  σs p := min (R₁.σs p) (R₂.σs p)
  vs p := min (R₁.vs p) (R₂.vs p)
  ζ p := min (R₁.ζ p) (R₂.ζ p)
  β₁ p := min (R₁.β₁ p) (R₂.β₁ p)
  cap p := min (R₁.cap p) (R₂.cap p)
  T p := max (R₁.T p) (R₂.T p)
  e p := min (R₁.e p) (R₂.e p)
  Lmax p V := max (R₁.Lmax p V) (R₂.Lmax p V)
  γ_pos p := lt_min (R₁.γ_pos p) (R₂.γ_pos p)
  γc_pos p := lt_min (R₁.γc_pos p) (R₂.γc_pos p)
  βc_pos p := lt_min (R₁.βc_pos p) (R₂.βc_pos p)
  β₂_pos p := lt_min (R₁.β₂_pos p) (R₂.β₂_pos p)
  σc_pos p := lt_min (R₁.σc_pos p) (R₂.σc_pos p)
  ε_pos p := lt_min (R₁.ε_pos p) (R₂.ε_pos p)
  μ_pos p := lt_min (R₁.μ_pos p) (R₂.μ_pos p)
  τ_pos p := lt_min (R₁.τ_pos p) (R₂.τ_pos p)
  s_pos p := lt_min (R₁.s_pos p) (R₂.s_pos p)
  b'_pos p := lt_min (R₁.b'_pos p) (R₂.b'_pos p)
  s'_pos p := lt_min (R₁.s'_pos p) (R₂.s'_pos p)
  Λ_pos p := lt_min (R₁.Λ_pos p) (R₂.Λ_pos p)
  w_pos p := lt_min (R₁.w_pos p) (R₂.w_pos p)
  b_pos p := lt_min (R₁.b_pos p) (R₂.b_pos p)
  σs_pos p := lt_min (R₁.σs_pos p) (R₂.σs_pos p)
  vs_pos p := lt_min (R₁.vs_pos p) (R₂.vs_pos p)
  ζ_pos p := lt_min (R₁.ζ_pos p) (R₂.ζ_pos p)
  β₁_pos p := lt_min (R₁.β₁_pos p) (R₂.β₁_pos p)
  cap_pos p := lt_min (R₁.cap_pos p) (R₂.cap_pos p)
  e_pos p := lt_min (R₁.e_pos p) (R₂.e_pos p)

/-- Meeting the common requests meets the first record. -/
theorem C14StagedRequests.Meets.inf_left {R₁ R₂ : C14StagedRequests} {P : C14PreFinal}
    (h : (R₁.inf R₂).Meets P) : R₁.Meets P where
  γ_le := h.γ_le.trans (min_le_left _ _)
  γc_le := h.γc_le.trans (min_le_left _ _)
  βc_le := h.βc_le.trans (min_le_left _ _)
  β₂_le := h.β₂_le.trans (min_le_left _ _)
  Δ_ge := (le_max_left _ _).trans h.Δ_ge
  σc_le := h.σc_le.trans (min_le_left _ _)
  ε_le := h.ε_le.trans (min_le_left _ _)
  μ_le := h.μ_le.trans (min_le_left _ _)
  τ_le := h.τ_le.trans (min_le_left _ _)
  s_le := h.s_le.trans (min_le_left _ _)
  b'_le := h.b'_le.trans (min_le_left _ _)
  s'_le := h.s'_le.trans (min_le_left _ _)
  Λ_le := h.Λ_le.trans (min_le_left _ _)
  w_le := h.w_le.trans (min_le_left _ _)
  b_le := h.b_le.trans (min_le_left _ _)
  σs_le := h.σs_le.trans (min_le_left _ _)
  vs_le := h.vs_le.trans (min_le_left _ _)
  ζ_le := h.ζ_le.trans (min_le_left _ _)
  β₁_le := h.β₁_le.trans (min_le_left _ _)
  cap_le := h.cap_le.trans (min_le_left _ _)
  T_ge := (le_max_left _ _).trans h.T_ge
  e_le := h.e_le.trans (min_le_left _ _)

/-- Meeting the common requests meets the second record. -/
theorem C14StagedRequests.Meets.inf_right {R₁ R₂ : C14StagedRequests} {P : C14PreFinal}
    (h : (R₁.inf R₂).Meets P) : R₂.Meets P where
  γ_le := h.γ_le.trans (min_le_right _ _)
  γc_le := h.γc_le.trans (min_le_right _ _)
  βc_le := h.βc_le.trans (min_le_right _ _)
  β₂_le := h.β₂_le.trans (min_le_right _ _)
  Δ_ge := (le_max_right _ _).trans h.Δ_ge
  σc_le := h.σc_le.trans (min_le_right _ _)
  ε_le := h.ε_le.trans (min_le_right _ _)
  μ_le := h.μ_le.trans (min_le_right _ _)
  τ_le := h.τ_le.trans (min_le_right _ _)
  s_le := h.s_le.trans (min_le_right _ _)
  b'_le := h.b'_le.trans (min_le_right _ _)
  s'_le := h.s'_le.trans (min_le_right _ _)
  Λ_le := h.Λ_le.trans (min_le_right _ _)
  w_le := h.w_le.trans (min_le_right _ _)
  b_le := h.b_le.trans (min_le_right _ _)
  σs_le := h.σs_le.trans (min_le_right _ _)
  vs_le := h.vs_le.trans (min_le_right _ _)
  ζ_le := h.ζ_le.trans (min_le_right _ _)
  β₁_le := h.β₁_le.trans (min_le_right _ _)
  cap_le := h.cap_le.trans (min_le_right _ _)
  T_ge := (le_max_right _ _).trans h.T_ge
  e_le := h.e_le.trans (min_le_right _ _)

/-- The `Lmax` request of the common record dominates the first one. -/
theorem C14StagedRequests.inf_Lmax_left (R₁ R₂ : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    R₁.Lmax P V ≤ (R₁.inf R₂).Lmax P V :=
  le_max_left _ _

/-- The `Lmax` request of the common record dominates the second one. -/
theorem C14StagedRequests.inf_Lmax_right (R₁ R₂ : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    R₂.Lmax P V ≤ (R₁.inf R₂).Lmax P V :=
  le_max_right _ _

/-- **The final `Lmax`** (A3, PBR01 PR24): `1 + max(1, max(400V, L_requested))`. -/
def c14Lmax (Rq : C14StagedRequests) (P : C14PreFinal) (V : ℝ) : ℝ :=
  1 + max 1 (max (400 * V) (Rq.Lmax P V))

/-- `Lmax > 400V` strictly. -/
theorem c14Lmax_gt (Rq : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    400 * V < c14Lmax Rq P V := by
  unfold c14Lmax
  have := (le_max_left (400 * V) (Rq.Lmax P V)).trans (le_max_right 1 _)
  linarith

/-- `Lmax` dominates the requested `Lmax`. -/
theorem c14Lmax_ge (Rq : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    Rq.Lmax P V ≤ c14Lmax Rq P V := by
  unfold c14Lmax
  have := (le_max_right (400 * V) (Rq.Lmax P V)).trans (le_max_right 1 _)
  linarith

/-- `Lmax > 1`. -/
theorem c14Lmax_gt_one (Rq : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    1 < c14Lmax Rq P V := by
  unfold c14Lmax
  have := le_max_left 1 (max (400 * V) (Rq.Lmax P V))
  linarith

/-- `Lmax > 0`. -/
theorem c14Lmax_pos (Rq : C14StagedRequests) (P : C14PreFinal) (V : ℝ) :
    0 < c14Lmax Rq P V :=
  one_pos.trans (c14Lmax_gt_one Rq P V)

/-! ### Stage lemmas (one producer binder group each, abstract continuation `Q`) -/

/-- **Stage 1**: `γ ≤ r` with `γ < 1/10`, `γ ≤ γ_T/20`, then the producer's `β₀`. -/
theorem c14_stage_circ_FAM2b (t : C14Tol) {a₂ r : ℝ} (ha₂ : 0 < a₂) (hr : 0 < r)
    {Q : ℝ → ℝ → Prop}
    (h : ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧ Q γ β₀) :
    ∃ p : C14PreCirc, p.toC14Tol = t ∧ p.a₂ = a₂ ∧ p.γ ≤ r ∧ Q p.γ p.β₀ := by
  have hT := t.γT_pos
  have hγ : 0 < min r (min (t.γT / 20) (1 / 20)) := by positivity
  have hγ1 : min r (min (t.γT / 20) (1 / 20)) < 1 / 10 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨β₀, hβ₀, hβ₀a, hQ⟩ := h _ hγ hγ1
  exact ⟨{
    toC14Tol := t
    a₂ := a₂
    γ := min r (min (t.γT / 20) (1 / 20))
    β₀ := β₀
    a₂_pos := ha₂
    γ_pos := hγ
    γ_lt := hγ1
    γ_le_γT := (min_le_right _ _).trans (min_le_left _ _)
    β₀_pos := hβ₀
    β₀_le := hβ₀a }, rfl, rfl, min_le_left _ _, hQ⟩

/-- **Stage 2**: `γc ≤ r₂` with `γc < 1/100`, then `βc ≤ r₁` with `βc < γc/1000`; the producer's
`σ₀, Δ₀`. -/
theorem c14_stage_collar_FAM2b (p : C14PreCirc) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    {Q : ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ Q βc γc σ₀ Δ₀) :
    ∃ q : C14PreCollar, q.toC14PreCirc = p ∧ q.βc ≤ r₁ ∧ q.γc ≤ r₂ ∧
      Q q.βc q.γc q.σ₀ q.Δ₀ := by
  have hγc : 0 < min r₂ (1 / 200) := by positivity
  have hγc1 : min r₂ (1 / 200) < 1 / 100 := (min_le_right _ _).trans_lt (by norm_num)
  have hβc : 0 < min r₁ (min r₂ (1 / 200) / 2000) := by positivity
  have hβcγ : min r₁ (min r₂ (1 / 200) / 2000) < min r₂ (1 / 200) / 1000 :=
    (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hQ⟩ := h _ _ hβc hβcγ hγc hγc1
  exact ⟨{
    toC14PreCirc := p
    βc := min r₁ (min r₂ (1 / 200) / 2000)
    γc := min r₂ (1 / 200)
    σ₀ := σ₀
    Δ₀ := Δ₀
    βc_pos := hβc
    βc_lt := hβcγ
    γc_pos := hγc
    γc_lt := hγc1
    σ₀_pos := hσ₀
    Δ₀_pos := hΔ₀ }, rfl, min_le_left _ _, min_le_left _ _, hQ⟩

/-- **Stage 3**: `β₂ ≤ r` with `β₂ ≤ β₀`, `β₂ ≤ 10⁻⁷`, `β₂ ≤ γ_T/20` (the producer's binder group
`β₂ Δ` is split legally: nothing is produced between them). -/
theorem c14_stage_excl_FAM2b (p : C14PreCollar) {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ → Prop}
    (h : ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ p.β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → p.Δ₀ ≤ Δ → Q β₂ Δ) :
    ∃ q : C14PreExcl, q.toC14PreCollar = p ∧ q.β₂ ≤ r ∧
      ∀ Δ : ℝ, 100 / q.β₂ < Δ → q.Δ₀ ≤ Δ → Q q.β₂ Δ := by
  have hβ₀ := p.β₀_pos
  have hT := p.γT_pos
  have hβ : 0 < min p.β₀ (min r (min (1 / 10000000) (p.γT / 20))) := by positivity
  have h7 : min p.β₀ (min r (min (1 / 10000000) (p.γT / 20))) ≤ 1 / 10000000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hβ1 : min p.β₀ (min r (min (1 / 10000000) (p.γT / 20))) < 1 / 100 :=
    h7.trans_lt (by norm_num)
  refine ⟨{
    toC14PreCollar := p
    β₂ := min p.β₀ (min r (min (1 / 10000000) (p.γT / 20)))
    β₂_pos := hβ
    β₂_le := min_le_left _ _
    β₂_lt := hβ1
    β₂_le7 := h7
    β₂_le_γT := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)) },
    rfl, (min_le_right _ _).trans (min_le_left _ _), fun Δ hΔ hΔ₀ => ?_⟩
  exact h _ Δ hβ (min_le_left _ _) hβ1 hΔ hΔ₀

/-- **Stage 4**: `r ≤ Δ` with `100/β₂ < Δ`, `Δ₀ ≤ Δ`, `10⁶ < Δ` and the root budget
`504000 (4000/γc)² < Δ` reserved; the producer's `τ₀, bc₀`. -/
theorem c14_stage_scale_FAM2b (p : C14PreExcl) (r : ℝ) {Q : ℝ → ℝ → ℝ → Prop}
    (h : ∀ Δ : ℝ, 100 / p.β₂ < Δ → p.Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧ Q Δ τ₀ bc₀) :
    ∃ q : C14PreScale, q.toC14PreExcl = p ∧ r ≤ q.Δ ∧ Q q.Δ q.τ₀ q.bc₀ := by
  set Δ := max (max p.Δ₀ r) (max (100 / p.β₂ + 1)
    (max (504000 * (4000 / p.γc) ^ 2 + 1) (1000000 + 1))) with hΔd
  have h1 : 100 / p.β₂ < Δ :=
    (lt_add_one _).trans_le ((le_max_left _ _).trans (le_max_right _ _))
  have h2 : p.Δ₀ ≤ Δ := (le_max_left _ _).trans (le_max_left _ _)
  have h3 : r ≤ Δ := (le_max_right _ _).trans (le_max_left _ _)
  have h4 : 504000 * (4000 / p.γc) ^ 2 < Δ :=
    (lt_add_one _).trans_le ((le_max_left _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))
  have h5 : (1000000 : ℝ) < Δ :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hQ⟩ := h Δ h1 h2
  exact ⟨{
    toC14PreExcl := p
    Δ := Δ
    τ₀ := τ₀
    bc₀ := bc₀
    Δ_gt := h1
    Δ₀_le := h2
    Δ_gt6 := h5
    Δ_root := h4
    τ₀_pos := hτ₀
    bc₀_pos := hbc₀ }, rfl, h3, hQ⟩

/-- `140√τ < ε²/20` once `0 ≤ τ < (ε²/2800)²`. -/
theorem c14_tau_sqrt_FAM2b {ε τ : ℝ} (hε : 0 < ε) (hτ0 : 0 ≤ τ) (hτ : τ < (ε ^ 2 / 2800) ^ 2) :
    140 * Real.sqrt τ < ε ^ 2 / 20 := by
  have h : Real.sqrt τ < ε ^ 2 / 2800 := by
    rw [show ε ^ 2 / 2800 = Real.sqrt ((ε ^ 2 / 2800) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt hτ0 hτ
  linarith

/-- `τ ≤ β₂/(8Δ)` with `0 < β₂, Δ` and `0 ≤ τ` gives `4τΔ < β₂`. -/
theorem c14_tau_delta_FAM2b {τ Δ β₂ : ℝ} (hΔ : 0 < Δ) (hβ₂ : 0 < β₂)
    (hτ : τ ≤ β₂ / (8 * Δ)) : 4 * τ * Δ < β₂ := by
  have h := (le_div_iff₀ (by positivity)).mp hτ
  nlinarith

/-- `x ≤ c / 2` with `0 < c` gives `x < c`. -/
theorem c14_half_FAM2b {x c : ℝ} (hc : 0 < c) (h : x ≤ c / 2) : x < c := by linarith

/-- **Stage 5**: `σc ε μ τ` (below their requests, with C14-KC's `σc ≤ 10⁻¹⁰`, `τ ≤ 10⁻³⁰`, the
root budget and PBR's bounds), then `s b' s'` (one stage for the requests: nothing is produced
between `τ` and `s`); the producer's `a₀, b₁`; then the free `σ = min(a₂, ϑ₃, a₀)`. -/
theorem c14_stage_edge_FAM2b (p : C14PreScale) {rσc rε rμ rτ rs rb' rs' : ℝ} (hrσc : 0 < rσc)
    (hrε : 0 < rε) (hrμ : 0 < rμ) (hrτ : 0 < rτ) (hrs : 0 < rs) (hrb' : 0 < rb') (hrs' : 0 < rs')
    {Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ p.σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ →
        μ ≤ 1 / 1000000 → 0 < τ → τ ≤ p.τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 →
        μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * p.Δ) → s' < 1 / (1000000 * p.Δ) →
        b' < τ * p.Δ / 1000000000 → s' < τ * p.Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ p.a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
        Q σc ε μ τ s b' s' a₀ b₁ σ) :
    ∃ q : C14PreEdge, q.toC14PreScale = p ∧ q.σc ≤ rσc ∧ q.ε ≤ rε ∧ q.μ ≤ rμ ∧ q.τ ≤ rτ ∧
      q.s ≤ rs ∧ q.b' ≤ rb' ∧ q.s' ≤ rs' ∧ Q q.σc q.ε q.μ q.τ q.s q.b' q.s' q.a₀ q.b₁ q.σ := by
  have hσ₀ := p.σ₀_pos
  have hτ₀ := p.τ₀_pos
  have hγc := p.γc_pos
  have hβ₂ := p.β₂_pos
  have hΔ : 0 < p.Δ := by linarith [p.Δ_gt6]
  have hthr := threeSplittingExclusionThreshold_pos.{0, 0}
  -- σc
  obtain ⟨σc, hσcd⟩ : ∃ σc : ℝ, σc = min (min p.σ₀ rσc) (1 / 10 ^ 10) := ⟨_, rfl⟩
  have hσc : 0 < σc := by rw [hσcd]; positivity
  have hσcσ₀ : σc ≤ p.σ₀ := by rw [hσcd]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hσcR : σc ≤ rσc := by rw [hσcd]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hσc10 : σc ≤ 1 / 10 ^ 10 := by rw [hσcd]; exact min_le_right _ _
  have hσc1 : σc < 1 := hσc10.trans_lt (by norm_num)
  -- ε
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min rε (min (1 / 10 ^ 8) (p.γc / 16000)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; positivity
  have hεR : ε ≤ rε := by rw [hεd]; exact min_le_left _ _
  have hε8 : ε ≤ 1 / 10 ^ 8 := by rw [hεd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεγ : ε < p.γc / 8000 := by
    have : ε ≤ p.γc / 16000 := by rw [hεd]; exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hε1 : ε < 1 / 100 := hε8.trans_lt (by norm_num)
  -- μ
  obtain ⟨μ, hμd⟩ : ∃ μ : ℝ, μ = min rμ (1 / (2 * 10 ^ 8)) := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμd]; positivity
  have hμR : μ ≤ rμ := by rw [hμd]; exact min_le_left _ _
  have hμh : μ ≤ 1 / (2 * 10 ^ 8) := by rw [hμd]; exact min_le_right _ _
  have hμ8 : μ ≤ 1 / 10 ^ 8 := hμh.trans (by norm_num)
  have hμ8' : μ < 1 / 10 ^ 8 := hμh.trans_lt (by norm_num)
  have hμ6 : μ ≤ 1 / 1000000 := hμh.trans (by norm_num)
  -- τ
  obtain ⟨τ, hτd⟩ : ∃ τ : ℝ, τ = min p.τ₀ (min rτ (min (1 / 10 ^ 30)
      (min ((p.γc / 4000) ^ 2 / 7560) (min ((ε ^ 2 / 2800) ^ 2 / 2) (p.β₂ / (8 * p.Δ)))))) :=
    ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτd]; positivity
  have hττ₀ : τ ≤ p.τ₀ := by rw [hτd]; exact min_le_left _ _
  have hτR : τ ≤ rτ := by rw [hτd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hτ30 : τ ≤ 1 / 10 ^ 30 := by
    rw [hτd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ8 : τ < 1 / 10 ^ 8 := hτ30.trans_lt (by norm_num)
  have hτroot : τ < (p.γc / 4000) ^ 2 / 3780 := by
    have : τ ≤ (p.γc / 4000) ^ 2 / 7560 := by
      rw [hτd]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _)))
    have hK : 0 < (p.γc / 4000) ^ 2 := by positivity
    linarith
  have hτε : τ < (ε ^ 2 / 2800) ^ 2 := by
    have : τ ≤ (ε ^ 2 / 2800) ^ 2 / 2 := by
      rw [hτd]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have hK : 0 < (ε ^ 2 / 2800) ^ 2 := by positivity
    linarith
  have hτΔ : 4 * τ * p.Δ < p.β₂ := by
    refine c14_tau_delta_FAM2b hΔ hβ₂ ?_
    rw [hτd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hθ := c14_tau_sqrt_FAM2b hε hτ.le hτε
  -- b', s'
  obtain ⟨b', hb'd⟩ : ∃ b' : ℝ, b' = min rb' (min (1 / (2 * (1000000 * p.Δ)))
      (min (τ * p.Δ / (2 * 1000000000)) (1 / (2 * 10 ^ 8)))) := ⟨_, rfl⟩
  have hb' : 0 < b' := by rw [hb'd]; positivity
  have hb'R : b' ≤ rb' := by rw [hb'd]; exact min_le_left _ _
  have hb'D : b' < 1 / (1000000 * p.Δ) := by
    refine c14_half_lt_FAM one_pos (by positivity) ?_
    rw [hb'd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hb'E : b' < τ * p.Δ / 1000000000 := by
    refine c14_half_lt_FAM (by positivity) (by norm_num) ?_
    rw [hb'd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb'8 : b' < 1 / 10 ^ 8 := by
    refine c14_half_lt_FAM one_pos (by norm_num) ?_
    rw [hb'd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s', hs'd⟩ : ∃ s' : ℝ, s' = min rs' (min (1 / (2 * (1000000 * p.Δ)))
      (min (τ * p.Δ / (2 * 1000000000)) (1 / (2 * 10 ^ 8)))) := ⟨_, rfl⟩
  have hs' : 0 < s' := by rw [hs'd]; positivity
  have hs'R : s' ≤ rs' := by rw [hs'd]; exact min_le_left _ _
  have hs'D : s' < 1 / (1000000 * p.Δ) := by
    refine c14_half_lt_FAM one_pos (by positivity) ?_
    rw [hs'd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs'E : s' < τ * p.Δ / 1000000000 := by
    refine c14_half_lt_FAM (by positivity) (by norm_num) ?_
    rw [hs'd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs'8 : s' < 1 / 10 ^ 8 := by
    refine c14_half_lt_FAM one_pos (by norm_num) ?_
    rw [hs'd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- s
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = min rs (min (min b' s' / (2 * 100000)) (1 / (2 * 10 ^ 6))) :=
    ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsd]; positivity
  have hsR : s ≤ rs := by rw [hsd]; exact min_le_left _ _
  have hs6 : s < 1 / 10 ^ 6 := by
    refine c14_half_lt_FAM one_pos (by norm_num) ?_
    rw [hsd]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hs1 : s < 1 / 100 := hs6.trans (by norm_num)
  have hsm : s ≤ min b' s' / (2 * 100000) := by
    rw [hsd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hsb' : s < b' / 100000 :=
    c14_half_lt_FAM hb' (by norm_num) (hsm.trans (div_le_div_of_nonneg_right (min_le_left _ _)
      (by norm_num)))
  have hss' : s < s' / 100000 :=
    c14_half_lt_FAM hs' (by norm_num) (hsm.trans (div_le_div_of_nonneg_right (min_le_right _ _)
      (by norm_num)))
  obtain ⟨a₀, b₁, ha₀, hb₁, hQ⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ6 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hs1 hsb' hss' hb'D hs'D hb'E hs'E
  have ha₂ := p.a₂_pos
  have hσ : 0 < min (min p.a₂ threeSplittingExclusionThreshold.{0, 0}) a₀ := by positivity
  exact ⟨{
    toC14PreScale := p
    σc := σc
    ε := ε
    μ := μ
    τ := τ
    s := s
    b' := b'
    s' := s'
    a₀ := a₀
    b₁ := b₁
    σ := min (min p.a₂ threeSplittingExclusionThreshold.{0, 0}) a₀
    σc_pos := hσc
    σc_le := hσcσ₀
    σc_lt := hσc1
    ε_pos := hε
    ε_lt := hε1
    μ_pos := hμ
    μ_le := hμ6
    τ_pos := hτ
    τ_le := hττ₀
    τ_sqrt := hθ
    ε_le8 := hε8
    μ_le8 := hμ8
    s_pos := hs
    s_lt := hs1
    s_lt_b' := hsb'
    s_lt_s' := hss'
    b'_lt := hb'D
    s'_lt := hs'D
    b'_lt_τ := hb'E
    s'_lt_τ := hs'E
    a₀_pos := ha₀
    b₁_pos := hb₁
    σ_pos := hσ
    σ_le_a₂ := (min_le_left _ _).trans (min_le_left _ _)
    σ_le_thr := (min_le_left _ _).trans (min_le_right _ _)
    σ_le_a₀ := min_le_right _ _
    σc_le10 := hσc10
    τ_le30 := hτ30
    ε_root := hεγ
    τ_root := hτroot
    τ_ε := hτε
    μ_lt8 := hμ8'
    τ_lt8 := hτ8
    τΔ_lt := hτΔ
    b'_lt8 := hb'8
    s'_lt8 := hs'8
    s_lt6 := hs6 }, rfl, hσcR, hεR, hμR, hτR, hsR, hb'R, hs'R,
    hQ _ hσ ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)⟩

/-- **The root budget from its reserved parts** (review 50, A2): `ε < γc/8000`,
`Δ > 504000 (4000/γc)²`, `Λ < γc/(1200000Δ)`, `τ < (γc/4000)²/3780` give
`2ε + 300ΔΛ + √(504000/Δ + 3780τ) < γc/1000`. -/
theorem c14_staged_budget_FAM2b {γc ε Δ Λ τ : ℝ} (hγc : 0 < γc) (hε : ε < γc / 8000)
    (hΔ : 504000 * (4000 / γc) ^ 2 < Δ) (hΛ : Λ < γc / (1200000 * Δ)) (hτ0 : 0 ≤ τ)
    (hτ : τ < (γc / 4000) ^ 2 / 3780) :
    2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 := by
  have hK : 0 < γc / 4000 := by positivity
  have hK2 : 0 < (γc / 4000) ^ 2 := by positivity
  have he : (4000 / γc) ^ 2 = 1 / (γc / 4000) ^ 2 := by rw [div_pow, div_pow, one_div_div]
  rw [he, mul_one_div, div_lt_iff₀ hK2] at hΔ
  have hΔpos : 0 < Δ := by nlinarith
  have h1 : 504000 / Δ < (γc / 4000) ^ 2 := by
    rw [div_lt_iff₀ hΔpos]; linarith
  have h2 : 0 ≤ 504000 / Δ + 3780 * τ := by positivity
  have h3 : Real.sqrt (504000 / Δ + 3780 * τ) < 3 / 2 * (γc / 4000) := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  have h4 : 300 * Δ * Λ < γc / 4000 := by
    have := (lt_div_iff₀ (by positivity)).mp hΛ
    nlinarith
  linarith

/-- **Stage 6**: `Λ ≤ r` with the producer's six conditions, the root budget part
`Λ < γc/(1200000Δ)` and each (RegScale) budget; the producer's `w₀`. -/
theorem c14_stage_lip_FAM2b (p : C14PreEdge) {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ → Prop}
    (h : ∀ Λ : ℝ, 0 < Λ → p.Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * p.Δ) →
        100 * p.Δ * Λ ≤ 1 / 1000000 →
        2 * p.ε + 300 * p.Δ * Λ + Real.sqrt (504000 / p.Δ + 3780 * p.τ) < p.γc / 1000 →
        Λ < p.s' / (100000000 * p.Δ ^ 2) → 100 * p.Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ Q Λ w₀) :
    ∃ q : C14PreLip, q.toC14PreEdge = p ∧ q.Λ ≤ r ∧ Q q.Λ q.w₀ := by
  have hΔ : 0 < p.Δ := by linarith [p.Δ_gt6]
  have hγc := p.γc_pos
  have hs'p : 0 < p.s' := by have := p.s_pos; have := p.s_lt_s'; linarith
  have hCρ := p.Cρ_pos
  have he₁ := p.e₁_pos
  have hC₁ := p.C₁_pos
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℝ, Λ = min r (min (1 / (10 ^ 12 * p.Δ))
      (min (p.γc / (2 * (1200000 * p.Δ))) (min (p.s' / (2 * (100000000 * p.Δ ^ 2)))
      (min (1 / (2000000 * p.Cρ * p.Δ)) (p.e₁ / (2000 * p.C₁ * p.Δ)))))) := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by rw [hΛd]; positivity
  have hΛR : Λ ≤ r := by rw [hΛd]; exact min_le_left _ _
  have hΛ12 : Λ ≤ 1 / (10 ^ 12 * p.Δ) := by
    rw [hΛd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hΛγ : Λ ≤ p.γc / (2 * (1200000 * p.Δ)) := by
    rw [hΛd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΛs : Λ ≤ p.s' / (2 * (100000000 * p.Δ ^ 2)) := by
    rw [hΛd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hΛC : Λ ≤ 1 / (2000000 * p.Cρ * p.Δ) := by
    rw [hΛd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hΛe : Λ ≤ p.e₁ / (2000 * p.C₁ * p.Δ) := by
    rw [hΛd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hΔΛ : Λ * (10 ^ 12 * p.Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp hΛ12
  have hc1 : p.Δ * Λ * 2000000 ≤ 1 / 100 := by nlinarith
  have hc2 : Λ < 1 / (1000000 * p.Δ) :=
    hΛ12.trans_lt (div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith))
  have hc3 : 100 * p.Δ * Λ ≤ 1 / 1000000 := by nlinarith
  have hroot : Λ < p.γc / (1200000 * p.Δ) := c14_half_lt_FAM hγc (by positivity) hΛγ
  have hbudget := c14_staged_budget_FAM2b hγc p.ε_root p.Δ_root hroot p.τ_pos.le p.τ_root
  have hc5 : Λ < p.s' / (100000000 * p.Δ ^ 2) := c14_half_lt_FAM hs'p (by positivity) hΛs
  have hc6 : 100 * p.Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hL : 1000000 * p.Δ * Λ < 1 / 100000 := by nlinarith
  have h8 : 100 * p.Δ * Λ < 1 / 10 ^ 8 := by nlinarith
  have hCρΔΛ : p.Cρ * p.Δ * Λ < 1 / 1000000 := by
    have := (le_div_iff₀ (by positivity)).mp hΛC
    nlinarith
  have he₁ΔΛ : p.Δ * Λ < p.e₁ / (1000 * p.C₁) := by
    have := (le_div_iff₀ (by positivity)).mp hΛe
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hone : 200000000 * p.Δ * Λ < 1 := by nlinarith
  obtain ⟨w₀, hw₀, hQ⟩ := h Λ hΛ hc1 hc2 hc3 hbudget hc5 hc6
  exact ⟨{
    toC14PreEdge := p
    Λ := Λ
    w₀ := w₀
    Λ_pos := hΛ
    Λ_c1 := hc1
    Λ_c2 := hc2
    Λ_c3 := hc3
    budget := hbudget
    Λ_c5 := hc5
    Λ_c6 := hc6
    Λ_root := hroot
    LΛ_lt := hL
    ΔΛ_lt8 := h8
    CρΔΛ_lt := hCρΔΛ
    ΔΛ_lt_e₁ := he₁ΔΛ
    ΔΛ_lt_one := hone
    w₀_pos := hw₀ }, rfl, hΛR, hQ⟩

/-- **Stage 7**: `w ≤ r` with `w < w₀`, `w < 4π/3`; the producer's `bd₀`. -/
theorem c14_stage_vol_FAM2b (p : C14PreLip) {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ → Prop}
    (h : ∀ w : ℝ, 0 < w → w < p.w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧ Q w bd₀) :
    ∃ q : C14PreVol, q.toC14PreLip = p ∧ q.w ≤ r ∧ Q q.w q.bd₀ := by
  have hw₀ := p.w₀_pos
  have hw : 0 < min r (min (p.w₀ / 2) 1) := by positivity
  have hww : min r (min (p.w₀ / 2) 1) < p.w₀ :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hwπ : min r (min (p.w₀ / 2) 1) < 4 * Real.pi / 3 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith [Real.pi_gt_three])
  obtain ⟨bd₀, hbd₀, hQ⟩ := h _ hw hww hwπ
  exact ⟨{
    toC14PreLip := p
    w := min r (min (p.w₀ / 2) 1)
    bd₀ := bd₀
    w_pos := hw
    w_lt := hww
    w_lt_pi := hwπ
    bd₀_pos := hbd₀ }, rfl, min_le_left _ _, hQ⟩

/-- **Stage 8**: `b ≤ r` with the producer's conditions and R20's `b < 10⁻⁶`. -/
theorem c14_stage_split_FAM2b (p : C14PreVol) {r : ℝ} (hr : 0 < r) {Q : ℝ → Prop}
    (h : ∀ b : ℝ, 0 < b → b < p.s / 100000 → b < p.bc₀ → b < p.b₁ → 100 * p.Δ < b⁻¹ →
      b < p.bd₀ → Q b) :
    ∃ q : C14PreSplit, q.toC14PreVol = p ∧ q.b ≤ r ∧ Q q.b := by
  have hΔ : 0 < p.Δ := by linarith [p.Δ_gt6]
  have hs := p.s_pos
  have hbc₀ := p.bc₀_pos
  have hb₁ := p.b₁_pos
  have hbd₀ := p.bd₀_pos
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = min r (min (p.s / (2 * 100000)) (min (p.bc₀ / 2)
      (min (p.b₁ / 2) (min (p.bd₀ / 2) (min (1 / (200 * p.Δ)) (1 / (2 * 10 ^ 6))))))) :=
    ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbd]; positivity
  have hbR : b ≤ r := by rw [hbd]; exact min_le_left _ _
  have hbs : b < p.s / 100000 := by
    refine c14_half_lt_FAM hs (by norm_num) ?_
    rw [hbd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hbc : b < p.bc₀ := by
    refine c14_half_FAM2b hbc₀ ?_
    rw [hbd]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbb₁ : b < p.b₁ := by
    refine c14_half_FAM2b hb₁ ?_
    rw [hbd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hbbd : b < p.bd₀ := by
    refine c14_half_FAM2b hbd₀ ?_
    rw [hbd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hinv : 100 * p.Δ < b⁻¹ := by
    refine c14_b_inv_FAM hb hΔ ?_
    rw [hbd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hb6 : b < 1 / 10 ^ 6 := by
    refine c14_half_lt_FAM one_pos (by norm_num) ?_
    rw [hbd]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  exact ⟨{
    toC14PreVol := p
    b := b
    b_pos := hb
    b_lt_s := hbs
    b_lt_bc₀ := hbc
    b_lt_b₁ := hbb₁
    b_inv := hinv
    b_lt_bd₀ := hbbd
    b_lt6 := hb6 }, rfl, hbR, h b hb hbs hbc hbb₁ hinv hbbd⟩

/-- **Stage 9**: `σs ≤ r₁` with `σs ≤ 1/100`, `vs ≤ r₂`; the producer's `b₀`. -/
theorem c14_stage_slim_FAM2b (p : C14PreSplit) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    {Q : ℝ → ℝ → ℝ → Prop}
    (h : ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧ Q σs vs b₀) :
    ∃ q : C14PreSlim, q.toC14PreSplit = p ∧ q.σs ≤ r₁ ∧ q.vs ≤ r₂ ∧ Q q.σs q.vs q.b₀ := by
  have hσs : 0 < min r₁ (1 / 100) := by positivity
  obtain ⟨b₀, hb₀, hQ⟩ := h _ r₂ hσs (min_le_right _ _) hr₂
  exact ⟨{
    toC14PreSplit := p
    σs := min r₁ (1 / 100)
    vs := r₂
    b₀ := b₀
    σs_pos := hσs
    σs_le := min_le_right _ _
    vs_pos := hr₂
    b₀_pos := hb₀ }, rfl, min_le_left _ _, le_rfl, hQ⟩

/-- **Stage 10**: `ζ ≤ r_ζ` is fixed BEFORE `β₁ ≤ r_β` (the producer needs `β₁ < ζ`); then
`β = (β₁, β₂, ϑ₃)` with `β 3 = ϑ₃`. The producer's binder group `ζ cap` is split legally. -/
theorem c14_stage_beta_FAM2b (p : C14PreSlim) {rζ rβ : ℝ} (hrζ : 0 < rζ) (hrβ : 0 < rβ)
    {Q : (ℕ → ℝ) → ℝ → ℝ → Prop}
    (h : ∀ β : ℕ → ℝ, β 2 = p.β₂ → 0 < β 1 → β 1 < p.b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap → Q β ζ cap) :
    ∃ q : C14PreBeta, q.toC14PreSlim = p ∧ q.ζ ≤ rζ ∧ q.β 1 ≤ rβ ∧
      ∀ cap : ℝ, 0 < cap → Q q.β q.ζ cap := by
  have hb₀ := p.b₀_pos
  obtain ⟨ζ, hζd⟩ : ∃ ζ : ℝ, ζ = min rζ (1 / 2) := ⟨_, rfl⟩
  have hζ : 0 < ζ := by rw [hζd]; positivity
  have hζR : ζ ≤ rζ := by rw [hζd]; exact min_le_left _ _
  have hζ1 : ζ < 1 := by rw [hζd]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨β₁, hβ₁d⟩ : ∃ β₁ : ℝ, β₁ = min (p.b₀ / 2) (min (ζ / 2) rβ) := ⟨_, rfl⟩
  have hβ₁ : 0 < β₁ := by rw [hβ₁d]; positivity
  have hβ₁b₀ : β₁ < p.b₀ := by rw [hβ₁d]; exact (min_le_left _ _).trans_lt (by linarith)
  have hβ₁ζ : β₁ < ζ := by
    rw [hβ₁d]; exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hβ₁R : β₁ ≤ rβ := by rw [hβ₁d]; exact (min_le_right _ _).trans (min_le_right _ _)
  let β : ℕ → ℝ := fun n =>
    if n = 2 then p.β₂ else if n = 3 then threeSplittingExclusionThreshold.{0, 0} else β₁
  have hβ2 : β 2 = p.β₂ := by simp [β]
  have hβ1 : β 1 = β₁ := by simp [β]
  have hβ3 : β 3 = threeSplittingExclusionThreshold.{0, 0} := by simp [β]
  have h1 : 0 < β 1 := by rw [hβ1]; exact hβ₁
  have h2 : β 1 < p.b₀ := by rw [hβ1]; exact hβ₁b₀
  have h3 : β 1 < ζ := by rw [hβ1]; exact hβ₁ζ
  have h4 : β 1 < 1 := h3.trans hζ1
  have h5 : β 1 ≤ rβ := by rw [hβ1]; exact hβ₁R
  have hQ := h β hβ2 h1 h2 h4 hβ3.le
  exact ⟨{
    toC14PreSlim := p
    ζ := ζ
    β := β
    ζ_lt := hζ1
    β_two := hβ2
    β₁_pos := h1
    β₁_lt_b₀ := h2
    β₁_lt := h4
    β_three := hβ3
    β₁_lt_ζ := h3 }, rfl, hζR, h5, fun cap hcap => hQ ζ cap h3 hζ1 hcap⟩

/-- **Stage 11**: `cap ≤ r` with `cap ≤ 1/100` (ZSP's `ε₀`); the producer's `εr < cap`, `δ'`,
`Λz`. -/
theorem c14_stage_zero_FAM2b (p : C14PreBeta) {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ → ℝ → Prop}
    (h : ∀ cap : ℝ, 0 < cap → ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧
      0 < Λ' ∧ Q εr δ' Λ') :
    ∃ q : C14PreZero, q.toC14PreBeta = p ∧ q.cap ≤ r ∧ Q q.εr q.δ' q.Λz := by
  have hcap : 0 < min r (1 / 100) := by positivity
  obtain ⟨εr, δ', Λz, hεr, hεr4, hεrcap, hδ', hΛz, hQ⟩ := h _ hcap
  exact ⟨{
    toC14PreBeta := p
    cap := min r (1 / 100)
    εr := εr
    δ' := δ'
    Λz := Λz
    cap_pos := hcap
    cap_le := min_le_right _ _
    εr_pos := hεr
    εr_lt := hεr4
    εr_lt_cap := hεrcap
    δ'_pos := hδ'
    Λz_pos := hΛz }, rfl, min_le_left _ _, hQ⟩

/-- **Stage 12**: `T ≥ r_T` with `20Λz ≤ T`, `1600 · 10⁶Δ ≤ T`; `e ≤ r_e` with `e < 1/1000`. -/
theorem c14_stage_final_FAM2b (p : C14PreZero) (rT : ℝ) {re : ℝ} (hre : 0 < re)
    {Q : ℝ → ℝ → Prop}
    (h : ∀ T : ℝ, 0 < T → 20 * p.Λz ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 → Q T e) :
    ∃ q : C14PreFinal, q.toC14PreZero = p ∧ rT ≤ q.T ∧ q.e ≤ re ∧ Q q.T q.e := by
  have hΛz := p.Λz_pos
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = max (max (20 * p.Λz) rT) (1600 * (1000000 * p.Δ)) := ⟨_, rfl⟩
  have hTΛ : 20 * p.Λz ≤ T := by rw [hTd]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hTR : rT ≤ T := by rw [hTd]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hTΔ : 1600 * (1000000 * p.Δ) ≤ T := by rw [hTd]; exact le_max_right _ _
  have hT : 0 < T := (by positivity : (0 : ℝ) < 20 * p.Λz).trans_le hTΛ
  have he : 0 < min re (1 / 2000) := by positivity
  have he3 : min re (1 / 2000) < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he1 : min re (1 / 2000) < 1 / 40 := he3.trans (by norm_num)
  exact ⟨{
    toC14PreZero := p
    T := T
    e := min re (1 / 2000)
    T_pos := hT
    T_Λz := hTΛ
    T_Δ := hTΔ
    e_pos := he
    e_lt := he1
    e_lt3 := he3 }, rfl, hTR, min_le_left _ _, h T hT hTΛ _ he he1⟩

/-- CGP01's numerical hypotheses (review 50, verdict 8) at every admissible prefix: `0 ≤ Λ`,
`0 < Δ`, `μ, τ ≤ 1/100`, `100ΔΛ ≤ 1/100`, `e ≤ 1/8`. -/
theorem C14PreFinal.cgp01_numerics_FAM2b (P : C14PreFinal) :
    0 ≤ P.Λ ∧ 0 < P.Δ ∧ P.μ ≤ 1 / 100 ∧ P.τ ≤ 1 / 100 ∧ 100 * P.Δ * P.Λ ≤ 1 / 100 ∧
      P.e ≤ 1 / 8 := by
  refine ⟨P.Λ_pos.le, by linarith [P.Δ_gt6], P.μ_le.trans (by norm_num),
    P.τ_le30.trans (by norm_num), P.Λ_c3.trans (by norm_num), ?_⟩
  linarith [P.e_lt]

/-- The Gram certificate's numerical side (review 50, verdict 6) at every admissible prefix:
`0 < γ_T ≤ 1`, `γ ≤ γ_T/20`, `β 2 ≤ min(10⁻⁷, γ_T/20)`. -/
theorem C14PreFinal.gram_numerics_FAM2b (P : C14PreFinal) :
    0 < P.γT ∧ P.γT ≤ 1 ∧ P.γ ≤ P.γT / 20 ∧ P.β 2 ≤ 1 / 10000000 ∧ P.β 2 ≤ P.γT / 20 := by
  rw [P.β_two]
  exact ⟨P.γT_pos, P.γT_le, P.γ_le_γT, P.β₂_le7, P.β₂_le_γT⟩

/-! ### The staged assignment -/

/-- **ONE staged admissible assignment** (review 50, A1–A3; lead decision T50-2): for the external
tolerances `t` and every staged requests record `Rq` there is ONE admissible prefix `P` (every
parameter of `eventually_nonempty_localChartPacketsC14` together with the producer's threshold
outputs, each stage below the request evaluated at the prefix BEFORE it) such that, for every
standing sequence, with the joint zero output `V ≥ T`, `δ < δ'` and
`Lmax := 1 + max(1, max(400V, Rq.Lmax P V))`, every late member carries the final family
`LocalChartPacketsC14` with exactly these parameters. -/
theorem exists_c14_staged_assignment (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequests) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.Meets P ∧
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
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        400 * V < c14Lmax Rq P V ∧ Rq.Lmax P V ≤ c14Lmax Rq P V ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax Rq P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14 K hK A hA
  obtain ⟨p1, rfl, rfl, h1γ, h⟩ := c14_stage_circ_FAM2b t ha₂ (Rq.γ_pos t) h
  obtain ⟨p2, rfl, h2βc, h2γc, h⟩ := c14_stage_collar_FAM2b p1 (Rq.βc_pos p1) (Rq.γc_pos p1) h
  obtain ⟨p3, rfl, h3β₂, h⟩ := c14_stage_excl_FAM2b p2 (Rq.β₂_pos p2) h
  obtain ⟨p4, rfl, h4Δ, h⟩ := c14_stage_scale_FAM2b p3 (Rq.Δ p3) h
  obtain ⟨p5, rfl, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', h⟩ := c14_stage_edge_FAM2b p4
    (Rq.σc_pos p4) (Rq.ε_pos p4) (Rq.μ_pos p4) (Rq.τ_pos p4) (Rq.s_pos p4) (Rq.b'_pos p4)
    (Rq.s'_pos p4) h
  obtain ⟨p6, rfl, h6Λ, h⟩ := c14_stage_lip_FAM2b p5 (Rq.Λ_pos p5) h
  obtain ⟨p7, rfl, h7w, h⟩ := c14_stage_vol_FAM2b p6 (Rq.w_pos p6) h
  obtain ⟨p8, rfl, h8b, h⟩ := c14_stage_split_FAM2b p7 (Rq.b_pos p7) h
  obtain ⟨p9, rfl, h9σs, h9vs, h⟩ := c14_stage_slim_FAM2b p8 (Rq.σs_pos p8) (Rq.vs_pos p8) h
  obtain ⟨p10, rfl, h10ζ, h10β, h⟩ := c14_stage_beta_FAM2b p9 (Rq.ζ_pos p9) (Rq.β₁_pos p9) h
  obtain ⟨p11, rfl, h11cap, h⟩ := c14_stage_zero_FAM2b p10 (Rq.cap_pos p10) h
  obtain ⟨P, rfl, h12T, h12e, h⟩ := c14_stage_final_FAM2b p11 (Rq.T p11) (Rq.e_pos p11) h
  refine ⟨P, rfl, ⟨h1γ, h2γc, h2βc, h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', h6Λ, h7w,
    h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h X g hmetric α hα hstand hder hor
  exact ⟨V, hTV, δ, hδ, hδδ', c14Lmax_gt Rq P V, c14Lmax_ge Rq P V,
    hV _ (c14Lmax_pos Rq P V)⟩

end DifferentialGeometry.Geometry.Collapse
