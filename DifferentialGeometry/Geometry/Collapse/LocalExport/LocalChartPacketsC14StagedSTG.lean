import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14DensityStaged

/-!
# Staged requests with the collar request `3βc ≤ β₂` (final family `LocalChartPacketsC14D`)

Lane C14-STG. Lane C14-EDP6's collar → circle step (`edp06_collar_circle_C14`,
`eventually_edp06_collar_circle_EDP6`) needs `3βc ≤ β 2`: the collar's plane-map tolerance `βc` is a
separate parameter, fixed by the producer at stage 2, BEFORE `β₂` (stage 3). The request is met by
choosing, at stage 2, first `γc` and then `βc ≤ β₂/3`, where `β₂`'s stage-3 value
`min(β₀, r, 10⁻⁷, γ_T/20)` is already known — which needs `β₂`'s request `r` to be read at
`C14PreGcSTG` (`C14PreCirc` and `γc`, before `βc`): with the request read at `C14PreCollar` (as in
`C14StagedRequests`) the record `β₂ p := p.βc` would force `β₂ ≤ βc < 3βc`. TCP04's request
`β₂ < γc/1000` (B:5483) still reads only `C14PreGcSTG`.

* `C14PreGcSTG` (`C14PreCirc` and `γc`), `C14PreCollar.toGc_STG`;
* `C14StagedRequestsSTG`: `C14StagedRequests` verbatim except `β₂ : C14PreGcSTG → ℝ`;
  `C14StagedRequestsSTG.toC14` (the induced `C14StagedRequests`: `Meets`, `c14Lmax` and every
  delivered row apply through it), `.trivial`, `.inf` (`toC14_inf`: `inf` commutes with `toC14`);
  `C14StagedRequests.withEarlyβ₂_STG` (an old record with an early `β₂` request) and
  `C14StagedRequests.Meets.of_withEarlyβ₂_STG` (it meets the old record when the early request is
  below the old one).
* `c14_stage_collar_STG` (stage 2, `βc`'s request reads the chosen `γc`), `c14_stage_excl_STG`
  (stage 3 with the explicit value of `β₂`).
* `exists_c14d_staged_assignment_STG`: `exists_c14d_staged_assignment` with `3 * P.βc ≤ P.β 2`.

The old contract (`LocalChartPacketsC14Staged`, `LocalChartPacketsC14DensityStaged`) is kept.
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

/-! ### The prefix with `γc`, and the STG record -/

/-- **The prefix with the collar quality `γc`** (lane C14-STG): `C14PreCirc` and `γc` (the
producer's binder group `βc γc` is split legally: `γc` first, nothing is produced between them).
`β₂`'s request reads this prefix. -/
structure C14PreGcSTG extends C14PreCirc where
  γc : ℝ
  γc_pos : 0 < γc
  γc_lt : γc < 1 / 100

/-- The `γc`-prefix of a stage-2 prefix. -/
def C14PreCollar.toGc_STG (q : C14PreCollar) : C14PreGcSTG where
  toC14PreCirc := q.toC14PreCirc
  γc := q.γc
  γc_pos := q.γc_pos
  γc_lt := q.γc_lt

/-- **The staged requests contract with the collar request `3βc ≤ β₂`** (lane C14-STG): the record
`C14StagedRequests` verbatim except that the `β₂` request reads the prefix `C14PreGcSTG`
(`C14PreCirc` and `γc`) BEFORE `βc` (the lower request `β₂ ≥ 3βc` is met only if every upper
request on `β₂` is known when `βc` is chosen; TCP04's `β₂ < γc/1000` stays expressible). Every
other request is read at the same prefix as in `C14StagedRequests`. -/
structure C14StagedRequestsSTG where
  γ : C14Tol → ℝ
  γc : C14PreCirc → ℝ
  βc : C14PreCirc → ℝ
  β₂ : C14PreGcSTG → ℝ
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

/-- **The induced `C14StagedRequests`**: the `β₂` request read through `C14PreCollar → C14PreGcSTG`;
every other request unchanged. -/
def C14StagedRequestsSTG.toC14 (R : C14StagedRequestsSTG) : C14StagedRequests where
  γ := R.γ
  γc := R.γc
  βc := R.βc
  β₂ p := R.β₂ p.toGc_STG
  Δ := R.Δ
  σc := R.σc
  ε := R.ε
  μ := R.μ
  τ := R.τ
  s := R.s
  b' := R.b'
  s' := R.s'
  Λ := R.Λ
  w := R.w
  b := R.b
  σs := R.σs
  vs := R.vs
  ζ := R.ζ
  β₁ := R.β₁
  cap := R.cap
  T := R.T
  e := R.e
  Lmax := R.Lmax
  γ_pos := R.γ_pos
  γc_pos := R.γc_pos
  βc_pos := R.βc_pos
  β₂_pos p := R.β₂_pos p.toGc_STG
  σc_pos := R.σc_pos
  ε_pos := R.ε_pos
  μ_pos := R.μ_pos
  τ_pos := R.τ_pos
  s_pos := R.s_pos
  b'_pos := R.b'_pos
  s'_pos := R.s'_pos
  Λ_pos := R.Λ_pos
  w_pos := R.w_pos
  b_pos := R.b_pos
  σs_pos := R.σs_pos
  vs_pos := R.vs_pos
  ζ_pos := R.ζ_pos
  β₁_pos := R.β₁_pos
  cap_pos := R.cap_pos
  e_pos := R.e_pos

/-- The trivial requests of the STG contract (every upper request `1`, every lower request `0`). -/
def C14StagedRequestsSTG.trivial : C14StagedRequestsSTG where
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

/-- **The common requests of two STG request records**: the minimum of every upper request and
the maximum of every lower request (as `C14StagedRequests.inf`). -/
def C14StagedRequestsSTG.inf (R₁ R₂ : C14StagedRequestsSTG) : C14StagedRequestsSTG where
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

/-- The common STG requests induce the common requests. -/
theorem C14StagedRequestsSTG.toC14_inf (R₁ R₂ : C14StagedRequestsSTG) :
    (R₁.inf R₂).toC14 = R₁.toC14.inf R₂.toC14 :=
  rfl

/-- **An old record with an early `β₂` request** `r` (read at `C14PreGcSTG`); every other request
of `R` unchanged. -/
def C14StagedRequests.withEarlyβ₂_STG (R : C14StagedRequests) (r : C14PreGcSTG → ℝ)
    (hr : ∀ p, 0 < r p) : C14StagedRequestsSTG where
  γ := R.γ
  γc := R.γc
  βc := R.βc
  β₂ := r
  Δ := R.Δ
  σc := R.σc
  ε := R.ε
  μ := R.μ
  τ := R.τ
  s := R.s
  b' := R.b'
  s' := R.s'
  Λ := R.Λ
  w := R.w
  b := R.b
  σs := R.σs
  vs := R.vs
  ζ := R.ζ
  β₁ := R.β₁
  cap := R.cap
  T := R.T
  e := R.e
  Lmax := R.Lmax
  γ_pos := R.γ_pos
  γc_pos := R.γc_pos
  βc_pos := R.βc_pos
  β₂_pos := hr
  σc_pos := R.σc_pos
  ε_pos := R.ε_pos
  μ_pos := R.μ_pos
  τ_pos := R.τ_pos
  s_pos := R.s_pos
  b'_pos := R.b'_pos
  s'_pos := R.s'_pos
  Λ_pos := R.Λ_pos
  w_pos := R.w_pos
  b_pos := R.b_pos
  σs_pos := R.σs_pos
  vs_pos := R.vs_pos
  ζ_pos := R.ζ_pos
  β₁_pos := R.β₁_pos
  cap_pos := R.cap_pos
  e_pos := R.e_pos

/-- A prefix meeting the record with the early `β₂` request `r` meets the old record `R` as soon as
`r` is below `R`'s `β₂` request (every delivered row record: `β₂`'s request reads only `C14Tol`). -/
theorem C14StagedRequests.Meets.of_withEarlyβ₂_STG {R : C14StagedRequests} {r : C14PreGcSTG → ℝ}
    {hr : ∀ p, 0 < r p} (hle : ∀ q : C14PreCollar, r q.toGc_STG ≤ R.β₂ q) {P : C14PreFinal}
    (h : (R.withEarlyβ₂_STG r hr).toC14.Meets P) : R.Meets P where
  γ_le := h.γ_le
  γc_le := h.γc_le
  βc_le := h.βc_le
  β₂_le := h.β₂_le.trans (hle _)
  Δ_ge := h.Δ_ge
  σc_le := h.σc_le
  ε_le := h.ε_le
  μ_le := h.μ_le
  τ_le := h.τ_le
  s_le := h.s_le
  b'_le := h.b'_le
  s'_le := h.s'_le
  Λ_le := h.Λ_le
  w_le := h.w_le
  b_le := h.b_le
  σs_le := h.σs_le
  vs_le := h.vs_le
  ζ_le := h.ζ_le
  β₁_le := h.β₁_le
  cap_le := h.cap_le
  T_ge := h.T_ge
  e_le := h.e_le

/-! ### Stages 2–3 with the reservation `3βc ≤ β₂` -/

/-- **`β₂`'s stage-3 value, known once `γc` is chosen**: `min(β₀, r, 10⁻⁷, γ_T/20)` with `r` the
early `β₂` request. Stage 2 chooses `βc ≤ c14β₂Value_STG Rq p / 3`. -/
def c14β₂Value_STG (Rq : C14StagedRequestsSTG) (p : C14PreGcSTG) : ℝ :=
  min p.β₀ (min (Rq.β₂ p) (min (1 / 10000000) (p.γT / 20)))

/-- `β₂`'s stage-3 value is positive. -/
theorem c14β₂Value_pos_STG (Rq : C14StagedRequestsSTG) (p : C14PreGcSTG) :
    0 < c14β₂Value_STG Rq p := by
  have := p.β₀_pos
  have := p.γT_pos
  have := Rq.β₂_pos p
  unfold c14β₂Value_STG
  positivity

/-- **Stage 2 with a `γc`-dependent `βc` request** (lane C14-STG): `c14_stage_collar_FAM2b`
verbatim, except that `βc`'s request `r₁` reads the prefix `C14PreGcSTG` with the chosen `γc` (the
binder group `βc γc` is split legally: `γc` first, nothing is produced between them). -/
theorem c14_stage_collar_STG (p : C14PreCirc) (r₁ : C14PreGcSTG → ℝ) (hr₁ : ∀ g, 0 < r₁ g)
    {r₂ : ℝ} (hr₂ : 0 < r₂)
    {Q : ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ Q βc γc σ₀ Δ₀) :
    ∃ q : C14PreCollar, q.toC14PreCirc = p ∧ q.βc ≤ r₁ q.toGc_STG ∧ q.γc ≤ r₂ ∧
      Q q.βc q.γc q.σ₀ q.Δ₀ := by
  have hγc : 0 < min r₂ (1 / 200) := by positivity
  have hγc1 : min r₂ (1 / 200) < 1 / 100 := (min_le_right _ _).trans_lt (by norm_num)
  let g : C14PreGcSTG :=
    { toC14PreCirc := p
      γc := min r₂ (1 / 200)
      γc_pos := hγc
      γc_lt := hγc1 }
  have hr₁g := hr₁ g
  have hβc : 0 < min (r₁ g) (min r₂ (1 / 200) / 2000) := by positivity
  have hβcγ : min (r₁ g) (min r₂ (1 / 200) / 2000) < min r₂ (1 / 200) / 1000 :=
    (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hQ⟩ := h _ _ hβc hβcγ hγc hγc1
  exact ⟨{
    toC14PreCirc := p
    βc := min (r₁ g) (min r₂ (1 / 200) / 2000)
    γc := min r₂ (1 / 200)
    σ₀ := σ₀
    Δ₀ := Δ₀
    βc_pos := hβc
    βc_lt := hβcγ
    γc_pos := hγc
    γc_lt := hγc1
    σ₀_pos := hσ₀
    Δ₀_pos := hΔ₀ }, rfl, min_le_left _ _, min_le_left _ _, hQ⟩

/-- **Stage 3 with the value of `β₂`** (lane C14-STG): `c14_stage_excl_FAM2b` verbatim, and `β₂` is
the explicit value `min(β₀, r, 10⁻⁷, γ_T/20)` (so a lower request reserved at stage 2 is kept). -/
theorem c14_stage_excl_STG (p : C14PreCollar) {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ → Prop}
    (h : ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ p.β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → p.Δ₀ ≤ Δ → Q β₂ Δ) :
    ∃ q : C14PreExcl, q.toC14PreCollar = p ∧ q.β₂ ≤ r ∧
      q.β₂ = min p.β₀ (min r (min (1 / 10000000) (p.γT / 20))) ∧
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
    rfl, (min_le_right _ _).trans (min_le_left _ _), rfl, fun Δ hΔ hΔ₀ => ?_⟩
  exact h _ Δ hβ (min_le_left _ _) hβ1 hΔ hΔ₀

/-! ### The staged assignment with `3βc ≤ β 2` -/

/-- **ONE staged admissible assignment for the family with LFR44 item 2, with the collar request
`3βc ≤ β 2`** (lane C14-STG; review 50, A1–A3; lead decision T50-2): for the external
tolerances `t` and every STG requests record `Rq` there is ONE admissible prefix `P` (every
parameter of `eventually_nonempty_localChartPacketsC14` together with the producer's threshold
outputs, each stage below the request evaluated at the prefix BEFORE it) such that, for every
standing sequence, with the joint zero output `V ≥ T`, `δ < δ'` and
`Lmax := 1 + max(1, max(400V, Rq.Lmax P V))`, every late member carries the final family
`LocalChartPacketsC14D` with exactly these parameters, and `3βc ≤ β 2` (lane C14-EDP6's request:
`γc` then `βc` are fixed at stage 2, `βc` below `β₂`'s stage-3 value divided by `3`; the proof of
`exists_c14d_staged_assignment` otherwise verbatim). -/
theorem exists_c14d_staged_assignment_STG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequestsSTG) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
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
        400 * V < c14Lmax Rq.toC14 P V ∧ Rq.Lmax P V ≤ c14Lmax Rq.toC14 P V ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14D (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax Rq.toC14 P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14D K hK A hA
  obtain ⟨p1, rfl, rfl, h1γ, h⟩ := c14_stage_circ_FAM2b t ha₂ (Rq.γ_pos t) h
  obtain ⟨p2, rfl, h2βc, h2γc, h⟩ := c14_stage_collar_STG p1
    (fun g => min (Rq.βc g.toC14PreCirc) (c14β₂Value_STG Rq g / 3))
    (fun g => lt_min (Rq.βc_pos _) (div_pos (c14β₂Value_pos_STG Rq g) zero_lt_three))
    (Rq.γc_pos p1) h
  have h2 : p2.βc ≤ min p2.β₀ (min (Rq.β₂ p2.toGc_STG) (min (1 / 10000000) (p2.γT / 20))) / 3 :=
    h2βc.trans (min_le_right _ _)
  obtain ⟨p3, rfl, h3β₂, h3v, h⟩ := c14_stage_excl_STG p2 (Rq.β₂_pos p2.toGc_STG) h
  have h3βc : 3 * p3.βc ≤ p3.β₂ := by
    rw [h3v]
    linarith
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
  refine ⟨P, rfl, ⟨h1γ, h2γc, h2βc.trans (min_le_left _ _), h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s,
    h5b', h5s', h6Λ, h7w, h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩,
    by rw [P.β_two]; exact h3βc, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h X g hmetric α hα hstand hder hor
  exact ⟨V, hTV, δ, hδ, hδδ', c14Lmax_gt Rq.toC14 P V, c14Lmax_ge Rq.toC14 P V,
    hV _ (c14Lmax_pos Rq.toC14 P V)⟩

end DifferentialGeometry.Geometry.Collapse
