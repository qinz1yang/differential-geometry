import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Staged
import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison
import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparisonApplications
import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualCircleGramExternalApplications

/-!
# The staged requests of SGP03, EGP04, TCP03 and the Gram certificate, met by ONE assignment

Lanes C14-FAM2 / C14-FAM2b (external review 50, A1–A3, T50-2): the numerical side conditions of
`sgp03_zero_row` (tolerance `θ_s`, accuracy `E = θ_s²/(2·10⁶)`), `egp04_row_RVZ` (tolerance `θ_e`),
`tcp03_zero_row` (tolerance `θ_2`, `ν = ϑ₃/3`) and of the circle Gram certificate
(`tcp01_gram_external`, tolerance `γ_T`) are discharged on the final family `LocalChartPacketsC14`
by the staged contract of `LocalChartPacketsC14Staged`.

* `sgp03StagedRq_FAM2b`, `egp04StagedRq_FAM2b`, `tcp03StagedRq_FAM2b`: each row's requests, every
  one at its legal stage (the rows' own thresholds `η₀`, `Lc`, `σ`, `η₂`, `γ₀`, `η₁` enter through
  `Classical.choose` of the row's threshold statement, evaluated at the prefix: `η₀` of SGP03 /
  EGP04 depends on `(Δ, β₂, θ)`, so the `b` and `β₁` requests see `C14PreVol` / `C14PreSlim`).
* `C14PreFinal.sgp03_FAM2b`, `C14PreFinal.egp04_FAM2b`, `C14PreFinal.tcp03_FAM2b`: every family
  with the parameters of a prefix meeting the row's requests (and `Lmax` above the row's request)
  satisfies the row's conclusion. `C14PreFinal.gram_FAM2b`: the Gram certificate `< γ_T/4` needs no
  request (built into the prefixes).
* `c14RowsRq_FAM2b` (the common requests of the three rows) and `exists_c14_staged_rows_FAM2b`: ONE
  assignment meets the three rows' requests and carries the final family.
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

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_FAM2b {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_FAM2b {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_FAM2b {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-! ### Prefix facts used by the rows -/

/-- `1 ≤ Δ` at every prefix after stage 4. -/
theorem C14PreScale.one_le_Δ_FAM2b (p : C14PreScale) : 1 ≤ p.Δ := by
  linarith [p.Δ_gt6]

/-- `0 < Δ` at every prefix after stage 4. -/
theorem C14PreScale.Δ_pos_FAM2b (p : C14PreScale) : 0 < p.Δ := by
  linarith [p.Δ_gt6]

/-- `β₂ < 10⁻⁶` at every prefix after stage 3. -/
theorem C14PreExcl.β₂_lt6_FAM2b (p : C14PreExcl) : p.β₂ < 1 / 1000000 :=
  p.β₂_le7.trans_lt (by norm_num)

/-- `β₂ < 1` at every prefix after stage 3. -/
theorem C14PreExcl.β₂_lt_one_FAM2b (p : C14PreExcl) : p.β₂ < 1 :=
  p.β₂_lt.trans (by norm_num)

/-- SGP03's accuracy `E = θ_s²/(2·10⁶)` is positive. -/
theorem C14Tol.sgp03_E_pos_FAM2b (t : C14Tol) : 0 < t.θs ^ 2 / (2 * 10 ^ 6) := by
  have := t.θs_pos
  positivity

/-- SGP03's accuracy `E = θ_s²/(2·10⁶)` is below `θ_s²/10⁶`. -/
theorem C14Tol.sgp03_E_lt_FAM2b (t : C14Tol) : t.θs ^ 2 / (2 * 10 ^ 6) < t.θs ^ 2 / 10 ^ 6 := by
  have : 0 < t.θs ^ 2 := by have := t.θs_pos; positivity
  apply div_lt_div_of_pos_left this (by positivity) (by norm_num)

/-- TCP03's `ν = ϑ₃/3` lies in `(0, 1)`. -/
theorem tcp03_ν_FAM2b :
    0 < threeSplittingExclusionThreshold.{0, 0} / 3 ∧
      threeSplittingExclusionThreshold.{0, 0} / 3 < 1 := by
  have h0 := threeSplittingExclusionThreshold_pos.{0, 0}
  have h1 := threeSplittingExclusionThreshold_lt.{0, 0}
  constructor <;> linarith

/-! ### SGP03 -/

/-- SGP03's curvature radius `Lc` at a prefix (`θ = θ_s`, `E = θ_s²/(2·10⁶)`). -/
def sgp03Lc_FAM2b (p : C14PreScale) : ℝ :=
  (sgp03_zero_row (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos
    (C14PreExcl.β₂_lt_one_FAM2b p.toC14PreExcl) p.θs_pos p.θs_lt
    (C14Tol.sgp03_E_pos_FAM2b p.toC14Tol) (C14Tol.sgp03_E_lt_FAM2b p.toC14Tol)).choose

/-- SGP03's raw quality `η₀` at a prefix (`θ = θ_s`, `E = θ_s²/(2·10⁶)`). -/
def sgp03η₀_FAM2b (p : C14PreScale) : ℝ :=
  (sgp03_zero_row (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos
    (C14PreExcl.β₂_lt_one_FAM2b p.toC14PreExcl) p.θs_pos p.θs_lt
    (C14Tol.sgp03_E_pos_FAM2b p.toC14Tol) (C14Tol.sgp03_E_lt_FAM2b p.toC14Tol)).choose_spec.choose

/-- `η₀ > 0`. -/
theorem sgp03η₀_pos_FAM2b (p : C14PreScale) : 0 < sgp03η₀_FAM2b p :=
  (sgp03_zero_row (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos
    (C14PreExcl.β₂_lt_one_FAM2b p.toC14PreExcl) p.θs_pos p.θs_lt
    (C14Tol.sgp03_E_pos_FAM2b p.toC14Tol)
    (C14Tol.sgp03_E_lt_FAM2b p.toC14Tol)).choose_spec.choose_spec.2.1

/-- **SGP03's staged requests** (tolerance `θ_s`): `σs ≤ θ_s²/(2·10⁶)`, `vs ≤ θ_s/200` (stage 9),
`ζ ≤ min(θ_s²/(2·10⁶), 1/(200 · 10⁶Δ))` and `β₁ ≤ η₀(Δ, β₂, θ_s)` (stage 10),
`cap ≤ θ_s/(100 · 10⁶Δ)` (stage 11), `Lmax ≥ Lc(Δ, β₂, θ_s)`. -/
def sgp03StagedRq_FAM2b : C14StagedRequests :=
  { C14StagedRequests.trivial with
    σs := fun p => p.θs ^ 2 / (2 * 10 ^ 6)
    vs := fun p => p.θs / 200
    ζ := fun p => min (p.θs ^ 2 / (2 * 10 ^ 6)) (1 / (200 * (1000000 * p.Δ)))
    β₁ := fun p => sgp03η₀_FAM2b p.toC14PreScale
    cap := fun p => p.θs / (100 * (1000000 * p.Δ))
    Lmax := fun P _ => sgp03Lc_FAM2b P.toC14PreScale
    σs_pos := fun p => C14Tol.sgp03_E_pos_FAM2b p.toC14Tol
    vs_pos := fun p => by have := p.θs_pos; positivity
    ζ_pos := fun p => by
      have := p.θs_pos
      have := C14PreScale.Δ_pos_FAM2b p.toC14PreScale
      positivity
    β₁_pos := fun p => sgp03η₀_pos_FAM2b p.toC14PreScale
    cap_pos := fun p => by
      have := p.θs_pos
      have := C14PreScale.Δ_pos_FAM2b p.toC14PreScale
      positivity }

/-- **SGP03 on the final family, side conditions discharged by the staged contract**: for a prefix
`P` meeting SGP03's staged requests and every family `F : LocalChartPacketsC14` with `P`'s
parameters and `Lmax ≥ Lc`, at every slim centre `i` whose `D_i` meets the support of the zero
ball at `k`, SGP03's conclusion holds at tolerance `θ_s` (accuracy `θ_s²/(2·10⁶)`). -/
theorem C14PreFinal.sgp03_FAM2b (P : C14PreFinal) (hP : sgp03StagedRq_FAM2b.Meets P)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ} {Lmax δ V : ℝ}
    (F : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s'
      P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz)
    (hL : sgp03StagedRq_FAM2b.Lmax P V ≤ Lmax) :
    ∀ i (hi : i ∈ F.slim.centres), ∀ k (hk : k ∈ F.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((F.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * P.Δ) * ρ i)).Nonempty →
      ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧
        (∀ x ∈ ball i (30 * (1000000 * P.Δ) * ρ i),
          |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw F.slim i x| <
            P.θs ^ 2 / (2 * 10 ^ 6)) ∧
        (∀ x ∈ ball i (95 / 100 * (1000000 * P.Δ) * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          |(F.zero.zero k hk).radius / ρ i *
              mvfderiv 𝓘(ℝ, E3) (F.zero.zero k hk).radial x w -
            a₀ * mvfderiv 𝓘(ℝ, E3) (F.slim.centre i hi).coord x w| ≤
            P.θs * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ x ∈ ball i (95 / 100 * (1000000 * P.Δ) * ρ i),
          |(F.zero.zero k hk).radius / ρ i * (F.zero.zero k hk).radial x -
            (a₀ * (F.slim.centre i hi).coord x +
              (F.zero.zero k hk).radius / ρ i * (F.zero.zero k hk).radial i)| < P.θs := by
  have hspec := (sgp03_zero_row (C14PreScale.one_le_Δ_FAM2b P.toC14PreScale) P.β₂_pos
    (C14PreExcl.β₂_lt_one_FAM2b P.toC14PreExcl) P.θs_pos P.θs_lt
    (C14Tol.sgp03_E_pos_FAM2b P.toC14Tol)
    (C14Tol.sgp03_E_lt_FAM2b P.toC14Tol)).choose_spec.choose_spec.2.2
  have hΔ := C14PreScale.Δ_pos_FAM2b P.toC14PreScale
  have hθ := P.θs_pos
  have hθ2 : 0 < P.θs ^ 2 := by positivity
  have hσs : P.σs < P.θs ^ 2 / 10 ^ 6 :=
    hP.σs_le.trans_lt (C14Tol.sgp03_E_lt_FAM2b P.toC14Tol)
  have hvs : P.vs < P.θs / 100 := by
    have h : P.vs ≤ P.θs / 200 := hP.vs_le
    linarith
  have hζ : P.ζ ≤ min (P.θs ^ 2 / (2 * 10 ^ 6)) (1 / (200 * (1000000 * P.Δ))) := hP.ζ_le
  have hζ0 : 0 < P.ζ := P.β₁_pos.trans P.β₁_lt_ζ
  have hζθ : P.ζ < P.θs ^ 2 / 10 ^ 6 :=
    (hζ.trans (min_le_left _ _)).trans_lt (C14Tol.sgp03_E_lt_FAM2b P.toC14Tol)
  have hζL : P.ζ < 1 / (100 * (1000000 * P.Δ)) := by
    refine (hζ.trans (min_le_right _ _)).trans_lt ?_
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    nlinarith
  have hεr : P.εr < P.θs / (100 * (1000000 * P.Δ)) := P.εr_lt_cap.trans_le hP.cap_le
  exact hspec X g hmetric ρ hρ P.Λ P.β P.σs K P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc Lmax
    P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz F.toLocalChartPacketsRVZ P.β_two hP.β₁_le hL
    P.Λ_pos.le P.LΛ_lt P.e_lt P.T_Δ P.T_Λz P.σs_pos hσs hvs hζ0 hζθ hζL hεr

/-! ### EGP04 -/

/-- EGP04's curvature radius `Lc` at a prefix (tolerance `θ_e`). -/
def egp04Lc_FAM2b (p : C14PreScale) : ℝ :=
  (egp04_row_RVZ (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos (C14PreExcl.β₂_lt6_FAM2b p.toC14PreExcl)
    p.θe_pos p.θe_lt).choose

/-- EGP04's raw quality `η₀` at a prefix (tolerance `θ_e`). -/
def egp04η₀_FAM2b (p : C14PreScale) : ℝ :=
  (egp04_row_RVZ (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos (C14PreExcl.β₂_lt6_FAM2b p.toC14PreExcl)
    p.θe_pos p.θe_lt).choose_spec.choose

/-- `η₀ > 0`. -/
theorem egp04η₀_pos_FAM2b (p : C14PreScale) : 0 < egp04η₀_FAM2b p :=
  (egp04_row_RVZ (C14PreScale.one_le_Δ_FAM2b p) p.β₂_pos (C14PreExcl.β₂_lt6_FAM2b p.toC14PreExcl)
    p.θe_pos p.θe_lt).choose_spec.choose_spec.2.1

/-- **EGP04's staged requests** (tolerance `θ_e`): `σc ≤ θ_e²/10⁸`, `μ ≤ θ_e/(200Δ)` (stage 5),
`b ≤ η₀(Δ, β₂, θ_e)` (stage 8), `σs ≤ θ_e²/10⁸`, `vs ≤ θ_e/200` (stage 9),
`ζ ≤ min(θ_e²/10⁸, 1/(1000 · 10⁶Δ))`, `β₁ ≤ η₀` (stage 10), `cap ≤ θ_e/(100 · 10⁶Δ)` (stage 11),
`Lmax ≥ Lc(Δ, β₂, θ_e)`. -/
def egp04StagedRq_FAM2b : C14StagedRequests :=
  { C14StagedRequests.trivial with
    σc := fun p => p.θe ^ 2 / 10 ^ 8
    μ := fun p => p.θe / (200 * p.Δ)
    b := fun p => egp04η₀_FAM2b p.toC14PreScale
    σs := fun p => p.θe ^ 2 / 10 ^ 8
    vs := fun p => p.θe / 200
    ζ := fun p => min (p.θe ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * p.Δ)))
    β₁ := fun p => egp04η₀_FAM2b p.toC14PreScale
    cap := fun p => p.θe / (100 * (1000000 * p.Δ))
    Lmax := fun P _ => egp04Lc_FAM2b P.toC14PreScale
    σc_pos := fun p => by have := p.θe_pos; positivity
    μ_pos := fun p => by
      have := p.θe_pos
      have := C14PreScale.Δ_pos_FAM2b p
      positivity
    b_pos := fun p => egp04η₀_pos_FAM2b p.toC14PreScale
    σs_pos := fun p => by have := p.θe_pos; positivity
    vs_pos := fun p => by have := p.θe_pos; positivity
    ζ_pos := fun p => by
      have := p.θe_pos
      have := C14PreScale.Δ_pos_FAM2b p.toC14PreScale
      positivity
    β₁_pos := fun p => egp04η₀_pos_FAM2b p.toC14PreScale
    cap_pos := fun p => by
      have := p.θe_pos
      have := C14PreScale.Δ_pos_FAM2b p.toC14PreScale
      positivity }

/-- **EGP04 on the final family, side conditions discharged by the staged contract**: for a prefix
`P` meeting EGP04's staged requests and every family `F : LocalChartPacketsC14` with `P`'s
parameters and `Lmax ≥ Lc`, EGP04's conclusion holds at every edge centre at tolerance `θ_e`. -/
theorem C14PreFinal.egp04_FAM2b (P : C14PreFinal) (hP : egp04StagedRq_FAM2b.Meets P)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ} {Lmax δ V : ℝ}
    (F : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s'
      P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz)
    (hL : egp04StagedRq_FAM2b.Lmax P V ≤ Lmax) :
    ∀ i ∈ F.edge.centres,
      (∀ j ∈ egpEdgeList F.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        ∀ x ∈ ball i (20 * P.Δ * ρ i),
          |ρ j / ρ i * F.edge.coord j x -
              (a * F.edge.coord i x + ρ j / ρ i * egpRaw F.edge j i)| < P.θe ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (F.edge.coord j) x w -
                a * mvfderiv 𝓘(ℝ, E3) (F.edge.coord i) x w| < P.θe) ∧
      (∀ j (hj : j ∈ F.slim.centres),
        (tsupport (F.slim.cutoff j) ∩ ball i (20 * P.Δ * ρ i)).Nonempty →
        ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * P.Δ * ρ i),
          |ρ j / ρ i * (F.slim.centre j hj).coord x -
              (a * F.edge.coord i x + ρ j / ρ i * sgpRaw F.slim j i)| < P.θe ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (F.edge.coord i) x w| < P.θe) ∧
      ∀ k (hk : k ∈ F.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((F.zero.zero k hk).radial y)) ∩ ball i (20 * P.Δ * ρ i)).Nonempty →
        ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (20 * P.Δ * ρ i),
          |(F.zero.zero k hk).radius / ρ i * (F.zero.zero k hk).radial x -
              (a₀ * F.edge.coord i x +
                (F.zero.zero k hk).radius / ρ i * (F.zero.zero k hk).radial i)| < P.θe ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
              |(F.zero.zero k hk).radius / ρ i *
                  mvfderiv 𝓘(ℝ, E3) (F.zero.zero k hk).radial x w -
                a₀ * mvfderiv 𝓘(ℝ, E3) (F.edge.coord i) x w| < P.θe := by
  have hspec := (egp04_row_RVZ (C14PreScale.one_le_Δ_FAM2b P.toC14PreScale) P.β₂_pos
    (C14PreExcl.β₂_lt6_FAM2b P.toC14PreExcl) P.θe_pos P.θe_lt).choose_spec.choose_spec.2.2
  have hΔ := C14PreScale.Δ_pos_FAM2b P.toC14PreScale
  have hθ := P.θe_pos
  have hμ : P.μ ≤ P.θe / (200 * P.Δ) := hP.μ_le
  have hμΔ : P.μ * P.Δ < P.θe / 100 := by
    have := (le_div_iff₀ (by positivity)).mp hμ
    nlinarith
  have hvs : P.vs < P.θe / 100 := by
    have h : P.vs ≤ P.θe / 200 := hP.vs_le
    linarith
  have hζ : P.ζ ≤ min (P.θe ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * P.Δ))) := hP.ζ_le
  have hζ0 : 0 < P.ζ := P.β₁_pos.trans P.β₁_lt_ζ
  have hεr : P.εr < P.θe / (100 * (1000000 * P.Δ)) := P.εr_lt_cap.trans_le hP.cap_le
  exact hspec X g hmetric ρ hρ P.Λ P.β P.σs K P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc Lmax
    P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz F.toLocalChartPacketsRVZ hP.b_le
    (P.s_lt6.trans_le (by norm_num)) hP.β₁_le hL P.Λ_pos.le P.LΛ_lt
    (P.μ_le.trans (by norm_num)) (P.τ_le30.trans (by norm_num)) hP.σc_le hμΔ P.σs_pos hP.σs_le
    hvs P.e_lt P.T_Δ P.T_Λz hζ0 (hζ.trans (min_le_left _ _)) (hζ.trans (min_le_right _ _)) hεr

/-! ### TCP03 -/

/-- TCP03's `σ` at tolerance `θ_2`, `ν = ϑ₃/3`. -/
def tcp03σ_FAM2b (t : C14Tol) : ℝ :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose

/-- TCP03's `η₂` at tolerance `θ_2`, `ν = ϑ₃/3`. -/
def tcp03η₂_FAM2b (t : C14Tol) : ℝ :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose

/-- TCP03's `γ₀` at tolerance `θ_2`, `ν = ϑ₃/3`. -/
def tcp03γ₀_FAM2b (t : C14Tol) : ℝ :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.2.choose

/-- TCP03's `η₁` at tolerance `θ_2`, `ν = ϑ₃/3`. -/
def tcp03η₁_FAM2b (t : C14Tol) : ℝ :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.2.choose_spec.2.choose

/-- `σ > 0`. -/
theorem tcp03σ_pos_FAM2b (t : C14Tol) : 0 < tcp03σ_FAM2b t :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.1

/-- `η₂ > 0`. -/
theorem tcp03η₂_pos_FAM2b (t : C14Tol) : 0 < tcp03η₂_FAM2b t :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.1

/-- `γ₀ > 0`. -/
theorem tcp03γ₀_pos_FAM2b (t : C14Tol) : 0 < tcp03γ₀_FAM2b t :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.2.choose_spec.1

/-- `η₁ > 0`. -/
theorem tcp03η₁_pos_FAM2b (t : C14Tol) : 0 < tcp03η₁_FAM2b t :=
  (tcp03_zero_row t.θ2_pos t.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.2.choose_spec.2.choose_spec.1

/-- **TCP03's staged requests** (tolerance `θ_2`, `ν = ϑ₃/3`): `γ ≤ γ₀(θ_2)` (stage 1),
`β₂ ≤ min(η₂(θ_2), σ(θ_2)/3)` (stage 3), `ζ ≤ θ_2²/1000`, `β₁ ≤ η₁(θ_2)` (stage 10),
`cap ≤ θ_2/100` (stage 11), `Lmax ≥ σ(θ_2)⁻¹`. -/
def tcp03StagedRq_FAM2b : C14StagedRequests :=
  { C14StagedRequests.trivial with
    γ := fun t => tcp03γ₀_FAM2b t
    β₂ := fun p => min (tcp03η₂_FAM2b p.toC14Tol) (tcp03σ_FAM2b p.toC14Tol / 3)
    ζ := fun p => p.θ2 ^ 2 / 1000
    β₁ := fun p => tcp03η₁_FAM2b p.toC14Tol
    cap := fun p => p.θ2 / 100
    Lmax := fun P _ => (tcp03σ_FAM2b P.toC14Tol)⁻¹
    γ_pos := fun t => tcp03γ₀_pos_FAM2b t
    β₂_pos := fun p => by
      have := tcp03η₂_pos_FAM2b p.toC14Tol
      have := tcp03σ_pos_FAM2b p.toC14Tol
      positivity
    ζ_pos := fun p => by have := p.θ2_pos; positivity
    β₁_pos := fun p => tcp03η₁_pos_FAM2b p.toC14Tol
    cap_pos := fun p => by have := p.θ2_pos; positivity }

/-- **TCP03 on the final family, side conditions discharged by the staged contract**: for a prefix
`P` meeting TCP03's staged requests and every family `F : LocalChartPacketsC14` with `P`'s
parameters and `Lmax ≥ σ⁻¹`, at every circle centre `i` and every zero ball whose support meets
`D_i`, TCP03's zero row holds at tolerance `θ_2`. -/
theorem C14PreFinal.tcp03_FAM2b (P : C14PreFinal) (hP : tcp03StagedRq_FAM2b.Meets P)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ} {Lmax δ V : ℝ}
    (F : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s'
      P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz)
    (hL : tcp03StagedRq_FAM2b.Lmax P V ≤ Lmax) :
    ∀ i (hi : i ∈ F.circle.centres), ∀ k (hk : k ∈ F.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((F.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
        A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
        (∀ x, dist x i < 1000 * ρ i →
          ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
            A₀ (circleRaw_KA3 F.toLocalChartPackets i x)‖ < P.θ2 ^ 2 / 2000) ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖EuclideanSpace.single 0 ((F.zero.zero k hk).radius / ρ i *
                ((F.zero.zero k hk).radial x - (F.zero.zero k hk).radial i)) -
              A₀ (cgpCircleCoord F.toLocalChartFamily i hi x)‖ ≤ P.θ2 / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖EuclideanSpace.single 0 ((F.zero.zero k hk).radius / ρ i *
                  mvfderiv 𝓘(ℝ, E3) (F.zero.zero k hk).radial x w) -
                A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.toLocalChartFamily i hi) x w)‖ ≤
              P.θ2 / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hthr := threeSplittingExclusionThreshold_lt.{0, 0}
  have hβ₂ : P.β₂ ≤ min (tcp03η₂_FAM2b P.toC14Tol) (tcp03σ_FAM2b P.toC14Tol / 3) := hP.β₂_le
  have hν : 3 * (threeSplittingExclusionThreshold.{0, 0} / 3) ≤ P.β 3 := by
    rw [P.β_three]; linarith
  have hβ3 : P.β 3 < 1 := by rw [P.β_three]; linarith
  have hσ : 3 * P.β 2 ≤ tcp03σ_FAM2b P.toC14Tol := by
    rw [P.β_two]; have := hβ₂.trans (min_le_right _ _); linarith
  have hη₂ : P.β 2 ≤ tcp03η₂_FAM2b P.toC14Tol := by
    rw [P.β_two]; exact hβ₂.trans (min_le_left _ _)
  have hζ0 : 0 < P.ζ := P.β₁_pos.trans P.β₁_lt_ζ
  exact (tcp03_zero_row P.θ2_pos P.θ2_lt tcp03_ν_FAM2b.1
    tcp03_ν_FAM2b.2).choose_spec.2.2.choose_spec.2.choose_spec.2.choose_spec.2
    F.toLocalChartPacketsZ P.Λ_pos.le (C14PreScale.one_le_Δ_FAM2b P.toC14PreScale)
    P.LΛ_lt P.e_lt P.T_Δ hν hβ3 hσ hη₂ hP.γ_le hP.β₁_le hζ0 hP.ζ_le
    (P.εr_lt_cap.trans_le hP.cap_le).le P.T_Λz hL

/-! ### The Gram certificate (built into the prefixes) -/

/-- **The circle Gram certificate on the final family**: for every admissible prefix `P` and every
family `F : LocalChartPacketsC14` with `P`'s parameters, `‖Dη_j(Dη_j)* − I‖ < γ_T/4` at every circle
centre `j` on `B(j, 200ρ(j))` in the normalized metric (no request: `γ ≤ γ_T/20` and
`β₂ ≤ min(10⁻⁷, γ_T/20)` are built into the prefixes). -/
theorem C14PreFinal.gram_FAM2b (P : C14PreFinal)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ} {Lmax δ V : ℝ}
    (F : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s'
      P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz)
    {j : X} (hj : j ∈ F.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ‖(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.toLocalChartFamily j hj) x).comp
        (ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.toLocalChartFamily j hj) x)) -
      ContinuousLinearMap.id ℝ ℝ²‖ < P.γT / 4 := by
  obtain ⟨hT, hT1, hγ, h7, hβT⟩ := C14PreFinal.gram_numerics_FAM2b P
  exact LocalChartPacketsC14.tcp01_gram_external_FAM2b F hT hT1 hγ h7 hβT hj hx

/-- **The right inverse of the circle differential on the final family**: for every admissible
prefix, both singular values of `Dη_j(x)` exceed `9/10` and `Dη_j(x)` has a right inverse of norm
`< 2` (normalized metric; `γ + β₂ < 1/10` from the built-in budgets). -/
theorem C14PreFinal.gram_right_inverse_FAM2b (P : C14PreFinal)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ} {Lmax δ V : ℝ}
    (F : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ P.β P.Δ P.σs K P.σc P.μ P.b P.s P.b' P.s'
      P.ε P.γc P.βc Lmax P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz)
    {j : X} (hj : j ∈ F.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ ξ : ℝ², ‖ξ‖ = 1 → 9 / 10 < ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.toLocalChartFamily j hj) x) ξ‖) ∧
    ∃ R : ℝ² →L[ℝ] TangentSpace 𝓘(ℝ, E3) x,
      (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.toLocalChartFamily j hj) x).comp R =
        ContinuousLinearMap.id ℝ ℝ² ∧ ‖R‖ < 2 := by
  obtain ⟨-, hT1, hγ, h7, -⟩ := C14PreFinal.gram_numerics_FAM2b P
  have hd : P.γ + P.β 2 < 1 / 10 := by linarith
  obtain ⟨h1, R, hR, -, hR2⟩ := LocalChartPacketsC14.tcp01_gram_right_inverse_FAM2b F h7 hd hj hx
  exact ⟨h1, R, hR, hR2⟩

/-! ### ONE assignment for the three rows -/

/-- The common staged requests of SGP03, EGP04 and TCP03 (common minima / maxima, A3). -/
def c14RowsRq_FAM2b : C14StagedRequests :=
  sgp03StagedRq_FAM2b.inf (egp04StagedRq_FAM2b.inf tcp03StagedRq_FAM2b)

/-- **ONE staged assignment for SGP03, EGP04, TCP03 and the Gram certificate** (review 50,
A1–A3): for the external tolerances `t` there is ONE admissible prefix `P` meeting the staged
requests of the three rows such that, for every standing sequence, with the joint zero output
`V ≥ T`, `δ < δ'` and `Lmax := c14Lmax c14RowsRq_FAM2b P V` (above `400V` and above each row's
`Lmax` request), every late member carries the final family `LocalChartPacketsC14` with these
parameters; the rows' conclusions then hold for it by `C14PreFinal.sgp03_FAM2b`,
`C14PreFinal.egp04_FAM2b`, `C14PreFinal.tcp03_FAM2b` and `C14PreFinal.gram_FAM2b`. -/
theorem exists_c14_staged_rows_FAM2b (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ sgp03StagedRq_FAM2b.Meets P ∧
      egp04StagedRq_FAM2b.Meets P ∧ tcp03StagedRq_FAM2b.Meets P ∧
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
        400 * V < c14Lmax c14RowsRq_FAM2b P V ∧
        sgp03StagedRq_FAM2b.Lmax P V ≤ c14Lmax c14RowsRq_FAM2b P V ∧
        egp04StagedRq_FAM2b.Lmax P V ≤ c14Lmax c14RowsRq_FAM2b P V ∧
        tcp03StagedRq_FAM2b.Lmax P V ≤ c14Lmax c14RowsRq_FAM2b P V ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax c14RowsRq_FAM2b P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz) := by
  obtain ⟨P, hPt, hM, h⟩ := exists_c14_staged_assignment K hK A hA t c14RowsRq_FAM2b
  refine ⟨P, hPt, hM.inf_left, hM.inf_right.inf_left, hM.inf_right.inf_right, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', h400, hL, hev⟩ := h X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ, hδδ', h400, (C14StagedRequests.inf_Lmax_left _ _ P V).trans hL,
    ((C14StagedRequests.inf_Lmax_left _ _ P V).trans
      (C14StagedRequests.inf_Lmax_right _ _ P V)).trans hL,
    ((C14StagedRequests.inf_Lmax_right _ _ P V).trans
      (C14StagedRequests.inf_Lmax_right _ _ P V)).trans hL, hev⟩

end DifferentialGeometry.Geometry.Collapse
