import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphEdgeGroup

/-!
# TCP05: assembly of the block errors at a point of `D_i`

Blueprint `master207B.tex`, TCP05 (B:5571–5594): "FC10, FC05 and TCP03–TCP04 therefore bound all
fixed-scale block errors by less than `C²θ` ... the scale-coordinate error is at most `10Λ`. The
total is less than `30CΔΛ` ... The sum `C²θ + 30CΔΛ` is less than `e`." Here every active block
error is bounded by ONE budget `b = tcpTagBudget θ Δ Λ` (`5C_B(N+1)θ + 200C_B√(N+1)ΔΛ`) and the
blocks are summed in `ℓ²` over the at most `N + 3` active tags.

* `block_assembly_KA7`: generic orthogonal summation of block errors of a map into `ℓ²(⊕ V_t)`
  against a block graph `orthogonalBlocks φ ∘ η`, values and derivatives.
* `tcpTagBudget`, `tcpTagBudget_*_KA7`: the per-block budget and the inequalities it dominates.
* `tg_slim_tag_KA7`, `tg_zero_tag_KA7`: (TG) for a listed slim / zero block (TCP03's scalar
  comparison, G12's `tg_scalar_tag_KA6`).
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

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA7A : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Generic

variable {κ : Type*} [Fintype κ] {W : κ → Type*} [∀ t, NormedAddCommGroup (W t)]
  [∀ t, InnerProductSpace ℝ (W t)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The components of the derivative of a map into `ℓ²(⊕ W_t)` are the derivatives of its
components. -/
theorem mvfderiv_piLp_apply_KA7 {F : M → PiLp 2 W} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, PiLp 2 W) F x) (w : TangentSpace I x) (t : κ) :
    mvfderiv I F x w t = mvfderiv I (fun y => F y t) x w :=
  (mvfderiv_comp_hasFDerivAt hF (PiLp.proj 2 W t).hasFDerivAt w).symm

/-- **Orthogonal assembly of block errors.** If on the finite set `A` every block error of
`R⁻¹F` against `φ_t ∘ η` is at most `b` (value) and `b ν(w)` (derivative along `w`), and off `A`
the block errors vanish, then the total errors are at most `√#A b` and `√#A b ν(w)`. -/
theorem block_assembly_KA7 {F : M → PiLp 2 W} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, PiLp 2 W) F x) {φ : ∀ t, Ep → W t}
    (hφ : ∀ t, Differentiable ℝ (φ t)) (η : M → Ep) (R : ℝ) (A : Finset κ) {b : ℝ}
    (hb : 0 ≤ b) (ν : TangentSpace I x → ℝ) (hν : ∀ w, 0 ≤ ν w)
    (hin : ∀ t ∈ A, ‖R⁻¹ • F x t - φ t (η x)‖ ≤ b ∧
      ∀ w, ‖R⁻¹ • mvfderiv I (fun y => F y t) x w -
        fderiv ℝ (φ t) (η x) (mvfderiv I η x w)‖ ≤ b * ν w)
    (hout : ∀ t, t ∉ A → R⁻¹ • F x t - φ t (η x) = 0 ∧
      ∀ w, R⁻¹ • mvfderiv I (fun y => F y t) x w -
        fderiv ℝ (φ t) (η x) (mvfderiv I η x w) = 0) :
    ‖R⁻¹ • F x - orthogonalBlocks φ (η x)‖ ≤ Real.sqrt (A.card : ℝ) * b ∧
      ∀ w, ‖R⁻¹ • mvfderiv I F x w - fderiv ℝ (orthogonalBlocks φ) (η x) (mvfderiv I η x w)‖ ≤
        Real.sqrt (A.card : ℝ) * (b * ν w) := by
  refine ⟨?_, fun w => ?_⟩
  · refine norm_le_of_active_blocks_KA6 _ A hb (fun t ht => ?_) (fun t ht => ?_)
    · rw [PiLp.sub_apply, PiLp.smul_apply]
      exact (hin t ht).1
    · rw [PiLp.sub_apply, PiLp.smul_apply]
      exact (hout t ht).1
  · refine norm_le_of_active_blocks_KA6 _ A (mul_nonneg hb (hν w)) (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [PiLp.sub_apply, PiLp.smul_apply, mvfderiv_piLp_apply_KA7 hF,
        fderiv_orthogonalBlocks_apply_KA6 hφ]
      exact (hin t ht).2 w
    · rw [PiLp.sub_apply, PiLp.smul_apply, mvfderiv_piLp_apply_KA7 hF,
        fderiv_orthogonalBlocks_apply_KA6 hφ]
      exact (hout t ht).2 w

end Generic

section Budget

/-- **The per-block budget of TCP05**: `5C_B(N+1)θ + 200C_B√(N+1)ΔΛ` (`C_B = tcpBlockBound`,
`N = fc07ActiveBound`). -/
def tcpTagBudget (θ Δ Λ : ℝ) : ℝ :=
  5 * tcpBlockBound * (fc07ActiveBound + 1) * θ +
    200 * tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * Δ * Λ

theorem tcpTagBudget_nonneg_KA7 {θ Δ Λ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) :
    0 ≤ tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hΔ0 : 0 ≤ Δ := by linarith
  rw [tcpTagBudget]
  have h1 : 0 ≤ 5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by positivity
  have h2 : 0 ≤ 200 * tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * Δ * Λ := by positivity
  linarith

/-- The budget dominates the fixed-scale term `5C_B(N+1)θ` and the `ΔΛ` term. -/
theorem tcpTagBudget_ge_KA7 {θ Δ Λ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) :
    5 * tcpBlockBound * (fc07ActiveBound + 1) * θ ≤ tcpTagBudget θ Δ Λ ∧
      200 * tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * Δ * Λ ≤ tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hΔ0 : 0 ≤ Δ := by linarith
  have h1 : 0 ≤ 5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by positivity
  have h2 : 0 ≤ 200 * tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * Δ * Λ := by positivity
  rw [tcpTagBudget]
  constructor <;> linarith

/-- A scalar `θ`-term `c C_B θ` with `c ≤ 5` is within the budget. -/
theorem tcpTagBudget_fixed_KA7 {θ Δ Λ c : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hc : c ≤ 5) : c * tcpBlockBound * θ ≤ tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hle := (tcpTagBudget_ge_KA7 hθ hΔ hΛ).1
  have h1 : c * tcpBlockBound * θ ≤ 5 * tcpBlockBound * θ := by
    have : 0 ≤ tcpBlockBound * θ := by positivity
    nlinarith
  have h2 : 5 * tcpBlockBound * θ ≤ 5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by
    have : 0 ≤ 5 * tcpBlockBound * θ := by positivity
    nlinarith
  linarith

/-- The edge block errors (`n ≤ N`, `q = √(n + 1)`): `C_B qθ` and `(C_B + 4C_B q) qθ` are within
the budget. -/
theorem tcpTagBudget_edge_KA7 {θ Δ Λ n : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hn : 0 ≤ n)
    (hnN : n ≤ fc07ActiveBound) :
    tcpBlockBound * (Real.sqrt (n + 1) * θ) ≤ tcpTagBudget θ Δ Λ ∧
      (tcpBlockBound + tcpBlockBound * (4 * Real.sqrt (n + 1))) * (Real.sqrt (n + 1) * θ) ≤
        tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hle := (tcpTagBudget_ge_KA7 hθ hΔ hΛ).1
  set q := Real.sqrt (n + 1) with hq
  have hq1 : 1 ≤ q := by rw [hq, Real.one_le_sqrt]; linarith
  have hq2 : q ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hq2N : q ^ 2 ≤ fc07ActiveBound + 1 := by linarith
  have hBθ : 0 ≤ tcpBlockBound * θ := by positivity
  have e1 : (tcpBlockBound + tcpBlockBound * (4 * q)) * (q * θ) =
      tcpBlockBound * θ * q + 4 * (tcpBlockBound * θ) * q ^ 2 := by ring
  have h1 : tcpBlockBound * θ * q ≤ tcpBlockBound * θ * (fc07ActiveBound + 1) :=
    mul_le_mul_of_nonneg_left (hqq.trans hq2N) hBθ
  have h2 : 4 * (tcpBlockBound * θ) * q ^ 2 ≤ 4 * (tcpBlockBound * θ) * (fc07ActiveBound + 1) :=
    mul_le_mul_of_nonneg_left hq2N (by positivity)
  constructor
  · have : tcpBlockBound * (q * θ) = tcpBlockBound * θ * q := by ring
    rw [this]
    have h3 : tcpBlockBound * θ * (fc07ActiveBound + 1) ≤
        5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by nlinarith
    linarith
  · rw [e1]
    have h3 : tcpBlockBound * θ * (fc07ActiveBound + 1) +
        4 * (tcpBlockBound * θ) * (fc07ActiveBound + 1) =
        5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by ring
    linarith

/-- The `E'` block errors (`n ≤ N`, `q = √(n + 1)`, `θ ≤ 1`): the value term
`10Λ(20qΔ) + C_B qθ` and the derivative term
`Λ(20qΔ) + 10Λ C_B (4q + qθ) + (C_B + 4C_B q) qθ` are within the budget. -/
theorem tcpTagBudget_marker_KA7 {θ Δ Λ n : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ : 1 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hn : 0 ≤ n) (hnN : n ≤ fc07ActiveBound) :
    10 * Λ * (20 * Real.sqrt (n + 1) * Δ) + tcpBlockBound * (Real.sqrt (n + 1) * θ) ≤
        tcpTagBudget θ Δ Λ ∧
      Λ * (20 * Real.sqrt (n + 1) * Δ) +
          10 * Λ * (tcpBlockBound * (4 * Real.sqrt (n + 1) + Real.sqrt (n + 1) * θ)) +
          (tcpBlockBound + tcpBlockBound * (4 * Real.sqrt (n + 1))) * (Real.sqrt (n + 1) * θ) ≤
        tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  set q := Real.sqrt (n + 1) with hq
  set qN := Real.sqrt (fc07ActiveBound + 1) with hqN
  have hqqN : q ≤ qN := Real.sqrt_le_sqrt (by linarith)
  have hq1 : 1 ≤ q := by rw [hq, Real.one_le_sqrt]; linarith
  have hq2 : q ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hq2N : q ^ 2 ≤ fc07ActiveBound + 1 := by linarith
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hΔ0 : 0 ≤ Δ := by linarith
  have hΔΛ : 0 ≤ Δ * Λ := mul_nonneg hΔ0 hΛ
  have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ
  -- the `θ` parts
  have hθq : tcpBlockBound * (q * θ) ≤ tcpBlockBound * (fc07ActiveBound + 1) * θ := by
    have : tcpBlockBound * (q * θ) = tcpBlockBound * θ * q := by ring
    rw [this]
    have h := mul_le_mul_of_nonneg_left (hqq.trans hq2N) (by positivity : 0 ≤ tcpBlockBound * θ)
    linarith
  have hθe := (tcpTagBudget_edge_KA7 hθ hΔ hΛ hn hnN).2
  -- the `ΔΛ` parts, all `≤ C_B qN ΔΛ` times a numeral
  have hBq : 0 ≤ tcpBlockBound * qN := by positivity
  have hv : 10 * Λ * (20 * q * Δ) ≤ 200 * tcpBlockBound * qN * Δ * Λ := by
    have h1 : q * (Δ * Λ) ≤ tcpBlockBound * qN * (Δ * Λ) := by
      have : q ≤ tcpBlockBound * qN := by nlinarith
      exact mul_le_mul_of_nonneg_right this hΔΛ
    nlinarith
  have hd1 : Λ * (20 * q * Δ) ≤ 20 * (tcpBlockBound * qN * (Δ * Λ)) := by
    have : q ≤ tcpBlockBound * qN := by nlinarith
    have h := mul_le_mul_of_nonneg_right this hΔΛ
    nlinarith
  have hd2 : 10 * Λ * (tcpBlockBound * (4 * q + q * θ)) ≤
      50 * (tcpBlockBound * qN * (Δ * Λ)) := by
    have h45 : 4 * q + q * θ ≤ 5 * qN := by nlinarith
    have h := mul_le_mul_of_nonneg_left h45 (by positivity : 0 ≤ 10 * Λ * tcpBlockBound)
    have h' : 10 * Λ * tcpBlockBound * (5 * qN) ≤ 50 * (tcpBlockBound * qN * (Δ * Λ)) := by
      have := mul_le_mul_of_nonneg_left hΛΔ (by positivity : 0 ≤ 50 * tcpBlockBound * qN)
      nlinarith
    nlinarith
  have hge := tcpTagBudget_ge_KA7 hθ hΔ hΛ
  have e200 : 200 * tcpBlockBound * qN * Δ * Λ = 200 * (tcpBlockBound * qN * (Δ * Λ)) := by ring
  have hpos : 0 ≤ tcpBlockBound * qN * (Δ * Λ) := by positivity
  have hfix : 5 * tcpBlockBound * (fc07ActiveBound + 1) * θ +
      200 * tcpBlockBound * qN * Δ * Λ = tcpTagBudget θ Δ Λ := by
    rw [tcpTagBudget]
  constructor
  · have h3 : tcpBlockBound * (fc07ActiveBound + 1) * θ ≤
        5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by
      have : 0 ≤ tcpBlockBound * (fc07ActiveBound + 1) * θ := by positivity
      linarith
    linarith
  · have h4 : (tcpBlockBound + tcpBlockBound * (4 * q)) * (q * θ) ≤
        5 * tcpBlockBound * (fc07ActiveBound + 1) * θ := by
      have := (tcpTagBudget_edge_KA7 hθ hΔ hΛ hn hnN).2
      rw [tcpTagBudget] at this
      have h5 : (tcpBlockBound + tcpBlockBound * (4 * q)) * (q * θ) =
          tcpBlockBound * θ * q + 4 * (tcpBlockBound * θ) * q ^ 2 := by ring
      rw [h5]
      have h6 := mul_le_mul_of_nonneg_left (hqq.trans hq2N) (by positivity : 0 ≤ tcpBlockBound * θ)
      have h7 := mul_le_mul_of_nonneg_left hq2N (by positivity : 0 ≤ 4 * (tcpBlockBound * θ))
      nlinarith
    linarith

/-- The scale block errors `10Λ` and `Λ` are within the budget. -/
theorem tcpTagBudget_scale_KA7 {θ Δ Λ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) :
    10 * Λ ≤ tcpTagBudget θ Δ Λ ∧ Λ ≤ tcpTagBudget θ Δ Λ := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hqN : 1 ≤ Real.sqrt (fc07ActiveBound + 1) := by rw [Real.one_le_sqrt]; linarith
  have hge := (tcpTagBudget_ge_KA7 hθ hΔ hΛ).2
  have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ
  have h1 : 10 * Λ ≤ 200 * tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * Δ * Λ := by
    have h2 : 1 ≤ tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) := by nlinarith
    have h3 : Δ * Λ ≤ tcpBlockBound * Real.sqrt (fc07ActiveBound + 1) * (Δ * Λ) :=
      le_mul_of_one_le_left (mul_nonneg (by linarith) hΛ) h2
    nlinarith
  constructor <;> linarith

end Budget

section Scalar

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05A_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05A_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05A_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **(TG) for a listed slim block** at `x ∈ B(j, 10⁶Δρ(j))` from TCP03's scalar comparison
`|s_jη_j − A₁η_i − c| ≤ ε`, `|s_j dη_j − A₁ dη_i| ≤ εν` (`s_j ≥ 99/100`, `‖A₁‖ ≤ 1`). -/
theorem tg_slim_tag_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) {i : X} (j : P.slim.finite_centres.toFinset) {x : X}
    (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1)) (hs : 99 / 100 ≤ ρ j.1 / ρ i)
    (hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
    (ηi : X → ℝ²) (A₁ : ℝ² →L[ℝ] ℝ) (hA₁ : ‖A₁‖ ≤ 1) (c : ℝ)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ : ℝ}
    (hval : |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x -
      A₁ (ηi x) - c| ≤ ε₀)
    (hder : ∀ w, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w -
        A₁ (mvfderiv 𝓘(ℝ, E3) ηi x w)| ≤ ε₀ * ν w)
    (hηi : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 2 * ν w) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inr (.inl j)) -
        blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i) (A₁ (ηi x) + c))‖ ≤
        tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inl j))) x w -
        fderiv ℝ (fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i) (A₁ a + c)))
          (ηi x) (mvfderiv 𝓘(ℝ, E3) ηi x w)‖ ≤ (tcpBlockBound + tcpBlockBound * 2) * ε₀ * ν w := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hf : (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inl j))) =ᶠ[𝓝 x]
      fun y => ρ i • blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
        (ρ j.1 / ρ i * (P.slim.centre j.1 hj).coord y)) := by
    filter_upwards [slim_cutoff_eventuallyEq_KA2 P.toLocalChartFamilyE.toLocalChartFamilyQ hj hxj]
      with y hy
    exact cgpGlobalMap_slim_eq_KA6 P j hri hΔ0 hy
  have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
  have hW (y : ℝ) := sgpModelBlock_derivative_bounds hℓ hs y
  have hsP : 50 * (sgpProfileBound + 1) ≤ tcpBlockBound := by
    linarith [tcpBlockBound_ge_KA6.1, tcpProfileBound_spec.2.1]
  exact tg_scalar_tag_KA6 ((contDiff_sgpModelBlock _ _).of_le (by simp))
    (fun y => (hW y).1.trans hsP) (fun y => (hW y).2.trans hsP) hri.ne' hf hcd A₁ hA₁ c ν hval
    hder hηi

/-- **(TG) for the zero block** (`s₀ = R₀/R ≥ 1`) at a point where the radial function is
differentiable, from TCP03's scalar comparison. -/
theorem tg_zero_tag_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (k : P.zero.finite_centres.toFinset) {x : X}
    (hs : 1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hrd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    (ηi : X → ℝ²) (A₁ : ℝ² →L[ℝ] ℝ) (hA₁ : ‖A₁‖ ≤ 1) (c : ℝ)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ : ℝ}
    (hval : |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x - A₁ (ηi x) - c| ≤ ε₀)
    (hder : ∀ w, |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
        A₁ (mvfderiv 𝓘(ℝ, E3) ηi x w)| ≤ ε₀ * ν w)
    (hηi : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 2 * ν w) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inr (.inr (.inr (.inl k)))) -
        blockLift_KC3 (zeroModelBlock
          ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i) (A₁ (ηi x) + c))‖ ≤
        tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inr (.inr (.inl k))))) x w -
        fderiv ℝ (fun a => blockLift_KC3 (zeroModelBlock
          ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i) (A₁ a + c)))
          (ηi x) (mvfderiv 𝓘(ℝ, E3) ηi x w)‖ ≤ (tcpBlockBound + tcpBlockBound * 2) * ε₀ * ν w := by
  have hri := hρ i
  have hf : (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y
      (.inr (.inr (.inr (.inl k))))) =ᶠ[𝓝 x]
      fun y => ρ i • blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y)) :=
    Filter.Eventually.of_forall fun y => cgpGlobalMap_zero_eq_KA6 P k hri y
  have hW (y : ℝ) := zeroModelBlock_derivative_bounds hs y
  have hzP : 50 * (zeroProfileBound + 1) ≤ tcpBlockBound := by
    linarith [tcpBlockBound_ge_KA6.1, tcpProfileBound_spec.2.2.1]
  exact tg_scalar_tag_KA6 ((contDiff_zeroModelBlock _).of_le (by simp))
    (fun y => (hW y).1.trans hzP) (fun y => (hW y).2.trans hzP) hri.ne' hf hrd A₁ hA₁ c ν hval
    hder hηi

end Scalar

section Cases

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05B_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05B_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05B_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **A listed circle block `j ≠ i`** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_circle_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.circle.finite_centres.toFinset)
    (hji : j.1 ≠ i) (hjS : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i)) (hxj : x ∈ ball j.1 (200 * ρ j.1))
    (hs : ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2) (hA : ‖Ac (.inl j)‖ ≤ 1)
    (hval : ‖(ρ j.1 / ρ i) • cgpCircleCoord P.toLocalChartFamily j.1
        ((Set.Finite.mem_toFinset _).mp j.2) x -
        Ac (.inl j) (cgpCircleCoord P.toLocalChartFamily i hi x) - cc (.inl j)‖ ≤ θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j.1
          ((Set.Finite.mem_toFinset _).mp j.2)) x w -
        Ac (.inl j) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inl j) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j)
          (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j)) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j) =
      fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
        (Ac (.inl j) a + cc (.inl j)) := by
    simp only [tcpModelComponent, hji, hjS, ite_false, ite_true]
  have h := tg_circle_tag_KA6 P hi j hxj hxi hs (Ac (.inl j)) hA (cc (.inl j)) hval hder
  have hP := tcpProfileBound_spec.1
  have hPB : 50 * (tcpProfileBound + 1) ≤ tcpBlockBound := tcpBlockBound_ge_KA6.1
  have hb1 : 50 * (tcpProfileBound + 1) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    have h2 : 50 * (tcpProfileBound + 1) * (θ / 2) ≤ 1 / 2 * tcpBlockBound * θ := by nlinarith
    linarith
  have hb2 : (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * (θ / 2) ≤
      tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    have h2 : (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * (θ / 2) ≤
        3 / 2 * tcpBlockBound * θ := by nlinarith
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **The own circle block** (`j.1 = i`): no error on `{|η_i| ≤ 8}`. -/
theorem tcp05_own_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.circle.finite_centres.toFinset)
    (hji : j.1 = i) {x : X} (hxi : x ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inl j) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j)
          (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j)) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inl j) =
      fun a => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)) := by
    simp only [tcpModelComponent, hji, ite_true]
  have hb := tcpTagBudget_nonneg_KA7 hθ hΔ hΛ
  obtain ⟨h1, h2⟩ := tg_own_tag_KA7 P hi j hji hxi h8
  rw [hcomp]
  refine ⟨?_, fun w => ?_⟩
  · rw [h1, sub_self, norm_zero]
    exact hb
  · rw [h2 w, sub_self, norm_zero]
    exact mul_nonneg hb (Real.sqrt_nonneg _)

open Classical in
/-- **A listed slim block** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_slim_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (j : P.slim.finite_centres.toFinset)
    (hjS : (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i)) (hxj : x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hs : 99 / 100 ≤ ρ j.1 / ρ i)
    (hcd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
    (hA : ‖A1 (.inr (.inl j))‖ ≤ 1)
    (hval : |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x -
      A1 (.inr (.inl j)) (cgpCircleCoord P.toLocalChartFamily i hi x) - c1 (.inr (.inl j))| ≤
        θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w -
        A1 (.inr (.inl j)) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inr (.inl j)) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inr (.inl j))
          (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inl j))) x w -
          fderiv ℝ
            (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ (.inr (.inl j)))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inl j)) = fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
        (A1 (.inr (.inl j)) a + c1 (.inr (.inl j)))) := by
    simp only [tcpModelComponent, hjS, ite_true]
  have h := tg_slim_tag_KA7 P hΔ j hxj hs hcd (cgpCircleCoord P.toLocalChartFamily i hi)
    (A1 (.inr (.inl j))) hA (c1 (.inr (.inl j))) _ hval hder
    (fun w => norm_mvfderiv_circleCoord_le_KA6 P hi hxi w)
  have hb1 : tcpBlockBound * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  have hb2 : (tcpBlockBound + tcpBlockBound * 2) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **The listed zero block** within the budget (TCP03 at accuracy `θ/2`). -/
theorem tcp05_zero_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (k : P.zero.finite_centres.toFinset)
    (hkS : (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∈ S) {x : X}
    (hxi : x ∈ ball i (200 * ρ i))
    (hs : 1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hrd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)
    (hA : ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1)
    (hval : |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
      (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
        A1 (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord P.toLocalChartFamily i hi x) -
        c1 (.inr (.inr (.inr (.inl k))))| ≤ θ / 2)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
        mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
        A1 (.inr (.inr (.inr (.inl k))))
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inr (.inr (.inr (.inl k)))) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
          (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y
            (.inr (.inr (.inr (.inl k))))) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
              (.inr (.inr (.inr (.inl k)))))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inr (.inr (.inl k)))) = fun a => blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
        (A1 (.inr (.inr (.inr (.inl k)))) a + c1 (.inr (.inr (.inr (.inl k)))))) := by
    simp only [tcpModelComponent, hkS, ite_true]
  have h := tg_zero_tag_KA7 P k hs hrd (cgpCircleCoord P.toLocalChartFamily i hi)
    (A1 (.inr (.inr (.inr (.inl k))))) hA (c1 (.inr (.inr (.inr (.inl k))))) _ hval hder
    (fun w => norm_mvfderiv_circleCoord_le_KA6 P hi hxi w)
  have hb1 : tcpBlockBound * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 1 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  have hb2 : (tcpBlockBound + tcpBlockBound * 2) * (θ / 2) ≤ tcpTagBudget θ Δ Λ := by
    have := tcpTagBudget_fixed_KA7 (c := 3 / 2) hθ hΔ hΛ (by norm_num)
    linarith
  rw [hcomp]
  refine ⟨h.1.trans hb1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)

open Classical in
/-- **A listed edge block** (`j ∈ S_e`) within the budget, from the input comparison
`ε = √(#S_e + 1) θ`, `L = 4√(#S_e + 1)`. -/
theorem tcp05_edge_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (j : P.toLocalChartFamily.edge.finite_centres.toFinset) (hj : j ∈ Se) {x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edge.cutoff k.1 y =
      edgeCoordinateProfile (P.edge.coord k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual P.toLocalChartFamily Se τf) x)
    (hval : ‖tcpEdgeActual P.toLocalChartFamily Se τf x -
      tcpEdgeInput P.toLocalChartFamily P.zero Se A1 c1 Bτ cτ
        (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ Real.sqrt ((Se.card : ℝ) + 1) * θ)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual P.toLocalChartFamily Se τf) x w -
        tcpEdgeLinear P.toLocalChartFamily P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        Real.sqrt ((Se.card : ℝ) + 1) * θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hbd : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖tcpEdgeLinear P.toLocalChartFamily P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        4 * Real.sqrt ((Se.card : ℝ) + 1) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inr (.inr (.inl j))) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
          (.inr (.inr (.inl j))) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inr (.inl j)))) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
              (.inr (.inr (.inl j))))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
      (.inr (.inr (.inl j))) = fun a => blockLift_KC3 (tcpNetwork Δ
        (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput P.toLocalChartFamily P.zero Se A1 c1 Bτ cτ a)
        (some ⟨j, hj⟩)) := by
    simp only [tcpModelComponent, hj, ↓reduceDIte]
  have h := tg_edge_tag_KA7 P.toLocalChartFamily P.zero Se τf A1 c1 Bτ cτ hΔ hx hcut hs hcard j hj
    hV (cgpCircleCoord P.toLocalChartFamily i hi) _ hval hder hbd
  have hb := tcpTagBudget_edge_KA7 hθ hΔ hΛ (Nat.cast_nonneg Se.card) hcard
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _)

open Classical in
/-- **The `E'` block** within the budget (`θ ≤ 1`). -/
theorem tcp05_marker_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edge.cutoff k.1 y =
      edgeCoordinateProfile (P.edge.coord k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hoff : ∀ y ∈ ball i (10 * ρ i), ∀ k ∉ Se, P.edge.cutoff k.1 y = 0)
    (hτm : ∀ y ∈ ball i (10 * ρ i),
      τf y = cgpHeight P.toLocalChartFamily y ∨
        (τf y = 0 ∧ cgpEdgeMarker P.toLocalChartFamily y = 0))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual P.toLocalChartFamily Se τf) x)
    (hval : ‖tcpEdgeActual P.toLocalChartFamily Se τf x -
      tcpEdgeInput P.toLocalChartFamily P.zero Se A1 c1 Bτ cτ
        (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ Real.sqrt ((Se.card : ℝ) + 1) * θ)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual P.toLocalChartFamily Se τf) x w -
        tcpEdgeLinear P.toLocalChartFamily P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        Real.sqrt ((Se.card : ℝ) + 1) * θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hbd : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖tcpEdgeLinear P.toLocalChartFamily P.zero Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        4 * Real.sqrt ((Se.card : ℝ) + 1) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (cgpEdgeTag P.toLocalChartFamily P.zero) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpEdgeTag P.toLocalChartFamily P.zero) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y
            (cgpEdgeTag P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
              (cgpEdgeTag P.toLocalChartFamily P.zero))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
      (cgpEdgeTag P.toLocalChartFamily P.zero) = fun a => blockLift_KC3 (tcpNetwork Δ
        (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput P.toLocalChartFamily P.zero Se A1 c1 Bτ cτ a)
        none) := rfl
  have h := tg_edgeMarker_tag_KA7 P.toLocalChartFamily P.zero Se τf A1 c1 Bτ cτ hΔ hΛ hx hcut hoff
    hτm hs hcard hV (cgpCircleCoord P.toLocalChartFamily i hi) hval hder hbd
  have hb := tcpTagBudget_marker_KA7 hθ hθ1 hΔ hΛ (Nat.cast_nonneg Se.card) hcard
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _)

open Classical in
/-- **The scale block** within the budget. -/
theorem tcp05_scale_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X} (hx : x ∈ ball i (10 * ρ i)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x
          (cgpScaleTag P.toLocalChartFamily P.zero) -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpScaleTag P.toLocalChartFamily P.zero) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤
        tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y
            (cgpScaleTag P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
              (cgpScaleTag P.toLocalChartFamily P.zero))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hcomp : tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
      (cgpScaleTag P.toLocalChartFamily P.zero) =
        fun _ => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ)) := rfl
  have h := tg_scale_tag_KA7 (hmetric := hmetric) P.toLocalChartFamily P.zero hΛ hx
  have hb := tcpTagBudget_scale_KA7 hθ hΔ hΛ
  rw [hcomp]
  refine ⟨h.1.trans hb.1, fun w => ?_⟩
  rw [fderiv_const_apply, zero_apply, sub_zero]
  exact (h.2 w).trans (mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg _))

open Classical in
/-- **An inactive tag**: off the active tags of the model (and with `x` outside the closed support
of its cutoff) both the block of `R⁻¹𝓔⁰` and the model block vanish, with their derivatives. -/
theorem tcp05_off_case_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S)
    (t : CGPTag P.toLocalChartFamily P.zero)
    (ht : t ∉ tcpModelActive P.toLocalChartFamily P.zero S Se) {x : X}
    (hx : x ∉ tsupport (cgpCutoff P.toLocalChartFamily P.zero t)) :
    (ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x t -
        tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ t
          (cgpCircleCoord P.toLocalChartFamily i hi x) = 0 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y t) x w -
          fderiv ℝ (tcpModelComponent P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ t)
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) = 0 := by
  have hz := tcpModelComponent_eq_zero P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ hown t
    ht
  obtain ⟨h1, h2⟩ := tg_unlisted_tag_KA7 P.toLocalChartFamily P.zero hx
  have h0 : (0 : ℝ² → WithLp 2 (ℝ² × ℝ)) = fun _ => 0 := rfl
  rw [hz, h0]
  refine ⟨?_, fun w => ?_⟩
  · rw [h1, smul_zero, sub_zero]
  · rw [h2 w, smul_zero, fderiv_const_apply, zero_apply, sub_zero]

end Cases

section Point

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05C_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05C_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05C_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **TCP05's (TG) at one point** `x ∈ D_i` with `|η_i(x)| ≤ 8`, for given model data: if every
listed circle / slim / zero block satisfies TCP03's comparison at accuracy `θ/2`, the edge
coordinates and `τ` satisfy the scalar comparison at accuracy `θ` (with the cutoff identities of
TCP04's case on `D_i`), and the unlisted cutoffs have `x` outside their closed supports, then
`‖R⁻¹𝓔⁰(x) − Φ_i(η_i(x))‖ ≤ √#A b` and the derivative error is `≤ √#A b |w|`
(`A = tcpModelActive`, `b = tcpTagBudget θ Δ Λ`). -/
theorem tcp05_point_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
    (Se : Finset P.toLocalChartFamily.edge.finite_centres.toFinset)
    (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
    (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
    (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (τf : X → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {x : X}
    (hF : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) x)
    (hx : x ∈ ball i (10 * ρ i)) (hxi : x ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8)
    (hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S)
    (hSe : ∀ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∉ S)
    (hC : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      x ∈ ball j.1 (200 * ρ j.1) ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 ∧ ‖Ac (.inl j)‖ ≤ 1 ∧
        ‖(ρ j.1 / ρ i) • cgpCircleCoord P.toLocalChartFamily j.1
            ((Set.Finite.mem_toFinset _).mp j.2) x -
          Ac (.inl j) (cgpCircleCoord P.toLocalChartFamily i hi x) - cc (.inl j)‖ ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j.1
              ((Set.Finite.mem_toFinset _).mp j.2)) x w -
            Ac (.inl j) (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hS : ∀ j : P.slim.finite_centres.toFinset,
      (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ 99 / 100 ≤ ρ j.1 / ρ i ∧
        MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x ∧
        ‖A1 (.inr (.inl j))‖ ≤ 1 ∧
        |ρ j.1 / ρ i * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x -
          A1 (.inr (.inl j)) (cgpCircleCoord P.toLocalChartFamily i hi x) -
          c1 (.inr (.inl j))| ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, |ρ j.1 / ρ i * mvfderiv 𝓘(ℝ, E3)
          (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x w -
            A1 (.inr (.inl j))
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hZ : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i ∧
        MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
        ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x -
            A1 (.inr (.inr (.inr (.inl k)))) (cgpCircleCoord P.toLocalChartFamily i hi x) -
            c1 (.inr (.inr (.inr (.inl k))))| ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          |(P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
            mvfderiv 𝓘(ℝ, E3) (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x w -
            A1 (.inr (.inr (.inr (.inl k))))
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hE : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 ∧ ‖A1 (.inr (.inr (.inl k.1)))‖ ≤ 2 ∧
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.edge.coord k.1.1) x ∧
      |P.edge.coord k.1.1 x - (A1 (.inr (.inr (.inl k.1)))
          (cgpCircleCoord P.toLocalChartFamily i hi x) + c1 (.inr (.inr (.inl k.1))))| ≤ θ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) (P.edge.coord k.1.1) x w -
        A1 (.inr (.inr (.inl k.1)))
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
        θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hτ : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ τf x ∧ ‖Bτ‖ ≤ 2 ∧
      |τf x - (Bτ (cgpCircleCoord P.toLocalChartFamily i hi x) + cτ)| ≤ θ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) τf x w -
        Bτ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)| ≤
        θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, P.edge.cutoff k.1 y =
      edgeCoordinateProfile (P.edge.coord k.1 y / Δ) * edgeHeightProfile (τf y / Δ))
    (hoff : ∀ y ∈ ball i (10 * ρ i), ∀ k ∉ Se, P.edge.cutoff k.1 y = 0)
    (hτm : ∀ y ∈ ball i (10 * ρ i),
      τf y = cgpHeight P.toLocalChartFamily y ∨
        (τf y = 0 ∧ cgpEdgeMarker P.toLocalChartFamily y = 0))
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hunlC : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∉ S → x ∉ tsupport (P.circle.cutoff j.1))
    (hunlS : ∀ j : P.slim.finite_centres.toFinset,
      (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∉ S → x ∉ tsupport (P.slim.cutoff j.1))
    (hunlZ : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∉ S →
      x ∉ tsupport (cgpCutoff P.toLocalChartFamily P.zero (.inr (.inr (.inr (.inl k)))))) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
        tcpModelGraph P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ
          (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤
        Real.sqrt ((tcpModelActive P.toLocalChartFamily P.zero S Se).card : ℝ) *
          tcpTagBudget θ Δ Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
          fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ)
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          Real.sqrt ((tcpModelActive P.toLocalChartFamily P.zero S Se).card : ℝ) *
            (tcpTagBudget θ Δ Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) := by
  set η := cgpCircleCoord P.toLocalChartFamily i hi with hη
  have hb := tcpTagBudget_nonneg_KA7 hθ hΔ hΛ
  have hηb : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) η x w‖ ≤ 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) :=
    fun w => norm_mvfderiv_circleCoord_le_KA6 P hi hxi w
  have hVs := contMDiffAt_tcpEdgeActual_KA7 P.toLocalChartFamily Se τf hτ.1
    (fun k hk => (hE ⟨k, hk⟩).2.2.1)
  have hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se))
      (tcpEdgeActual P.toLocalChartFamily Se τf) x := hVs.mdifferentiableAt (by simp)
  obtain ⟨hcv, hcd, hcb⟩ := tcp_edgeActual_compare_KA7 P.toLocalChartFamily P.zero Se τf A1 c1 Bτ
    cτ η _ (fun w => Real.sqrt_nonneg _) hθ hV (fun k => ⟨(hE k).2.2.2.1, (hE k).2.2.2.2⟩)
    ⟨hτ.2.2.1, hτ.2.2.2⟩ (fun k => (hE k).2.1) hτ.2.1 hηb
  have hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 := fun k => (hE k).1
  refine block_assembly_KA7 hF (fun t => (contDiff_tcpModelComponent P.toLocalChartFamily P.zero
    i S Se Ac cc A1 c1 Bτ cτ t).differentiable (by simp)) η (ρ i)
    (tcpModelActive P.toLocalChartFamily P.zero S Se) hb _ (fun w => Real.sqrt_nonneg _)
    (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with j | j | j | k | q
    · by_cases hji : j.1 = i
      · exact tcp05_own_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hji hxi h8
      · have hjS : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S := by
          simpa [tcpModelActive] using ht
        obtain ⟨h1, h2, h3, h4, h5⟩ := hC j hji hjS
        exact tcp05_circle_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hji hjS hxi h1 h2 h3
          h4 h5
    · have hjS : (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈ S := by
        simpa [tcpModelActive] using ht
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS j hjS
      exact tcp05_slim_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ j hjS hxi h1 h2 h3 h4 h5 h6
    · have hj : j ∈ Se := by
        have h := ht
        simp only [tcpModelActive, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at h
        rcases h with (h | ⟨a, ha, hae⟩) | h
        · exact (hSe j h).elim
        · cases hae
          exact ha
        · rcases h with h | h <;> cases h
      exact tcp05_edge_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ τf hθ hΔ hΛ j hj hx hcut hs hcard hV
        hcv hcd hcb
    · have hkS : (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∈ S := by
        simpa [tcpModelActive] using ht
      obtain ⟨h1, h2, h3, h4, h5⟩ := hZ k hkS
      exact tcp05_zero_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ k hkS hxi h1 h2 h3 h4 h5
    · cases q
      · exact tcp05_scale_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hθ hΔ hΛ hx
      · exact tcp05_marker_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ τf hθ hθ1 hΔ hΛ hx hcut hoff hτm
          hs hcard hV hcv hcd hcb
  · refine tcp05_off_case_KA7 P hi S Se Ac cc A1 c1 Bτ cτ hown t ht ?_
    rcases t with j | j | j | k | q
    · have hji : j.1 ≠ i := fun h => ht (by
        simp only [tcpModelActive, Finset.mem_union]
        exact Or.inl (Or.inl (hown j h)))
      have hjS : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∉ S := fun h => ht (by
        simp only [tcpModelActive, Finset.mem_union]
        exact Or.inl (Or.inl h))
      exact hunlC j hji hjS
    · have hjS : (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∉ S := fun h => ht (by
        simp only [tcpModelActive, Finset.mem_union]
        exact Or.inl (Or.inl h))
      exact hunlS j hjS
    · have hj : j ∉ Se := fun h => ht (by
        simp only [tcpModelActive, Finset.mem_union]
        exact Or.inl (Or.inr (Finset.mem_image_of_mem _ h)))
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hoff y hy j hj
    · have hkS : (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∉ S :=
        fun h => ht (by
          simp only [tcpModelActive, Finset.mem_union]
          exact Or.inl (Or.inl h))
      exact hunlZ k hkS
    · exfalso
      apply ht
      simp only [tcpModelActive, Finset.mem_union]
      right
      cases q <;> simp [cgpScaleTag, cgpEdgeTag]

end Point

end DifferentialGeometry.Geometry.Collapse
