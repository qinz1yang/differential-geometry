import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitativeApplications

/-!
# CGP02 (b): the Riemannian block budgets of the actual global map `𝓔⁰`

Blueprint `master207B.tex`, CGP02 (`prop:fibration-actual-global-derivative`, B:3956–4002), the
block budgets of its proof, on the ACTUAL blocks of CGP01's `𝓔⁰ = cgpGlobalMap L Z`
(`ActualGlobalBlockMap.lean`), in the physical Riemannian norm `ν = √(g_x(v, v))`, at a point of
the block's closed support. Every bound is `(a + (C + 1)(b + l)) ν` of FC02's one-block lemma
`norm_mvfderiv_block_apply_le` with `R|dη| ≤ a ν`, `R|dζ| ≤ b ν`, `|dR| ≤ l ν`, `|η| ≤ C`.

* `cgpProfileBound` (`P₀ ≥ 1`): one numerical constant bounding the first derivatives of the fixed
  profiles of `𝓔⁰` (circle bump, slim profile, the two edge profiles, LC31's annular profile, the
  `E'` profile `h`, the edge-sum ramp `χ_{1/2,1}`), fixed before every parameter.
* circle (`circle_block_budget_KA2`, `L : LocalChartFamilyQ`): `(2 + 20P₀) ν`.
* slim (`slim_block_budget_KA2`): `((1 + σ) + (89·10⁴Δ + 1) P₀(1 + σ)/(10⁵Δ)) ν`.
* zero (`zero_block_budget_KA2`, any zero-model ball, `e ≤ 1/8`):
  `((1 + ε) + (9/10 + 2e + 1) P₀(1 + ε)) ν`.
* edge (`edge_block_budget_KA2`, with the zero-extension margin): `((1 + σ) + (9Δ + 1) K) ν`,
  `K = P₀((1 + σ) + (100/99)(1 + γ))/Δ` (`EdgeFamily.cutoff_deriv_budget_KA2`: the actual cutoff
  `f(η/Δ) g(t/Δ)`; where `g` varies the point is a collar point, `ρ|dt| ≤ 1 + γ`,
  `ρ(x) ≥ (99/100)ρ(j)`, `EdgeFamily.height_lipschitz_of_collar_KA2`).
* `E'` (`edgeMarker_block_budget_KA2`): `((1 + γ) + (10Δ + 1)(b_E + Λ)) ν`,
  `b_E = P₀(1 + γ)/Δ + P₀ n (1 + 100ΔΛ) K`, `n` the number of edge cutoffs whose closed support
  contains the point.
The scale block is `norm_mvfderiv_scaleBlock_le_riemannian` (`ManifoldBlockDerivativeApplications`).
Tools: `RiemannianDerivativeTools.lean` (local Lipschitz ⇒ Riemannian derivative bound, chain
rules) and the generic lemmas `mvfderiv_apply_congr_KA2`, `mvfderiv_sum_apply_KA2`,
`mvfderiv_mul_apply_KA2`, `abs_mvfderiv_profile_div_le_KA2`, `le_of_mem_tsupport_KA2`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Profiles

/-- One constant `P₀ ≥ 1` bounding the first derivatives of every fixed profile of `𝓔⁰`. -/
theorem exists_cgpProfileBound : ∃ P : ℝ, 1 ≤ P ∧
    (∀ v : ℝ², ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ P) ∧
    (∀ t, |deriv slimCutoffProfile_LC87 t| ≤ P) ∧
    (∀ t, |deriv edgeCoordinateProfile t| ≤ P) ∧
    (∀ t, |deriv edgeHeightProfile t| ≤ P) ∧
    (∀ t, |deriv (Calculus.annularCutoff Calculus.cutoffProfile) t| ≤ P) ∧
    (∀ t, |deriv cgpEdgeH t| ≤ P) ∧
    (∀ t, |deriv (cfsRamp lc87EdgeTransition (1 / 2) 1) t| ≤ P) := by
  obtain ⟨A1, B1, hA1, hB1, h1⟩ := circleCutoffBump_budget_LC87
  have tails : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → ∀ a b cl cr : ℝ, (∀ x ≤ a, f x = cl) →
      (∀ x, b ≤ x → f x = cr) → ∃ P : ℝ, 1 ≤ P ∧ ∀ t, |deriv f t| ≤ P := by
    intro f hf a b cl cr hl hr
    obtain ⟨P, hP, hD, -⟩ := exists_derivative_bounds_of_constant_tails (hf.of_le (by simp)) hl hr
    exact ⟨P, hP, fun t => by rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]; exact hD t⟩
  obtain ⟨P2, -, h2⟩ := tails slimCutoffProfile_LC87
    (contDiff_intervalPlateauProfile _ _ _ _) (-89 / 10) (89 / 10) 0 0
    (fun _ hx => intervalPlateauProfile_zero_left (by norm_num) hx)
    (fun _ hx => intervalPlateauProfile_zero_right (by norm_num) hx)
  obtain ⟨P3, -, h3⟩ := tails edgeCoordinateProfile edgeProfiles_contDiff.1 (-9) 9 0 0
    (fun _ hx => intervalPlateauProfile_zero_left (by norm_num) hx)
    (fun _ hx => intervalPlateauProfile_zero_right (by norm_num) hx)
  obtain ⟨P4, -, h4⟩ := tails edgeHeightProfile edgeProfiles_contDiff.2.1 8 9 1 0
    (fun _ hx => descendingIntervalProfile_one (by norm_num) hx)
    (fun _ hx => descendingIntervalProfile_zero (by norm_num) hx)
  obtain ⟨P5, -, h5⟩ := Calculus.exists_abs_deriv_annularCutoff_le Calculus.cutoffProfile_contDiff
    fun _ ht => Calculus.cutoffProfile_eq_zero ht
  obtain ⟨P6, -, h6⟩ := tails cgpEdgeH cgpEdgeH_contDiff (1 / 5) 9 0 0
    (fun _ hx => cgpEdgeH_eq_zero_of_le hx) (fun _ hx => cgpEdgeH_eq_zero_of_ge hx)
  obtain ⟨P7, -, h7⟩ := tails (cfsRamp lc87EdgeTransition (1 / 2) 1)
    (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _) (1 / 2) 1 0 1
    (fun _ hx => cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) hx)
    (fun _ hx => cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hx)
  refine ⟨max 1 (max A1 (max P2 (max P3 (max P4 (max P5 (max P6 P7)))))), le_max_left _ _,
    fun v => (h1 v).1.trans ?_, fun t => (h2 t).trans ?_, fun t => (h3 t).trans ?_,
    fun t => (h4 t).trans ?_, fun t => (h5 t).trans ?_, fun t => (h6 t).trans ?_,
    fun t => (h7 t).trans ?_⟩ <;> simp only [le_max_iff, le_refl, true_or, or_true]

/-- **The profile constant `P₀`** of CGP02: one number `≥ 1` bounding the first derivatives of the
circle bump, the slim profile, the two edge profiles, LC31's annular profile, the `E'` height profile
`h` and the edge-sum ramp `χ_{1/2,1}` (all fixed before every parameter). -/
def cgpProfileBound : ℝ := Classical.choose exists_cgpProfileBound

theorem cgpProfileBound_spec : 1 ≤ cgpProfileBound ∧
    (∀ v : ℝ², ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ cgpProfileBound) ∧
    (∀ t, |deriv slimCutoffProfile_LC87 t| ≤ cgpProfileBound) ∧
    (∀ t, |deriv edgeCoordinateProfile t| ≤ cgpProfileBound) ∧
    (∀ t, |deriv edgeHeightProfile t| ≤ cgpProfileBound) ∧
    (∀ t, |deriv (Calculus.annularCutoff Calculus.cutoffProfile) t| ≤ cgpProfileBound) ∧
    (∀ t, |deriv cgpEdgeH t| ≤ cgpProfileBound) ∧
    (∀ t, |deriv (cfsRamp lc87EdgeTransition (1 / 2) 1) t| ≤ cgpProfileBound) :=
  Classical.choose_spec exists_cgpProfileBound

end Profiles

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two functions equal near `x` have the same derivative at `x`. -/
theorem mvfderiv_apply_congr_KA2 {f f' : M → F} {x : M} (h : f =ᶠ[𝓝 x] f')
    (v : TangentSpace I x) : mvfderiv I f x v = mvfderiv I f' x v := by
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC, h.mfderiv_eq]
  rfl

/-- A function continuous at a point of the closed support of `f` where `f ≠ 0 ⇒ u < c` has
`u ≤ c` there. -/
theorem le_of_mem_tsupport_KA2 {Y : Type*} [TopologicalSpace Y] {f : Y → ℝ} {u : Y → ℝ} {c : ℝ}
    {x : Y} (hx : x ∈ tsupport f) (hu : ContinuousAt u x) (hf : ∀ y, f y ≠ 0 → u y < c) :
    u x ≤ c := by
  by_contra h
  rw [not_le] at h
  have hev : ∀ᶠ y in 𝓝 x, c < u y := hu.eventually (lt_mem_nhds h)
  have h0 : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hev] with y hy
    by_contra hne
    exact absurd (hf y hne) (not_lt.mpr hy.le)
  exact (notMem_tsupport_iff_eventuallyEq.mpr h0) hx

/-- The derivative of a finite sum of real functions is the sum of the derivatives. -/
theorem mvfderiv_sum_apply_KA2 {ι : Type*} (t : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) (v : TangentSpace I x) :
    mvfderiv I (fun y => ∑ i ∈ t, f i y) x v = ∑ i ∈ t, mvfderiv I (f i) x v := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [mvfderiv_const]
    rfl
  | insert i t hi IH =>
    have hft : ∀ k ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f k) x :=
      fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ k ∈ t, f k y) x := by
      have h := MDifferentiableAt.sum (t := t) hft
      convert h using 1
      funext y
      exact (Finset.sum_apply y t f).symm
    simp only [Finset.sum_insert hi]
    rw [mvfderiv_fun_add (hf i (Finset.mem_insert_self i t)) hsum, add_apply,
      IH hft]

/-- The derivative of a product of two real functions (Leibniz rule, applied to `v`). -/
theorem mvfderiv_mul_apply_KA2 {f f' : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hf' : MDifferentiableAt I 𝓘(ℝ, ℝ) f' x) (v : TangentSpace I x) :
    mvfderiv I (fun y => f y * f' y) x v =
      f x * mvfderiv I f' x v + f' x * mvfderiv I f x v := by
  rw [mvfderiv_fun_mul hf hf']
  rfl

/-- The derivative of `t ↦ f(t/c)` for a differentiable profile `f`. -/
theorem hasDerivAt_comp_div_KA2 {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c t : ℝ) :
    HasDerivAt (fun s => f (s / c)) (deriv f (t / c) * (1 / c)) t :=
  (hf (t / c)).hasDerivAt.comp t ((hasDerivAt_id' t).div_const c)

/-- A profile `f` with `|f'| ≤ P` after `u/c`: `|d(f(u/c))(v)| ≤ (P/c)|du(v)|`. -/
theorem abs_mvfderiv_profile_div_le_KA2 {f : ℝ → ℝ} (hf : Differentiable ℝ f) {P : ℝ}
    (hP : ∀ s, |deriv f s| ≤ P) {c : ℝ} (hc : 0 < c) {u : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) (v : TangentSpace I x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f (u y / c)) x ∧
      |mvfderiv I (fun y => f (u y / c)) x v| ≤ P / c * |mvfderiv I u x v| := by
  have hd := hasDerivAt_comp_div_KA2 hf c (u x)
  refine ⟨hd.differentiableAt.comp_mdifferentiableAt hu, ?_⟩
  rw [mvfderiv_comp_hasDerivAt hu hd v, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hc)]
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  calc |deriv f (u x / c)| * (1 / c) * |mvfderiv I u x v| ≤ P * (1 / c) * |mvfderiv I u x v| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hP _) (one_div_pos.mpr hc).le)
          (abs_nonneg _)
    _ = P / c * |mvfderiv I u x v| := by ring

end Generic

section Families

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}

/-- The circle chart coordinate `η_j : X → ℝ²` of the family (normalized at `j`); the coordinate
of the circle block of `𝓔⁰`. -/
def cgpCircleCoord (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (j : X) (hj : j ∈ L.circle.centres) : X → ℝ² :=
  let c := L.circle.chart j hj
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  c.coord

/-- The circle coordinate `η_j` is `2/ρ(j)`-Lipschitz on the physical ball `B(j, 200ρ(j))`. -/
theorem cgpCircleCoord_lipschitz
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.circle.centres) :
    ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
      ‖cgpCircleCoord L j hj y - cgpCircleCoord L j hj z‖ ≤ 2 / ρ j * dist y z := by
  intro y hy z hz
  have hc := L.circle.chart_center j hj
  have hrj := hρ j
  have hy1 : (ρ j)⁻¹ * dist y j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have hz1 : (ρ j)⁻¹ * dist z j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hz
  have he : ((2 : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) = 2 / ρ j * dist y z := by
    push_cast
    ring
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have hy' : y ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist y c.center < 200
    rw [hc']
    exact hy1
  have hz' : z ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist z c.center < 200
    rw [hc']
    exact hz1
  have h := c.lipschitz.dist_le_mul y hy' z hz'
  change @dist ℝ² _ (c.coord y) (c.coord z) ≤
    ((2 : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change ‖c.coord y - c.coord z‖ ≤ 2 / ρ j * @dist X mX.toDist y z
  rw [← dist_eq_norm]
  linarith

/-- The circle coordinate is smooth on the physical ball `B(j, 200ρ(j))`. -/
theorem cgpCircleCoord_contMDiffOn
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.circle.centres) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCircleCoord L j hj) (ball j (200 * ρ j)) := by
  have hc := L.circle.chart_center j hj
  have hrj := hρ j
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  refine c.contMDiffOn_coord.mono fun x hx => ?_
  have hd := @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j x 200 hrj hx
  change (ρ j)⁻¹ * @dist X mX.toDist x c.center < 200
  rw [hc']
  exact hd

/-- Near a point of the physical ball `B(j, 200ρ(j))` the circle cutoff is `ψ ∘ η_j`
(LC87 packet (ii)). -/
theorem circle_cutoff_eventuallyEq_KA2
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax) {j : X}
    (hj : j ∈ L.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    L.circle.cutoff j =ᶠ[𝓝 x]
      fun y => circleCutoffBump_LC87 (cgpCircleCoord L.toLocalChartFamily j hj y) := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have h : L.circle.cutoff j y = if dist y j < 200 * ρ j then
      circleCutoffBump_LC87 (cgpCircleCoord L.toLocalChartFamily j hj y) else 0 :=
    L.circle_cutoff_apply hj y
  simp only [h, mem_ball.mp hy, ↓reduceIte]

/-- **CGP02 (b), circle block.** At a point of the closed support of the circle cutoff `ζ_j`, the
circle block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` has Riemannian derivative at most `(2 + 20P₀) ν`
(`R|dη| ≤ 2`, `R|dζ| ≤ 2P₀`, `‖η‖ ≤ 9`). -/
theorem circle_block_budget_KA2
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax) {j : X}
    (hj : j ∈ L.circle.centres) {x : X} (hx : x ∈ tsupport (L.circle.cutoff j))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * L.circle.cutoff j y) •
        cgpCircleCoord L.toLocalChartFamily j hj y, ρ j * L.circle.cutoff j y)) x v‖ ≤
      (2 + 20 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  have hxb : x ∈ ball j (200 * ρ j) := L.circle.tsupport_subset_ball j hj hx
  obtain ⟨hP1, hψ, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  set η := cgpCircleCoord L.toLocalChartFamily j hj with hηdef
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) η x :=
    ((cgpCircleCoord_contMDiffOn L.toLocalChartFamily hj).contMDiffAt
      (isOpen_ball.mem_nhds hxb)).mdifferentiableAt (by simp)
  have hη : ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ 2 / ρ j * Real.sqrt (g.inner x v v) :=
    norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hxb hηd (by positivity)
      (cgpCircleCoord_lipschitz L.toLocalChartFamily hj) v
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.circle.cutoff j) x :=
    (L.circle.contMDiff_cutoff j hj x).mdifferentiableAt (by simp)
  have hψd : HasFDerivAt (circleCutoffBump_LC87 : ℝ² → ℝ)
      (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) (η x)) (η x) :=
    ((circleCutoffBump_LC87.contDiff (n := 1)).differentiable (by simp) (η x)).hasFDerivAt
  have hζ : |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
      cgpProfileBound * (2 / ρ j * Real.sqrt (g.inner x v v)) := by
    rw [mvfderiv_apply_congr_KA2 (circle_cutoff_eventuallyEq_KA2 L hj hxb) v,
      mvfderiv_comp_hasFDerivAt hηd hψd v, ← Real.norm_eq_abs]
    exact ((fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) (η x)).le_opNorm _).trans
      (mul_le_mul (hψ _) hη (norm_nonneg _) (by linarith))
  have hC : ‖η x‖ ≤ 9 :=
    le_of_mem_tsupport_KA2 (u := fun y => ‖η y‖) hx hηd.continuousAt.norm
      (fun y hy => (L.circle.coord_lt_of_cutoff_ne_zero j hj y hy).2)
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ 2 * Real.sqrt (g.inner x v v) := by
    calc ρ j * ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ ρ j * (2 / ρ j * Real.sqrt (g.inner x v v)) :=
          mul_le_mul_of_nonneg_left hη hrj.le
      _ = 2 * Real.sqrt (g.inner x v v) := by field_simp
  have hb : ρ j * |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
      2 * cgpProfileBound * Real.sqrt (g.inner x v v) := by
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
          ρ j * (cgpProfileBound * (2 / ρ j * Real.sqrt (g.inner x v v))) :=
          mul_le_mul_of_nonneg_left hζ hrj.le
      _ = 2 * cgpProfileBound * Real.sqrt (g.inner x v v) := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * Real.sqrt (g.inner x v v) := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := L.circle.cutoff j)
    (η := η) mdifferentiableAt_const hζd hηd v hrj.le (L.circle.cutoff_mem_Icc j hj x) hC ha hb hl
  have he : (2 + (9 + 1) * (2 * cgpProfileBound + 0)) * Real.sqrt (g.inner x v v) =
      (2 + 20 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by ring
  rw [he] at h
  exact h

/-- The slim coordinate is `(1 + σ)/ρ(j)`-Lipschitz for the physical distance. -/
theorem slimCentre_coord_lipschitz_KA2 {β₁ : ℝ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ 1 + σs) (y z : X) :
    |c.coord y - c.coord z| ≤ (1 + σs) / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σs) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + σs) / ρ j * dist y z := by
    rw [Real.coe_toNNReal _ hσs]
    field_simp
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := P.lipschitz.dist_le_mul y z
  change |P.coord y - P.coord z| ≤
    ((Real.toNNReal (1 + σs) : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change |P.coord y - P.coord z| ≤ (1 + σs) / ρ j * @dist X mX.toDist y z
  linarith

/-- Where the slim cutoff is nonzero, `|η_j| < 89·10⁴Δ`. -/
theorem slimCentre_abs_coord_lt_of_cutoff_ne_zero_KA2 {β₁ : ℝ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {y : X} (hy : c.cutoff y ≠ 0) :
    |c.coord y| < 89 * 10 ^ 4 * Δ := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact (P.cutoff_ne_zero y hy).2

theorem slimFamily_cutoff_eq_KA2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.slim.centres) : L.slim.cutoff j = (L.slim.centre j hj).cutoff := by
  unfold SlimFamily.cutoff
  rw [dite_eq_left hj]

/-- Near a point of the physical ball `B(j, 10⁶Δρ(j))` the slim cutoff is `φ(η_j/(10⁵Δ))`
(LC87 packet (ii)). -/
theorem slim_cutoff_eventuallyEq_KA2
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax) {j : X}
    (hj : j ∈ L.slim.centres) {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) :
    L.slim.cutoff j =ᶠ[𝓝 x]
      fun y => slimCutoffProfile_LC87 ((L.slim.centre j hj).coord y / (10 ^ 5 * Δ)) := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [slimFamily_cutoff_eq_KA2 L.toLocalChartFamily hj, L.slim_cutoff_apply hj y]
  simp only [mem_ball.mp hy, ↓reduceIte]

/-- **CGP02 (b), slim block.** At a point of the closed support of the slim cutoff `ζ_j`, the slim
block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` (`η_j` on the axis of `ℝ²`) has Riemannian derivative at most
`((1 + σ) + (89·10⁴Δ + 1)·P₀(1 + σ)/(10⁵Δ)) ν` (`ℓ = 10⁵Δ`: `R|dη| ≤ 1 + σ`,
`R|dζ| ≤ P₀(1 + σ)/ℓ`, `|η| ≤ 8.9ℓ`). -/
theorem slim_block_budget_KA2
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΔ : 0 < Δ) (hσs : 0 ≤ σs) {j : X} (hj : j ∈ L.slim.centres) {x : X}
    (hx : x ∈ tsupport (L.slim.cutoff j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * L.slim.cutoff j y) •
        planeAxis ((L.slim.centre j hj).coord y), ρ j * L.slim.cutoff j y)) x v‖ ≤
      ((1 + σs) + (89 * 10 ^ 4 * Δ + 1) * (cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ))) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  obtain ⟨h1, h2, h3, hcm⟩ := fc18_slim_row L.toLocalChartFamily hΔ hj
  have hxb : x ∈ ball j (10 ^ 6 * Δ * ρ j) := h3 (h2 (h1 hx))
  obtain ⟨hP1, -, hφ, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hc0 : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  set u := (L.slim.centre j hj).coord with hudef
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    (hcm.contMDiffAt (isOpen_ball.mem_nhds hxb)).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + σs) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hxb hud
      (fun y _ z _ => slimCentre_coord_lipschitz_KA2 _ (by linarith) y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (u y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hη : ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ = |mvfderiv 𝓘(ℝ, E3) u x v| := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.slim.cutoff j) x := by
    rw [slimFamily_cutoff_eq_KA2 L.toLocalChartFamily hj]
    exact ((L.slim.centre j hj).contMDiff_cutoff x).mdifferentiableAt (by simp)
  have hφd : HasDerivAt (fun t => slimCutoffProfile_LC87 (t / (10 ^ 5 * Δ)))
      (deriv slimCutoffProfile_LC87 (u x / (10 ^ 5 * Δ)) * (1 / (10 ^ 5 * Δ))) (u x) := by
    have hd : DifferentiableAt ℝ slimCutoffProfile_LC87 (u x / (10 ^ 5 * Δ)) :=
      ((contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).differentiable
        (by simp)) _
    exact hd.hasDerivAt.comp (u x) ((hasDerivAt_id' (u x)).div_const (10 ^ 5 * Δ))
  have hζ : |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff j) x v| ≤
      cgpProfileBound * (1 / (10 ^ 5 * Δ)) * ((1 + σs) / ρ j * ν) := by
    rw [mvfderiv_apply_congr_KA2 (slim_cutoff_eventuallyEq_KA2 L hj hxb) v,
      mvfderiv_comp_hasDerivAt hud hφd v, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hc0)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hφ _) (one_div_pos.mpr hc0).le) hu
      (abs_nonneg _) (by positivity)
  have hC : ‖planeAxis (u x)‖ ≤ 89 * 10 ^ 4 * Δ := by
    rw [norm_planeAxis]
    refine le_of_mem_tsupport_KA2 (u := fun y => |u y|) hx hud.continuousAt.abs fun y hy => ?_
    rw [slimFamily_cutoff_eq_KA2 L.toLocalChartFamily hj] at hy
    exact slimCentre_abs_coord_lt_of_cutoff_ne_zero_KA2 _ hy
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ ≤ (1 + σs) * ν := by
    rw [hη]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) u x v| ≤ ρ j * ((1 + σs) / ρ j * ν) :=
          mul_le_mul_of_nonneg_left hu hrj.le
      _ = (1 + σs) * ν := by field_simp
  have hb : ρ j * |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff j) x v| ≤
      cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ) * ν := by
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff j) x v| ≤
          ρ j * (cgpProfileBound * (1 / (10 ^ 5 * Δ)) * ((1 + σs) / ρ j * ν)) :=
          mul_le_mul_of_nonneg_left hζ hrj.le
      _ = cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ) * ν := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := L.slim.cutoff j)
    (η := fun y => planeAxis (u y)) mdifferentiableAt_const hζd hηd v hrj.le
    ((slimFamily_cutoff_eq_KA2 L.toLocalChartFamily hj) ▸ (L.slim.centre j hj).cutoff_mem_Icc x)
    hC ha hb hl
  rw [add_zero] at h
  exact h

omit [CompactSpace X] in
/-- Physical facts of the original radial function of a zero-model ball (from its LC30 clauses at
the scale `radius`). -/
theorem zeroModelBall_radial_facts_KA2 {N' C' : X → Type} [∀ a, MetricSpace (N' a)]
    [∀ a, ChartedSpace E3 (N' a)] [∀ a, MetricSpace (C' a)] {o' : ∀ a, C' a} {δ' εr e : ℝ}
    (Zb : ZeroModelBall 𝓘(ℝ, E3) X g N' C' o' δ' εr e) (hεr : 0 ≤ 1 + εr) :
    (∀ y z, |Zb.radial y - Zb.radial z| ≤ (1 + εr) / Zb.radius * dist y z) ∧
      (∀ y, 0 ≤ Zb.radial y) ∧
      (∀ y, |Zb.radial y - Zb.radius⁻¹ * dist y Zb.center| < e) ∧
      tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)) ⊆
        {y | 1 / 5 - e < Zb.radius⁻¹ * dist y Zb.center ∧
          Zb.radius⁻¹ * dist y Zb.center < 9 / 10 + e} ∧
      ∃ O : Set X, IsOpen O ∧ {y | 3 / 40 ≤ Zb.radius⁻¹ * dist y Zb.center ∧
          Zb.radius⁻¹ * dist y Zb.center ≤ 11} ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ Zb.radial O := by
  have hr := Zb.radius_pos
  have he : ∀ y z : X, ((Real.toNNReal (1 + εr) : NNReal) : ℝ) * (Zb.radius⁻¹ * dist y z) =
      (1 + εr) / Zb.radius * dist y z := fun y z => by
    rw [Real.coe_toNNReal _ hεr]
    field_simp
  obtain ⟨hlip, ⟨O, hO, hOsub, hOsm⟩, hclose, -, -, hnn, -, -, -, -, -, hcut⟩ := Zb.radial_spec
  obtain ⟨-, -, -, -, -, -, hts, -⟩ := hcut
  refine ⟨fun y z => ?_, hnn, fun y => ?_, hts, O, hO, hOsub, hOsm⟩
  · have h' : |Zb.radial y - Zb.radial z| ≤
        ((Real.toNNReal (1 + εr) : NNReal) : ℝ) * (Zb.radius⁻¹ * dist y z) :=
      @LipschitzWith.dist_le_mul X ℝ
        (mX.rescale Zb.radius⁻¹ (inv_pos.mpr Zb.radius_pos)).toPseudoMetricSpace _ _ _ hlip y z
    linarith [he y z]
  · have h := hclose y
    rw [@Metric.infDist_singleton X
      (mX.rescale Zb.radius⁻¹ (inv_pos.mpr Zb.radius_pos)).toPseudoMetricSpace] at h
    exact h

/-- **CGP02 (b), zero block.** At a point of the closed support of LC31's annular cutoff
`Φ ∘ r` of a zero-model ball (`e ≤ 1/8`), the zero block `(R Φ(r) r, R Φ(r))` (`r` on the axis of
`ℝ²`, `R` the ball's radius) has Riemannian derivative at most
`((1 + ε) + (9/10 + 2e + 1)·P₀(1 + ε)) ν` (`R|dr| ≤ 1 + ε`, `R|dζ| ≤ P₀(1 + ε)`,
`|r| ≤ 9/10 + 2e`). -/
theorem zero_block_budget_KA2 {N' C' : X → Type} [∀ a, MetricSpace (N' a)]
    [∀ a, ChartedSpace E3 (N' a)] [∀ a, MetricSpace (C' a)] {o' : ∀ a, C' a} {δ' εr e : ℝ}
    (Zb : ZeroModelBall 𝓘(ℝ, E3) X g N' C' o' δ' εr e)
    (hmet : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (hεr : 0 ≤ εr)
    (he : e ≤ 1 / 8) {x : X} (hx : x ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2
        ((Zb.radius * Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)) •
          planeAxis (Zb.radial y),
        Zb.radius * Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y))) x v‖ ≤
      ((1 + εr) + (9 / 10 + 2 * e + 1) * (cgpProfileBound * (1 + εr))) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  obtain ⟨hlip, hnn, hclose, hts, O, hO, hOsub, hOsm⟩ :=
    zeroModelBall_radial_facts_KA2 Zb (by linarith)
  have hxs := hts hx
  have hxO : x ∈ O := hOsub ⟨by linarith [hxs.1], by linarith [hxs.2]⟩
  obtain ⟨hP1, -, -, -, -, hΦ, -⟩ := cgpProfileBound_spec
  have hr := Zb.radius_pos
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  set u := Zb.radial with hudef
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    (hOsm.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + εr) / Zb.radius * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmet isOpen_univ (mem_univ x) hud
      (fun y _ z _ => hlip y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (u y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hη : ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ = |mvfderiv 𝓘(ℝ, E3) u x v| := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
  have hΦd : HasDerivAt (Calculus.annularCutoff Calculus.cutoffProfile)
      (deriv (Calculus.annularCutoff Calculus.cutoffProfile) (u x)) (u x) :=
    ((Calculus.annularCutoff_contDiff Calculus.cutoffProfile_contDiff).differentiable (by simp)
      (u x)).hasDerivAt
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x :=
    hΦd.differentiableAt.comp_mdifferentiableAt hud
  have hζ : |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v|
      ≤ cgpProfileBound * ((1 + εr) / Zb.radius * ν) := by
    rw [mvfderiv_comp_hasDerivAt hud hΦd v, abs_mul]
    exact mul_le_mul (hΦ _) hu (abs_nonneg _) (by linarith)
  have hC : ‖planeAxis (u x)‖ ≤ 9 / 10 + 2 * e := by
    rw [norm_planeAxis, abs_of_nonneg (hnn x)]
    have h := abs_lt.mp (hclose x)
    linarith [hxs.2]
  have ha : Zb.radius * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ ≤ (1 + εr) * ν := by
    rw [hη]
    calc Zb.radius * |mvfderiv 𝓘(ℝ, E3) u x v| ≤ Zb.radius * ((1 + εr) / Zb.radius * ν) :=
          mul_le_mul_of_nonneg_left hu hr.le
      _ = (1 + εr) * ν := by field_simp
  have hb : Zb.radius *
      |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v| ≤
      cgpProfileBound * (1 + εr) * ν := by
    calc Zb.radius *
          |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v|
        ≤ Zb.radius * (cgpProfileBound * ((1 + εr) / Zb.radius * ν)) :=
          mul_le_mul_of_nonneg_left hζ hr.le
      _ = cgpProfileBound * (1 + εr) * ν := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => Zb.radius) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have hz : Calculus.annularCutoff Calculus.cutoffProfile (u x) ∈ Icc (0 : ℝ) 1 :=
    Calculus.annularCutoff_mem_Icc Calculus.cutoffProfile_mem_Icc _
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => Zb.radius)
    (ζ := fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y))
    (η := fun y => planeAxis (u y)) mdifferentiableAt_const hζd hηd v hr.le hz hC ha hb hl
  rw [add_zero] at h
  exact h

/-- The edge coordinate `η_j` is `(1 + σ)/ρ(j)`-Lipschitz for the physical distance. -/
theorem EdgeFamily.coord_lipschitz_KA2 {β : ℕ → ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hσc : 0 ≤ 1 + σc) {j : X}
    (hj : j ∈ F.centres) (y z : X) :
    |F.coord j y - F.coord j z| ≤ (1 + σc) / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + σc) / ρ j * dist y z := by
    rw [Real.coe_toNNReal _ hσc]
    field_simp
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := C.lipschitz.dist_le_mul y z
  change |C.coord y - C.coord z| ≤
    ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change |C.coord y - C.coord z| ≤ (1 + σc) / ρ j * @dist X mX.toDist y z
  linarith

theorem abs_euclid_one_sub_le_KA2 (u w : ℝ²) : |u 1 - w 1| ≤ ‖u - w‖ := by
  have h := PiLp.norm_apply_le (u - w) 1
  rw [Real.norm_eq_abs] at h
  exact h

/-- **The edge height near a collar point** (LFR38's collar, LC84 item 3): at a collar point `x` of
the chart at `j`, `ρ(x)/ρ(j) ≥ 99/100` and `t = F/ρ` is `(1 + γ)/ρ(x)`-Lipschitz on the physical
ball `B(x, 100ρ(x))`. -/
theorem EdgeFamily.height_lipschitz_of_collar_KA2 {β : ℕ → ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hcoord : |F.coord j x| ≤ 10 * Δ)
    (h1 : Δ / 10 ≤ F.smoothing x / ρ x) (h2 : F.smoothing x / ρ x ≤ 10 * Δ) :
    99 / 100 ≤ ρ x / ρ j ∧ ∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x),
      |F.smoothing y / ρ y - F.smoothing z / ρ z| ≤ (1 + γc) / ρ x * dist y z := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : ∀ y, Fs y / ρ j / (ρ y / ρ j) = Fs y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hball : ∀ y ∈ ball x (100 * ρ x), (ρ j)⁻¹ * dist y x < 100 * (ρ x / ρ j) := by
    intro y hy
    have := mem_ball.mp hy
    rw [inv_mul_lt_iff₀ hrj]
    field_simp
    linarith
  have hlipeq : ∀ y z : X, (1 + γc) * ((ρ j)⁻¹ * dist y z / (ρ x / ρ j)) =
      (1 + γc) / ρ x * dist y z := fun y z => by
    field_simp
  unfold EdgeFamily.coord at hcoord
  rw [dite_eq_left hj] at hcoord
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  have hcoord' : |C.coord x| ≤ 10 * Δ := hcoord
  have h1' : Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) := by rw [hq]; exact h1
  have h2' : Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by rw [hq]; exact h2
  obtain ⟨hqq, -, -, -, hJlip, -⟩ := C.collar x hmem hcoord' h1' h2'
  refine ⟨hqq.1, fun y hy z hz => ?_⟩
  have hy' : y ∈ ball x (100 * (ρ x / ρ j)) := hball y hy
  have hz' : z ∈ ball x (100 * (ρ x / ρ j)) := hball z hz
  have h := (abs_euclid_one_sub_le_KA2 _ _).trans (hJlip y hy' z hz')
  change |Fs y / ρ j / (ρ y / ρ j) - Fs z / ρ j / (ρ z / ρ j)| ≤
    (1 + γc) * ((ρ j)⁻¹ * @dist X mX.toDist y z / (ρ x / ρ j)) at h
  rw [hq y, hq z, hlipeq y z] at h
  exact h

/-- **The actual edge cutoff's derivative budget** on the physical chart ball (CGP02's
`R|dζ| ≤ 5P₀/Δ`, here `P₀((1 + σ) + (100/99)(1 + γ))/Δ`): the cutoff is
`f(η_j/Δ) g(t/Δ)`; where `g` varies the point is a collar point (`ρ(x) ≥ (99/100)ρ(j)`,
`ρ|dt| ≤ 1 + γ`). -/
theorem EdgeFamily.cutoff_deriv_budget_KA2 {β : ℕ → ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) (hσc : 0 ≤ σc)
    (hγc : 0 ≤ γc) (hρc : Continuous ρ) {j : X} (hj : j ∈ F.centres) {x : X}
    (hxb : x ∈ ball j (100 * Δ * ρ j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ρ j * |mvfderiv 𝓘(ℝ, E3) (F.cutoff j) x v| ≤
      cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  obtain ⟨hP1, -, -, hf, hg, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hrx := hρ x
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hK : 0 ≤ cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by positivity
  have hfd : Differentiable ℝ edgeCoordinateProfile :=
    edgeProfiles_contDiff.1.differentiable (by simp)
  have hgd : Differentiable ℝ edgeHeightProfile :=
    edgeProfiles_contDiff.2.1.differentiable (by simp)
  set u := F.coord j with hudef
  set t : X → ℝ := fun y => F.smoothing y / ρ y with htdef
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have heq : F.cutoff j =ᶠ[𝓝 x] fun y => edgeCoordinateProfile (u y / Δ) *
      edgeHeightProfile (t y / Δ) := by
    filter_upwards [hball] with y hy
    exact F.cutoff_eq_formula hj hy
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    ((F.contMDiffOn_coord hj).contMDiffAt hball).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + σc) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
      (fun y _ z _ => F.coord_lipschitz_KA2 (by linarith) hj y z) v
  obtain ⟨hAd, hA⟩ := abs_mvfderiv_profile_div_le_KA2 hfd hf hΔ hud v
  have htc : Continuous fun y => t y / Δ :=
    (F.lipschitz_smoothing.continuous.div hρc fun y => (hρ y).ne').div_const Δ
  have hzero : F.cutoff j =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) →
      ρ j * |mvfderiv 𝓘(ℝ, E3) (F.cutoff j) x v| ≤
        cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by
    intro h0
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [mvfderiv_apply_congr_KA2 heq v]
  -- case analysis
  by_cases hcx : 9 * Δ < |u x|
  · have hA0 : (fun y => edgeCoordinateProfile (u y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      have hcc : ContinuousAt u x := hud.continuousAt
      rcases lt_abs.mp hcx with hpos | hneg
      · filter_upwards [hcc.eventually (lt_mem_nhds hpos)] with y hy
        refine intervalPlateauProfile_zero_right (by norm_num) ?_
        rw [le_div_iff₀ hΔ]
        linarith
      · have hneg' : u x < -(9 * Δ) := by linarith
        filter_upwards [hcc.eventually (gt_mem_nhds hneg')] with y hy
        refine intervalPlateauProfile_zero_left (by norm_num) ?_
        rw [div_le_iff₀ hΔ]
        linarith
    have h0 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [hA0] with y hy
      rw [hy, zero_mul]
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [not_lt] at hcx
  by_cases h9 : 9 < t x / Δ
  · have h0 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [htc.continuousAt.eventually (lt_mem_nhds h9)] with y hy
      rw [show edgeHeightProfile (t y / Δ) = 0 from
        descendingIntervalProfile_zero (by norm_num) hy.le, mul_zero]
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [not_lt] at h9
  by_cases h8 : t x / Δ < 8
  · have h1 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun y => edgeCoordinateProfile (u y / Δ) := by
      filter_upwards [htc.continuousAt.eventually (gt_mem_nhds h8)] with y hy
      rw [show edgeHeightProfile (t y / Δ) = 1 from
        descendingIntervalProfile_one (by norm_num) hy.le, mul_one]
    rw [mvfderiv_apply_congr_KA2 h1 v]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
        ≤ ρ j * (cgpProfileBound / Δ * ((1 + σc) / ρ j * ν)) :=
          mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hu (by positivity)))
            hrj.le
      _ = cgpProfileBound * (1 + σc) / Δ * ν := by field_simp
      _ ≤ cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by
          have h0 : 0 ≤ cgpProfileBound * (100 / 99 * (1 + γc)) / Δ * ν := by positivity
          have he : cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν =
              cgpProfileBound * (1 + σc) / Δ * ν +
                cgpProfileBound * (100 / 99 * (1 + γc)) / Δ * ν := by ring
          linarith
  rw [not_lt] at h8
  -- collar case
  have htx : t x = Δ * (t x / Δ) := by field_simp
  have hc1 : Δ / 10 ≤ F.smoothing x / ρ x := by
    change Δ / 10 ≤ t x
    rw [htx]
    nlinarith
  have hc2 : F.smoothing x / ρ x ≤ 10 * Δ := by
    change t x ≤ 10 * Δ
    rw [htx]
    nlinarith
  have hcoord10 : |F.coord j x| ≤ 10 * Δ := by
    change |u x| ≤ 10 * Δ
    linarith
  obtain ⟨hratio, htlip⟩ := F.height_lipschitz_of_collar_KA2 hj hxb hcoord10 hc1 hc2
  have htd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) t x :=
    (F.contMDiffAt_height_of_collar hj hxb hcoord10 hc1 hc2).mdifferentiableAt (by simp)
  have hx100 : x ∈ ball x (100 * ρ x) := mem_ball_self (by positivity)
  have ht : |mvfderiv 𝓘(ℝ, E3) t x v| ≤ (1 + γc) / ρ x * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100 htd htlip v
  obtain ⟨hBd, hB⟩ := abs_mvfderiv_profile_div_le_KA2 hgd hg hΔ htd v
  rw [mvfderiv_mul_apply_KA2 hAd hBd v]
  have hfx := (edgeProfiles_mem_Icc (u x / Δ)).1
  have hgx := (edgeProfiles_mem_Icc (t x / Δ)).2.1
  have hratio' : ρ j / ρ x ≤ 100 / 99 := by
    rw [div_le_iff₀ hrx]
    rw [le_div_iff₀ hrj] at hratio
    linarith
  have hT1 : |edgeCoordinateProfile (u x / Δ) *
      mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v| ≤
      cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) := by
    rw [abs_mul, abs_of_nonneg hfx.1]
    calc edgeCoordinateProfile (u x / Δ) *
          |mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v|
        ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) t x v|) :=
          mul_le_mul hfx.2 hB (abs_nonneg _) zero_le_one
      _ ≤ cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hT2 : |edgeHeightProfile (t x / Δ) *
      mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v| ≤
      cgpProfileBound / Δ * ((1 + σc) / ρ j * ν) := by
    rw [abs_mul, abs_of_nonneg hgx.1]
    calc edgeHeightProfile (t x / Δ) *
          |mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
        ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) u x v|) :=
          mul_le_mul hgx.2 hA (abs_nonneg _) zero_le_one
      _ ≤ cgpProfileBound / Δ * ((1 + σc) / ρ j * ν) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hsum := (abs_add_le _ _).trans (add_le_add hT1 hT2)
  have hrjx : ρ j * ((1 + γc) / ρ x) ≤ 100 / 99 * (1 + γc) := by
    rw [mul_div_assoc', mul_comm (ρ j), mul_div_assoc]
    calc (1 + γc) * (ρ j / ρ x) ≤ (1 + γc) * (100 / 99) :=
          mul_le_mul_of_nonneg_left hratio' (by linarith)
      _ = 100 / 99 * (1 + γc) := by ring
  calc ρ j * |edgeCoordinateProfile (u x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v +
        edgeHeightProfile (t x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
      ≤ ρ j * (cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) +
          cgpProfileBound / Δ * ((1 + σc) / ρ j * ν)) := mul_le_mul_of_nonneg_left hsum hrj.le
    _ = cgpProfileBound / Δ * ν * (ρ j * ((1 + γc) / ρ x)) +
          cgpProfileBound * (1 + σc) / Δ * ν := by field_simp
    _ ≤ cgpProfileBound / Δ * ν * (100 / 99 * (1 + γc)) +
          cgpProfileBound * (1 + σc) / Δ * ν := by gcongr
    _ = cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by ring

/-- The actual edge cutoff takes values in `[0, 1]`. -/
theorem EdgeFamily.cutoff_mem_Icc_KA2 {β : ℕ → ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) (j x : X) :
    F.cutoff j x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : F.cutoff j x = 0
  · rw [h]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨hj, hball, -, -⟩ := F.mem_of_cutoff_ne_zero hΔ h
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [F.cutoff_eq_formula hj hx]
  have h1 := (edgeProfiles_mem_Icc (F.coord j x / Δ)).1
  have h2 := (edgeProfiles_mem_Icc (F.smoothing x / ρ x / Δ)).2.1
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **CGP02 (b), edge block.** At a point of the closed support of the actual edge cutoff `ζ_j`
(with the zero-extension margin), the edge block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` has Riemannian
derivative at most `((1 + σ) + (9Δ + 1) K) ν`, `K = P₀((1 + σ) + (100/99)(1 + γ))/Δ`
(`R|dη| ≤ 1 + σ`, `R|dζ| ≤ K`, `|η| ≤ 9Δ`). -/
theorem edge_block_budget_KA2 {β : ℕ → ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) (hσc : 0 ≤ σc)
    (hγc : 0 ≤ γc) (hρc : Continuous ρ) {j : X} (hj : j ∈ F.centres)
    (hm : tsupport (F.cutoff j) ⊆ ball j (100 * Δ * ρ j)) {x : X}
    (hx : x ∈ tsupport (F.cutoff j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * F.cutoff j y) • planeAxis (F.coord j y),
        ρ j * F.cutoff j y)) x v‖ ≤
      ((1 + σc) + (9 * Δ + 1) * (cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ)) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  have hxb := hm hx
  have hrj := hρ j
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.coord j) x :=
    ((F.contMDiffOn_coord hj).contMDiffAt hball).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) (F.coord j) x v| ≤ (1 + σc) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
      (fun y _ z _ => F.coord_lipschitz_KA2 (by linarith) hj y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (F.coord j y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.cutoff j) x :=
    (F.contMDiff_cutoff_of_margin hΔ hρc hm x).mdifferentiableAt (by simp)
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (F.coord j y)) x v‖ ≤
      (1 + σc) * ν := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (F.coord j) x v| ≤ ρ j * ((1 + σc) / ρ j * ν) :=
          mul_le_mul_of_nonneg_left hu hrj.le
      _ = (1 + σc) * ν := by field_simp
  have hb := F.cutoff_deriv_budget_KA2 hΔ hσc hγc hρc hj hxb v
  have hC : ‖planeAxis (F.coord j x)‖ ≤ 9 * Δ := by
    rw [norm_planeAxis]
    exact le_of_mem_tsupport_KA2 (u := fun y => |F.coord j y|) hx hud.continuousAt.abs
      fun y hy => (F.mem_of_cutoff_ne_zero hΔ hy).2.2.1
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := F.cutoff j)
    (η := fun y => planeAxis (F.coord j y)) mdifferentiableAt_const hζd hηd v hrj.le
    (F.cutoff_mem_Icc_KA2 hΔ j x) hC ha hb hl
  rw [add_zero] at h
  exact h

open Classical in
/-- **CGP02 (b), the `E'` block** `(ρ z₀ t, ρ z₀)`, `z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i)`, at a point of
its closed support (with the edge zero-extension margin): its Riemannian derivative is at most
`((1 + γ) + (10Δ + 1)(b_E + Λ)) ν` with
`b_E = P₀(1 + γ)/Δ + P₀ n (1 + 100ΔΛ) K` (`n` = number of edge cutoffs whose closed support contains
the point, `K` the edge budget): `ρ|dt| ≤ 1 + γ` (collar), `|dρ| ≤ Λ`, `t ≤ 10Δ`,
`ρ(x) ≤ (1 + 100ΔΛ)ρ(i)` on `B̄(i, 100Δρ(i))`. -/
theorem edgeMarker_block_budget_KA2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hσc : 0 ≤ σc) (hγc : 0 ≤ γc)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j))
    {x : X} (hx : x ∈ tsupport (cgpEdgeMarker L)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ y * cgpEdgeMarker L y) •
        planeAxis (cgpHeight L y), ρ y * cgpEdgeMarker L y)) x v‖ ≤
      ((1 + γc) + (10 * Δ + 1) * (cgpProfileBound * (1 + γc) / Δ +
        cgpProfileBound * ((Finset.univ.filter fun i : L.edge.finite_centres.toFinset =>
          x ∈ tsupport (L.edge.cutoff i)).card : ℝ) *
          ((1 + 100 * Δ * Λ) * (cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ)) +
        Λ)) * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  obtain ⟨hP1, -, -, -, -, -, hH, hRmp⟩ := cgpProfileBound_spec
  set Kb := cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ with hKdef
  set ν := Real.sqrt (g.inner x v v) with hνdef
  set n : ℝ := ((Finset.univ.filter fun i : L.edge.finite_centres.toFinset =>
    x ∈ tsupport (L.edge.cutoff i)).card : ℝ) with hndef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Kb := by positivity
  have hrx := hρ x
  have hρc : Continuous ρ := L.contMDiff_scale.continuous
  obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := tsupport_cgpEdgeMarker_subset L hΔ hmargin hx
  obtain ⟨-, htlip⟩ := L.edge.height_lipschitz_of_collar_KA2 hk hxk hck.le hk1.le hk2.le
  have htd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpHeight L) x :=
    (L.edge.contMDiffAt_height_of_collar hk hxk hck.le hk1.le hk2.le).mdifferentiableAt (by simp)
  have hx100 : x ∈ ball x (100 * ρ x) := mem_ball_self (by positivity)
  have ht : |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| ≤ (1 + γc) / ρ x * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100 htd htlip v
  have hρd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ρ x :=
    (L.contMDiff_scale x).mdifferentiableAt (by simp)
  have hρv : |mvfderiv 𝓘(ℝ, E3) ρ x v| ≤ Λ * ν :=
    Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf g hmetric hΛ L.lipschitz_scale
      hρd v
  -- the edge sum
  have hcut_d : ∀ i : L.edge.finite_centres.toFinset,
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edge.cutoff i) x := fun i =>
    (L.edge.contMDiff_cutoff_of_margin hΔ hρc (hmargin i.1 ((Set.Finite.mem_toFinset _).mp i.2))
      x).mdifferentiableAt (by simp)
  have hSd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpEdgeSum L) x :=
    (continuous_cgpEdgeSum L hΔ hmargin x).mdifferentiableAt (by simp)
  have hSv : mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v =
      ∑ i : L.edge.finite_centres.toFinset, mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v :=
    mvfderiv_sum_apply_KA2 Finset.univ (f := fun i : L.edge.finite_centres.toFinset =>
      L.edge.cutoff i) (fun i _ => hcut_d i) v
  have hterm : ∀ i : L.edge.finite_centres.toFinset,
      ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v| ≤
        if x ∈ tsupport (L.edge.cutoff i) then (1 + 100 * Δ * Λ) * Kb * ν else 0 := by
    intro i
    have hi' := (Set.Finite.mem_toFinset _).mp i.2
    split_ifs with hi
    · have hxbi := hmargin i.1 hi' hi
      have hbi := L.edge.cutoff_deriv_budget_KA2 hΔ hσc hγc hρc hi' hxbi v
      have hri := hρ i.1
      have hlip := L.lipschitz_scale.dist_le_mul x i.1
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
      have hdi : dist x i.1 < 100 * Δ * ρ i.1 := mem_ball.mp hxbi
      have hratio : ρ x ≤ (1 + 100 * Δ * Λ) * ρ i.1 := by
        have h1 := (abs_le.mp hlip).2
        have h2 : Λ * dist x i.1 ≤ Λ * (100 * Δ * ρ i.1) :=
          mul_le_mul_of_nonneg_left hdi.le hΛ
        nlinarith
      calc ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v|
          ≤ (1 + 100 * Δ * Λ) * ρ i.1 * |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
        _ = (1 + 100 * Δ * Λ) * (ρ i.1 * |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v|) := by ring
        _ ≤ (1 + 100 * Δ * Λ) * (Kb * ν) :=
            mul_le_mul_of_nonneg_left hbi (by positivity)
        _ = (1 + 100 * Δ * Λ) * Kb * ν := by ring
    · have h0 := notMem_tsupport_iff_eventuallyEq.mp hi
      rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_zero]
      simp
  have hS : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v| ≤ n * ((1 + 100 * Δ * Λ) * Kb * ν) := by
    rw [hSv]
    calc ρ x * |∑ i : L.edge.finite_centres.toFinset, mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v|
        ≤ ρ x * ∑ i : L.edge.finite_centres.toFinset,
            |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hrx.le
      _ = ∑ i : L.edge.finite_centres.toFinset,
            ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edge.cutoff i) x v| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ i : L.edge.finite_centres.toFinset, (if x ∈ tsupport (L.edge.cutoff i) then
            (1 + 100 * Δ * Λ) * Kb * ν else 0) := Finset.sum_le_sum fun i _ => hterm i
      _ = n * ((1 + 100 * Δ * Λ) * Kb * ν) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the marker
  obtain ⟨hAd, hA⟩ := abs_mvfderiv_profile_div_le_KA2 (cgpEdgeH_contDiff.differentiable (by simp))
    hH hΔ htd v
  have hRd : HasDerivAt (cfsRamp lc87EdgeTransition (1 / 2) 1)
      (deriv (cfsRamp lc87EdgeTransition (1 / 2) 1) (cgpEdgeSum L x)) (cgpEdgeSum L x) :=
    (((contDiff_cfsRamp lc87EdgeTransition_contDiff (1 / 2) 1).differentiable (by simp))
      (cgpEdgeSum L x)).hasDerivAt
  have hBd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y)) x :=
    hRd.differentiableAt.comp_mdifferentiableAt hSd
  have hB : |mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y))
      x v| ≤ cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v| := by
    rw [mvfderiv_comp_hasDerivAt hSd hRd v, abs_mul]
    exact mul_le_mul_of_nonneg_right (hRmp _) (abs_nonneg _)
  have hzv : mvfderiv 𝓘(ℝ, E3) (cgpEdgeMarker L) x v =
      cgpEdgeH (cgpHeight L x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y)) x v +
        cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x) *
          mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight L y / Δ)) x v :=
    mvfderiv_mul_apply_KA2 hAd hBd v
  have hHx := cgpEdgeH_mem_Icc (cgpHeight L x / Δ)
  have hRx := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 2) 1 (cgpEdgeSum L x)
  have hzd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpEdgeMarker L) x :=
    (contMDiff_cgpEdgeMarker L hΔ hmargin x).mdifferentiableAt (by simp)
  have hb : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeMarker L) x v| ≤
      (cgpProfileBound * (1 + γc) / Δ + cgpProfileBound * n * ((1 + 100 * Δ * Λ) * Kb)) * ν := by
    rw [hzv]
    have hT1 : |cgpEdgeH (cgpHeight L x / Δ) *
        mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y)) x v| ≤
        cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v| := by
      rw [abs_mul, abs_of_nonneg hHx.1]
      calc cgpEdgeH (cgpHeight L x / Δ) *
            |mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y))
              x v| ≤ 1 * (cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v|) :=
            mul_le_mul hHx.2 hB (abs_nonneg _) zero_le_one
        _ = cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v| := one_mul _
    have hT2 : |cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x) *
        mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight L y / Δ)) x v| ≤
        cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| := by
      rw [abs_mul, abs_of_nonneg hRx.1]
      calc cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x) *
            |mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight L y / Δ)) x v|
          ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v|) :=
            mul_le_mul hRx.2 hA (abs_nonneg _) zero_le_one
        _ = cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| := one_mul _
    have hsum := (abs_add_le _ _).trans (add_le_add hT1 hT2)
    have hρt : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| ≤ (1 + γc) * ν := by
      calc ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| ≤ ρ x * ((1 + γc) / ρ x * ν) :=
            mul_le_mul_of_nonneg_left ht hrx.le
        _ = (1 + γc) * ν := by field_simp
    have hP0 : 0 ≤ cgpProfileBound := by linarith
    calc ρ x * |cgpEdgeH (cgpHeight L x / Δ) *
            mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y))
              x v +
          cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x) *
            mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight L y / Δ)) x v|
        ≤ ρ x * (cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v| +
            cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v|) :=
          mul_le_mul_of_nonneg_left hsum hrx.le
      _ = cgpProfileBound * (ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum L) x v|) +
            cgpProfileBound / Δ * (ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v|) := by ring
      _ ≤ cgpProfileBound * (n * ((1 + 100 * Δ * Λ) * Kb * ν)) +
            cgpProfileBound / Δ * ((1 + γc) * ν) := by
          gcongr
      _ = (cgpProfileBound * (1 + γc) / Δ + cgpProfileBound * n * ((1 + 100 * Δ * Λ) * Kb)) *
            ν := by ring
  -- the block
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (cgpHeight L y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt htd
  have ha : ρ x * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (cgpHeight L y)) x v‖ ≤
      (1 + γc) * ν := by
    rw [mvfderiv_clm_comp htd planeAxis v, norm_planeAxis]
    calc ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight L) x v| ≤ ρ x * ((1 + γc) / ρ x * ν) :=
          mul_le_mul_of_nonneg_left ht hrx.le
      _ = (1 + γc) * ν := by field_simp
  have hC : ‖planeAxis (cgpHeight L x)‖ ≤ 10 * Δ := by
    rw [norm_planeAxis, abs_of_nonneg (cgpHeight_nonneg L x)]
    exact hk2.le
  have h := norm_mvfderiv_block_apply_le (R := ρ) (ζ := cgpEdgeMarker L)
    (η := fun y => planeAxis (cgpHeight L y)) hρd hzd hηd v hrx.le (cgpEdgeMarker_mem_Icc L x)
    hC ha hb hρv
  exact h

end Families

end DifferentialGeometry.Geometry.Collapse
