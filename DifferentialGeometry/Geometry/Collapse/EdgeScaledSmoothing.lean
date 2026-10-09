import DifferentialGeometry.Geometry.Collapse.EdgeNearestDirections
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalizedDistanceSmoothing
import DifferentialGeometry.Geometry.Collapse.DistancePerturbationGradient
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeSublevelProfile

/-!
# LFR27 and LFR34: scaled distance smoothing with a smooth constant core

Blueprint 207A, LFR27 (`lem:collapse-edge-scaled-core-smoothing`, A:27151–27221) and LFR34
(`lem:collapse-edge-low-collar-smoothing`, A:27872–27920), on a complete Riemannian manifold.

Tiers.
* `inner_gradFun_le_of_mem_minimizingDirectionsTo`: LC29 for a closed SET — if `F - d_A` is `ε`-Lipschitz
  and `F` is differentiable at `x ∉ A`, every nearest direction `v` has `g(∇F, v) ≤ -(1 - ε)`.
* `exists_distance_smoothing_with_gradient`: LC28 (with `ε' = ε²/5`) plus that bound give LFR02's gradient
  clause `‖∇F + v‖ < ε` for every `v ∈ V_x(A)` on the compact set, under the direction diameter `< ε²/20`.
  (LFR02's optional threshold `min{1, ε}/100` needs LFR02's Rademacher route; this is the recorded deviation.)
* `mfderiv_div_apply`, `sqrt_gInner_gradFun_div_sub_le`: the quotient rule for `η = F/ρ` and the derivative
  estimate (LFR27.2), keeping the `dρ` term.
* `edgeProfile_core_clauses`: `H = Δ ψ(η/Δ)` with the fixed profile `ψ = edgeSublevelProfile` is smooth on
  `B(p, 20Δ) ∩ {d_A < 10.25Δ}` (constant zero near the nonsmooth core), has EXACTLY the sublevels of `η` for
  levels `≥ 2Δ`, the same level sets above `2Δ`, and agrees with `η` near every point where `η > 2Δ`.
* `exists_edge_scaled_smoothing` (LFR27) and `exists_edge_low_collar_smoothing` (LFR34).

Deviations (all recorded in the lane sheet): threshold `30√τ < ε²/20` (LFR34: `140√τ < ε²/20`); `ρ` is taken
globally `Λ`-Lipschitz (the LFR29.1 form used by LFR28/LFR33) instead of `|dρ| ≤ Λ` on the ball, and its
positivity on the ball is derived; the quotient estimate is proved as `≤ 100ΔΛ`, which gives the row's strict
`< 150ΔΛ` whenever `Λ > 0` (for `Λ = 0` the row's strict form is false: both sides vanish).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC29 for a closed set: if `F - d_A` is `ε`-Lipschitz (`ε ≥ 0`) and `F` is differentiable at `q` with
`d_A(q) > 0`, then `g(∇F(q), v) ≤ -(1 - ε)` for every nearest direction `v ∈ V_q(A)`. -/
theorem inner_gradFun_le_of_mem_minimizingDirectionsTo (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {A : Set M} {ε : ℝ} (hε : 0 ≤ ε) {F : M → ℝ}
    (hlip : ∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) {q : M}
    (hq : 0 < infDist q A) (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F q) {u : TangentSpace I q}
    (hu : u ∈ minimizingDirectionsTo g hEnorm A q) :
    g.inner q (gradFun g F q) u ≤ -(1 - ε) := by
  obtain ⟨hu1, hend⟩ := hu
  set d := infDist q A with hd_def
  let γ := intrinsicGeodesic g hEnorm q u
  have hγ0 : γ 0 = q := intrinsicGeodesic_zero g hEnorm q u
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm q u
  have hcomp := hasDerivAt_comp_mfderiv_along I F γ 0 (by simpa only [hγ0] using hF)
    (hγ.contMDiffAt.mdifferentiableAt (by simp))
  have hstep (t : ℝ) (ht : t ∈ Icc 0 d) : F (γ t) - F (γ 0) ≤ -(1 - ε) * t := by
    have hdist := infDist_intrinsicGeodesic_to_set g hEnorm hu1 hend ht
    have hqt : dist q (γ t) ≤ t := by
      simpa only [intrinsicGeodesic_zero, hu1, Real.sqrt_one, one_mul, sub_zero] using
        dist_intrinsicGeodesic_le_mul g hEnorm q u ht.1
    have hl := (abs_le.mp (hlip (γ t) q)).2
    rw [dist_comm (γ t) q] at hl
    have hdist' : infDist (γ t) A = d - t := hdist
    rw [hγ0]
    nlinarith [mul_le_mul_of_nonneg_left hqt hε]
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ))
    (by simp)).mp hcomp.hasDerivWithinAt
  have hD : _ ≤ -(1 - ε) := le_of_tendsto hslope (by
    filter_upwards [Ioo_mem_nhdsGT hq] with t ht
    rw [slope_def_field, sub_zero, div_le_iff₀ ht.1]
    exact hstep t ⟨ht.1.le, ht.2.le⟩)
  change mvfderiv (I := I) F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) ≤ -(1 - ε) at hD
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero g hEnorm q u
  rw [hvel] at hD
  erw [hγ0] at hD
  have h := inner_gradientFun g F q u
  exact h.trans_le hD

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompleteSpace M] in
/-- A `L`-Lipschitz function has gradient norm at most `L` at every differentiability point. -/
theorem sqrt_gInner_gradFun_le_of_lipschitzWith (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {x : M}
    (hx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    Real.sqrt (g.inner x (gradFun g f x) (gradFun g f x)) ≤ L :=
  grad_norm_le_lip g (fun y z => by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I)]
    exact hf.edist_le_mul y z) hx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M]
  [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem gInner_self_nonneg_of_isMetricNorm {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g) {x : M} (z : TangentSpace I x) :
    0 ≤ g.inner x z z := by
  have h := norm_tangent_eq_sqrt_gInner hEnorm z
  by_contra hneg
  push Not at hneg
  have hcs := abs_inner_le_sqrt_mul_sqrt g x z z
  rw [Real.sqrt_eq_zero'.mpr hneg.le, mul_zero] at hcs
  linarith [abs_pos.mpr hneg.ne]

/-- LC28 plus the set version of LC29: with direction diameter `δ < ε²/20` on `U` the smoothing has, at every
point of the compact set, `‖∇F + v‖ < ε` for EVERY nearest direction `v`. -/
theorem exists_distance_smoothing_with_gradient (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε δ e : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {A U C : Set M}
    (hA : IsClosed A) (hAne : A.Nonempty) (hU : IsOpen U) (hUA : U ⊆ Aᶜ)
    (hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q, Real.sqrt (g.inner q (v - v') (v - v')) ≤ δ)
    (hδ : δ < ε ^ 2 / 20) (hC : IsCompact C) (hCU : C ⊆ U) (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - infDist x A| < e) ∧ (∀ x, x ∉ U → F x = infDist x A) ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      ∀ x ∈ C, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
        Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε := by
  set ε' := ε ^ 2 / 5 with hε'_def
  have hε' : 0 < ε' := by positivity
  have hε'ε : ε' ≤ ε := by rw [hε'_def]; nlinarith
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlip⟩ :=
    exists_localized_distance_smoothing g hEnorm hε' hA hAne hU hUA
      (fun q hq v hv v' hv' => (hdiam q hq v hv v' hv').trans_lt (by rw [hε'_def]; linarith))
      hC hCU he
  refine ⟨F, O, hO, hCO, hFO, hclose, hout, fun x y => (hdiff x y).trans
    (mul_le_mul_of_nonneg_right hε'ε dist_nonneg), hlip.weaken ?_, fun x hx v hv => ?_⟩
  · exact Real.toNNReal_le_toNNReal (by linarith)
  have hx0 : 0 < infDist x A := (hA.notMem_iff_infDist_pos hAne).1 (hUA (hCU hx))
  have hFx : MDifferentiableAt I 𝓘(ℝ, ℝ) F x :=
    (hFO.contMDiffAt (hO.mem_nhds (hCO hx))).mdifferentiableAt (by simp)
  have hin := inner_gradFun_le_of_mem_minimizingDirectionsTo g hEnorm hε'.le hdiff hx0 hFx hv
  have hgr := sqrt_gInner_gradFun_le_of_lipschitzWith g hEnorm hlip hFx
  rw [Real.coe_toNNReal _ (by linarith)] at hgr
  have hnn := gInner_self_nonneg_of_isMetricNorm hEnorm (gradFun g F x)
  have hsq : g.inner x (gradFun g F x) (gradFun g F x) ≤ (1 + ε') ^ 2 := by
    have h := Real.sq_sqrt hnn
    nlinarith [Real.sqrt_nonneg (g.inner x (gradFun g F x) (gradFun g F x))]
  have hexp : g.inner x (gradFun g F x + v) (gradFun g F x + v) =
      g.inner x (gradFun g F x) (gradFun g F x) + 2 * g.inner x (gradFun g F x) v +
        g.inner x v v := by
    simp only [map_add, add_apply, g.symm x v (gradFun g F x)]
    ring
  rw [Real.sqrt_lt' hε, hexp, hv.1]
  rw [hε'_def] at hsq hin
  nlinarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The quotient rule for `F / ρ` on a manifold, evaluated on a tangent vector. -/
theorem mvfderiv_div_apply {F ρ : M → ℝ} {x : M} (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x) (hne : ρ x ≠ 0) (w : TangentSpace I x) :
    mvfderiv (I := I) (fun y => F y / ρ y) x w =
      (ρ x)⁻¹ * mvfderiv (I := I) F x w - F x * (ρ x ^ 2)⁻¹ * mvfderiv (I := I) ρ x w := by
  have hinv : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => (ρ y)⁻¹) x
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(ρ x ^ 2)⁻¹)).comp
        (mfderiv I 𝓘(ℝ, ℝ) ρ x)) :=
    ((hasDerivAt_inv hne).hasFDerivAt.hasMFDerivAt).comp x hρ.hasMFDerivAt
  have hmul := hF.hasMFDerivAt.mul hinv
  have heq : (fun y => F y / ρ y) = F * fun y => (ρ y)⁻¹ := by
    funext y
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have key : mvfderiv (I := I) (F * fun y => (ρ y)⁻¹) x w =
      F x * (mvfderiv (I := I) ρ x w * (-(ρ x ^ 2)⁻¹)) + (ρ x)⁻¹ * mvfderiv (I := I) F x w := by
    unfold mvfderiv
    rw [hmul.mfderiv]
    rfl
  rw [heq, key]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- LFR27.2 tier: if `|∇F| ≤ 1 + ε`, `|∇ρ| ≤ Λ'`, `|ρ(x) - 1| ≤ r ≤ 1/2` and `|F(x)| ≤ K`, then
`‖∇(F/ρ) - ∇F‖ ≤ 2r(1 + ε) + 4KΛ'` (the `dρ` term is kept). -/
theorem sqrt_gInner_gradFun_div_sub_le (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F ρ : M → ℝ} {x : M} {ε Λ' K r : ℝ}
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x) (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hFgrad : Real.sqrt (g.inner x (gradFun g F x) (gradFun g F x)) ≤ 1 + ε)
    (hρgrad : Real.sqrt (g.inner x (gradFun g ρ x) (gradFun g ρ x)) ≤ Λ')
    (hρx : |ρ x - 1| ≤ r) (hr : r ≤ 1 / 2) (hFx : |F x| ≤ K) :
    Real.sqrt (g.inner x (gradFun g (fun y => F y / ρ y) x - gradFun g F x)
      (gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ 2 * r * (1 + ε) + 4 * K * Λ' := by
  set D := gradFun g (fun y => F y / ρ y) x - gradFun g F x with hD
  have hρpos : 1 / 2 ≤ ρ x := by linarith [(abs_le.mp hρx).1]
  have hne : ρ x ≠ 0 := by linarith
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hρx
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hFx
  have hΛ0 : 0 ≤ Λ' := (Real.sqrt_nonneg _).trans hρgrad
  have hε0 : 0 ≤ 1 + ε := (Real.sqrt_nonneg _).trans hFgrad
  have hinv1 : |(ρ x)⁻¹ - 1| ≤ 2 * r := by
    have h1 : |(ρ x)⁻¹ - 1| = |ρ x - 1| / ρ x := by
      rw [show (ρ x)⁻¹ - 1 = -(ρ x - 1) / ρ x by field_simp; ring, abs_div, abs_neg,
        abs_of_pos (by linarith : 0 < ρ x)]
    rw [h1, div_le_iff₀ (by linarith)]
    nlinarith
  have hinv2 : |F x * (ρ x ^ 2)⁻¹| ≤ 4 * K := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (ρ x ^ 2)⁻¹)]
    have h4 : (ρ x ^ 2)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [abs_nonneg (F x)]
  set C := 2 * r * (1 + ε) + 4 * K * Λ' with hC
  have hkey : ∀ w : TangentSpace I x, |g.inner x D w| ≤ C * Real.sqrt (g.inner x w w) := by
    intro w
    have hDw : g.inner x D w = ((ρ x)⁻¹ - 1) * mvfderiv (I := I) F x w -
        F x * (ρ x ^ 2)⁻¹ * mvfderiv (I := I) ρ x w := by
      have h1 := inner_gradientFun g (fun y => F y / ρ y) x w
      have h2 := inner_gradientFun g F x w
      rw [mvfderiv_div_apply hF hρ hne] at h1
      change g.inner x (gradientFun g (fun y => F y / ρ y) x - gradientFun g F x) w = _
      rw [map_sub, sub_apply, h1, h2]
      ring
    have hFw : |mvfderiv (I := I) F x w| ≤ (1 + ε) * Real.sqrt (g.inner x w w) := by
      rw [← inner_gradientFun]
      exact (abs_inner_le_sqrt_mul_sqrt g x _ w).trans
        (mul_le_mul_of_nonneg_right hFgrad (Real.sqrt_nonneg _))
    have hρw : |mvfderiv (I := I) ρ x w| ≤ Λ' * Real.sqrt (g.inner x w w) := by
      rw [← inner_gradientFun]
      exact (abs_inner_le_sqrt_mul_sqrt g x _ w).trans
        (mul_le_mul_of_nonneg_right hρgrad (Real.sqrt_nonneg _))
    rw [hDw]
    have hs := Real.sqrt_nonneg (g.inner x w w)
    calc |((ρ x)⁻¹ - 1) * mvfderiv (I := I) F x w -
          F x * (ρ x ^ 2)⁻¹ * mvfderiv (I := I) ρ x w|
        ≤ |(ρ x)⁻¹ - 1| * |mvfderiv (I := I) F x w| +
          |F x * (ρ x ^ 2)⁻¹| * |mvfderiv (I := I) ρ x w| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ (2 * r) * ((1 + ε) * Real.sqrt (g.inner x w w)) +
          (4 * K) * (Λ' * Real.sqrt (g.inner x w w)) := by
          gcongr
      _ = C * Real.sqrt (g.inner x w w) := by rw [hC]; ring
  have hDD := (le_abs_self _).trans (hkey D)
  have hnn := gInner_self_nonneg_of_isMetricNorm hEnorm D
  have hsq := Real.sq_sqrt hnn
  have hs0 := Real.sqrt_nonneg (g.inner x D D)
  have hC0 : 0 ≤ C := by positivity
  nlinarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The profile clauses of LFR27: with `η = F/ρ` and `H = Δ ψ(η/Δ)`, `H` is smooth on
`B(p, 20Δ) ∩ {d_A < 10.25Δ}` (constant zero near the core `d_A < cΔ`), has exactly the sublevels of `η` for
levels `≥ 2Δ`, the same level sets above `2Δ`, and agrees with `η` near every point where `η > 2Δ`. -/
theorem edgeProfile_core_clauses {F ρ : M → ℝ} {A O : Set M} {p : M} {Δ μ c : ℝ} {Λ : ℝ≥0}
    (hΔ : 0 < Δ) (hO : IsOpen O) (hFO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hcollar : ∀ x ∈ ball p (20 * Δ), c * Δ ≤ infDist x A → infDist x A < 41 / 4 * Δ → x ∈ O)
    (hFd : ∀ x, |F x - infDist x A| < μ * Δ) (hFc : Continuous F)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)))
    (hlam : 100 * Δ * Λ ≤ 1 / 100) (hcμ : c + μ ≤ 98 / 100) :
    (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) x) ∧
    (∀ s, 2 * Δ ≤ s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔ F x / ρ x ≤ s)) ∧
    (∀ s, 2 * Δ < s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) = s ↔ F x / ρ x = s)) ∧
    (∀ x ∈ ball p (100 * Δ), 2 * Δ < F x / ρ x →
      (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  have hρclose (y : M) : |ρ y - 1| ≤ Λ * dist y p := by
    have h := hρ.dist_le_mul y p
    rwa [Real.dist_eq, hρp] at h
  have hρlow (y : M) (hy : y ∈ ball p (100 * Δ)) : 99 / 100 ≤ ρ y := by
    have h1 := hρclose y
    have h2 : (Λ : ℝ) * dist y p ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) Λ.coe_nonneg
    linarith [(abs_le.mp h1).1]
  refine ⟨fun x hx hxd => ?_, fun s hs x => ?_, fun s hs x => ?_, fun x hx hη => ?_⟩
  · have hx100 : x ∈ ball p (100 * Δ) :=
      (show dist x p < 20 * Δ from hx).trans (by linarith)
    by_cases hc : c * Δ ≤ infDist x A
    · have hFx := hFO.contMDiffAt (hO.mem_nhds (hcollar x hx hc hxd))
      have hρx := hρs.contMDiffAt (isOpen_ball.mem_nhds hx100)
      have hne : ρ x ≠ 0 := by linarith [hρlow x hx100]
      have hη := hFx.div₀ hρx hne
      have hg : ContDiff ℝ ∞ (fun t : ℝ => Δ * edgeSublevelProfile (t / Δ)) :=
        contDiff_const.mul (contDiff_edgeSublevelProfile.comp (contDiff_id.div_const Δ))
      exact hg.comp_contMDiffAt hη
    · push Not at hc
      have hW : {y | infDist y A < c * Δ} ∩ ball p (100 * Δ) ∈ 𝓝 x :=
        ((isOpen_lt (continuous_infDist_pt A) continuous_const).inter isOpen_ball).mem_nhds
          ⟨hc, hx100⟩
      refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hW] with y hy
      have hρy := hρlow y hy.2
      have hFy := (abs_lt.mp (hFd y)).2
      have hdy : infDist y A < c * Δ := hy.1
      have hle : F y / ρ y / Δ ≤ 1 := by
        rw [div_le_one hΔ, div_le_iff₀ (by linarith)]
        nlinarith
      simp only [edgeSublevelProfile_eq_zero hle, mul_zero]
  · rw [← le_div_iff₀' hΔ, edgeSublevelProfile_le_iff ((le_div_iff₀ hΔ).mpr (by linarith)),
      div_le_div_iff_of_pos_right hΔ]
  · have hs2 : 2 < s / Δ := (lt_div_iff₀ hΔ).mpr (by linarith)
    constructor
    · intro h
      have hq : 2 < F x / ρ x / Δ := by
        by_contra hq
        push Not at hq
        have := edgeSublevelProfile_le_two hq
        nlinarith
      rw [edgeSublevelProfile_eq_self hq.le] at h
      field_simp at h
      linarith
    · intro h
      rw [h, edgeSublevelProfile_eq_self hs2.le]
      field_simp
  · have hne : ρ x ≠ 0 := by linarith [hρlow x hx]
    have hcont : ContinuousAt (fun y => F y / ρ y) x :=
      hFc.continuousAt.div hρ.continuous.continuousAt hne
    filter_upwards [hcont.eventually (lt_mem_nhds hη)] with y hy
    rw [edgeSublevelProfile_eq_self ((le_div_iff₀ hΔ).mpr (by linarith))]
    field_simp

/-- The assembly behind LFR27 and LFR34: one LC28 smoothing on `U` with every direction set of diameter
`≤ δ < ε²/20`, followed by the gradient, quotient and profile clauses on the compact collar `C`. -/
theorem exists_edge_profile_smoothing_of_directions (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {A U C : Set M} {p : M} {ρ : M → ℝ} {Λ : ℝ≥0} {Δ ε μ δ c : ℝ}
    (hA : IsClosed A) (hpA : p ∈ A) (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hU : IsOpen U) (hUd : ∀ x ∈ U, μ * Δ < infDist x A)
    (hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q, Real.sqrt (g.inner q (v - v') (v - v')) ≤ δ)
    (hδ : δ < ε ^ 2 / 20) (hC : IsCompact C) (hCU : C ⊆ U)
    (hCsub : ∀ x ∈ C, dist x p ≤ 20 * Δ ∧ infDist x A ≤ 21 / 2 * Δ)
    (hcollar : ∀ x ∈ ball p (20 * Δ), c * Δ ≤ infDist x A → infDist x A < 41 / 4 * Δ → x ∈ C)
    (hcμ : c + μ ≤ 98 / 100)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ))) (hlam : 100 * Δ * Λ < 1 / 100) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x, |F x - infDist x A| < μ * Δ) ∧ (∀ x, x ∉ U → F x = infDist x A) ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      (∀ x ∈ C, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
        Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
      (∀ x ∈ C, Real.sqrt (g.inner x (gradFun g (fun y => F y / ρ y) x - gradFun g F x)
        (gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ 100 * Δ * Λ) ∧
      (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) x) ∧
      (∀ s, 2 * Δ ≤ s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔ F x / ρ x ≤ s)) ∧
      (∀ s, 2 * Δ < s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) = s ↔ F x / ρ x = s)) ∧
      (∀ x ∈ ball p (100 * Δ), 2 * Δ < F x / ρ x →
        (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  have hμΔ : 0 < μ * Δ := mul_pos hμ hΔ
  have hUA : U ⊆ Aᶜ := fun x hx hxA => by
    have := hUd x hx
    rw [infDist_zero_of_mem hxA] at this
    linarith
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlip, hgrad⟩ :=
    exists_distance_smoothing_with_gradient g hEnorm hε (by linarith) hA ⟨p, hpA⟩ hU hUA hdiam hδ
      hC hCU hμΔ
  have hprof := edgeProfile_core_clauses (I := I) hΔ hO hFO
    (fun x hx hc hxd => hCO (hcollar x hx hc hxd)) hclose hlip.continuous hρ hρp hρs hlam.le hcμ
  refine ⟨F, O, hO, hCO, hFO, fun x => ?_, hlip, hclose, hout, hdiff, hgrad, fun x hx => ?_, hprof⟩
  · by_cases hxU : x ∈ U
    · linarith [(abs_lt.mp (hclose x)).1, hUd x hxU]
    · rw [hout x hxU]
      exact infDist_nonneg
  · obtain ⟨hxp, hxd⟩ := hCsub x hx
    have hx100 : x ∈ ball p (100 * Δ) := (show dist x p < 100 * Δ by linarith)
    have hFx : MDifferentiableAt I 𝓘(ℝ, ℝ) F x :=
      (hFO.contMDiffAt (hO.mem_nhds (hCO hx))).mdifferentiableAt (by simp)
    have hρx : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x :=
      (hρs.contMDiffAt (isOpen_ball.mem_nhds hx100)).mdifferentiableAt (by simp)
    have hFgrad := sqrt_gInner_gradFun_le_of_lipschitzWith g hEnorm hlip hFx
    rw [Real.coe_toNNReal _ (by linarith)] at hFgrad
    have hρgrad := sqrt_gInner_gradFun_le_of_lipschitzWith g hEnorm hρ hρx
    have hΛ0 := Λ.coe_nonneg
    have hr : |ρ x - 1| ≤ 20 * Δ * Λ := by
      have h := hρ.dist_le_mul x p
      rw [Real.dist_eq, hρp] at h
      nlinarith
    have hFb : |F x| ≤ 1061 / 100 * Δ := by
      have h := abs_lt.mp (hclose x)
      have hd0 : 0 ≤ infDist x A := infDist_nonneg
      rw [abs_le]
      constructor <;> nlinarith
    have h := sqrt_gInner_gradFun_div_sub_le g hEnorm hFx hρx hFgrad hρgrad hr (by nlinarith) hFb
    refine h.trans ?_
    have hΔΛ : 0 ≤ Δ * Λ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hε1.le hΔΛ]

/-- **LFR27**: scaled distance smoothing with a smooth constant core. Coarse-border chart (LFR25.1,
unbundled), `sec ≥ -κ²` on `B(p, 1000Δ)`, `κΔ ≤ 1/100`, `0 < ε, μ < 1/100`, `30√τ < ε²/20`, and a
`Λ`-Lipschitz scale `ρ`, smooth on `B(p, 100Δ)`, `ρ(p) = 1`, `100ΔΛ < 1/100`. Then there is a global
nonnegative Lipschitz `F` with `|F - d_A| < μΔ`, `Lip(F - d_A) ≤ ε`, smooth near
`C = B̄(p, 20Δ) ∩ {3Δ/4 ≤ d_A ≤ 10.5Δ}` with `‖∇F + v‖ < ε` for EVERY `v ∈ V_x(A)`, the quotient estimate
for `η = F/ρ` on `C`, and the profile clauses for `H = Δ ψ(η/Δ)`. -/
theorem exists_edge_scaled_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {ρ : M → ℝ}
    {Λ : ℝ≥0} {Δ τ κ ε μ : ℝ}
    (hA : IsClosed A) (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ))) (hlam : 100 * Δ * Λ < 1 / 100) :
    let C : Set M := closedBall p (20 * Δ) ∩
      {x | 3 / 4 * Δ ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ}
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x, |F x - infDist x A| < μ * Δ) ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      (∀ x ∈ C, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
        Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
      (∀ x ∈ C, Real.sqrt (g.inner x (gradFun g (fun y => F y / ρ y) x - gradFun g F x)
        (gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ 100 * Δ * Λ) ∧
      (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) x) ∧
      (∀ s, 2 * Δ ≤ s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔ F x / ρ x ≤ s)) ∧
      (∀ s, 2 * Δ < s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) = s ↔ F x / ρ x = s)) ∧
      (∀ x ∈ ball p (100 * Δ), 2 * Δ < F x / ρ x →
        (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  intro C
  set U : Set M := ball p (30 * Δ) ∩ {x | Δ / 2 < infDist x A ∧ infDist x A < 12 * Δ} with hU_def
  have hU : IsOpen U := isOpen_ball.inter
    ((isOpen_lt continuous_const (continuous_infDist_pt A)).inter
      (isOpen_lt (continuous_infDist_pt A) continuous_const))
  have hsq : 2 * Real.sqrt (200 * τ) < 30 * Real.sqrt τ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 200)]
    have h200 : Real.sqrt 200 < 15 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith
  have hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q,
        Real.sqrt (g.inner q (v - v') (v - v')) ≤ 2 * Real.sqrt (200 * τ) := fun q hq =>
    (coarseBorder_nearest_directions g hEnorm hΔ hτ hτsmall hQp hdist hheight hcover hpA hborder
      hbordercover hκ hκΔ hsec hq.1 hq.2.1.le hq.2.2.le).2.1
  have hC : IsCompact C := (soul_isCompact_closedBall (I := I) g hEnorm p (20 * Δ)).inter_right
    ((isClosed_le continuous_const (continuous_infDist_pt A)).inter
      (isClosed_le (continuous_infDist_pt A) continuous_const))
  have hCU : C ⊆ U := fun x hx => ⟨(show dist x p < 30 * Δ by
      have : dist x p ≤ 20 * Δ := hx.1
      linarith), by linarith [hx.2.1], by linarith [hx.2.2]⟩
  obtain ⟨F, O, hO, hCO, hFO, hnn, hlip, hclose, -, hdiff, hgrad, hquot, hprof⟩ :=
    exists_edge_profile_smoothing_of_directions g hEnorm (c := 3 / 4) hA hpA hΔ hε hε1 hμ hμ1 hU
      (fun x hx => by nlinarith [hx.2.1]) hdiam (hsq.trans hθ) hC hCU
      (fun x hx => ⟨hx.1, hx.2.2⟩)
      (fun x hx hc hxd => ⟨(show dist x p ≤ 20 * Δ from le_of_lt hx), hc, by linarith⟩)
      (by linarith) hρ hρp hρs hlam
  exact ⟨F, O, hO, hCO, hFO, hnn, hlip, hclose, hdiff, hgrad, hquot, hprof⟩

/-- **LFR34**: distance smoothing down to the full collar. As LFR27 with `140√τ < ε²/20` and
`μ < 10⁻³`: `F` is smooth near `C⁺ = B̄(p, 20Δ) ∩ {Δ/25 ≤ d_A ≤ 10.5Δ}` with all LFR27 clauses there, and
`F - d_A` has compact support inside `U⁺ = B(p, 30Δ) ∩ {Δ/50 < d_A < 12Δ}`. -/
theorem exists_edge_low_collar_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {ρ : M → ℝ}
    {Λ : ℝ≥0} {Δ τ κ ε μ : ℝ}
    (hA : IsClosed A) (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 1000)
    (hθ : 140 * Real.sqrt τ < ε ^ 2 / 20)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ))) (hlam : 100 * Δ * Λ < 1 / 100) :
    let C : Set M := closedBall p (20 * Δ) ∩
      {x | Δ / 25 ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ}
    let U : Set M := ball p (30 * Δ) ∩ {x | Δ / 50 < infDist x A ∧ infDist x A < 12 * Δ}
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x, |F x - infDist x A| < μ * Δ) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∀ x, x ∉ K → F x = infDist x A) ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      (∀ x ∈ C, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
        Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
      (∀ x ∈ C, Real.sqrt (g.inner x (gradFun g (fun y => F y / ρ y) x - gradFun g F x)
        (gradFun g (fun y => F y / ρ y) x - gradFun g F x)) ≤ 100 * Δ * Λ) ∧
      (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) x) ∧
      (∀ s, 2 * Δ ≤ s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔ F x / ρ x ≤ s)) ∧
      (∀ s, 2 * Δ < s → ∀ x, (Δ * edgeSublevelProfile (F x / ρ x / Δ) = s ↔ F x / ρ x = s)) ∧
      (∀ x ∈ ball p (100 * Δ), 2 * Δ < F x / ρ x →
        (fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  intro C U
  set U' : Set M := ball p (25 * Δ) ∩ {x | Δ / 40 < infDist x A ∧ infDist x A < 23 / 2 * Δ}
    with hU'_def
  set K : Set M := closedBall p (25 * Δ) ∩ {x | Δ / 40 ≤ infDist x A ∧ infDist x A ≤ 23 / 2 * Δ}
    with hK_def
  have hU' : IsOpen U' := isOpen_ball.inter
    ((isOpen_lt continuous_const (continuous_infDist_pt A)).inter
      (isOpen_lt (continuous_infDist_pt A) continuous_const))
  have hK : IsCompact K := (soul_isCompact_closedBall (I := I) g hEnorm p (25 * Δ)).inter_right
    ((isClosed_le continuous_const (continuous_infDist_pt A)).inter
      (isClosed_le (continuous_infDist_pt A) continuous_const))
  have hU'K : U' ⊆ K := fun x hx => ⟨ball_subset_closedBall hx.1, hx.2.1.le, hx.2.2.le⟩
  have hKU : K ⊆ U := fun x hx => ⟨(show dist x p < 30 * Δ by
      have : dist x p ≤ 25 * Δ := hx.1
      linarith), by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hsq : 2 * Real.sqrt (4600 * τ) < 140 * Real.sqrt τ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4600)]
    have h4600 : Real.sqrt 4600 < 70 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith
  have hdiam : ∀ q ∈ U', ∀ v ∈ minimizingDirectionsTo g hEnorm A q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm A q,
        Real.sqrt (g.inner q (v - v') (v - v')) ≤ 2 * Real.sqrt (4600 * τ) := fun q hq =>
    (coarseBorder_nearest_directions_low g hEnorm hΔ hτ hτsmall hQp hdist hheight hcover hpA
      hborder hbordercover hκ hκΔ hsec (hKU (hU'K hq)).1 (by linarith [hq.2.1]) (hq.2.2.le.trans
        (by linarith))).2.1
  have hC : IsCompact C := (soul_isCompact_closedBall (I := I) g hEnorm p (20 * Δ)).inter_right
    ((isClosed_le continuous_const (continuous_infDist_pt A)).inter
      (isClosed_le (continuous_infDist_pt A) continuous_const))
  have hCU : C ⊆ U' := fun x hx => ⟨(show dist x p < 25 * Δ by
      have : dist x p ≤ 20 * Δ := hx.1
      linarith), by linarith [hx.2.1], by linarith [hx.2.2]⟩
  obtain ⟨F, O, hO, hCO, hFO, hnn, hlip, hclose, hout, hdiff, hgrad, hquot, hprof⟩ :=
    exists_edge_profile_smoothing_of_directions g hEnorm (c := 1 / 25) hA hpA hΔ hε hε1 hμ
      (by linarith) hU' (fun x hx => by nlinarith [hx.2.1]) hdiam (hsq.trans hθ) hC hCU
      (fun x hx => ⟨hx.1, hx.2.2⟩)
      (fun x hx hc hxd => ⟨(show dist x p ≤ 20 * Δ from le_of_lt hx), by linarith, by linarith⟩)
      (by linarith) hρ hρp hρs hlam
  exact ⟨F, O, hO, hCO, hFO, hnn, hlip, hclose,
    ⟨K, hK, hKU, fun x hx => hout x (fun h => hx (hU'K h))⟩, hdiff, hgrad, hquot, hprof⟩

end DifferentialGeometry.Geometry.Collapse
