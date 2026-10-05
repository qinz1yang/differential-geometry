import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualCircleGram
import DifferentialGeometry.Geometry.Fibration.RiemannianDirectionalComparison
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# TCP03 (circle blocks): constant-radius block comparisons with the reference circle chart

Blueprint `master207B.tex`, TCP03 (`lem:fibration-first-constant-comparison`, B:5370), for the
listed CIRCLE charts on the final family `LocalChartPackets`, with TCP02's raw alignment
(`tcp02_pair_KA3`, `ActualRawAlignment.lean`).

* `kl_lift_KA4`: a normalized product splitting lifts a Euclidean displacement `tξ` (coverage +
  distortion).
* `exists_scaled_minimizing_dir_KA4`: one physical minimizing direction serves every normalized
  scale (geodesics of `R⁻² g` are those of `g`, reparametrized).
* `norm_tangent_radialScaled_KA4`: the tangent norm of the bundle `R⁻² g`.
* `circle_tests_common_dir_KA4`: the original long tests of packet (i) of EVERY circle chart along
  the SAME physical direction.
* `coisometry_adjoint_single_KA4`, `saturation_scalar_KA4`, `listed_component_vector_KA4`,
  `reference_component_vector_KA4`, `circle_reference_lift_KA4`: the steps of the saturation.
* `circle_component_saturation_KA4`: both covectors saturate on one direction (lift of
  `u_i(x) + 400 A* e_a`, the two long tests, (TR) at both endpoints).
* `circle_derivative_comparison_KA4`: FC15's rowwise Riesz calculation on the normalized tangent
  space of `ρ(i)⁻² g`; `circle_value_comparison_KA4`: the value clause; `riesz_budget_KA4`.
* `tcp03_circle_row`: TCP03 (TR) + (TC) for every listed circle chart, with the early `σ`, `η₂`
  (circle splitting quality) and `γ₀` (circle adaptation quality) chosen before `Δ`.

The (TC) bounds are `θ/2` (value) and `(θ/2)|w|` (differential, norm of `ρ(i)⁻² g`), so the `C¹`
norm on `D_i` is `< θ`. Edge, slim and zero blocks are in separate modules (the slim block uses
`LocalChartPacketsRV`, the zero block `LocalChartPacketsZ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- A normalized product splitting lifts a Euclidean displacement: for `x ∈ B(p, R)`, a unit
`ξ ∈ ℝᵏ` and a length `t ≥ 0` with `R + t + 2β ≤ β⁻¹`, some `y ∈ B(p, β⁻¹)` has
`|d(x, y) − t| ≤ 3β`, `‖u(y) − u(x) − tξ‖ < 2β` and `d(y, p) < R + t + 4β`. -/
theorem kl_lift_KA4 {X Y : Type*} [MetricSpace X] [MetricSpace Y] {k : ℕ} {p : X} {a : Y}
    {β : ℝ} (sp : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a)) β)
    {x : X} {R t : ℝ} (hx : dist x p < R) (ξ : EuclideanSpace ℝ (Fin k)) (hξ : ‖ξ‖ = 1)
    (ht : 0 ≤ t) (hroom : R + t + 2 * β ≤ β⁻¹) :
    ∃ y ∈ ball p β⁻¹, |dist x y - t| ≤ 3 * β ∧
      ‖(sp.toFun y).fst - (sp.toFun x).fst - t • ξ‖ < 2 * β ∧ dist y p < R + t + 4 * β := by
  have hβ := sp.error_pos
  have hxB : x ∈ ball p β⁻¹ := by rw [mem_ball]; linarith
  have hpB : p ∈ ball p β⁻¹ := mem_ball_self (inv_pos.mpr hβ)
  have hbase := sp.basepoint
  have hsx : dist (sp.toFun x) (sp.toFun p) ≤ dist x p + β := by
    have := sp.distortion x hxB p hpB
    linarith [(abs_le.mp this).2]
  set ys : WithLp 2 (EuclideanSpace ℝ (Fin k) × Y) :=
    WithLp.toLp 2 ((sp.toFun x).fst + t • ξ, (sp.toFun x).snd) with hys
  have h1 : dist ((sp.toFun x).fst + t • ξ) (sp.toFun x).fst = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hξ, Real.norm_eq_abs, abs_of_nonneg ht,
      mul_one]
  have hy1 : dist ys (sp.toFun x) = t :=
    (dist_toLp_same_snd_KA2 ((sp.toFun x).fst + t • ξ) (sp.toFun x).fst (sp.toFun x).snd).trans h1
  have hy0 : dist ys (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a)) < β⁻¹ - β := by
    rw [← hbase]
    have := dist_triangle ys (sp.toFun x) (sp.toFun p)
    linarith
  obtain ⟨y, hyB, hyd⟩ := sp.coverage_witness ys hy0
  refine ⟨y, hyB, ?_, ?_, ?_⟩
  · have hxy := sp.distortion x hxB y hyB
    have e1 := dist_triangle (sp.toFun x) ys (sp.toFun y)
    have e2 := dist_triangle ys (sp.toFun y) (sp.toFun x)
    have e3 := dist_comm ys (sp.toFun x)
    have e4 := dist_comm (sp.toFun y) (sp.toFun x)
    rw [abs_le] at hxy ⊢
    constructor <;> linarith [hxy.1, hxy.2]
  · have h := WithLp.dist_fst_le (sp.toFun y) ys
    have h2 : dist (sp.toFun y) ys < 2 * β := by rw [dist_comm]; exact hyd
    rw [dist_eq_norm] at h
    have he : (sp.toFun y).fst - ys.fst = (sp.toFun y).fst - (sp.toFun x).fst - t • ξ := by
      rw [hys]
      change (sp.toFun y).fst - ((sp.toFun x).fst + t • ξ) = _
      abel
    rw [he] at h
    exact lt_of_le_of_lt h h2
  · have hyp := sp.distortion y hyB p hpB
    have f1 := dist_triangle (sp.toFun y) ys (sp.toFun p)
    have f2 := dist_triangle ys (sp.toFun x) (sp.toFun p)
    have f3 := dist_comm (sp.toFun y) ys
    linarith [(abs_le.mp hyp).1]

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- A physical minimizing direction serves every normalized scale: for `x ≠ y` there is a
`g`-unit `w₀` such that, for every `R > 0`, the intrinsic geodesic of `R⁻² g` (rescaled instances)
with initial velocity `R w₀` reaches `y` at time `R⁻¹ d(x, y)`. -/
theorem exists_scaled_minimizing_dir_KA4 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {x y : X}
    (hxy : x ≠ y) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧ ∀ (R : ℝ) (hR : 0 < R),
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x (R • w₀) (dist x y) = y := by
  let _ : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, E3) X := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have _ : CompleteSpace X := complete_of_compact
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) g := isMetricNorm_of_riemannianBundle g
  have hfin : riemannianEDist 𝓘(ℝ, E3) x y ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm x y
    hfin
  have hdlen : (riemannianEDist 𝓘(ℝ, E3) x y).toReal = dist x y := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdlen] at hlen
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hvpos : 0 < g.inner x v v := Real.sqrt_pos.mp (hlen ▸ hdpos)
  have hvv : g.inner x v v = dist x y ^ 2 := by
    rw [← hlen, Real.sq_sqrt hvpos.le]
  refine ⟨(dist x y)⁻¹ • v, ?_, fun R hR => ?_⟩
  · rw [gInner_smul_self, hvv]
    field_simp
  · have hgeo : intrinsicGeodesic g hEnorm x ((dist x y)⁻¹ • v) (dist x y) = y := by
      rw [← intrinsicGeodesic_smul g hEnorm x ((dist x y)⁻¹ • v) (dist x y), smul_smul,
        mul_inv_cancel₀ hdpos.ne', one_smul]
      exact hv
    have hEq := intrinsicGeodesic_radialScaled_eq g hEnorm hR x (R • ((dist x y)⁻¹ • v))
    simp only at hEq ⊢
    rw [hEq, intrinsicGeo_smul_apply g hEnorm x _ R, MetricSpace.rescale_dist, ← mul_assoc,
      mul_inv_cancel₀ hR.ne', one_mul]
    exact hgeo

omit [CompactSpace X] in
/-- The norm of a tangent vector for the normalized bundle `R⁻² g`. -/
theorem norm_tangent_radialScaled_KA4 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) {R : ℝ}
    (hR : 0 < R) (x : X) (w : TangentSpace 𝓘(ℝ, E3) x) :
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    ‖w‖ = Real.sqrt (R⁻¹ ^ 2 * g.inner x w w) := by
  let _ := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  have h := isMetricNorm_of_riemannianBundle (I := 𝓘(ℝ, E3)) (M := X)
    (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) x w
  rw [scaleMetric_inner, ← ofReal_norm] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).mp h

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP03_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP03_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP03_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Circle tests along one physical minimizing direction.** For `x ≠ z` there is a `g`-unit
`w₀` (the initial velocity of a minimizing geodesic from `x` to `z`) such that EVERY circle chart
`j` with `x ∈ B(j, 200ρ(j))`, `z ∈ B(j, 201·10⁴ρ(j))` and `201ρ(j) < d(x, z)` satisfies its original
long test `‖ρ(j) dη_j(w₀) − (ρ(j)/d(x, z))(u_j(z) − u_j(x))‖ < γ` (packet (i)). -/
theorem circle_tests_common_dir_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {x z : X} (hxz : x ≠ z) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧
      ∀ j (hj : j ∈ P.circle.centres), x ∈ ball j (200 * ρ j) →
        z ∈ ball j (201 * 10000 * ρ j) → 201 * ρ j < dist x z →
        ‖ρ j • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w₀ -
          (ρ j / dist x z) • (circleRaw_KA3 P j z - circleRaw_KA3 P j x)‖ < γ := by
  obtain ⟨w₀, hw₀, hgeo⟩ := exists_scaled_minimizing_dir_KA4 g hmetric hxz
  refine ⟨w₀, hw₀, fun j hj hx hz hd => ?_⟩
  have hrj := hρ j
  have hc := P.circle.chart_center j hj
  let A := P.circleAdapted j hj
  have htest := A.test
  have hgj := hgeo (ρ j) hrj
  have hxR : (ρ j)⁻¹ * dist x j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hzR : (ρ j)⁻¹ * dist z j < 201 * 10000 := by
    have := inv_mul_dist_lt_of_mem_ball_LC87 hrj hz
    linarith
  have hdR : 201 < (ρ j)⁻¹ * dist x z := by
    rw [lt_inv_mul_iff₀ hrj]
    linarith
  have hunit : (scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrj) 2) g).inner x (ρ j • w₀)
      (ρ j • w₀) = 1 := by
    rw [scaleMetric_inner, gInner_smul_self, hw₀]
    field_simp
  have hT := htest x hxR z hzR hdR (ρ j • w₀) hunit hgj
  rw [circleRaw_KA3_eq P hj, circleRaw_KA3_eq P hj]
  have hlin : mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x (ρ j • w₀) =
      ρ j • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w₀ := map_smul _ _ _
  have hinv : ((ρ j)⁻¹ * dist x z)⁻¹ = ρ j / dist x z := by
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  change ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x (ρ j • w₀) -
    ((ρ j)⁻¹ * dist x z)⁻¹ • _‖ < γ at hT
  rw [hlin, hinv] at hT
  exact hT

/-- The adjoint of a coisometry on a coordinate vector: `ξ = A* e_a` is a unit vector with
`A ξ = e_a`, and `(A v)_a = ⟨v, ξ⟩`. -/
theorem coisometry_adjoint_single_KA4 {m k : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) (a : Fin k) :
    ‖ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1)‖ = 1 ∧
      A (ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1)) =
        EuclideanSpace.single a 1 ∧
      ∀ v, A v a = inner ℝ v (ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1)) := by
  have hAA : A (ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1)) =
      EuclideanSpace.single a 1 := by
    have := congrArg (fun T => T (EuclideanSpace.single a (1 : ℝ))) hA
    simpa using this
  have hin : ∀ v, A v a = inner ℝ v (ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1)) :=
    fun v => by
      rw [ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_single_right]
      simp
  refine ⟨?_, hAA, hin⟩
  have h1 := hin (ContinuousLinearMap.adjoint A (EuclideanSpace.single a 1))
  rw [hAA, real_inner_self_eq_norm_sq] at h1
  norm_num at h1
  have hn := norm_nonneg (ContinuousLinearMap.adjoint A (EuclideanSpace.single a (1 : ℝ)))
  nlinarith

/-- Scalar step of TCP03's saturation: a test value `c` within `γ` of `q(400 + r)` with
`q ≥ 1/(400 + 3β)`, `|r| ≤ 2E₀ + 2β` (small `β, E₀ ≥ 0`) is at least `1 − (γ + E₀ + β)`. -/
theorem saturation_scalar_KA4 {c q r γ E₀ β : ℝ} (hq : 1 / (400 + 3 * β) ≤ q)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1000) (hE0 : 0 ≤ E₀) (hE : E₀ ≤ 1)
    (hr : |r| ≤ 2 * E₀ + 2 * β) (hc : |c - q * (400 + r)| ≤ γ) :
    1 - (γ + E₀ + β) ≤ c := by
  have hden : 0 < 400 + 3 * β := by linarith
  have hfrac : 1 - (5 * β + 2 * E₀) / (400 + 3 * β) =
      (1 / (400 + 3 * β)) * (400 - 2 * E₀ - 2 * β) := by
    field_simp
    ring
  have h400 : 1 - (5 * β + 2 * E₀) / (400 + 3 * β) ≤ q * (400 - 2 * E₀ - 2 * β) := by
    rw [hfrac]
    exact mul_le_mul_of_nonneg_right hq (by linarith)
  have hsmall : (5 * β + 2 * E₀) / (400 + 3 * β) ≤ E₀ + β := by
    rw [div_le_iff₀ hden]
    have h0 : 0 ≤ E₀ * (398 + 3 * β) + β * (395 + 3 * β) := by positivity
    linarith only [h0]
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  have hlow : q * (400 - 2 * E₀ - 2 * β) ≤ q * (400 + r) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hr).1]) hq0
  linarith [(abs_le.mp hc).1]

/-- Vector step of TCP03 for a listed chart: (TR) at `x` and `y`, the lift
`‖W_y − W_x − 400ξ‖ < 2β` with `Aξ = e_a`, and the chart's test `‖v − q s (U_y − U_x)‖ < γ`
give `|v_a − q(400 + r)| ≤ γ` with `|r| ≤ 2E₀ + 2β`. -/
theorem listed_component_vector_KA4 {k : ℕ}
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) (a : Fin k)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hAξ : A ξ = EuclideanSpace.single a 1)
    {Uy Ux c v : EuclideanSpace ℝ (Fin k)} {Wy Wx : EuclideanSpace ℝ (Fin 2)} {s q γ E₀ β : ℝ}
    (hy : ‖s • Uy - A Wy - c‖ < E₀) (hx : ‖s • Ux - A Wx - c‖ < E₀)
    (hl : ‖Wy - Wx - (400 : ℝ) • ξ‖ < 2 * β) (ht : ‖v - (q * s) • (Uy - Ux)‖ < γ) :
    ∃ r : ℝ, |r| ≤ 2 * E₀ + 2 * β ∧ |v a - q * (400 + r)| ≤ γ := by
  set R : EuclideanSpace ℝ (Fin k) := s • (Uy - Ux) - (400 : ℝ) • EuclideanSpace.single a 1
    with hR
  have hdecomp : R = ((s • Uy - A Wy - c) - (s • Ux - A Wx - c)) + A (Wy - Wx - (400 : ℝ) • ξ) := by
    rw [hR, map_sub, map_sub, map_smul, hAξ, smul_sub]
    abel
  have hAn := DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one A hA
  have h3 : ‖A (Wy - Wx - (400 : ℝ) • ξ)‖ ≤ ‖Wy - Wx - (400 : ℝ) • ξ‖ := by
    have := A.le_opNorm (Wy - Wx - (400 : ℝ) • ξ)
    nlinarith [norm_nonneg (Wy - Wx - (400 : ℝ) • ξ)]
  have hRn : ‖R‖ ≤ 2 * E₀ + 2 * β := by
    rw [hdecomp]
    calc _ ≤ ‖(s • Uy - A Wy - c) - (s • Ux - A Wx - c)‖ + ‖A (Wy - Wx - (400 : ℝ) • ξ)‖ :=
          norm_add_le _ _
      _ ≤ (‖s • Uy - A Wy - c‖ + ‖s • Ux - A Wx - c‖) + ‖Wy - Wx - (400 : ℝ) • ξ‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ 2 * E₀ + 2 * β := by linarith
  refine ⟨R a, (PiLp.norm_apply_le R a).trans hRn, ?_⟩
  have hkey : (q * s) • (Uy - Ux) = q • ((400 : ℝ) • EuclideanSpace.single a 1 + R) := by
    rw [hR, add_sub_cancel, smul_smul]
  rw [hkey] at ht
  have h := PiLp.norm_apply_le (v - q • ((400 : ℝ) • EuclideanSpace.single a 1 + R)) a
  have hc : (v - q • ((400 : ℝ) • EuclideanSpace.single a 1 + R) : EuclideanSpace ℝ (Fin k)) a =
      v a - q * (400 + R a) := by
    simp
    ring
  rw [hc] at h
  exact h.trans ht.le

/-- Vector step of TCP03 for the reference chart: the lift `‖W_y − W_x − 400ξ‖ < 2β` (`‖ξ‖ = 1`)
and the reference test `‖v − q(W_y − W_x)‖ < γ` give `|⟨v, ξ⟩ − q(400 + r)| ≤ γ`, `|r| ≤ 2β`. -/
theorem reference_component_vector_KA4 {ξ v Wy Wx : EuclideanSpace ℝ (Fin 2)} {q γ β : ℝ}
    (hξ : ‖ξ‖ = 1) (hl : ‖Wy - Wx - (400 : ℝ) • ξ‖ < 2 * β) (ht : ‖v - q • (Wy - Wx)‖ < γ) :
    ∃ r : ℝ, |r| ≤ 2 * β ∧ |inner ℝ v ξ - q * (400 + r)| ≤ γ := by
  set e' := Wy - Wx - (400 : ℝ) • ξ with he'
  refine ⟨inner ℝ e' ξ, ?_, ?_⟩
  · have := abs_real_inner_le_norm e' ξ
    rw [hξ, mul_one] at this
    linarith
  · have hdec : q • (Wy - Wx) = q • ((400 : ℝ) • ξ + e') := by rw [he', add_sub_cancel]
    rw [hdec] at ht
    have h1 := abs_real_inner_le_norm (v - q • ((400 : ℝ) • ξ + e')) ξ
    rw [hξ, mul_one] at h1
    have h2 : inner ℝ (v - q • ((400 : ℝ) • ξ + e')) ξ =
        inner ℝ v ξ - q * (400 + inner ℝ e' ξ) := by
      rw [inner_sub_left, real_inner_smul_left, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hξ]
      ring
    rw [h2] at h1
    exact h1.trans ht.le

/-- The lift of TCP03 in the reference chart: for `x ∈ D_i` and a unit `ξ`, a point `y` with
`397ρ(i) ≤ d(x, y) ≤ (400 + 3β₂)ρ(i)`, `d(y, i) < 415ρ(i)` and `‖u_i(y) − u_i(x) − 400ξ‖ < 2β₂`. -/
theorem circle_reference_lift_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {x : X} (hx : x ∈ ball i (10 * ρ i))
    (hβ : β 2 ≤ 1 / 1000) (ξ : ℝ²) (hξ : ‖ξ‖ = 1) :
    ∃ y, 397 * ρ i ≤ dist x y ∧ dist x y ≤ (400 + 3 * β 2) * ρ i ∧ dist y i < 415 * ρ i ∧
      ‖circleRaw_KA3 P i y - circleRaw_KA3 P i x - (400 : ℝ) • ξ‖ < 2 * β 2 := by
  have hri := hρ i
  let Ai := P.circleAdapted i hi
  let _ := Ai.instY
  have hβpos : 0 < β 2 := @KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri))
    _ _ _ _ Ai.split
  have hxR : @dist X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)).toDist x i < 10 := by
    rw [MetricSpace.rescale_dist]
    exact inv_mul_dist_lt_of_mem_ball_LC87 hri hx
  have hroom : 10 + 400 + 2 * β 2 ≤ (β 2)⁻¹ := by
    have : (1000 : ℝ) ≤ (β 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hβpos]; linarith
    linarith
  obtain ⟨y, -, hdxy, hlift, hyi⟩ := @kl_lift_KA4 X Ai.Y (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri))
    Ai.instY 2 i Ai.a (β 2) Ai.split x 10 400 hxR ξ hξ (by norm_num) hroom
  rw [MetricSpace.rescale_dist] at hdxy hyi
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · have h' : 397 ≤ (ρ i)⁻¹ * dist x y := by linarith [(abs_le.mp hdxy).1]
    have := (le_inv_mul_iff₀ hri).mp h'
    linarith
  · have h' : (ρ i)⁻¹ * dist x y ≤ 400 + 3 * β 2 := by linarith [(abs_le.mp hdxy).2]
    have := (inv_mul_le_iff₀ hri).mp h'
    linarith
  · have h' : (ρ i)⁻¹ * dist y i < 415 := by linarith
    have := (inv_mul_lt_iff₀ hri).mp h'
    linarith
  · rw [circleRaw_KA3_eq P hi, circleRaw_KA3_eq P hi]
    exact hlift

/-- **TCP03, one circle component** (saturation of both covectors on one physical direction).
At `x ∈ D_i = B(i, 10ρ(i))`, for a listed circle chart `j` (ratio `s = ρ(j)/ρ(i) ∈ (.99, 1.01)`,
`d(j, i) ≤ 214ρ(i)`, `x ∈ B(j, 200ρ(j))`) with (TR) `|s u_j − A u_i − s u_j(i)| < E₀` on
`B(i, 1000ρ(i))`, and a component `a`, some `g`-unit `w₀` has
`(ρ(j) dη_j(w₀))_a ≥ 1 − (γ + E₀ + β₂)` and `(A(ρ(i) dη_i(w₀)))_a ≥ 1 − (γ + E₀ + β₂)`
(the lift of `u_i(x) + 400 A* e_a` and the two original long tests). -/
theorem circle_component_saturation_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.circle.centres)
    (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100)) (hdij : dist j i ≤ 214 * ρ i)
    {x : X} (hx : x ∈ ball i (10 * ρ i)) (hxj : x ∈ ball j (200 * ρ j))
    (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) (A : ℝ² →L[ℝ] ℝ²)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖(ρ j / ρ i) • circleRaw_KA3 P j z - A (circleRaw_KA3 P i z) -
        (ρ j / ρ i) • circleRaw_KA3 P j i‖ < E₀)
    (a : Fin 2) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧
      1 - (γ + E₀ + β 2) ≤
        (ρ j • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w₀) a ∧
      1 - (γ + E₀ + β 2) ≤
        A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀) a := by
  have hri := hρ i
  have hrj := hρ j
  obtain ⟨hs1, hs2⟩ := hs
  have hrj1 : ρ j < 101 / 100 * ρ i := by rwa [div_lt_iff₀ hri] at hs2
  have hrj2 : 99 / 100 * ρ i < ρ j := by rwa [lt_div_iff₀ hri] at hs1
  obtain ⟨hξ, hAξ, hcomp⟩ := coisometry_adjoint_single_KA4 A hA a
  let _ := (P.circleAdapted i hi).instY
  have hβpos : 0 < β 2 := @KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri))
    _ _ _ _ (P.circleAdapted i hi).split
  obtain ⟨y, hD1, hD2, hyi, hlift⟩ := circle_reference_lift_KA4 P hi hx hβ _ hξ
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hDpos : 0 < dist x y := by linarith
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  obtain ⟨w₀, hw₀, htests⟩ := circle_tests_common_dir_KA4 P hxy
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hq : 1 / (400 + 3 * β 2) ≤ ρ i / dist x y := by
    rw [div_le_div_iff₀ (by linarith) hDpos]
    linarith
  refine ⟨w₀, hw₀, ?_, ?_⟩
  · have hyj : y ∈ ball j (201 * 10000 * ρ j) := by
      rw [mem_ball]
      have := dist_triangle y i j
      rw [dist_comm i j] at this
      linarith
    have hT := htests j hj hxj hyj (by linarith)
    have hqs : ρ j / dist x y = ρ i / dist x y * (ρ j / ρ i) := by
      field_simp
    rw [hqs] at hT
    obtain ⟨r, hr, hc⟩ := listed_component_vector_KA4 A hA a hAξ (hTR y (by linarith))
      (hTR x (by linarith)) hlift hT
    exact saturation_scalar_KA4 hq hβpos.le hβ hE0 hE hr hc
  · have hxi2 : x ∈ ball i (200 * ρ i) := by rw [mem_ball]; linarith
    have hyi2 : y ∈ ball i (201 * 10000 * ρ i) := by rw [mem_ball]; linarith
    have hT := htests i hi hxi2 hyi2 (by linarith)
    obtain ⟨r, hr, hc⟩ := reference_component_vector_KA4 hξ hlift hT
    rw [hcomp]
    exact saturation_scalar_KA4 hq hβpos.le hβ hE0 hE (by linarith) hc

/-- **TCP03, circle derivative clause** (FC15's rowwise Riesz calculation on the normalized
tangent space of `ρ(i)⁻² g`): under the hypotheses of `circle_component_saturation_KA4`, with
`ε = γ + E₀ + β₂`, every tangent vector `w` at `x` has
`‖s dη_j(w) − A dη_i(w)‖ ≤ 2√(2(4ε + ε²)) · √(ρ(i)⁻² g(w, w))`. -/
theorem circle_derivative_comparison_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.circle.centres)
    (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100)) (hdij : dist j i ≤ 214 * ρ i)
    {x : X} (hx : x ∈ ball i (10 * ρ i)) (hxj : x ∈ ball j (200 * ρ j))
    (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) (A : ℝ² →L[ℝ] ℝ²)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖(ρ j / ρ i) • circleRaw_KA3 P j z - A (circleRaw_KA3 P i z) -
        (ρ j / ρ i) • circleRaw_KA3 P j i‖ < E₀)
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
      2 * Real.sqrt (2 * (4 * (γ + E₀ + β 2) + (γ + E₀ + β 2) ^ 2)) *
        Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hrj := hρ j
  let _ := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
  have hnorm : ∀ v : TangentSpace 𝓘(ℝ, E3) x, ‖v‖ = Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) :=
    norm_tangent_radialScaled_KA4 g hri x
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  let _ := (P.circleAdapted i hi).instY
  have hβpos : 0 < β 2 := @KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri))
    _ _ _ _ (P.circleAdapted i hi).split
  set ε' := γ + E₀ + β 2 with hε'
  have hε0 : 0 ≤ ε' := by positivity
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  set f : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ² :=
    (ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x with hfdef
  set gg : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ² :=
    mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x with hgdef
  have hsq : ∀ v : TangentSpace 𝓘(ℝ, E3) x, (ρ j / ρ i) * Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x v v) =
      Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := fun v => by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (inv_pos.mpr hrj).le, Real.sqrt_sq (inv_pos.mpr hri).le]
    field_simp
  have hfb : ‖f‖ ≤ 1 + ε' := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h := circleAdapted_gram_upper_KA2 P hγ hj hxj v
    change ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x v‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrj hri), hnorm v, ← hsq v]
    have hs0 : 0 ≤ ρ j / ρ i := (div_pos hrj hri).le
    have hv0 := Real.sqrt_nonneg ((ρ j)⁻¹ ^ 2 * g.inner x v v)
    calc ρ j / ρ i * ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x v‖
        ≤ ρ j / ρ i * ((1 + γ) * Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x v v)) :=
          mul_le_mul_of_nonneg_left h hs0
      _ ≤ (1 + ε') * (ρ j / ρ i * Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x v v)) := by
          have : 1 + γ ≤ 1 + ε' := by linarith
          nlinarith [mul_nonneg hs0 hv0]
  have hgb : ‖gg‖ ≤ 1 + ε' := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h := circleAdapted_gram_upper_KA2 P hγ hi hxi v
    rw [hnorm v]
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc ‖gg v‖ ≤ (1 + γ) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := h
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + γ ≤ 1 + ε' := by linarith
          nlinarith
  have hrows : ∀ a : Fin 2, ‖(EuclideanSpace.proj a : StrongDual ℝ ℝ²).comp f‖ ≤ 1 + ε' := by
    intro a
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hp : ‖(EuclideanSpace.proj a : StrongDual ℝ ℝ²)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro y
      change ‖y a‖ ≤ 1 * ‖y‖
      simpa only [one_mul] using PiLp.norm_apply_le y a
    calc _ ≤ 1 * (1 + ε') := mul_le_mul hp hfb (norm_nonneg _) zero_le_one
      _ = 1 + ε' := one_mul _
  have htests : ∀ a : Fin 2, ∃ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖w‖ = 1 ∧ 1 - ε' ≤ f w a ∧ 1 - ε' ≤ A (gg w) a := by
    intro a
    obtain ⟨w₀, hw₀, h1, h2⟩ := circle_component_saturation_KA4 P hi hj hs hdij hx hxj hβ hE A hA
      hTR a
    refine ⟨ρ i • w₀, ?_, ?_, ?_⟩
    · rw [hnorm, gInner_smul_self, hw₀]
      have : (ρ i)⁻¹ ^ 2 * (ρ i ^ 2 * 1) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    · have hfe : f (ρ i • w₀) =
          ρ j • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w₀ := by
        rw [hfdef, smul_apply, map_smul, smul_smul]
        congr 1
        field_simp
      rw [hfe]
      exact h1
    · have hge : gg (ρ i • w₀) =
          ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀ := map_smul _ _ _
      rw [hge]
      exact h2
  have hR := DifferentialGeometry.Geometry.Fibration.norm_difference_of_common_directions f gg A hA
    hε0 hrows hgb htests
  have hw := (f - A.comp gg).le_opNorm w
  rw [hnorm w] at hw
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast] at hR
  calc ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ =
        ‖(f - A.comp gg) w‖ := rfl
    _ ≤ ‖f - A.comp gg‖ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := hw
    _ ≤ _ := mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _)

/-- **TCP03, circle value clause**: `|s η_j(x) − A η_i(x) − s u_j(i)| < sγ + E₀ + γ` from the two
adapted value errors and (TR) at `x`. -/
theorem circle_value_comparison_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.circle.centres)
    {x : X} (hx : x ∈ ball i (10 * ρ i)) (hxj : x ∈ ball j (200 * ρ j)) {E₀ : ℝ}
    (A : ℝ² →L[ℝ] ℝ²) (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
        (ρ j / ρ i) • circleRaw_KA3 P j i‖ < E₀) :
    ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
        A (cgpCircleCoord P.toLocalChartFamily i hi x) - (ρ j / ρ i) • circleRaw_KA3 P j i‖ <
      ρ j / ρ i * γ + E₀ + γ := by
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; have := hρ i; linarith
  have hvj : ‖cgpCircleCoord P.toLocalChartFamily j hj x - circleRaw_KA3 P j x‖ < γ := by
    have h := (circleAdapted_physical_KA2 P hγ hj).1 x hxj
    rw [circleRaw_KA3_eq P hj]
    exact h
  have hvi : ‖cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x‖ < γ := by
    have h := (circleAdapted_physical_KA2 P hγ hi).1 x hxi
    rw [circleRaw_KA3_eq P hi]
    exact h
  have hs0 : 0 < ρ j / ρ i := div_pos (hρ j) (hρ i)
  have hAn := DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one A hA
  have hdec : (ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
      A (cgpCircleCoord P.toLocalChartFamily i hi x) - (ρ j / ρ i) • circleRaw_KA3 P j i =
      (ρ j / ρ i) • (cgpCircleCoord P.toLocalChartFamily j hj x - circleRaw_KA3 P j x) +
        ((ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
          (ρ j / ρ i) • circleRaw_KA3 P j i) -
        A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x) := by
    rw [map_sub, smul_sub]
    abel
  rw [hdec]
  have h3 : ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x)‖ < γ := by
    refine lt_of_le_of_lt ?_ hvi
    have := A.le_opNorm (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x)
    nlinarith [norm_nonneg (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x)]
  have h1 : ‖(ρ j / ρ i) • (cgpCircleCoord P.toLocalChartFamily j hj x - circleRaw_KA3 P j x)‖ ≤
      ρ j / ρ i * γ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left hvj.le hs0.le
  calc _ ≤ ‖(ρ j / ρ i) • (cgpCircleCoord P.toLocalChartFamily j hj x - circleRaw_KA3 P j x) +
        ((ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
          (ρ j / ρ i) • circleRaw_KA3 P j i)‖ +
        ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x)‖ := norm_sub_le _ _
    _ ≤ (‖(ρ j / ρ i) • (cgpCircleCoord P.toLocalChartFamily j hj x - circleRaw_KA3 P j x)‖ +
        ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
          (ρ j / ρ i) • circleRaw_KA3 P j i‖) +
        ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P i x)‖ := by
        gcongr; exact norm_add_le _ _
    _ < ρ j / ρ i * γ + E₀ + γ := by linarith

/-- The circle adaptation error is nonnegative (packet (i) at its own centre). -/
theorem circle_quality_nonneg_KA4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) : 0 ≤ γ := by
  have hA := (P.circleAdapted i hi).adapted
  have hiB : i ∈ @ball X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))).toPseudoMetricSpace i 200 :=
    @mem_ball_self X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))).toPseudoMetricSpace i 200
      (by norm_num)
  exact (norm_nonneg _).trans (hA i hiB).le

/-- TCP03's Riesz budget: `0 ≤ ε ≤ 3θ²/1000`, `0 < θ < 1` give `2√(2(4ε + ε²)) ≤ θ/2`. -/
theorem riesz_budget_KA4 {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 3 * θ ^ 2 / 1000) : 2 * Real.sqrt (2 * (4 * ε + ε ^ 2)) ≤ θ / 2 := by
  have hε1 : ε ≤ 1 := by nlinarith
  have h1 : 2 * (4 * ε + ε ^ 2) ≤ (θ / 4) ^ 2 := by nlinarith
  have h2 : Real.sqrt (2 * (4 * ε + ε ^ 2)) ≤ θ / 4 := by
    calc Real.sqrt (2 * (4 * ε + ε ^ 2)) ≤ Real.sqrt ((θ / 4) ^ 2) := Real.sqrt_le_sqrt h1
      _ = θ / 4 := Real.sqrt_sq (by positivity)
  linarith

/-- **TCP03 (circle blocks)** (`lem:fibration-first-constant-comparison`, B:5370) on
`LocalChartPackets`: for an early `0 < θ < 1` (and the exclusion quality `ν`, `3ν ≤ β₃ < 1`) there
are an early `σ`, an early circle quality bound `η₂` and an early adaptation bound `γ₀` (all before
`Δ`) such that, with FC07's parameter ranges, `3β₂ ≤ σ`, `β₂ ≤ η₂`, `γ ≤ γ₀` and `σ⁻¹ ≤ Lmax`: at
every circle centre `i`, every listed circle chart `j` (closed support meeting `D_i = B(i, 10ρ(i))`)
has ONE coisometry `A_j` with TCP02's (TR) at accuracy `θ²/1000` on `B(i, 1000ρ(i))` and (TC) on
`D_i` for the SAME smooth coordinates, `λ_j(a) = A_j a + s_j u_j(p_i)`, norms of `ρ(i)⁻² g`:
`|s_j η_j − λ_j(η_i)| ≤ θ/2` and `|s_j dη_j(w) − A_j dη_i(w)| ≤ (θ/2)|w|`, so
`‖·‖_{C¹(D_i)} < θ`. -/
theorem tcp03_circle_row {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres) j (hj : j ∈ P.circle.centres),
        (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x, dist x i < 1000 * ρ i →
            ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
              (ρ j / ρ i) • circleRaw_KA3 P j i‖ < θ ^ 2 / 1000) ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
                A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                (ρ j / ρ i) • circleRaw_KA3 P j i‖ ≤ θ / 2 ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hE₀ : (0 : ℝ) < θ ^ 2 / 1000 := by positivity
  obtain ⟨σ₂, hσ₂, hσ₂1, h2⟩ := tcp02_pair_KA3 hE₀ hν hν1 (j := 2) one_le_two le_rfl
  obtain ⟨η, hη, hk2⟩ := h2 214 (by norm_num)
  refine ⟨σ₂, hσ₂, hσ₂1, min η (θ ^ 2 / 1000), lt_min hη hE₀, θ ^ 2 / 1000, hE₀, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hγ hσL i hi j hj hmeet
  have hγ0 := circle_quality_nonneg_KA4 P hi
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hβθ : β 2 ≤ θ ^ 2 / 1000 := hβ2.trans (min_le_right _ _)
  have hβ1000 : β 2 ≤ 1 / 1000 := by nlinarith
  have hsec₂ := tcp02_sectional_KA3 P hσ₂ (by linarith) hσL i
  have hno := circle_no_three_KA3 P.circle hi hν3 hβ3
  obtain ⟨-, hcirc, -, -, -, -⟩ := fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT i
  obtain ⟨hratio, hdist, hsub1, hsub2, -⟩ := hcirc j hj hmeet
  have hdist' : dist j i ≤ 214 * ρ i := by linarith
  obtain ⟨-, hC1, -⟩ := tcp01_row P hΛ hΔ hμ hτ hLΛ hLmax he hT hγ0 hi
  obtain ⟨hs, -⟩ := hC1 j hj hmeet
  let Ai := P.circleAdapted i hi
  let Aj := P.circleAdapted j hj
  obtain ⟨A, hA, hal⟩ := @hk2 X mX _ _ _ g hmetric i j (ρ i) (ρ j) (hρ i) (hρ j) hratio.1
    hratio.2 (by rw [dist_comm]; linarith) hsec₂ hno Aj.Y Ai.Y Aj.instY Ai.instY Aj.a Ai.a (β 2)
    (β 2) (hβ2.trans (min_le_left _ _)) hβ2σ Aj.split Ai.split
  have hTR : ∀ x, dist x i < 1000 * ρ i →
      ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
        (ρ j / ρ i) • circleRaw_KA3 P j i‖ < θ ^ 2 / 1000 := by
    intro x hx
    rw [circleRaw_KA3_eq P hj, circleRaw_KA3_eq P hi, circleRaw_KA3_eq P hj]
    exact hal x hx
  refine ⟨A, hA, hTR, fun x hx => ⟨?_, fun w => ?_⟩⟩
  · have hxj : x ∈ ball j (200 * ρ j) := hsub2 (hsub1 hx)
    have hv := circle_value_comparison_KA4 P hγ0 hi hj hx hxj A hA
      (hTR x (by have := mem_ball.mp hx; have := hρ i; linarith))
    have hs2 : ρ j / ρ i < 101 / 100 := hs.2
    have : ρ j / ρ i * γ ≤ 101 / 100 * (θ ^ 2 / 1000) := by
      have hs0 : 0 ≤ ρ j / ρ i := (div_pos (hρ j) (hρ i)).le
      nlinarith
    linarith
  · have hxj : x ∈ ball j (200 * ρ j) := hsub2 (hsub1 hx)
    have hd := circle_derivative_comparison_KA4 P hγ0 hi hj hs hdist' hx hxj hβ1000
      (E₀ := θ ^ 2 / 1000) (by nlinarith) A hA hTR w
    let _ := Ai.instY
    have hβpos : 0 < β 2 := @KleinerLottApprox.error_pos X _
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ _ _ _ Ai.split
    have hb := riesz_budget_KA4 hθ hθ1 (ε := γ + θ ^ 2 / 1000 + β 2) (by linarith) (by linarith)
    exact hd.trans (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry.Collapse
