import DifferentialGeometry.Geometry.Collapse.RankOneAdaptedCoordinates
import DifferentialGeometry.Geometry.Comparison.AdaptedCoordinateTransfer
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound

/-!
# Calibrated comparison with the prescribed radial coordinate

All directional estimates use actual minimizing inward prefixes for the
original distance function, and ambient distances on the same unit ball.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem hasDerivAt_unit_geodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (w : TangentSpace I x) :
    HasDerivAt (fun t => f (intrinsicGeodesic g hEnorm x w t))
      (mvfderiv (I := I) f x w) 0 := by
  let c := intrinsicGeodesic g hEnorm x w
  have hc0 : c 0 = x := intrinsicGeodesic_zero g hEnorm x w
  have hc := intrinsicGeodesic_contMDiff g hEnorm x w
  have hline := hasDerivAt_comp_mfderiv_along I f c 0
    (by simpa only [hc0] using hf) (hc.contMDiffAt.mdifferentiableAt (by simp))
  change HasDerivAt (fun t => f (c t))
    (mvfderiv (I := I) f (c 0)
      (mfderiv 𝓘(ℝ, ℝ) I c 0 (realTangentOne 0))) 0 at hline
  have hspeed : mfderiv 𝓘(ℝ, ℝ) I c 0 (realTangentOne 0) = w := by
    change mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) = w
    exact intrinsicGeodesic_mfderiv_zero g hEnorm x w
  simp only [hspeed] at hline
  rw [hc0] at hline
  exact hline

private theorem unit_derivative_bound_of_lipschitzOn (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {U : Set M} {x : M} {L : ℝ}
    (hL : 0 ≤ L) (hU : IsOpen U) (hx : x ∈ U)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hlip : ∀ y ∈ U, ∀ z ∈ U, |f y - f z| ≤ L * dist y z)
    (w : TangentSpace I x) (hw : g.inner x w w = 1) :
    |mvfderiv (I := I) f x w| ≤ L := by
  let c := intrinsicGeodesic g hEnorm x w
  have hc0 : c 0 = x := intrinsicGeodesic_zero g hEnorm x w
  have hc := intrinsicGeodesic_contMDiff g hEnorm x w
  have hcU : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U := by
    have ht := hc.continuous.tendsto 0
    rw [intrinsicGeodesic_zero] at ht
    exact ht.eventually (hU.mem_nhds hx)
  have hline := hasDerivAt_unit_geodesic g hEnorm hf w
  have hb := hline.le_of_lip' hL (show ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖f (c t) - f (c 0)‖ ≤ L * ‖t - 0‖ from by
    filter_upwards [hcU] with t ht
    have hl := hlip (c t) ht x hx
    have hd := (lipschitzWith_one_intrinsicGeodesic g hEnorm x w hw).dist_le_mul t 0
    simp only [NNReal.coe_one, one_mul, intrinsicGeodesic_zero] at hd
    rw [hc0, Real.norm_eq_abs]
    exact hl.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.dist_eq, Real.norm_eq_abs] using hd) hL))
  simpa only [Real.norm_eq_abs] using hb

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gradient_norm_bound_of_unit_derivative_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {f : M → ℝ} {x : M} {L : ℝ} (hL : 0 ≤ L)
    (hder : ∀ w : TangentSpace I x, g.inner x w w = 1 →
      |mvfderiv (I := I) f x w| ≤ L) : ‖gradientFun g f x‖ ≤ L := by
  let v := gradientFun g f x
  by_cases hv : v = 0
  · simpa only [v, hv, norm_zero] using hL
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : TangentSpace I x := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
    exact inv_mul_cancel₀ hn.ne'
  have hw : g.inner x w w = 1 := by
    rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, hwn]
    norm_num
  have hd := hder w hw
  rw [← inner_gradientFun, ← hEnorm.inner_eq] at hd
  have he : inner ℝ v w = ‖v‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  change |inner ℝ v w| ≤ L at hd
  rw [he, abs_of_pos hn] at hd
  exact hd

private theorem calibrated_reference_gradient
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p q x : M} {φ : M → ℝ} {γ : ℝ}
    (hγ : 0 < γ) (hγthird : γ < 1 / 3) (hpq : 3 < dist p q)
    (hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1))
    (hlip : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q 1,
      |φ y - φ z| ≤ (1 + γ) * dist y z)
    (htest : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist y z →
      ∀ w : TangentSpace I y, g.inner y w w = 1 →
      intrinsicGeodesic g hEnorm y w (dist y z) = z →
      |mvfderiv (I := I) φ y w -
        ((dist p z - dist p q) - (dist p y - dist p q)) / dist y z| < γ)
    (hx : x ∈ Metric.ball q 1) (v : TangentSpace I x) (hv : g.inner x v v = 1)
    (hend : intrinsicGeodesic g hEnorm x v (dist x p) = p) :
    ‖gradientFun g φ x + v‖ ≤ Real.sqrt (4 * γ + γ ^ 2) := by
  have hxq : dist x q < 1 := Metric.mem_ball.mp hx
  have hxp : 2 < dist x p := by
    have htri := dist_triangle p x q
    rw [dist_comm p x] at htri
    linarith
  let y := intrinsicGeodesic g hEnorm x v 2
  have hremain : dist y p = dist x p - 2 := by
    have hh := infDist_intrinsicGeodesic_to_set g hEnorm hv
      (S := {p}) (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hend)
      (t := 2) (by simp only [Metric.infDist_singleton]; exact ⟨by norm_num, hxp.le⟩)
    simpa only [Metric.infDist_singleton] using hh
  have hxyLe : dist x y ≤ 2 := by
    have hd := (lipschitzWith_one_intrinsicGeodesic g hEnorm x v hv).dist_le_mul 0 2
    simpa only [intrinsicGeodesic_zero, NNReal.coe_one, one_mul, Real.dist_eq,
      zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hd
  have hxy : dist x y = 2 := by
    have htri := dist_triangle x y p
    linarith
  have hyq : dist y q < 3 := by
    have htri := dist_triangle y x q
    rw [dist_comm y x, hxy] at htri
    linarith
  have hinv : 3 < γ⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hγ]
    linarith
  have hy : y ∈ Metric.ball q γ⁻¹ := Metric.mem_ball.mpr (hyq.trans hinv)
  have hdir := htest x hx y hy (by rw [hxy]; norm_num) v hv
    (by rw [hxy])
  have hquot : ((dist p y - dist p q) - (dist p x - dist p q)) / dist x y = -1 := by
    rw [dist_comm p y, dist_comm p x, hremain, hxy]
    ring
  rw [hquot, sub_neg_eq_add] at hdir
  have hφx := (hφ x hx).contMDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hnorm : ‖gradientFun g φ x‖ ≤ 1 + γ :=
    gradient_norm_bound_of_unit_derivative_bound g hEnorm (by linarith)
      (unit_derivative_bound_of_lipschitzOn g hEnorm (by linarith) Metric.isOpen_ball hx
        (hφx.mdifferentiableAt (by simp)) hlip)
  have hvnorm : ‖v‖ = 1 := by
    have he := hEnorm.inner_eq x v v
    rw [real_inner_self_eq_norm_sq, hv] at he
    nlinarith [norm_nonneg v]
  have hcal : inner ℝ (gradientFun g φ x) v ≤ -1 + γ := by
    rw [hEnorm.inner_eq, inner_gradientFun]
    linarith [(abs_lt.mp hdir).2]
  have hsq := norm_add_unit_sq_le hnorm hvnorm hcal
  exact Real.le_sqrt_of_sq_le hsq

private theorem norm_le_of_unit_inner_abs {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : V} {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ w : V, ‖w‖ = 1 → |inner ℝ v w| ≤ L) : ‖v‖ ≤ L := by
  by_cases hv : v = 0
  · simpa only [hv, norm_zero] using hL
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
    exact inv_mul_cancel₀ hn.ne'
  have he : inner ℝ v w = ‖v‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h := hb w hw
  rwa [he, abs_of_pos hn] at h

theorem radial_smoothing_calibrated_gradient_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p q : M} {φ ψ : M → ℝ} {γ ε : ℝ}
    (hγ : 0 < γ) (hγthird : γ < 1 / 3) (hε : 0 ≤ ε) (hpq : 3 < dist p q)
    (hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1))
    (hψ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (Metric.ball q 1))
    (hlip : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q 1,
      |φ y - φ z| ≤ (1 + γ) * dist y z)
    (htest : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist y z →
      ∀ w : TangentSpace I y, g.inner y w w = 1 →
      intrinsicGeodesic g hEnorm y w (dist y z) = z →
      |mvfderiv (I := I) φ y w -
        ((dist p z - dist p q) - (dist p y - dist p q)) / dist y z| < γ)
    (hdiff : ∀ y z, |(ψ y - (dist p y - dist p q)) -
      (ψ z - (dist p z - dist p q))| ≤ ε * dist y z) :
    ∀ x ∈ Metric.ball q 1,
      ‖gradientFun g ψ x - gradientFun g φ x‖ ≤
        Real.sqrt (4 * γ + γ ^ 2) + Real.sqrt (4 * ε + ε ^ 2) := by
  intro x hx
  have hxq : dist x q < 1 := Metric.mem_ball.mp hx
  have hxp : 0 < dist x p := by
    have htri := dist_triangle p x q
    rw [dist_comm p x] at htri
    linarith
  have hψx := (hψ x hx).contMDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have herror : ∀ y z, |(ψ y - Metric.infDist y ({p} : Set M)) -
      (ψ z - Metric.infDist z ({p} : Set M))| ≤ ε * dist y z := by
    intro y z
    simp only [Metric.infDist_singleton]
    have hd := hdiff y z
    rw [dist_comm p y, dist_comm p z] at hd
    convert hd using 1
    congr 1
    ring
  obtain ⟨u, hu, hψu⟩ := exists_minimizingDirection_smoothing_derivative_bound
    g hEnorm hε isClosed_singleton (singleton_nonempty p)
      (by simpa only [Metric.infDist_singleton] using hxp)
      (hψx.mdifferentiableAt (by simp)) herror
  have hφu := calibrated_reference_gradient g hEnorm hγ hγthird hpq hφ hlip htest hx u hu.1
    (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2)
  have hψunorm : ‖gradientFun g ψ x + u‖ ≤ ε := by
    apply norm_le_of_unit_inner_abs hε
    intro w hwn
    have hw : g.inner x w w = 1 := by
      rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, hwn]
      norm_num
    have hh := hψu w hw
    rw [_root_.inner_add_left, hEnorm.inner_eq, inner_gradientFun, hEnorm.inner_eq]
    exact hh
  have hsub := norm_sub_le (gradientFun g ψ x + u) (gradientFun g φ x + u)
  rw [add_sub_add_right_eq_sub] at hsub
  exact (hsub.trans (add_le_add hψunorm hφu)).trans (by
    have he := le_sqrt_four_mul_add_sq hε
    linarith)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem unit_derivative_difference_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {φ ψ : M → ℝ} {x : M} {A : ℝ}
    (hb : ‖gradientFun g ψ x - gradientFun g φ x‖ ≤ A)
    (w : TangentSpace I x) (hw : g.inner x w w = 1) :
    |mvfderiv (I := I) ψ x w - mvfderiv (I := I) φ x w| ≤ A := by
  have hwn : ‖w‖ = 1 := by
    have he := hEnorm.inner_eq x w w
    rw [real_inner_self_eq_norm_sq, hw] at he
    nlinarith [norm_nonneg w]
  have hh := abs_real_inner_le_norm (gradientFun g ψ x - gradientFun g φ x) w
  rw [_root_.inner_sub_left, hEnorm.inner_eq, inner_gradientFun,
    hEnorm.inner_eq, inner_gradientFun, hwn, mul_one] at hh
  exact hh.trans hb

private theorem centered_value_bound_of_gradient_difference
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {q : M} {φ ψ : M → ℝ} {A : ℝ}
    (hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1))
    (hψ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (Metric.ball q 1))
    (hφq : φ q = 0) (hψq : ψ q = 0)
    (hgrad : ∀ x ∈ Metric.ball q 1, ‖gradientFun g ψ x - gradientFun g φ x‖ ≤ A) :
    ∀ x ∈ Metric.ball q 1, |ψ x - φ x| ≤ A * dist q x := by
  intro x hx
  by_cases hqx : q = x
  · subst x
    simp only [hφq, hψq, sub_self, abs_zero, dist_self, mul_zero, le_refl]
  have hL : 0 < dist q x := dist_pos.mpr hqx
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm q x hL
  let c := intrinsicGeodesic g hEnorm q u
  have hc := intrinsicGeodesic_contMDiff g hEnorm q u
  have hc0 : c 0 = q := intrinsicGeodesic_zero g hEnorm q u
  have hcL : c (dist q x) = x := hend
  have hcball : ∀ t ∈ Icc (0 : ℝ) (dist q x), c t ∈ Metric.ball q 1 := by
    intro t ht
    have hd := (lipschitzWith_one_intrinsicGeodesic g hEnorm q u hu).dist_le_mul t 0
    simp only [intrinsicGeodesic_zero, NNReal.coe_one, one_mul, Real.dist_eq,
      sub_zero, abs_of_nonneg ht.1] at hd
    change dist (c t) q ≤ t at hd
    apply Metric.mem_ball.mpr
    have hx1 := Metric.mem_ball.mp hx
    rw [dist_comm x q] at hx1
    linarith [ht.2]
  let d : ℝ → ℝ := fun t =>
    mvfderiv (I := I) ψ (c t) (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t)) -
    mvfderiv (I := I) φ (c t) (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t))
  have hd : ∀ t ∈ Icc (0 : ℝ) (dist q x),
      HasDerivWithinAt (fun s => ψ (c s) - φ (c s)) (d t) (Icc 0 (dist q x)) t := by
    intro t ht
    have hcqt := hcball t ht
    have hψt := (hψ (c t) hcqt).contMDiffAt (Metric.isOpen_ball.mem_nhds hcqt)
    have hφt := (hφ (c t) hcqt).contMDiffAt (Metric.isOpen_ball.mem_nhds hcqt)
    have hψline := hasDerivAt_comp_mfderiv_along I ψ c t
      (hψt.mdifferentiableAt (by simp)) (hc.contMDiffAt.mdifferentiableAt (by simp))
    have hφline := hasDerivAt_comp_mfderiv_along I φ c t
      (hφt.mdifferentiableAt (by simp)) (hc.contMDiffAt.mdifferentiableAt (by simp))
    exact (hψline.sub hφline).hasDerivWithinAt
  have hb : ∀ t ∈ Ico (0 : ℝ) (dist q x), ‖d t‖ ≤ A := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) (dist q x) := ⟨ht.1, ht.2.le⟩
    have hs : g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t))
        (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t)) = 1 := by
      change g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)
        (mfderiv 𝓘(ℝ, ℝ) I c t 1) = 1
      exact (intrinsicGeodesic_speedSq_eq g hEnorm q u t).trans hu
    have hh := unit_derivative_difference_bound g hEnorm (hgrad (c t) (hcball t htcc))
      (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t)) hs
    simpa only [d, Real.norm_eq_abs] using hh
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    (dist q x) (right_mem_Icc.mpr hL.le)
  simpa only [hcL, hc0, hφq, hψq, sub_self, sub_zero, Real.norm_eq_abs] using hbound

theorem radial_smoothing_adapted_clauses
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p q : M} {φ ψ : M → ℝ} {γ ε ζ : ℝ}
    (hγ : 0 < γ) (hγthird : γ < 1 / 3) (hε : 0 ≤ ε) (hpq : 3 < dist p q)
    (hζ : γ + (Real.sqrt (4 * γ + γ ^ 2) + Real.sqrt (4 * ε + ε ^ 2)) ≤ ζ)
    (hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1))
    (hψ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (Metric.ball q 1))
    (hφq : φ q = 0) (hψq : ψ q = 0)
    (hlip : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q 1,
      |φ y - φ z| ≤ (1 + γ) * dist y z)
    (himage1 : ∀ x ∈ Metric.ball q 1, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ)
    (himage2 : ∀ t ∈ Ioo (-1 : ℝ) 1,
      Metric.infDist t (φ '' Metric.ball q 1) ≤ γ)
    (htest : ∀ y ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist y z →
      ∀ w : TangentSpace I y, g.inner y w w = 1 →
      intrinsicGeodesic g hEnorm y w (dist y z) = z →
      |mvfderiv (I := I) φ y w -
        ((dist p z - dist p q) - (dist p y - dist p q)) / dist y z| < γ)
    (hdiff : ∀ y z, |(ψ y - (dist p y - dist p q)) -
      (ψ z - (dist p z - dist p q))| ≤ ε * dist y z) :
    (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
    (∀ x ∈ Metric.ball q 1, Metric.infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, Metric.infDist t (ψ '' Metric.ball q 1) ≤ ζ) ∧
    ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q ζ⁻¹, 1 < dist x z →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      |mvfderiv (I := I) ψ x w -
        ((dist p z - dist p q) - (dist p x - dist p q)) / dist x z| < ζ := by
  let A := Real.sqrt (4 * γ + γ ^ 2) + Real.sqrt (4 * ε + ε ^ 2)
  have hA : 0 ≤ A := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hgrad := radial_smoothing_calibrated_gradient_bound g hEnorm hγ hγthird hε hpq
    hφ hψ hlip htest hdiff
  have hval := centered_value_bound_of_gradient_difference g hEnorm hφ hψ hφq hψq hgrad
  have hvalA : ∀ x ∈ Metric.ball q 1, |ψ x - φ x| ≤ A := by
    intro x hx
    apply (hval x hx).trans
    have hx1 : dist q x ≤ 1 := by
      rw [dist_comm]
      exact (Metric.mem_ball.mp hx).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hA
  obtain ⟨himg1, himg2⟩ := image_clauses_of_perturbation hζ hA hvalA himage1 himage2
  refine ⟨?_, himg1, himg2, ?_⟩
  · intro x hx y hy
    have he := le_sqrt_four_mul_add_sq hε
    have hrad : |(dist p x - dist p q) - (dist p y - dist p q)| ≤ dist x y := by
      rw [sub_sub_sub_cancel_right]
      simpa only [dist_comm x p, dist_comm y p] using abs_dist_sub_le x y p
    have hsplit : ψ x - ψ y =
        ((ψ x - (dist p x - dist p q)) - (ψ y - (dist p y - dist p q))) +
          ((dist p x - dist p q) - (dist p y - dist p q)) := by ring
    rw [hsplit]
    have hsum := abs_add_le
      ((ψ x - (dist p x - dist p q)) - (ψ y - (dist p y - dist p q)))
      ((dist p x - dist p q) - (dist p y - dist p q))
    have hεζ : ε ≤ ζ := by
      dsimp [A] at hA
      linarith [Real.sqrt_nonneg (4 * γ + γ ^ 2)]
    calc _ ≤ _ := hsum
      _ ≤ ε * dist x y + dist x y := add_le_add (hdiff x y) hrad
      _ ≤ (1 + ζ) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
  · intro x hx z hz hxz w hw hwz
    have hγζ : γ ≤ ζ := by linarith
    have hzγ := ball_inv_subset_of_le q hγ hγζ hz
    have hc := htest x hx z hzγ hxz w hw hwz
    have hd := unit_derivative_difference_bound g hEnorm (hgrad x hx) w hw
    exact derivative_clause_of_perturbation hζ hc hd

end DifferentialGeometry.Geometry.Collapse
