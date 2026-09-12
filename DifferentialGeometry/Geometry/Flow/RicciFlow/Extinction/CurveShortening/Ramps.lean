import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Continuation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section RampSupport
namespace ProductCurve

def ricciTangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (G : SolutionFamily (I := I) (M := M))
    (lambda x t : ℝ) : ℝ :=
  G.ricciAt t (c.projection.lift x t)
    (vec2 (c.unitTangent G.metric lambda x t).1 (c.unitTangent G.metric lambda x t).1)

def initialMinAngle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda a : ℝ) : ℝ :=
  sInf ((fun x => c.angle g lambda x a) '' Icc (0 : ℝ) 1)

def initialMaxCurvature {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda a : ℝ) : ℝ :=
  sSup ((fun x => c.curvature g lambda x a) '' Icc (0 : ℝ) 1)

def curvatureEnvelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c₀ : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda B₀ C a b t : ℝ) : ℝ :=
  Real.exp ((C + B₀) * (t - a)) *
    ((c₀.initialMaxCurvature g lambda a + 1) / c₀.initialMinAngle g lambda a +
      C * (t - a) / (c₀.initialMinAngle g lambda a * Real.exp (-B₀ * (b - a))))

end ProductCurve

namespace ProductCurve

private theorem inner_X_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by
  rw [inner]
  simp only [X]
  ring

private theorem inner_X_self_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    0 ≤ c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
  rw [inner_X_self]
  have h1 : 0 ≤ (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := by
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · simp only [h, map_zero]; rfl
    · exact ((g t).pos (c.projection.lift x t) _ h).le
  nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

private theorem speed_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.speed g lambda x t ^ 2 =
      c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
  Real.sq_sqrt (inner_X_self_nonneg c g lambda x t)

private theorem angle_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.angle g lambda x t = lambda * (c.speed g lambda x t)⁻¹ * deriv (fun z => c.y z t) x := by
  rw [angle, inner, unitTangent, verticalUnit]
  simp only [X, Prod.smul_fst, Prod.smul_snd, map_zero, smul_eq_mul]
  rcases eq_or_ne lambda 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

end ProductCurve

private theorem slice_slice_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.y p.1 p.2) (univ ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun z : ℝ => c.y z t) univ := by
  have hz : ContDiffOn ℝ ∞ (fun z : ℝ => (z, t)) univ := by fun_prop
  have h := hc.comp hz (fun z _ => ⟨mem_univ z, ht⟩)
  simpa [Function.comp_def] using h

private theorem ramp_angle_sq_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    c.angle g lambda x t ^ 2 ≤ 1 := by
  rcases eq_or_ne (c.speed g lambda x t) 0 with h0 | h0
  · have hang : c.angle g lambda x t = 0 := by
      rw [ProductCurve.angle_eq c g lambda x t, h0]
      simp
    rw [hang]
    norm_num
  · have hang : c.angle g lambda x t * c.speed g lambda x t =
        lambda * deriv (fun z => c.y z t) x := by
      rw [ProductCurve.angle_eq c g lambda x t]
      field_simp
    have hsp2 : c.speed g lambda x t ^ 2 =
        c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
      ProductCurve.speed_sq c g lambda x t
    have hinner : c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
        (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
            (c.projection.X (I := I) x t) +
          lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 :=
      ProductCurve.inner_X_self c g lambda x t
    have hsq : (c.angle g lambda x t * c.speed g lambda x t) ^ 2 ≤
        c.speed g lambda x t ^ 2 := by
      rw [hang, mul_pow, hsp2, hinner]
      nlinarith [DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t)
        (c.projection.X (I := I) x t)]
    have hpos : 0 < c.speed g lambda x t ^ 2 := by positivity
    have heq : c.angle g lambda x t ^ 2 =
        (c.angle g lambda x t * c.speed g lambda x t) ^ 2 / c.speed g lambda x t ^ 2 := by
      field_simp
    rw [heq]
    exact (div_le_one hpos).mpr hsq

private theorem ramp_speed_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.ImmersedOn (I := I) J)
    {x t : ℝ} (ht : t ∈ J) : 0 < c.speed g lambda x t := by
  have hX : c.X (I := I) x t ≠ 0 := hc x t ht
  rw [ProductCurve.speed, Real.sqrt_pos, ProductCurve.inner_X_self]
  rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
  · have hdy : deriv (fun z => c.y z t) x ≠ 0 := by
      intro hd
      exact hX (by simp [ProductCurve.X, h, hd])
    have hprod : 0 < lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 :=
      mul_pos (pow_pos hlambda 2) (sq_pos_of_ne_zero hdy)
    have hzero : (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) = 0 := by simp [h]
    rw [hzero, zero_add]
    exact hprod
  · have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) := (g t).pos _ _ h
    nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

private theorem ramp_deriv_y_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    {x t : ℝ} (ht : t ∈ J) (hangle : 0 < c.angle g lambda x t) :
    0 < deriv (fun z => c.y z t) x := by
  have hsp : 0 < c.speed g lambda x t :=
    ramp_speed_pos c g lambda hlambda hc.immersed ht
  have key : deriv (fun z => c.y z t) x =
      c.angle g lambda x t * c.speed g lambda x t / lambda := by
    rw [ProductCurve.angle_eq c g lambda x t]
    field_simp
  rw [key]
  exact div_pos (mul_pos hangle hsp) hlambda

private theorem ramp_degree_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {s v t : ℝ} (ht : t ∈ Icc s v)
    (hc : c.IsSolutionOn g lambda (Icc s v))
    (hangle : ∀ x t, t ∈ Icc s v → 0 < c.angle g lambda x t) :
    0 < c.degree := by
  have hmono : StrictMono (fun z => c.y z t) :=
    strictMono_of_deriv_pos (fun x => ramp_deriv_y_pos c g lambda hlambda hc ht (hangle x t ht))
  have hlt : c.y 0 t < c.y 1 t := hmono (by norm_num)
  have hincr : c.y 1 t = c.y 0 t + (c.degree : ℝ) := by
    simpa using c.increment 0 t
  have hreal : 0 < (c.degree : ℝ) := by linarith
  exact_mod_cast hreal

private theorem ramp_angle_mul_speed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (x t : ℝ) :
    c.angle g lambda x t * c.speed g lambda x t = lambda * deriv (fun z => c.y z t) x := by
  rcases eq_or_ne (c.speed g lambda x t) 0 with h0 | h0
  · have h1 := ProductCurve.speed_sq c g lambda x t
    have h2 := ProductCurve.inner_X_self c g lambda x t
    rw [h0] at h1
    rw [← h1] at h2
    have hsum : (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) + lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 = 0 := by
      simpa using h2.symm
    have hmul : lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 = 0 := by
      nlinarith [DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t)
        (c.projection.X (I := I) x t), sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]
    have hsq : (deriv (fun z => c.y z t) x) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h (pow_ne_zero 2 (ne_of_gt hlambda))
      · exact h
    have hdy : deriv (fun z => c.y z t) x = 0 := sq_eq_zero_iff.mp hsq
    have hang : c.angle g lambda x t = 0 := by
      rw [ProductCurve.angle_eq c g lambda x t, h0, hdy]
      simp
    rw [hang, h0, hdy]
    ring
  · rw [ProductCurve.angle_eq c g lambda x t]
    field_simp

theorem productCurve_integral_angle_of_smoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hsmooth : c.SmoothOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) :
    c.integral g lambda (c.angle g lambda) t = c.degree * lambda := by
  have hslice := slice_slice_contDiffOn (H := H) (I := I) c ht hsmooth.2
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (fun z : ℝ => c.y z t) x := fun x =>
    (hslice.differentiableOn (by norm_num)).differentiableAt Filter.univ_mem
  have hderiv : ∀ x : ℝ, HasDerivAt (fun z : ℝ => c.y z t)
      (deriv (fun z : ℝ => c.y z t) x) x := fun x => (hdiff x).hasDerivAt
  have hcont : Continuous (deriv (fun z : ℝ => c.y z t)) :=
    (contDiffOn_univ.mp hslice).continuous_deriv (by norm_num)
  have hint : IntervalIntegrable (deriv (fun z : ℝ => c.y z t)) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  calc c.integral g lambda (c.angle g lambda) t
      = ∫ x in (0 : ℝ)..1, lambda * deriv (fun z => c.y z t) x := by
        rw [ProductCurve.integral]
        exact intervalIntegral.integral_congr
          (fun x _ => ramp_angle_mul_speed c g lambda hlambda x t)
    _ = lambda * ∫ x in (0 : ℝ)..1, deriv (fun z => c.y z t) x :=
        intervalIntegral.integral_const_mul lambda _
    _ = lambda * (c.y 1 t - c.y 0 t) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
    _ = c.degree * lambda := by
        have hincr : c.y 1 t = c.y 0 t + (c.degree : ℝ) := by simpa using c.increment 0 t
        rw [hincr]
        ring

theorem productCurve_integral_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    {t : ℝ} (ht : t ∈ J) :
    c.integral g lambda (c.angle g lambda) t = c.degree * lambda :=
  productCurve_integral_angle_of_smoothOn c g lambda hlambda hc.smooth ht

private theorem ramp_slice_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) {t : ℝ} (ht : t ∈ J) :
    Continuous (fun z : Surgery.Topology.Circle => c.map z t) := by
  let f : ℝ → M × Surgery.Topology.Circle := fun x => c.map (x : Surgery.Topology.Circle) t
  have hfperiod : f 0 = f (0 + 1) := by
    simp only [f, zero_add, AddCircle.coe_zero, AddCircle.coe_period]
  have hproj : ContinuousOn (fun x : ℝ => c.projection.lift x t) (Icc (0:ℝ) (0 + 1)) :=
    (CurveMap.space_slice_contMDiffOn (I := I) c.projection J hc.smooth.1 t ht).continuousOn.mono
      (fun x _ => mem_univ x)
  have hy : ContinuousOn (fun x : ℝ => c.y x t) (Icc (0:ℝ) (0 + 1)) := by
    have h := (slice_slice_contDiffOn (H := H) (I := I) c ht hc.smooth.2).continuousOn
    exact h.mono (fun x _ => mem_univ x)
  have hyc : ContinuousOn (fun x : ℝ => (c.y x t : Surgery.Topology.Circle))
      (Icc (0:ℝ) (0 + 1)) :=
    (AddCircle.continuous_mk' (1:ℝ)).comp_continuousOn hy
  have hf : ContinuousOn f (Icc (0:ℝ) (0 + 1)) := by
    have h := hproj.prodMk hyc
    refine h.congr ?_
    intro x _
    exact Prod.ext rfl (c.lift_eq x t).symm
  have hlift := AddCircle.liftIco_continuous (p := (1:ℝ)) (a := (0:ℝ)) hfperiod hf
  refine hlift.congr ?_
  intro z
  have hz : z = ((AddCircle.equivIco (1:ℝ) 0 z).val : Surgery.Topology.Circle) :=
    (AddCircle.coe_equivIco (p := (1:ℝ)) (a := (0:ℝ)) (y := z)).symm
  rw [hz, AddCircle.liftIco_coe_apply (AddCircle.equivIco (1:ℝ) 0 z).coe_prop]

private theorem ramp_slice_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    (hangle : ∀ x t, t ∈ J → 0 < c.angle g lambda x t) (hdegree : c.degree = 1)
    {t : ℝ} (ht : t ∈ J) :
    Function.Injective (fun z : Surgery.Topology.Circle => c.map z t) := by
  have hmono : StrictMono (fun x : ℝ => c.y x t) :=
    strictMono_of_deriv_pos (fun x => ramp_deriv_y_pos c g lambda hlambda hc ht (hangle x t ht))
  intro z₁ z₂ hz
  obtain ⟨x₁, hx₁I, hx₁⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z₁
  obtain ⟨x₂, hx₂I, hx₂⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z₂
  have hsecond : (c.y x₁ t : Surgery.Topology.Circle) = (c.y x₂ t : Surgery.Topology.Circle) := by
    rw [c.lift_eq x₁ t, c.lift_eq x₂ t, hx₁, hx₂]
    exact congrArg Prod.snd hz
  have hsub : ((c.y x₁ t - c.y x₂ t : ℝ) : Surgery.Topology.Circle) = 0 := by
    rw [AddCircle.coe_sub, hsecond, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at hsub
  obtain ⟨n, hn⟩ := hsub
  simp only [zsmul_eq_mul, mul_one] at hn
  rcases lt_trichotomy x₁ x₂ with hlt | heq | hgt
  · have hy : c.y x₁ t < c.y x₂ t := hmono hlt
    have hx : x₂ < x₁ + 1 := by linarith [hx₁I.1, hx₂I.2]
    have hy2 : c.y x₂ t < c.y x₁ t + 1 := by
      have h := hmono hx
      change c.y x₂ t < c.y (x₁ + 1) t at h
      rw [c.increment x₁ t, hdegree] at h
      norm_num at h
      exact h
    have h1 : (n : ℝ) < 0 := by linarith
    have h2 : (-1 : ℝ) < (n : ℝ) := by linarith
    have h1' : n < 0 := by exact_mod_cast h1
    have h2' : (-1 : ℤ) < n := by exact_mod_cast h2
    omega
  · rw [← hx₁, ← hx₂, heq]
  · have hy : c.y x₂ t < c.y x₁ t := hmono hgt
    have hx : x₁ < x₂ + 1 := by linarith [hx₂I.1, hx₁I.2]
    have hy2 : c.y x₁ t < c.y x₂ t + 1 := by
      have h := hmono hx
      change c.y x₁ t < c.y (x₂ + 1) t at h
      rw [c.increment x₂ t, hdegree] at h
      norm_num at h
      exact h
    have h1 : (0 : ℝ) < (n : ℝ) := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    omega

private theorem ramp_slice_isEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    (hangle : ∀ x t, t ∈ J → 0 < c.angle g lambda x t) (hdegree : c.degree = 1)
    {t : ℝ} (ht : t ∈ J) :
    Topology.IsEmbedding (fun z : Surgery.Topology.Circle => c.map z t) :=
  (Continuous.isClosedEmbedding (ramp_slice_continuous c g lambda hc ht)
    (ramp_slice_injective c g lambda hlambda hc hangle hdegree ht)).isEmbedding


def productEmbeddedCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c : ProductCurve M) (x t : ℝ) : EuclideanSpace ℝ (Fin N) × ℂ :=
  (e.map (c.projection.lift x t),
    ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))
      (c.map (x : Surgery.Topology.Circle) t).2 : ℂ))

private theorem productEmbeddedCoordinates_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) {J : Set ℝ}
    {d d' : ProductCurve M} (h : ∀ z t, t ∈ J → d.map z t = d'.map z t) :
    ∀ x t, t ∈ J →
      productEmbeddedCoordinates e d x t = productEmbeddedCoordinates e d' x t := by
  intro x t ht
  have hm := h (x : Surgery.Topology.Circle) t ht
  simp only [productEmbeddedCoordinates, ProductCurve.projection, CurveMap.lift]
  rw [hm]

@[instance_reducible]
def smoothProductInitialTopology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) (a : ℝ) :
    TopologicalSpace (ProductCurve M) :=
  TopologicalSpace.generateFrom {U | ∃ c : ProductCurve M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y => productEmbeddedCoordinates e d y a) x -
        iteratedDeriv m (fun y => productEmbeddedCoordinates e c y a) x‖ ≤ ρ}}

@[instance_reducible]
def smoothProductCylinderTopology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) (J : Set ℝ) :
    TopologicalSpace (ProductCurve M) :=
  TopologicalSpace.generateFrom {U | ∃ c : ProductCurve M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
          (univ ×ˢ J) p -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
          (univ ×ˢ J) p‖ ≤ ρ}}

private theorem productCylinder_generateFrom_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) {J : Set ℝ}
    {d d' : ProductCurve M} (h : ∀ z t, t ∈ J → d.map z t = d'.map z t) :
    ∀ s ∈ {U | ∃ c : ProductCurve M, ∃ m : ℕ, ∃ ε : ℝ,
      0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
            (univ ×ˢ J) p -
          iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
            (univ ×ˢ J) p‖ ≤ ρ}},
    d ∈ s ↔ d' ∈ s := by
  rintro s ⟨c, m, ε, hε, rfl⟩
  have hjet : ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ J),
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
          (univ ×ˢ J) p =
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d' q.1 q.2)
          (univ ×ˢ J) p := fun p hp =>
    iteratedFDerivWithin_congr
      (s := (univ : Set ℝ) ×ˢ J)
      (fun q hq => productEmbeddedCoordinates_congr e h q.1 q.2 hq.2)
      ⟨mem_univ p.1, hp.2⟩ m
  constructor <;> rintro ⟨ρ, hρ, hb⟩ <;> refine ⟨ρ, hρ, fun p hp => ?_⟩
  · rw [← hjet p hp]; exact hb p hp
  · rw [hjet p hp]; exact hb p hp

private theorem productCylinder_continuousAt_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) {J : Set ℝ}
    {P : Type*} [TopologicalSpace P] {f g : P → ProductCurve M} {p : P}
    (h : ∀ᶠ q in 𝓝 p, ∀ z t, t ∈ J → (f q).map z t = (g q).map z t)
    (hg : @ContinuousAt P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e J) g p) :
    @ContinuousAt P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e J) f p := by
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hg ⊢
  rintro s ⟨c, m, ε, hε, rfl⟩ hfs
  have hp_eq : ∀ z t, t ∈ J → (f p).map z t = (g p).map z t :=
    fun z t ht => h.self_of_nhds z t ht
  have hgs : g p ∈ {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
          (univ ×ˢ J) p -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
          (univ ×ˢ J) p‖ ≤ ρ} :=
    ((productCylinder_generateFrom_congr e hp_eq) _ ⟨c, m, ε, hε, rfl⟩).mp hfs
  filter_upwards [hg _ ⟨c, m, ε, hε, rfl⟩ hgs, h] with q hq hqeq
  exact ((productCylinder_generateFrom_congr e hqeq) _ ⟨c, m, ε, hε, rfl⟩).mpr hq



private theorem continuousAt_comp_same_type {α X : Type*} (tα : TopologicalSpace α)
    (tX tY : TopologicalSpace X) {f : α → X} {g : X → X} {x : α}
    (hg : @ContinuousAt X X tX tY g (f x)) (hf : @ContinuousAt α X tα tX f x) :
    @ContinuousAt α X tα tY (fun a => g (f a)) x := by
  have h1 : @Filter.Tendsto X X g (@nhds X tX (f x)) (@nhds X tY (g (f x))) := hg
  have h2 : @Filter.Tendsto α X f (@nhds α tα x) (@nhds X tX (f x)) := hf
  exact @Filter.Tendsto.comp α X X f g (@nhds α tα x) (@nhds X tX (f x))
    (@nhds X tY (g (f x))) h1 h2

end RampSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [hBoundary : I.Boundaryless]



variable {D : RealTimeInterval} {a b s v : ℝ}


structure RampAngleInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda s v : ℝ) where
  pde : ∀ (c : ProductCurve M) (u₀ : ℝ), 0 < u₀ →
    c.IsSolutionOn B.family.metric lambda (Icc s v) →
    (∀ x, u₀ ≤ c.angle B.family.metric lambda x s) →
    ∀ x t, t ∈ Icc s v →
      derivWithin (c.angle B.family.metric lambda x) (Icc s v) t =
        c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
          (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
            c.angle B.family.metric lambda x t
  comparison : ∀ (c : ProductCurve M) (u₀ : ℝ), 0 < u₀ →
    c.IsSolutionOn B.family.metric lambda (Icc s v) →
    (∀ x, u₀ ≤ c.angle B.family.metric lambda x s) →
    ∀ x t, t ∈ Icc s v →
      u₀ * Real.exp (-B.B₀ * (t - s)) ≤ c.angle B.family.metric lambda x t

structure RampCurvatureInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (J : Set ℝ) where
  slice_continuous_at_start : ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
    c.IsRampOn B.family.metric lambda {a} →
      Continuous (fun x : ℝ => c.angle B.family.metric lambda x a)
  curvature_envelope : ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
    c.IsRampOn B.family.metric lambda {a} →
      ∀ x t, t ∈ J → c.curvature B.family.metric lambda x t ≤
        c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

structure RampExistenceInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) where
  exists_solution : ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      (∀ x t, t ∈ Icc a b → c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t)
  unique : ∀ (c₀ c d : ProductCurve M),
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    d.IsSolutionOn B.family.metric lambda (Icc a b) →
    (∀ z, c.map z a = c₀.map z a) → (∀ z, d.map z a = c₀.map z a) →
    ∀ z t, t ∈ Icc a b → d.map z t = c.map z t

structure RampFamilyInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ} {N : ℕ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) where
  local_dependence : ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ sol : ProductCurve M → ProductCurve M,
      @ContinuousAt (ProductCurve M) (ProductCurve M)
        (smoothProductInitialTopology e a) (smoothProductCylinderTopology e (Icc a b)) sol c₀ ∧
      ∀ c : ProductCurve M, (sol c).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (sol c).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (sol c).map z a = c.map z a

private theorem ramp_initialMinAngle_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda a : ℝ)
    (hcont : Continuous fun x : ℝ => c.angle g lambda x a)
    (hramp : c.IsRampOn g lambda {a}) :
    0 < c.initialMinAngle g lambda a := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨(0 : ℝ), by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) hcont.continuousOn
  have hle : c.angle g lambda x₀ a ≤
      sInf ((fun x => c.angle g lambda x a) '' Icc (0 : ℝ) 1) :=
    le_csInf ⟨_, x₀, hx₀, rfl⟩ (by rintro y ⟨x, hx, rfl⟩; exact hmin hx)
  exact lt_of_lt_of_le (hramp.2 x₀ a (mem_singleton a)) hle

include hT2 hCompact hNonempty hBoundary

theorem rfs_csf_ramp_angle (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (u₀ : ℝ) (hu₀ : 0 < u₀) (hinit : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s)
    (K : RampAngleInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda s v) :
    (∀ x t, t ∈ Icc s v →
      derivWithin (c.angle B.family.metric lambda x) (Icc s v) t =
        c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
          (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
            c.angle B.family.metric lambda x t) ∧
    (∀ x t, t ∈ Icc s v →
      u₀ * Real.exp (-B.B₀ * (t - s)) ≤ c.angle B.family.metric lambda x t ∧
        c.angle B.family.metric lambda x t ≤ 1) ∧
    (∀ t ∈ Icc s v,
      c.integral B.family.metric lambda (c.angle B.family.metric lambda) t = c.degree * lambda) ∧
    0 < c.degree ∧
    (c.degree = 1 → ∀ t ∈ Icc s v, Topology.IsEmbedding (fun z => c.map z t)) := by
  let _ := hwindow
  have hpos : ∀ x t, t ∈ Icc s v → 0 < c.angle B.family.metric lambda x t := fun x t ht =>
    lt_of_lt_of_le (mul_pos hu₀ (Real.exp_pos _)) (K.comparison c u₀ hu₀ hc hinit x t ht)
  refine ⟨K.pde c u₀ hu₀ hc hinit, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    exact ⟨K.comparison c u₀ hu₀ hc hinit x t ht,
      (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp
        (ramp_angle_sq_le_one c B.family.metric lambda x t))).2⟩
  · intro t ht
    exact productCurve_integral_angle c B.family.metric lambda hlambda hc ht
  · exact ramp_degree_pos c B.family.metric lambda hlambda ⟨le_rfl, hsv.le⟩ hc hpos
  · intro hdeg t ht
    exact ramp_slice_isEmbedding c B.family.metric lambda hlambda hc hpos hdeg ht

theorem ramp_curvature_bound (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (T : ℝ) (haT : a < T) (hTb : T ≤ b) (J : Set ℝ)
    (hJ : J = Ico a T ∨ J = Icc a T) (c : ProductCurve M)
    (hc : c.IsSolutionOn B.family.metric lambda J)
    (hramp : c.IsRampOn B.family.metric lambda {a})
    (K : RampCurvatureInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda J) :
    0 < c.initialMinAngle B.family.metric lambda a ∧
      ∀ x t, t ∈ J → c.curvature B.family.metric lambda x t ≤
        c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t := by
  let _ := hlambda
  let _ := hlambda_one
  let _ := haT
  let _ := hTb
  let _ := hJ
  exact ⟨ramp_initialMinAngle_pos c B.family.metric lambda a
      (K.slice_continuous_at_start c hc hramp) hramp,
    K.curvature_envelope c hc hramp⟩

theorem rfs_csf_ramp_existence (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (c₀ : ProductCurve M) (hsmooth : c₀.SmoothOn (I := I) {a})
    (hramp : c₀.IsRampOn B.family.metric lambda {a})
    (K : RampExistenceInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      (∀ x t, t ∈ Icc a b → c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t) ∧
      (∀ d : ProductCurve M, d.IsSolutionOn B.family.metric lambda (Icc a b) →
        (∀ z, d.map z a = c₀.map z a) →
        ∀ z t, t ∈ Icc a b → d.map z t = c.map z t) := by
  let _ := hlambda
  let _ := hlambda_one
  obtain ⟨c, hsol, hramp', hinit, hcurv⟩ := K.exists_solution c₀ hsmooth hramp
  exact ⟨c, hsol, hramp', hinit, hcurv,
    fun d hd hd0 z t ht => K.unique c₀ c d hsol hd hinit hd0 z t ht⟩

theorem rfs_csf_ramp_family (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P] (initial : P → ProductCurve M)
    (hcontinuous : @Continuous P (ProductCurve M) inferInstance
      (smoothProductInitialTopology e a) initial)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a})
    (K : RampExistenceInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda)
    (L : RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N) B lambda e) :
    ∃ solutions : P → ProductCurve M,
      (@Continuous P (ProductCurve M) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions) ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a := by
  classical
  let _ := hlambda
  let _ := hlambda_one
  have hdata : ∀ p : P, ∃ sol : ProductCurve M → ProductCurve M,
      @ContinuousAt (ProductCurve M) (ProductCurve M)
        (smoothProductInitialTopology e a) (smoothProductCylinderTopology e (Icc a b)) sol
        (initial p) ∧
      ∀ c : ProductCurve M, (sol c).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (sol c).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (sol c).map z a = c.map z a :=
    fun p => L.local_dependence (initial p) (hsmooth p) (hramp p)
  let S : P → ProductCurve M → ProductCurve M := fun p => Classical.choose (hdata p)
  have hS : ∀ p : P, @ContinuousAt (ProductCurve M) (ProductCurve M)
        (smoothProductInitialTopology e a) (smoothProductCylinderTopology e (Icc a b)) (S p)
        (initial p) ∧
      ∀ c : ProductCurve M, ((S p) c).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        ((S p) c).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, ((S p) c).map z a = c.map z a :=
    fun p => Classical.choose_spec (hdata p)
  let solutions : P → ProductCurve M := fun p => S p (initial p)
  refine ⟨solutions, ?_, ?_⟩
  · refine (@continuous_iff_continuousAt P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) (f := solutions)).mpr ?_
    intro p₀
    have hcand : @ContinuousAt P (ProductCurve M) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) (fun p => S p₀ (initial p)) p₀ :=
      continuousAt_comp_same_type (inferInstance : TopologicalSpace P)
        (smoothProductInitialTopology e a) (smoothProductCylinderTopology e (Icc a b))
        (hS p₀).1
        (@Continuous.continuousAt P (ProductCurve M) inferInstance
          (smoothProductInitialTopology e a) initial p₀ hcontinuous)
    refine productCylinder_continuousAt_congr e ?_ hcand
    filter_upwards with p
    intro z t ht
    exact (K.unique (initial p) (S p (initial p)) (S p₀ (initial p))
      ((hS p).2 (initial p)).1 ((hS p₀).2 (initial p)).1
      ((hS p).2 (initial p)).2.2 ((hS p₀).2 (initial p)).2.2 z t ht).symm
  · intro p
    exact ⟨((hS p).2 (initial p)).1, ((hS p).2 (initial p)).2.1,
      ((hS p).2 (initial p)).2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
