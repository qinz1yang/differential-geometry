import DifferentialGeometry.Analysis.Parabolic.Energy.Supersolution
import DifferentialGeometry.Analysis.Parabolic.Moser.Sobolev
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

def rpowSource (q : ℝ) (u source : ℝ → M → ℝ) : ℝ → M → ℝ :=
  fun t x => q * u t x ^ (q - 1) * source t x

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_rpow_of_pos
    {u : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) (q : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2 ^ q) := by
  intro p
  simpa only [Function.comp_apply] using
    (Real.contDiffAt_rpow_const_of_ne (p := q) (hpos p.1 p.2).ne').comp_contMDiffAt
      (x := p) (hu p)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_rpowSource_of_pos
    {u source : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) (q : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rpowSource q u source p.1 p.2) := by
  exact (contMDiff_const.mul (contMDiff_rpow_of_pos hu hpos (q - 1))).mul hsource

theorem rpow_subsolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} {x : M}
    (hpde :
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x) :
    deriv (fun s => u s x ^ q) t ≤
      Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun t x => u t x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t).toContMDiffMap x +
        rpowSource q u source t x := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let huq := contMDiff_rpow_of_pos hu hpos q
  let uqt := smoothScalarSlice (I := I) g (fun s y => u s y ^ q) huq t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => u s x ^ q) t =
        q * u t x ^ (q - 1) * deriv (fun s => u s x) t := by
    have h := ((htime.differentiable (by norm_num) t).hasDerivAt.rpow_const (p := q)
      (Or.inl (hpos t x).ne')).deriv
    rw [h]
    ring
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x
  have hlap_raw := laplacian_rpow (I := I)
    (LeviCivita (I := I) g) g q
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g uqt.toContMDiffMap x =
        (q * u t x ^ (q - 1)) * Δ_g (I := I) g ut.toContMDiffMap x +
          (q * (q - 1) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    unfold SmoothScalar.toContMDiffMap
    rw [← laplacian_levi_eq (I := I) g uqt.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, uqt, smoothScalarSlice_toFun] using hlap_raw
  have hcoeff : 0 ≤ q * u t x ^ (q - 1) :=
    mul_nonneg (zero_le_one.trans hq) (Real.rpow_nonneg (hpos t x).le _)
  have hgradient :
      0 ≤ (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (zero_le_one.trans hq) (sub_nonneg.mpr hq))
        (Real.rpow_nonneg (hpos t x).le _))
      (metric_inner_self_nonneg (I := I) (M := M) g x _)
  rw [htime_deriv, hlap]
  change q * u t x ^ (q - 1) * deriv (fun s => u s x) t ≤
    q * u t x ^ (q - 1) * Δ_g (I := I) g ut.toContMDiffMap x +
      (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) +
      q * u t x ^ (q - 1) * source t x
  have hmul := mul_le_mul_of_nonneg_left hpde hcoeff
  nlinarith

theorem rpow_subsolution_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : q ≤ 0)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x ≤
        deriv (fun s => u s x) t) :
    deriv (fun s => u s x ^ q) t ≤
      Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun t x => u t x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t).toContMDiffMap x +
        rpowSource q u source t x := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let huq := contMDiff_rpow_of_pos hu hpos q
  let uqt := smoothScalarSlice (I := I) g (fun s y => u s y ^ q) huq t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => u s x ^ q) t =
        q * u t x ^ (q - 1) * deriv (fun s => u s x) t := by
    have h := ((htime.differentiable (by norm_num) t).hasDerivAt.rpow_const (p := q)
      (Or.inl (hpos t x).ne')).deriv
    rw [h]
    ring
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x
  have hlap_raw := laplacian_rpow (I := I)
    (LeviCivita (I := I) g) g q
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g uqt.toContMDiffMap x =
        (q * u t x ^ (q - 1)) * Δ_g (I := I) g ut.toContMDiffMap x +
          (q * (q - 1) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    unfold SmoothScalar.toContMDiffMap
    rw [← laplacian_levi_eq (I := I) g uqt.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, uqt, smoothScalarSlice_toFun] using hlap_raw
  have hcoeff : q * u t x ^ (q - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hq (Real.rpow_nonneg (hpos t x).le _)
  have hqq : 0 ≤ q * (q - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hq (by linarith)
  have hgradient :
      0 ≤ (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) := by
    exact mul_nonneg
      (mul_nonneg hqq (Real.rpow_nonneg (hpos t x).le _))
      (metric_inner_self_nonneg (I := I) (M := M) g x _)
  rw [htime_deriv, hlap]
  change q * u t x ^ (q - 1) * deriv (fun s => u s x) t ≤
    q * u t x ^ (q - 1) * Δ_g (I := I) g ut.toContMDiffMap x +
      (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) +
      q * u t x ^ (q - 1) * source t x
  have hmul := mul_le_mul_of_nonpos_left hpde hcoeff
  nlinarith

theorem rpow_supersolution_with_gradient_term
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_nonneg : 0 ≤ q)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x ≤
        deriv (fun s => u s x) t) :
    Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun t x => u t x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t).toContMDiffMap x +
        rpowSource q u source t x +
        (q * (1 - q) * u t x ^ (q - 2)) *
          g.inner x
            (gradientFun (I := I) g
              (smoothScalarSlice (I := I) g u hu t).toFun x)
            (gradientFun (I := I) g
              (smoothScalarSlice (I := I) g u hu t).toFun x) ≤
      deriv (fun s => u s x ^ q) t := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let huq := contMDiff_rpow_of_pos hu hpos q
  let uqt := smoothScalarSlice (I := I) g (fun s y => u s y ^ q) huq t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => u s x ^ q) t =
        q * u t x ^ (q - 1) * deriv (fun s => u s x) t := by
    have h := ((htime.differentiable (by norm_num) t).hasDerivAt.rpow_const (p := q)
      (Or.inl (hpos t x).ne')).deriv
    rw [h]
    ring
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x
  have hlap_raw := laplacian_rpow (I := I)
    (LeviCivita (I := I) g) g q
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g uqt.toContMDiffMap x =
        (q * u t x ^ (q - 1)) * Δ_g (I := I) g ut.toContMDiffMap x +
          (q * (q - 1) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    unfold SmoothScalar.toContMDiffMap
    rw [← laplacian_levi_eq (I := I) g uqt.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, uqt, smoothScalarSlice_toFun] using hlap_raw
  have hcoeff : 0 ≤ q * u t x ^ (q - 1) :=
    mul_nonneg hq_nonneg (Real.rpow_nonneg (hpos t x).le _)
  have hmul := mul_le_mul_of_nonneg_left hpde hcoeff
  rw [htime_deriv, hlap]
  change
    q * u t x ^ (q - 1) * Δ_g (I := I) g ut.toContMDiffMap x +
          (q * (q - 1) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) +
        q * u t x ^ (q - 1) * source t x +
        (q * (1 - q) * u t x ^ (q - 2)) *
          g.inner x
            (gradientFun (I := I) g ut.toFun x)
            (gradientFun (I := I) g ut.toFun x) ≤
      q * u t x ^ (q - 1) * deriv (fun s => u s x) t
  have hcancel :
      q * (q - 1) * u t x ^ (q - 2) +
          q * (1 - q) * u t x ^ (q - 2) = 0 := by
    ring
  nlinarith

theorem rpow_supersolution_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_one : q ≤ 1)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x ≤
        deriv (fun s => u s x) t) :
    Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun t x => u t x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t).toContMDiffMap x +
        rpowSource q u source t x ≤
      deriv (fun s => u s x ^ q) t := by
  have hmain := rpow_supersolution_with_gradient_term
    (I := I) (M := M) g u source hu hpos hq_nonneg hpde
  have hgradient :
      0 ≤ (q * (1 - q) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g
            (smoothScalarSlice (I := I) g u hu t).toFun x)
          (gradientFun (I := I) g
            (smoothScalarSlice (I := I) g u hu t).toFun x) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hq_nonneg (sub_nonneg.mpr hq_one))
        (Real.rpow_nonneg (hpos t x).le _))
      (metric_inner_self_nonneg (I := I) (M := M) g x _)
  linarith

variable [SigmaCompactSpace M] [CompactSpace M]

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedL2Mass_rpow_half
    (g : SmoothRiemannianMetric I M) (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) (p t : ℝ) :
    localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ (p / 2))
          (contMDiff_rpow_of_pos hu hpos (p / 2)) t) =
      ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply integral_congr_ae
  filter_upwards with x
  change cutoff.toFun x ^ 2 * (u t x ^ (p / 2)) ^ 2 =
    cutoff.toFun x ^ 2 * u t x ^ p
  congr 1
  rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
    ← Real.rpow_mul (hpos t x).le]
  congr 1
  ring

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private theorem positive_rpow_cross_term_le
    (g : SmoothRiemannianMetric I M)
    (cutoff u : SmoothScalar g) {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (x : M) (hpos : 0 < u.toFun x) :
    2 * cutoff.toFun x *
        g.inner x
          (gradientFun (I := I) g cutoff.toFun x)
          (gradientFun (I := I) g (fun y => u.toFun y ^ q) x) ≤
      (1 / 2 : ℝ) * cutoff.toFun x ^ 2 *
          ((q * (1 - q) * u.toFun x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g u.toFun x)
              (gradientFun (I := I) g u.toFun x)) +
        (2 * q / (1 - q)) * u.toFun x ^ q *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g cutoff.toFun x) := by
  rw [gradientFun_rpow (I := I) g q (u.smooth.mdifferentiable (by simp) x) hpos]
  simp only [map_smul, smul_eq_mul]
  let a := cutoff.toFun x
  let z := u.toFun x
  let U := gradientFun (I := I) g u.toFun x
  let V := gradientFun (I := I) g cutoff.toFun x
  have hnonneg := metric_inner_self_nonneg (I := I) (M := M) g x
    (((1 - q) * a) • U - (2 * z) • V)
  have hfactor : 0 ≤ q / 2 * z ^ (q - 2) := by
    exact mul_nonneg (div_nonneg hq_pos.le (by norm_num))
      (Real.rpow_nonneg hpos.le _)
  have hscaled := mul_nonneg hfactor hnonneg
  have hz1 : z ^ (q - 2) * z = z ^ (q - 1) := by
    rw [← Real.rpow_add_one hpos.ne' (q - 2)]
    congr 1
    ring
  have hz2 : z ^ (q - 2) * z ^ 2 = z ^ q := by
    rw [← Real.rpow_two, ← Real.rpow_add hpos (q - 2) 2]
    congr 1
    ring
  have hz1q : q * z ^ (q - 2) * z = q * z ^ (q - 1) := by
    calc
      q * z ^ (q - 2) * z = q * (z ^ (q - 2) * z) := by ring
      _ = q * z ^ (q - 1) := by rw [hz1]
  have hz1q2 : q ^ 2 * z ^ (q - 2) * z = q ^ 2 * z ^ (q - 1) := by
    calc
      q ^ 2 * z ^ (q - 2) * z = q ^ 2 * (z ^ (q - 2) * z) := by ring
      _ = q ^ 2 * z ^ (q - 1) := by rw [hz1]
  have hz2q : q * z ^ (q - 2) * z ^ 2 = q * z ^ q := by
    calc
      q * z ^ (q - 2) * z ^ 2 = q * (z ^ (q - 2) * z ^ 2) := by ring
      _ = q * z ^ q := by rw [hz2]
  simp only [map_sub, ContinuousLinearMap.sub_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hscaled
  rw [g.symm x V U] at hscaled
  have hcore :
      (1 - q) * (2 * a * (q * z ^ (q - 1) * g.inner x U V)) ≤
        (1 - q) * ((1 / 2 : ℝ) * a ^ 2 *
          ((q * (1 - q) * z ^ (q - 2)) * g.inner x U U)) +
          2 * q * z ^ q * g.inner x V V := by
    ring_nf at hz1q hz1q2 hz2q hscaled ⊢
    rw [hz1q, hz1q2, hz2q] at hscaled
    nlinarith
  have hdenom : 0 < 1 - q := sub_pos.mpr hq_one
  have hdiv :
      2 * a * (q * z ^ (q - 1) * g.inner x U V) -
          (1 / 2 : ℝ) * a ^ 2 *
            ((q * (1 - q) * z ^ (q - 2)) * g.inner x U U) ≤
        (2 * q * z ^ q * g.inner x V V) / (1 - q) := by
    apply (le_div_iff₀ hdenom).2
    nlinarith
  rw [g.symm x V U]
  change 2 * a * (q * z ^ (q - 1) * g.inner x U V) ≤
    (1 / 2 : ℝ) * a ^ 2 *
        ((q * (1 - q) * z ^ (q - 2)) * g.inner x U U) +
      (2 * q / (1 - q)) * z ^ q * g.inner x V V
  have herr :
      (2 * q * z ^ q * g.inner x V V) / (1 - q) =
        (2 * q / (1 - q)) * z ^ q * g.inner x V V := by
    field_simp
  rw [← herr]
  linarith

theorem localized_energy_positive_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) *
        ∫ x, cutoff.toFun x ^ 2 *
          ((q * (1 - q) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g
                (smoothScalarSlice (I := I) g u hu t).toFun x)
              (gradientFun (I := I) g
                (smoothScalarSlice (I := I) g u hu t).toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s)) t +
        ∫ x, (2 * q / (1 - q)) * u t x ^ q *
            g.inner x
              (gradientFun (I := I) g cutoff.toFun x)
              (gradientFun (I := I) g cutoff.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let uq : ℝ → M → ℝ := fun s x => u s x ^ q
  let dissipation : ℝ → M → ℝ := fun s x =>
    (q * (1 - q) * u s x ^ (q - 2)) *
      g.inner x
        (gradientFun (I := I) g (u s) x)
        (gradientFun (I := I) g (u s) x)
  let error : ℝ → M → ℝ := fun s x =>
    (2 * q / (1 - q)) * u s x ^ q *
      g.inner x
        (gradientFun (I := I) g cutoff.toFun x)
        (gradientFun (I := I) g cutoff.toFun x)
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := fun _ => g
      connection := fun _ => LeviCivita (I := I) g
      metricCompatible := fun _ => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) }
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hspace := chartGramMatrix_entry_contMDiffOn (I := I) g x₀ i j
    simpa only [G] using hspace.comp contMDiffOn_snd (fun p hp => hp.2)
  have hgrad_joint : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        g.inner p.2
          (gradientFun (I := I) g (u p.1) p.2)
          (gradientFun (I := I) g (u p.1) p.2)) := by
    have h := gradSq_joint (I := I) G.metric isOpen_univ hgram u hu.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using h
  have hcutoff_grad : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      g.inner x
        (gradientFun (I := I) g cutoff.toFun x)
        (gradientFun (I := I) g cutoff.toFun x)) := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g cutoff.toContMDiffMap) (grad_g (I := I) g cutoff.toContMDiffMap)
    simpa only [grad_g_apply] using h
  have hdissipation : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => dissipation p.1 p.2) := by
    exact ((contMDiff_const.mul (contMDiff_rpow_of_pos hu hpos (q - 2))).mul
      hgrad_joint)
  have herror : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => error p.1 p.2) := by
    exact ((contMDiff_const.mul (contMDiff_rpow_of_pos hu hpos q)).mul
      (hcutoff_grad.comp contMDiff_snd))
  have hmain := localized_energy_differential_of_supersolution
    (I := I) (M := M) g cutoff uq dissipation error huq hdissipation herror t
    (fun x => by
      simpa only [uq, dissipation, rpowSource, smoothScalarSlice_toFun,
        mul_zero, zero_mul, add_zero] using
        rpow_supersolution_with_gradient_term
          (I := I) (M := M) g u (fun _ _ => 0) hu hpos hq_pos.le
            (t := t) (x := x) (by simpa only [add_zero] using hpde x))
    (fun x => by
      simpa only [uq, dissipation, error, smoothScalarSlice_toFun] using
        positive_rpow_cross_term_le (I := I) (M := M) g cutoff
          (smoothScalarSlice (I := I) g u hu t) hq_pos hq_one x (hpos t x))
  simpa only [uq, dissipation, error, huq, smoothScalarSlice_toFun] using hmain

theorem caccioppoli_positive_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (2 * (1 - q) / q) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) t) ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s)) t +
        (2 * q / (1 - q)) *
          cutoffGradientError (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
              (contMDiff_rpow_of_pos hu hpos (q / 2)) t) := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let wt := smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2)) huHalf t
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hraw := localized_energy_positive_rpow_of_supersolution
    (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one t hpde
  have hleft :
      (2 * (1 - q) / q) *
          localizedDirichletEnergy (I := I) (M := M) cutoff wt =
        (1 / 2 : ℝ) *
          ∫ x, cutoff.toFun x ^ 2 *
            ((q * (1 - q) * u t x ^ (q - 2)) *
              g.inner x
                (gradientFun (I := I) g (u t) x)
                (gradientFun (I := I) g (u t) x)) ∂μ := by
    rw [localizedDirichletEnergy, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [← gradient_eq_gradFun]
    have hgrad := gradientFun_rpow (I := I) g (q / 2)
      ((smoothScalarSlice (I := I) g u hu t).smooth.mdifferentiable (by simp) x)
      (hpos t x)
    have hgrad' :
        gradientFun (I := I) g wt.toFun x =
          (q / 2 * u t x ^ (q / 2 - 1)) •
            gradientFun (I := I) g (u t) x := by
      simpa only [wt, smoothScalarSlice_toFun] using hgrad
    have hrpow :
        u t x ^ (q / 2 - 1) * u t x ^ (q / 2 - 1) = u t x ^ (q - 2) := by
      rw [← Real.rpow_add (hpos t x) (q / 2 - 1) (q / 2 - 1)]
      congr 1
      ring
    rw [hgrad']
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    calc
      2 * (1 - q) / q *
            (cutoff.toFun x ^ 2 *
              (q / 2 * u t x ^ (q / 2 - 1) *
                (q / 2 * u t x ^ (q / 2 - 1) *
                  g.inner x
                    (gradientFun (I := I) g (u t) x)
                    (gradientFun (I := I) g (u t) x)))) =
          2 * (1 - q) / q * cutoff.toFun x ^ 2 *
            ((q / 2) ^ 2 *
              (u t x ^ (q / 2 - 1) * u t x ^ (q / 2 - 1)) *
              g.inner x
                (gradientFun (I := I) g (u t) x)
                (gradientFun (I := I) g (u t) x)) := by ring
      _ = (1 / 2 : ℝ) *
          (cutoff.toFun x ^ 2 *
            (q * (1 - q) * u t x ^ (q - 2) *
              g.inner x
                (gradientFun (I := I) g (u t) x)
                (gradientFun (I := I) g (u t) x))) := by
        rw [hrpow]
        field_simp [hq_pos.ne']
  have herror :
      ∫ x, (2 * q / (1 - q)) * u t x ^ q *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g cutoff.toFun x) ∂μ =
        (2 * q / (1 - q)) *
          cutoffGradientError (I := I) (M := M) cutoff wt := by
    rw [cutoffGradientError, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    have hrpow : (u t x ^ (q / 2)) ^ 2 = u t x ^ q := by
      rw [← Real.rpow_two, ← Real.rpow_mul (hpos t x).le]
      congr 1
      ring
    simp only [wt, smoothScalarSlice_toFun, hrpow, ← gradient_eq_gradFun]
    ring
  rw [hleft, ← herror]
  simpa only [μ, smoothScalarSlice_toFun] using hraw

theorem weighted_caccioppoli_positive_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) a) -
        weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) b) +
        ∫ t in a..b, weight t *
          ((2 * (1 - q) / q) *
            localizedDirichletEnergy (I := I) (M := M) cutoff
              (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
                (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) ≤
      ∫ t in a..b,
        (-dweight t) * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
              (contMDiff_rpow_of_pos hu hpos (q / 2)) t) +
          weight t *
            ((2 * q / (1 - q)) *
              cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
                  (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let dirichlet : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let c := 2 * (1 - q) / q
  let e := 2 * q / (1 - q)
  let negMass : ℝ → ℝ := fun t => -mass t
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using
      contDiff_localizedL2Mass (I := I) (M := M) cutoff w huHalf
  have hnegMass_smooth : ContDiff ℝ ∞ negMass := by
    exact hmass_smooth.neg
  have hdnegMass_cont : ContinuousOn (deriv negMass) (Icc a b) :=
    (hnegMass_smooth.continuous_deriv (by simp)).continuousOn
  have hnegMass_deriv : ∀ t ∈ Icc a b, HasDerivAt negMass (deriv negMass t) t := by
    intro t _
    exact (hnegMass_smooth.differentiable (by simp) t).hasDerivAt
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdirichlet_cont : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using
      (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff w huHalf)
        |>.continuous.continuousOn
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using
      (contDiff_cutoffGradientError (I := I) (M := M) cutoff w huHalf)
        |>.continuous.continuousOn
  have hdissipation : ContinuousOn (fun t => weight t * (c * dirichlet t))
      (Icc a b) :=
    hweight_cont.mul (continuousOn_const.mul hdirichlet_cont)
  have hrhs : ContinuousOn
      (fun t => dweight t * negMass t + weight t * (e * error t)) (Icc a b) :=
    (hdweight.mul hnegMass_smooth.continuous.continuousOn).add
      (hweight_cont.mul (continuousOn_const.mul herror_cont))
  have hmass_eq : mass = fun t =>
      localizedIntegral (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
          (contMDiff_rpow_of_pos hu hpos q) t) := by
    funext t
    simpa only [mass, w, huHalf, localizedIntegral] using
      localizedL2Mass_rpow_half (I := I) (M := M) g cutoff u hu hpos q t
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * negMass t + weight t * deriv negMass t +
          weight t * (c * dirichlet t) ≤
        dweight t * negMass t + weight t * (e * error t) := by
    intro t ht
    have hdiff := caccioppoli_positive_rpow_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one t (hpde t ht)
    have hderiv_eq := congrArg (fun f : ℝ → ℝ => deriv f t) hmass_eq
    change deriv mass t =
      deriv
        (fun s => localizedIntegral (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) s)) t at hderiv_eq
    change c * dirichlet t ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s)) t + e * error t at hdiff
    have hdiff' : c * dirichlet t ≤ deriv mass t + e * error t := by
      rw [hderiv_eq]
      exact hdiff
    have hneg_deriv : deriv negMass t = -deriv mass t := by
      have h := ((hmass_smooth.differentiable (by simp) t).hasDerivAt.neg).deriv
      simpa only [negMass] using h
    have hbase : deriv negMass t + c * dirichlet t ≤ e * error t := by
      rw [hneg_deriv]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbase (hweight_nonneg t ht)
    ring_nf at hmul ⊢
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdnegMass_cont hnegMass_deriv hdissipation hrhs hpointwise
  simp only [negMass, mass, dirichlet, error, c, e, w,
    mul_neg, sub_neg_eq_add] at hresult
  convert hresult using 1
  · ring
  · apply intervalIntegral.integral_congr
    intro t _
    ring

theorem backward_caccioppoli_inner_energy_positive_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    {weight dweight : ℝ → ℝ} {a t₁ b A : ℝ}
    (hat₁ : a ≤ t₁) (ht₁b : t₁ ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hweight_b : weight b = 0)
    (hweight_inner : ∀ t ∈ Icc a t₁, weight t = 1)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hrhs_le : ∀ t ∈ Icc a t₁,
      (∫ s in t..b,
        (-dweight s) * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ (q / 2))
              (contMDiff_rpow_of_pos hu hpos (q / 2)) s) +
          weight s *
            ((2 * q / (1 - q)) *
              cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun r x => u r x ^ (q / 2))
                  (contMDiff_rpow_of_pos hu hpos (q / 2)) s))) ≤ A) :
    (∀ t ∈ Icc a t₁,
      localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
          (contMDiff_rpow_of_pos hu hpos (q / 2)) t) ≤ A) ∧
      (∫ t in a..t₁,
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) ≤
        (q / (2 * (1 - q))) * A := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let dirichlet : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t)
  let c := 2 * (1 - q) / q
  let e := 2 * q / (1 - q)
  let dissipation : ℝ → ℝ := fun t => c * dirichlet t
  let source : ℝ → ℝ := fun t =>
    (-dweight t) * mass t + weight t *
      (e * cutoffGradientError (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf t))
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdirichlet_cont : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using
      (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff w huHalf)
        |>.continuous.continuousOn
  have hdissipation_cont : ContinuousOn dissipation (Icc a b) :=
    continuousOn_const.mul hdirichlet_cont
  have hc_pos : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hq_one)) hq_pos
  have hbase := backward_inner_mass_and_dissipation_le
    (weight := weight) (mass := mass) (dissipation := dissipation) (source := source)
    hat₁ ht₁b hweight_cont hdissipation_cont hweight_nonneg
    (fun t _ => mul_nonneg hc_pos.le
      (localizedDirichletEnergy_nonneg (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g w huHalf t)))
    hweight_b hweight_inner
    (fun t _ => localizedL2Mass_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g w huHalf t))
    (by simpa only [source, mass, e, w, huHalf] using hrhs_le)
    (fun t ht => by
      have htb : t ≤ b := ht.2.trans ht₁b
      have hsubset : Icc t b ⊆ Icc a b := fun s hs => ⟨ht.1.trans hs.1, hs.2⟩
      have henergy := weighted_caccioppoli_positive_rpow_of_supersolution
        (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one htb
        (hdweight.mono hsubset)
        (fun s hs => hweight s (hsubset hs))
        (fun s hs => hweight_nonneg s (hsubset hs))
        (fun s hs => hpde s (hsubset hs))
      simpa only [mass, dissipation, source, c, e, w, huHalf] using henergy)
  refine ⟨by simpa only [mass, w, huHalf] using hbase.1, ?_⟩
  have hscaled : c * (∫ t in a..t₁, dirichlet t) ≤ A := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [dissipation] using hbase.2
  let k := q / (2 * (1 - q))
  have hk_nonneg : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg hq_pos.le
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq_one.le))
  have hkc : k * c = 1 := by
    dsimp only [k, c]
    field_simp [hq_pos.ne', sub_ne_zero.mpr (ne_of_gt hq_one)]
  have hmul := mul_le_mul_of_nonneg_left hscaled hk_nonneg
  rw [← mul_assoc, hkc, one_mul] at hmul
  simpa only [dirichlet, k, w, huHalf] using hmul

theorem caccioppoli_rpow_of_subsolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x ^ q *
                  rpowSource q u source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let hsourceq := contMDiff_rpowSource_of_pos hu hsource hpos q
  apply caccioppoli_of_subsolution
    (I := I) (M := M) cutoff (fun t x => u t x ^ q)
      (rpowSource q u source) huq hsourceq hab hdweight hweight hweight_nonneg
  · intro t _ x
    exact (Real.rpow_pos_of_pos (hpos t x) q).le
  · intro t ht x
    exact rpow_subsolution (I := I) (M := M) g u source hu hpos hq (hpde t ht x)

theorem caccioppoli_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : q ≤ 0)
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x ≤
        deriv (fun s => u s x) t) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x ^ q *
                  rpowSource q u source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let hsourceq := contMDiff_rpowSource_of_pos hu hsource hpos q
  apply caccioppoli_of_subsolution
    (I := I) (M := M) cutoff (fun t x => u t x ^ q)
      (rpowSource q u source) huq hsourceq hab hdweight hweight hweight_nonneg
  · intro t _ x
    exact (Real.rpow_pos_of_pos (hpos t x) q).le
  · intro t ht x
    exact rpow_subsolution_of_supersolution
      (I := I) (M := M) g u source hu hpos hq (hpde t ht x)

theorem rpow_moser_step_le
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A K L : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s) +
          weight s *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) s) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u s x ^ q *
                  rpowSource q u source s x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g))) ≤ A)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (houterMass_le :
      (∫ t in t₀..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t)) ≤ L) :
    (∫ t in t₀..t₁, ∫ x,
        |cutoff.toFun x * u t x ^ q| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - t₀ + 1) * A + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let sourceq := rpowSource q u source
  have hsourceq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => sourceq p.1 p.2) := by
    simpa only [sourceq] using contMDiff_rpowSource_of_pos hu hsource hpos q
  have hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t))
      (Icc a t₁) :=
    (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff
      (fun s x => u s x ^ q) huq).continuous.continuousOn
  have hpdeq : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x ^ q) t ≤
        Δ_g (I := I) g
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t).toContMDiffMap x +
          sourceq t x := by
    intro t ht x
    simpa only [huq, sourceq] using
      rpow_subsolution (I := I) (M := M) g u source hu hpos hq (hpde t ht x)
  have henergy := caccioppoli_inner_energy_of_subsolution
    (I := I) (M := M) cutoff (fun t x => u t x ^ q) sourceq huq hsourceq
    hat₀ ht₀t₁ hdweight hweight hweight_nonneg hweight_a hweight_inner
    (fun t _ x => (Real.rpow_pos_of_pos (hpos t x) q).le)
    hpdeq
    (by simpa only [huq, sourceq] using hrhs_le)
  apply localized_parabolic_sobolev_of_nested_cutoffs_le
    (I := I) (M := M) g hdim cutoff outer (fun t x => u t x ^ q) huq
    ht₀t₁ hA hK henergy.1
  · exact hdirichlet.mono (fun t ht => ⟨hat₀.trans ht.1, ht.2⟩)
  · exact henergy.2
  · exact hgrad
  · simpa only [huq] using houterMass_le

theorem rpow_moser_step
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A K L : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s) +
          weight s *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) s) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u s x ^ q *
                  rpowSource q u source s x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g))) ≤ A)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (houterMass_le :
      (∫ t in t₀..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t)) ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in t₀..t₁, ∫ x,
          |cutoff.toFun x * u t x ^ q| ^
            (2 + 4 / (Module.finrank ℝ E : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        C * (((t₁ - t₀ + 1) * A + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  refine ⟨localizedSobolevConstant (I := I) (M := M) g hdim,
    localizedSobolevConstant_nonneg (I := I) (M := M) g hdim, ?_⟩
  exact rpow_moser_step_le (I := I) (M := M) g hdim cutoff outer u source hu hsource
    hpos hq hat₀ ht₀t₁ hA hK hdweight hweight hweight_nonneg hweight_a
    hweight_inner hpde hrhs_le hgrad houterMass_le

theorem rpow_moser_step_homogeneous_le
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {a t₀ t₁ D K L : ℝ}
    (hat₀ : a < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    (hcutoff : ∀ x : M, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (hderiv_le : ∀ s ∈ Icc a t₁, timeCutoffDeriv a t₀ s ≤ D)
    (houterMass_le :
      (∫ t in a..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t)) ≤ L) :
    (∫ t in t₀..t₁, ∫ x,
        |cutoff.toFun x * u t x ^ q| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - t₀ + 1) * ((D + 4 * K) * L) + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let zeroSource : ℝ → M → ℝ := fun _ _ => 0
  have hzeroSource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => zeroSource p.1 p.2) := contMDiff_const
  have hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        timeCutoffDeriv a t₀ s * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q) huq s) +
          timeCutoff a t₀ s *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun r x => u r x ^ q) huq s) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u s x ^ q *
                  rpowSource q u zeroSource s x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g))) ≤
        (D + 4 * K) * L := by
    intro t ht
    have h := timeCutoff_caccioppoli_rhs_le
      (I := I) (M := M) cutoff outer (fun s x => u s x ^ q) huq
      hat₀ ht.1 ht.2 hD hK hcutoff hgrad hderiv_le
      (by simpa only [huq] using houterMass_le)
    simpa only [zeroSource, rpowSource, mul_zero, integral_zero, add_zero, huq] using h
  have houterMass_inner_le :
      (∫ t in t₀..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t)) ≤ L := by
    let mass : ℝ → ℝ := fun t =>
      localizedL2Mass (I := I) (M := M) outer
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t)
    have hmass_cont : ContinuousOn mass (Icc a t₁) := by
      simpa only [mass] using
        (contDiff_localizedL2Mass (I := I) (M := M) outer
          (fun s x => u s x ^ q) huq).continuous.continuousOn
    have hmass_int : IntervalIntegrable mass volume a t₁ := by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le (hat₀.le.trans ht₀t₁)] using hmass_cont
    have hmono : (∫ t in t₀..t₁, mass t) ≤ ∫ t in a..t₁, mass t := by
      exact intervalIntegral.integral_mono_interval hat₀.le ht₀t₁ le_rfl
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact localizedL2Mass_nonneg (I := I) (M := M) outer
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t))
        hmass_int
    exact hmono.trans (by simpa only [mass, huq] using houterMass_le)
  apply rpow_moser_step_le (I := I) (M := M) g hdim cutoff outer u zeroSource
    hu hzeroSource hpos hq hat₀.le ht₀t₁
    (mul_nonneg (add_nonneg hD (mul_nonneg (by norm_num) hK)) hL) hK
    (contDiff_timeCutoffDeriv a t₀).continuous.continuousOn
    (fun t _ => hasDerivAt_timeCutoff a t₀ t)
    (fun t _ => (timeCutoff_mem_Icc a t₀ t).1)
    (timeCutoff_eq_zero a hat₀)
    (fun t ht => timeCutoff_eq_one_of_le hat₀ ht.1)
  · intro t ht x
    simpa only [zeroSource, add_zero] using hpde t ht x
  · simpa only [huq, zeroSource] using hrhs_le
  · exact hgrad
  · simpa only [huq] using houterMass_inner_le

theorem rpow_moser_step_homogeneous
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {a t₀ t₁ D K L : ℝ}
    (hat₀ : a < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    (hcutoff : ∀ x : M, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (hderiv_le : ∀ s ∈ Icc a t₁, timeCutoffDeriv a t₀ s ≤ D)
    (houterMass_le :
      (∫ t in a..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t)) ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in t₀..t₁, ∫ x,
          |cutoff.toFun x * u t x ^ q| ^
            (2 + 4 / (Module.finrank ℝ E : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        C * (((t₁ - t₀ + 1) * ((D + 4 * K) * L) + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  refine ⟨localizedSobolevConstant (I := I) (M := M) g hdim,
    localizedSobolevConstant_nonneg (I := I) (M := M) g hdim, ?_⟩
  exact rpow_moser_step_homogeneous_le
    (I := I) (M := M) g hdim cutoff outer u hu hpos hq hat₀ ht₀t₁ hD hK hL
      hpde hcutoff hgrad hderiv_le houterMass_le

end DifferentialGeometry.Analysis.Parabolic.Moser

end
