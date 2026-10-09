import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceTent
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Analysis.Integration.EntropyJensen
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [T2Space M] [I.Boundaryless]

omit [CompactSpace M] [T2Space M] in
private lemma gradFun_eq_zero_of_nonneg_of_eq_zero
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} (hu : ∀ y, 0 ≤ u y)
    {x : M} (hx : u x = 0) : gradFun g u x = 0 := by
  by_cases hd : MDifferentiableAt I 𝓘(ℝ) u x
  · have hmin : IsLocalMin u x := Eventually.of_forall fun y => by rw [hx]; exact hu y
    exact gradFun_eq_zero_of_mfderiv_eq_zero g u (mfderiv_eq_zero_at_spatial_min hmin hd)
  · exact gradFun_eq_zero_of_mfderiv_eq_zero g u (mfderiv_zero_of_not_mdifferentiableAt hd)

omit [CompactSpace M] [I.Boundaryless] in
private lemma ball_isOpen (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) :
    IsOpen (riemannianBallOf g x r) :=
  isOpen_lt (by
    unfold riemannianEDistOf
    exact Geometry.Riemannian.continuous_riemannianEDist g x) continuous_const

omit [I.Boundaryless] in
private lemma energy_integrable (g : SmoothRiemannianMetric I M)
    {G : ∀ x : M, TangentSpace I x}
    (hG : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g)) :
    Integrable (fun x => g.inner x (G x) (G x)) (riemannianVolumeMeasure I M g) :=
  hG.integrable_sq.congr (Eventually.of_forall fun x =>
    Real.sq_sqrt (metric_inner_self_nonneg g x (G x)))


theorem exists_entropy_cutoff (g : SmoothRiemannianMetric I M) (x : M)
    {r : ℝ} (hr : 0 < r) :
    ∃ η : M → ℝ, Continuous η ∧ (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
      (∀ y ∈ riemannianBallOf g x (r / 2), η y = 1) ∧
      Function.support η ⊆ riemannianBallOf g x r ∧
      HasWeakRiemannianGradLp g η (gradFun g η) ∧
      MemLp (fun y => Real.sqrt (g.inner y (gradFun g η y) (gradFun g η y))) 2
        (riemannianVolumeMeasure I M g) ∧
      (∀ y, Real.sqrt (g.inner y (gradFun g η y) (gradFun g η y)) ≤ 3 / r) ∧
      (∀ y ∉ riemannianBallOf g x r, gradFun g η y = 0) := by
  let ρ : ℝ := 4 * r / 3
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let η : M → ℝ := riemDistTent g x hρ
  let L : ℝ≥0 := ⟨3 / r, by positivity⟩
  have hscale : 4 / ρ = 3 / r := by dsimp only [ρ]; field_simp [hr.ne']
  have hL : (⟨4 / ρ, div_nonneg (by norm_num) hρ.le⟩ : ℝ≥0) = L :=
    NNReal.eq hscale
  have hηlip : ∀ y z, edist (η y) (η z) ≤ (L : ℝ≥0∞) * riemannianEDistOf g y z := by
    intro y z
    simpa only [hL] using riemTent_lip g x hρ y z
  have hηrange (y : M) : η y ∈ Icc (0 : ℝ) 1 := riemTent_mem_Icc g x hρ y
  have hηbound (y : M) : ‖η y‖₊ ≤ (1 : ℝ≥0) := by
    exact_mod_cast (show ‖η y‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (hηrange y).1]
      exact (hηrange y).2)
  have hηcont : Continuous η := intrinsic_lip_cont g hηlip
  have hηsupp : Function.support η ⊆ riemannianBallOf g x r := by
    have hrad : 3 * ρ / 4 = r := by dsimp only [ρ]; ring
    simpa only [hrad, riemannianBallOf] using riemTent_support g x hρ
  have hgrad (y : M) : Real.sqrt (g.inner y (gradFun g η y) (gradFun g η y)) ≤ 3 / r :=
    Geometry.Riemannian.grad_norm_le_lip_all g hηlip
  have hgrad2 : MemLp (fun y => Real.sqrt (g.inner y (gradFun g η y) (gradFun g η y))) 2
      (riemannianVolumeMeasure I M g) := by
    let : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
    exact MemLp.of_bound (grad_norm_aesm g
      (DifferentialGeometry.Analysis.Sobolev.Chart.ae_mdiff_of_lip g hηlip)) (3 / r)
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact hgrad y)
  refine ⟨η, hηcont, hηrange, ?_, hηsupp, weak_grad_of_lip g hηlip hηbound, hgrad2, hgrad, ?_⟩
  · intro y hy
    apply riemTent_eq_one g x hρ
    exact hy.le.trans (ENNReal.ofReal_le_ofReal (by dsimp only [ρ]; linarith))
  · intro y hy
    have hz : η y = 0 := by
      by_contra hz
      exact hy (hηsupp hz)
    exact gradFun_eq_zero_of_nonneg_of_eq_zero g (fun z => (hηrange z).1) hz


theorem exists_normalized_cutoff_wform (g : SmoothRiemannianMetric I M) (x : M)
    {r D b : ℝ} (hr : 0 < r) (hD : 1 ≤ D)
    (hdoubling : (riemannianVolumeMeasure I M g (riemannianBallOf g x r)).toReal ≤
      D * (riemannianVolumeMeasure I M g (riemannianBallOf g x (r / 2))).toReal)
    {R : M → ℝ} (hR : Continuous R)
    (hscalar : ∀ y ∈ riemannianBallOf g x r, R y ≤ b * r⁻¹ ^ 2) :
    ∃ w : M → ℝ, ∃ G : ∀ y : M, TangentSpace I y,
      Continuous w ∧ MemLp w 2 (riemannianVolumeMeasure I M g) ∧
      HasWeakRiemannianGradLp g w G ∧
      MemLp (fun y => Real.sqrt (g.inner y (G y) (G y))) 2 (riemannianVolumeMeasure I M g) ∧
      (∀ y, 0 ≤ w y) ∧ (∫ y, w y ^ 2 ∂riemannianVolumeMeasure I M g) = 1 ∧
      (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) + r ^ 2 * R y * w y ^ 2 -
        w y ^ 2 * Real.log (w y ^ 2) ∂riemannianVolumeMeasure I M g) ≤
        36 * D + b + Real.log (riemannianVolumeMeasure I M g (riemannianBallOf g x r)).toReal := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let A := riemannianBallOf g x (r / 2)
  let U := riemannianBallOf g x r
  have hA : MeasurableSet A := (ball_isOpen g x (r / 2)).measurableSet
  have hU : MeasurableSet U := (ball_isOpen g x r).measurableSet
  have hApos : 0 < (μ A).toReal := by
    apply ENNReal.toReal_pos
    · apply ne_of_gt
      apply (ball_isOpen g x (r / 2)).measure_pos μ
      refine ⟨x, ?_⟩
      change riemannianEDistOf g x x < ENNReal.ofReal (r / 2)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (half_pos hr)
    · exact measure_ne_top μ A
  obtain ⟨η, hηcont, hηrange, hηone, hηsupp, hηweak, hηgrad2, hηgrad, hηzero⟩ :=
    exists_entropy_cutoff g x hr
  have hη2 : MemLp η 2 μ := hηcont.memLp_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hηsq := hη2.integrable_sq
  let m : ℝ := ∫ y, η y ^ 2 ∂μ
  have hAm : (μ A).toReal ≤ m := by
    calc
      _ = ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂μ := by simp [hA, Measure.real]
      _ ≤ ∫ y, η y ^ 2 ∂μ := by
        apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) hηsq
        intro y
        change A.indicator (fun _ => (1 : ℝ)) y ≤ η y ^ 2
        by_cases hy : y ∈ A
        · rw [indicator_of_mem hy, hηone y hy]
          norm_num
        · rw [indicator_of_notMem hy]
          exact sq_nonneg _
  have hmpos : 0 < m := hApos.trans_le hAm
  have hηoutside (y : M) (hy : y ∉ U) : η y = 0 := by
    by_contra h
    exact hy (hηsupp h)
  have hmU : m ≤ (μ U).toReal := by
    calc
      m ≤ ∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂μ := by
        apply integral_mono hηsq ((integrable_const (1 : ℝ)).indicator hU)
        intro y
        change η y ^ 2 ≤ U.indicator (fun _ => (1 : ℝ)) y
        by_cases hy : y ∈ U
        · rw [indicator_of_mem hy]
          nlinarith [(hηrange y).1, (hηrange y).2]
        · rw [indicator_of_notMem hy, hηoutside y hy]
          norm_num
      _ = (μ U).toReal := by simp [hU, Measure.real]
  have hUm : (μ U).toReal ≤ D * m :=
    hdoubling.trans (mul_le_mul_of_nonneg_left hAm (zero_le_one.trans hD))
  have hηenergy := energy_integrable g hηgrad2
  have henergy : (∫ y, g.inner y (gradFun g η y) (gradFun g η y) ∂μ) ≤
      (3 / r) ^ 2 * (μ U).toReal := by
    calc
      _ ≤ ∫ y, U.indicator (fun _ => (3 / r) ^ 2) y ∂μ := by
        apply integral_mono hηenergy ((integrable_const ((3 / r) ^ 2)).indicator hU)
        intro y
        change g.inner y (gradFun g η y) (gradFun g η y) ≤ U.indicator (fun _ => (3 / r) ^ 2) y
        by_cases hy : y ∈ U
        · rw [indicator_of_mem hy]
          have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
            (by positivity : 0 ≤ 3 / r)).2 (hηgrad y)
          rwa [Real.sq_sqrt (metric_inner_self_nonneg g y (gradFun g η y))] at hs
        · rw [indicator_of_notMem hy, hηzero y hy]
          simp
      _ = (3 / r) ^ 2 * (μ U).toReal := by simp [hU, Measure.real, mul_comm]
  let c : ℝ := (Real.sqrt m)⁻¹
  have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hmpos)
  have hc2 : c ^ 2 = m⁻¹ := by dsimp only [c]; rw [inv_pow, Real.sq_sqrt hmpos.le]
  have hc2m : c ^ 2 * m = 1 := by rw [hc2]; exact inv_mul_cancel₀ hmpos.ne'
  let w : M → ℝ := fun y => c * η y
  let G : ∀ y : M, TangentSpace I y := fun y => c • gradFun g η y
  have hwcont : Continuous w := continuous_const.mul hηcont
  have hw2 : MemLp w 2 μ := hη2.const_mul c
  have hwpos (y : M) : 0 ≤ w y := mul_nonneg hcpos.le (hηrange y).1
  have hwmass : (∫ y, w y ^ 2 ∂μ) = 1 := by
    simp only [w, mul_pow, integral_const_mul]
    exact hc2m
  have hwgrad2 : MemLp (fun y => Real.sqrt (g.inner y (G y) (G y))) 2 μ := by
    have hpoint (y : M) : Real.sqrt (g.inner y (G y) (G y)) =
        c * Real.sqrt (g.inner y (gradFun g η y) (gradFun g η y)) := by
      dsimp only [G]
      rw [Geometry.Riemannian.sqrt_inner_smul, abs_of_nonneg hcpos.le]
    simpa only [hpoint] using hηgrad2.const_mul c
  have hwweak : HasWeakRiemannianGradLp g w G :=
    hηweak.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) c hη2
  have hGenergy := energy_integrable g hwgrad2
  have hGeq : (∫ y, g.inner y (G y) (G y) ∂μ) =
      c ^ 2 * (∫ y, g.inner y (gradFun g η y) (gradFun g η y) ∂μ) := by
    simp only [G, SmoothRiemannianMetric.metric_inner_smul_self, integral_const_mul]
  have hgradbound : 4 * r ^ 2 * (∫ y, g.inner y (G y) (G y) ∂μ) ≤ 36 * D := by
    rw [hGeq]
    calc
      _ ≤ 4 * r ^ 2 * (c ^ 2 * ((3 / r) ^ 2 * (μ U).toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (sq_nonneg c))
          (mul_nonneg (by norm_num) (sq_nonneg r))
      _ = 36 * (c ^ 2 * (μ U).toReal) := by field_simp [hr.ne']; ring
      _ ≤ 36 * (c ^ 2 * (D * m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUm (sq_nonneg c)) (by norm_num)
      _ = 36 * D := by rw [mul_left_comm (c ^ 2) D m, hc2m, mul_one]
  have hwsupp : Function.support w ⊆ U := by
    intro y hy
    by_contra hout
    exact hy (by dsimp only [w]; rw [hηoutside y hout, mul_zero])
  have hRs : Integrable (fun y => R y * w y ^ 2) μ :=
    integrable_of_continuous_compactSpace g (hR.mul (hwcont.pow 2))
  have hscalarbound : r ^ 2 * (∫ y, R y * w y ^ 2 ∂μ) ≤ b := by
    have hRint : (∫ y, R y * w y ^ 2 ∂μ) ≤ b * r⁻¹ ^ 2 := by
      calc
        _ ≤ ∫ y, (b * r⁻¹ ^ 2) * w y ^ 2 ∂μ := by
          apply integral_mono hRs (hw2.integrable_sq.const_mul _)
          intro y
          by_cases hy : y ∈ U
          · exact mul_le_mul_of_nonneg_right (hscalar y hy) (sq_nonneg _)
          · have hz : w y = 0 := by by_contra h; exact hy (hwsupp h)
            simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
        _ = b * r⁻¹ ^ 2 := by rw [integral_const_mul, hwmass, mul_one]
    calc
      _ ≤ r ^ 2 * (b * r⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hRint (sq_nonneg r)
      _ = b := by field_simp [hr.ne']
  have hH : Integrable (fun y => w y ^ 2 * Real.log (w y ^ 2)) μ :=
    integrable_of_continuous_compactSpace g (Real.continuous_mul_log.comp (hwcont.pow 2))
  have hsqSupp : Function.support (fun y => w y ^ 2) ⊆ U := by
    intro y hy
    apply hwsupp
    intro hz
    exact hy (by change w y ^ 2 = 0; rw [hz]; norm_num)
  have hentropy := DifferentialGeometry.Analysis.Integration.entropy_support_le μ
    (hwcont.pow 2).measurable hw2.integrable_sq (fun y => sq_nonneg (w y)) hwmass hH hsqSupp
  change -(∫ y, w y ^ 2 * Real.log (w y ^ 2) ∂μ) ≤ Real.log (μ U).toReal at hentropy
  refine ⟨w, G, hwcont, hw2, hwweak, hwgrad2, hwpos, hwmass, ?_⟩
  have hW : (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) + r ^ 2 * R y * w y ^ 2 -
      w y ^ 2 * Real.log (w y ^ 2) ∂μ) =
      4 * r ^ 2 * (∫ y, g.inner y (G y) (G y) ∂μ) +
        r ^ 2 * (∫ y, R y * w y ^ 2 ∂μ) - (∫ y, w y ^ 2 * Real.log (w y ^ 2) ∂μ) := by
    simp_rw [mul_assoc (r ^ 2)]
    have hsum : Integrable (fun y => 4 * r ^ 2 * g.inner y (G y) (G y) +
        r ^ 2 * (R y * w y ^ 2)) μ :=
      (hGenergy.const_mul (4 * r ^ 2)).add (hRs.const_mul (r ^ 2))
    rw [integral_sub hsum hH,
      integral_add (hGenergy.const_mul (4 * r ^ 2)) (hRs.const_mul (r ^ 2)),
      integral_const_mul, integral_const_mul]
  rw [hW]
  change 4 * r ^ 2 * (∫ y, g.inner y (G y) (G y) ∂μ) +
    r ^ 2 * (∫ y, R y * w y ^ 2 ∂μ) - (∫ y, w y ^ 2 * Real.log (w y ^ 2) ∂μ) ≤
      36 * D + b + Real.log (μ U).toReal
  linarith only [hgradbound, hscalarbound, hentropy]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
