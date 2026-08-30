import DifferentialGeometry.Analysis.Integration.L2.TensorFiberNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Analysis.Spectral

open scoped ContDiff Manifold Topology ENNReal
open MeasureTheory
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_sq_eq_fiber_int
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x =>
      Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
        (I := I) (M := M)
        (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g r s _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_sq_le_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (F : M → ℝ)
    (hF : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g))
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (S.toSection x) ≤ F x) :
    ‖S‖ ^ 2 ≤
      ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [SmoothCcTensor.norm_def (I := I) (M := M) S,
    l2_sq_eq_fiber_int (I := I) (M := M) g r s S]
  have hint : Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x
        (S.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r s S
  exact integral_mono hint hF hpt

noncomputable def fiberLpFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : M → ℝ := fun x =>
  Real.sqrt
    (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem fiberLpFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : Continuous (fiberLpFun g r s S) := by
  apply Real.continuous_sqrt.comp
  have h := SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine h.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g r s x (S.toSection x),
    ← SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem fiberLpFun_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) : 0 ≤ fiberLpFun g r s S x :=
  Real.sqrt_nonneg _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem fiber_lp2_eq_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    lpNorm (fiberLpFun g r s S) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hcont := fiberLpFun_continuous (I := I) (M := M) g r s S
  have hmeas : AEStronglyMeasurable (fiberLpFun g r s S) μ :=
    hcont.aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hmeas]
  have hpoint : ∀ x : M,
      ‖fiberLpFun g r s S x‖ ^ ((2 : ENNReal).toReal) =
        riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toSection x) := by
    intro x
    rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num,
      Real.norm_eq_abs, abs_of_nonneg (fiberLpFun_nonneg g r s S x),
      Real.rpow_two]
    exact Real.sq_sqrt
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)
  simp_rw [hpoint]
  rw [show ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow]
  rw [← l2_sq_eq_fiber_int
    (I := I) (M := M) g r s S,
    Real.sqrt_sq (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun),
    ← SmoothCcTensor.norm_def (I := I) (M := M) S]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem fiber_mul3_l632
    (g : SmoothRiemannianMetric I M)
    (r6 s6 r3 s3 r2 s2 : ℕ)
    (A : SmoothCcTensor g r6 s6)
    (B : SmoothCcTensor g r3 s3)
    (C : SmoothCcTensor g r2 s2) :
    ∫ x, fiberLpFun g r6 s6 A x * fiberLpFun g r3 s3 B x *
          fiberLpFun g r2 s2 C x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      lpNorm (fiberLpFun g r6 s6 A) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) *
        lpNorm (fiberLpFun g r3 s3 B) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) * ‖C‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let f6 : M → ℝ := fiberLpFun g r6 s6 A
  let f3 : M → ℝ := fiberLpFun g r3 s3 B
  let f2 : M → ℝ := fiberLpFun g r2 s2 C
  have hf6c : Continuous f6 :=
    fiberLpFun_continuous (I := I) (M := M) g r6 s6 A
  have hf3c : Continuous f3 :=
    fiberLpFun_continuous (I := I) (M := M) g r3 s3 B
  have hf2c : Continuous f2 :=
    fiberLpFun_continuous (I := I) (M := M) g r2 s2 C
  have hf6mem : MemLp f6 6 μ :=
    hf6c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf3mem : MemLp f3 3 μ :=
    hf3c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf2mem : MemLp f2 2 μ :=
    hf2c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfc : Continuous (fun x => f6 x * f3 x * f2 x) :=
    (hf6c.mul hf3c).mul hf2c
  have : ENNReal.HolderTriple (6 : ENNReal) 3 2 := by
    exact ENNReal.HolderTriple.of_toReal (by
      rw [Real.holderTriple_iff]
      norm_num)
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := by
    exact ENNReal.HolderTriple.of_toReal (by
      rw [Real.holderTriple_iff]
      norm_num)
  have h63 :
      eLpNorm (fun x => f6 x * f3 x) 2 μ ≤
        eLpNorm f6 6 μ * eLpNorm f3 3 μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := (6 : ENNReal)) (q := 3) (r := 2) (μ := μ)
        hf6c.aestronglyMeasurable hf3c.aestronglyMeasurable
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun _ => by
          rw [Real.norm_eq_abs, abs_mul]
          norm_num)))
  have h221 :
      eLpNorm (fun x => (f6 x * f3 x) * f2 x) 1 μ ≤
        eLpNorm (fun x => f6 x * f3 x) 2 μ * eLpNorm f2 2 μ := by
    have h :=
      eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := (2 : ENNReal)) (q := 2) (r := 1) (μ := μ)
        (hf6c.mul hf3c).aestronglyMeasurable hf2c.aestronglyMeasurable
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun _ => by
          rw [Real.norm_eq_abs, abs_mul]
          norm_num))
    have hmul : f6 * f3 = fun x => f6 x * f3 x := by
      funext x
      rfl
    rw [hmul] at h
    simpa only [ENNReal.coe_one, one_mul] using h
  have hENN :
      eLpNorm (fun x => f6 x * f3 x * f2 x) 1 μ ≤
        (eLpNorm f6 6 μ * eLpNorm f3 3 μ) * eLpNorm f2 2 μ :=
    h221.trans (mul_le_mul_left h63 _)
  have hfinite :
      (eLpNorm f6 6 μ * eLpNorm f3 3 μ) * eLpNorm f2 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hf6mem.eLpNorm_ne_top hf3mem.eLpNorm_ne_top)
      hf2mem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hENN
  rw [toReal_eLpNorm hfc.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    toReal_eLpNorm hf6mem.aestronglyMeasurable,
    toReal_eLpNorm hf3mem.aestronglyMeasurable,
    toReal_eLpNorm hf2mem.aestronglyMeasurable] at hreal
  rw [lpNorm_one_eq_integral_norm hfc.aestronglyMeasurable] at hreal
  have hnonneg : ∀ x : M, 0 ≤ f6 x * f3 x * f2 x := fun x =>
    mul_nonneg
      (mul_nonneg (fiberLpFun_nonneg g r6 s6 A x)
        (fiberLpFun_nonneg g r3 s3 B x))
      (fiberLpFun_nonneg g r2 s2 C x)
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] at hreal
  rw [fiber_lp2_eq_l2 (I := I) (M := M) g r2 s2 C] at hreal
  simpa only [μ, f6, f3, f2, mul_assoc] using hreal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem fiber_mul3_linf22
    (g : SmoothRiemannianMetric I M)
    (rInf sInf r2a s2a r2b s2b : ℕ)
    (A : SmoothCcTensor g rInf sInf)
    (B : SmoothCcTensor g r2a s2a)
    (C : SmoothCcTensor g r2b s2b)
    (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ x : M, fiberLpFun g rInf sInf A x ≤ K) :
    ∫ x, fiberLpFun g rInf sInf A x * fiberLpFun g r2a s2a B x *
          fiberLpFun g r2b s2b C x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      K * ‖B‖ * ‖C‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let fInf : M → ℝ := fiberLpFun g rInf sInf A
  let f2a : M → ℝ := fiberLpFun g r2a s2a B
  let f2b : M → ℝ := fiberLpFun g r2b s2b C
  have hfInfc : Continuous fInf :=
    fiberLpFun_continuous (I := I) (M := M) g rInf sInf A
  have hf2ac : Continuous f2a :=
    fiberLpFun_continuous (I := I) (M := M) g r2a s2a B
  have hf2bc : Continuous f2b :=
    fiberLpFun_continuous (I := I) (M := M) g r2b s2b C
  have hf2amem : MemLp f2a 2 μ :=
    hf2ac.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf2bmem : MemLp f2b 2 μ :=
    hf2bc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfc : Continuous (fun x => f2a x * f2b x) := hf2ac.mul hf2bc
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := by
    exact ENNReal.HolderTriple.of_toReal (by
      rw [Real.holderTriple_iff]
      norm_num)
  have h22 :
      eLpNorm (fun x => f2a x * f2b x) 1 μ ≤
        eLpNorm f2a 2 μ * eLpNorm f2b 2 μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := (2 : ENNReal)) (q := 2) (r := 1) (μ := μ)
        hf2ac.aestronglyMeasurable hf2bc.aestronglyMeasurable
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun _ => by
          rw [Real.norm_eq_abs, abs_mul]
          norm_num)))
  have hfinite : eLpNorm f2a 2 μ * eLpNorm f2b 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf2amem.eLpNorm_ne_top hf2bmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite h22
  rw [toReal_eLpNorm hfc.aestronglyMeasurable,
    ENNReal.toReal_mul,
    toReal_eLpNorm hf2amem.aestronglyMeasurable,
    toReal_eLpNorm hf2bmem.aestronglyMeasurable] at hreal
  rw [lpNorm_one_eq_integral_norm hfc.aestronglyMeasurable] at hreal
  have hprod_nonneg : ∀ x : M, 0 ≤ f2a x * f2b x := fun x =>
    mul_nonneg (fiberLpFun_nonneg g r2a s2a B x)
      (fiberLpFun_nonneg g r2b s2b C x)
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hprod_nonneg _)] at hreal
  rw [fiber_lp2_eq_l2 (I := I) (M := M) g r2a s2a B,
    fiber_lp2_eq_l2 (I := I) (M := M) g r2b s2b C] at hreal
  have hleft : Integrable (fun x => fInf x * f2a x * f2b x) μ :=
    ((hfInfc.mul hf2ac).mul hf2bc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x => K * (f2a x * f2b x)) μ :=
    (continuous_const.mul (hf2ac.mul hf2bc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ∫ x, fiberLpFun g rInf sInf A x * fiberLpFun g r2a s2a B x *
          fiberLpFun g r2b s2b C x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, fInf x * f2a x * f2b x ∂μ := by rfl
    _ ≤ ∫ x, K * (f2a x * f2b x) ∂μ := by
      exact integral_mono hleft hright (fun x => by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hA x) (hprod_nonneg x))
    _ = K * ∫ x, f2a x * f2b x ∂μ := by
      rw [integral_const_mul]
    _ ≤ K * (‖B‖ * ‖C‖) := mul_le_mul_of_nonneg_left hreal hK
    _ = K * ‖B‖ * ‖C‖ := by ring

omit [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem fiberLp_slotExtend
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (p : ℝ≥0∞) :
    lpNorm (fiberLpFun g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s S)) p
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      Real.sqrt (Module.finrank ℝ E) *
        lpNorm (fiberLpFun g r s S) p
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let k : ℝ := Real.sqrt (Module.finrank ℝ E)
  have hfun :
      fiberLpFun g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s S) =
        k • fiberLpFun g r s S := by
    funext x
    change Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
          ((slotExtend (I := I) (M := M) g r s S).toSection x)) =
      k * Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toSection x))
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g r s S x,
      Real.sqrt_mul (Nat.cast_nonneg (Module.finrank ℝ E))]
  rw [hfun, lpNorm_const_smul]
  rw [coe_nnnorm, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fiberLp3_le_6
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
      lpNorm (fiberLpFun g r s S) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ) ^
            (1 / 6 : ℝ)).toReal *
          lpNorm (fiberLpFun g r s S) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcont := fiberLpFun_continuous (I := I) (M := M) g r s S
  have hmem : MemLp (fiberLpFun g r s S) 6 μ :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := fiberLpFun g r s S) (p := (3 : ℝ≥0∞)) (q := 6)
    (by norm_num) hcont.aestronglyMeasurable
  have hpow : μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have htop : eLpNorm (fiberLpFun g r s S) 6 μ * μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top hmem.eLpNorm_ne_top hpow
  have hreal := ENNReal.toReal_mono htop hcmp
  rw [toReal_eLpNorm hcont.aestronglyMeasurable, ENNReal.toReal_mul,
    toReal_eLpNorm hcont.aestronglyMeasurable,
    show 1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal =
      (1 / 6 : ℝ) by norm_num] at hreal
  simpa only [μ, mul_comm] using hreal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fiberLp3_le_lp6
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g r s,
      lpNorm (fiberLpFun g r s S) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * lpNorm (fiberLpFun g r s S) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let V : ℝ := (μ Set.univ ^ (1 / 6 : ℝ)).toReal
  refine ⟨V, ENNReal.toReal_nonneg, ?_⟩
  intro S
  have hcont := fiberLpFun_continuous (I := I) (M := M) g r s S
  have hmem : MemLp (fiberLpFun g r s S) 6 μ :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := fiberLpFun g r s S) (p := (3 : ℝ≥0∞)) (q := 6)
    (by norm_num) hcont.aestronglyMeasurable
  have hpow : μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have htop : eLpNorm (fiberLpFun g r s S) 6 μ * μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top hmem.eLpNorm_ne_top hpow
  have hreal := ENNReal.toReal_mono htop hcmp
  rw [toReal_eLpNorm hcont.aestronglyMeasurable, ENNReal.toReal_mul,
    toReal_eLpNorm hcont.aestronglyMeasurable,
    show 1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal =
      (1 / 6 : ℝ) by norm_num] at hreal
  simpa only [V, mul_comm] using hreal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldApplication_l2_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r)
    (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x
        (W.toSection x) ≤ B ^ 2) :
    ‖operatorFieldApply (I := I) (M := M) g r s Φ W‖ ≤ ‖Φ‖ * B := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g r s x
      (Φ.toSection x) with hF_def
  have hF_int : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r s Φ).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) ≤ F x := by
    intro x
    rw [operatorFieldApplication_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g 0 r s x (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    calc
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x)
          ≤ riemannianFiberNormSq (I := I) (M := M) g r s x
              (Φ.toSection x) * B ^ 2 :=
        mul_le_mul_of_nonneg_left (hW x)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)
      _ = B ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x
          (Φ.toSection x) := by ring
  have hsq : ‖operatorFieldApply (I := I) (M := M) g r s Φ W‖ ^ 2 ≤
      ‖Φ‖ ^ 2 * B ^ 2 := by
    have h1 := l2_sq_le_integral
      (I := I) (M := M) g 0 s
      (operatorFieldApply (I := I) (M := M) g r s Φ W) F hF_int hpt
    rw [hF_def, integral_const_mul] at h1
    have hbridge :=
      l2_sq_eq_fiber_int
        (I := I) (M := M) g r s Φ
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    nlinarith [h1]
  have hrhs : 0 ≤ ‖Φ‖ * B := mul_nonneg (norm_nonneg _) hB
  refine le_of_sq_le_sq ?_ hrhs
  rw [mul_pow]
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldApplication_l6_l3_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ‖operatorFieldApply (I := I) (M := M) g r s Φ W‖ ≤
      lpNorm (fiberLpFun g r s Φ) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) *
        lpNorm (fiberLpFun g 0 r W) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let Y : SmoothCcTensor g 0 s :=
    operatorFieldApply (I := I) (M := M) g r s Φ W
  have hΦc := fiberLpFun_continuous (I := I) (M := M) g r s Φ
  have hWc := fiberLpFun_continuous (I := I) (M := M) g 0 r W
  have hYc := fiberLpFun_continuous (I := I) (M := M) g 0 s Y
  have hΦmem : MemLp (fiberLpFun g r s Φ) 6 μ :=
    hΦc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWmem : MemLp (fiberLpFun g 0 r W) 3 μ :=
    hWc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hYmem : MemLp (fiberLpFun g 0 s Y) 2 μ :=
    hYc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : ENNReal.HolderTriple (6 : ENNReal) 3 2 := by
    exact ENNReal.HolderTriple.of_toReal (by
      rw [Real.holderTriple_iff]
      norm_num)
  have hpt : ∀ x : M,
      fiberLpFun g 0 s Y x ≤
        fiberLpFun g r s Φ x * fiberLpFun g 0 r W x := by
    intro x
    dsimp [fiberLpFun, Y]
    have h := riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g 0 r s x (Φ.toSection x) (W.toSection x)
    refine (Real.sqrt_le_sqrt h).trans_eq ?_
    rw [Real.sqrt_mul
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)]
  have hmono :
      eLpNorm (fiberLpFun g 0 s Y) 2 μ ≤
        eLpNorm (fun x => fiberLpFun g r s Φ x * fiberLpFun g 0 r W x) 2 μ := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (fiberLpFun_nonneg g 0 s Y x),
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (fiberLpFun_nonneg g r s Φ x)
          (fiberLpFun_nonneg g 0 r W x))]
    exact hpt x
  have hholder :
      eLpNorm (fun x => fiberLpFun g r s Φ x * fiberLpFun g 0 r W x) 2 μ ≤
        eLpNorm (fiberLpFun g r s Φ) 6 μ *
          eLpNorm (fiberLpFun g 0 r W) 3 μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := (6 : ENNReal)) (q := 3) (r := 2) (μ := μ)
        (hΦc.aestronglyMeasurable) (hWc.aestronglyMeasurable)
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          norm_num)))
  have hENN := hmono.trans hholder
  have hfinite :
      eLpNorm (fiberLpFun g r s Φ) 6 μ *
          eLpNorm (fiberLpFun g 0 r W) 3 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hΦmem.eLpNorm_ne_top hWmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hENN
  rw [toReal_eLpNorm hYmem.aestronglyMeasurable,
    ENNReal.toReal_mul, toReal_eLpNorm hΦmem.aestronglyMeasurable,
    toReal_eLpNorm hWmem.aestronglyMeasurable] at hreal
  rw [← fiber_lp2_eq_l2 (I := I) (M := M) g 0 s Y]
  exact hreal

end DifferentialGeometry.Analysis.Spectral
