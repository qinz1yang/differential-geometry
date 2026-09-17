import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleMultiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivativeComposition
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDifferentiation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.MultiplicationInclusion
import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

def parameterDerivativeParabolicForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a b : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (f₀ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) : TensorHs g 0 0 0 :=
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
        ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₀ := parameterSecondDerivativeHs g 0
    let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
    let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
    scalarH0ContinuousMul g (C a) (Z (Q₀ v)) +
      scalarH0ContinuousMul g (C (R v)) (Z (D a)) - Z (L₀ v) +
      (scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh f₀))) +
        scalarH0ContinuousMul g (C (Q₁ f₀)) (Z (D a)) + Z (D b))

theorem parameterDerivative_parabolic_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (a b f : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
        ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₀ := parameterSecondDerivativeHs g 0
    let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
    let L₁ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
    let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
    L₁ u + f = scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)) + b →
      Z (D f + (D.comp L₁ - L₀.comp Dh) u) =
        scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh u))) +
          scalarH0ContinuousMul g (C (R (Dh u))) (Z (D a)) - Z (L₀ (Dh u)) +
          (scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh f₀))) +
            scalarH0ContinuousMul g (C (Q₁ f₀)) (Z (D a)) + Z (D b)) := by
  intro D Dh Z C Q₁ Q₀ R L₁ L₀ heq
  have hmul : Z (D (scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)))) =
      scalarH0ContinuousMul g (C a) (Z (D (Q₁ (f₀ + u)))) +
        scalarH0ContinuousMul g (C (Q₁ (f₀ + u))) (Z (D a)) :=
    parameterDerivativeHs_scalarHsMul g a (Q₁ (f₀ + u))
  have hcomm (v : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :
      D (Q₁ v) = Q₀ (Dh v) :=
    parameterDerivativeHs_parameterSecondDerivativeHs g 0 v
  have hfirst : Q₁ u = R (Dh u) := by
    simp only [Q₁, R, Dh, parameterSecondDerivativeHs, ContinuousLinearMap.comp_apply]
    rw [← tensorHsInclusion_trans_apply]
  have h : Z (D (L₁ u)) + Z (D f) =
      Z (D (scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)))) + Z (D b) := by
    rw [← Z.map_add, ← D.map_add, heq, D.map_add, Z.map_add]
  rw [hmul, hcomm] at h
  simp only [map_add, add_apply] at h
  rw [hfirst] at h
  calc
    _ = Z (D (L₁ u)) + Z (D f) - Z (L₀ (Dh u)) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
      abel
    _ = _ := by rw [h]; abel

def parameterDerivativeParabolicForcingHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) (hn : 1 ≤ n)
    (a b : TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))
    (f₀ : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 ((n : ℝ) + 2)) : TensorHs g 0 0 (n : ℝ) :=
  let D := (parameterDerivativeHs g n).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0) (by norm_num))
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n)
  let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)).comp
      ((parameterDerivativeHs g (n + 2)).comp (tensorHsInclusion
        (g := g) (r := 0) (s := 0)
        (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by push_cast; linarith)))
  let R := (parameterDerivativeHs g n).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0)
    (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))
  let m := scalarHsMul g n (by simpa using hn)
  let Qhi := parameterSecondDerivativeHs g (n + 1)
  let Qlo := parameterSecondDerivativeHs g n
  let L := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
  m (J a) (Qlo v) + m (R v) (D a) - L v +
    (m (J a) (Qlo (Dh f₀)) + m (J (Qhi f₀)) (D a) + D b)

theorem parameterDerivative_parabolic_equation_of_one_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (f₀ u : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))
    (a b f : TensorHs g 0 0 ((n + 1 : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g n).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num))
    let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)).comp
        ((parameterDerivativeHs g (n + 2)).comp (tensorHsInclusion
          (g := g) (r := 0) (s := 0)
          (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by push_cast; linarith)))
    let Lhi := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ)
    let Llo := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
    Lhi u + f = scalarHsMul g (n + 1) (by simp) a
        (parameterSecondDerivativeHs g (n + 1) (f₀ + u)) + b →
      D f + (D.comp Lhi - Llo.comp Dh) u =
        parameterDerivativeParabolicForcingHs g n hn a b f₀ (Dh u) := by
  intro D Dh Lhi Llo heq
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n)
  let R := (parameterDerivativeHs g n).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0)
    (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))
  let m := scalarHsMul g n (by simpa using hn)
  let Qhi := parameterSecondDerivativeHs g (n + 1)
  let Qlo := parameterSecondDerivativeHs g n
  have hmul : D (scalarHsMul g (n + 1) (by simp) a (Qhi (f₀ + u))) =
      m (J a) (D (Qhi (f₀ + u))) + m (J (Qhi (f₀ + u))) (D a) :=
    parameterDerivativeHs_scalarHsMul_of_one_le g hn a (Qhi (f₀ + u))
  have hcomm (v : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)) :
      D (Qhi v) = Qlo (Dh v) :=
    parameterDerivativeHs_parameterSecondDerivativeHs g n v
  have hfirst : J (Qhi u) = R (Dh u) := by
    refine (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 2)).induction_on u ?_ ?_
    · exact isClosed_eq (J.continuous.comp Qhi.continuous) (R.continuous.comp Dh.continuous)
    intro S
    simp only [ccToHsLin_apply, J, R, Dh, Qhi, ContinuousLinearMap.comp_apply,
      tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      parameterSecondDerivativeHs_apply_ccTensorToHs]
  have h : D (Lhi u) + D f =
      D (scalarHsMul g (n + 1) (by simp) a (Qhi (f₀ + u))) + D b := by
    rw [← D.map_add, heq, D.map_add]
  rw [hmul, hcomm] at h
  simp only [map_add, add_apply] at h
  rw [hfirst] at h
  change D f + (D.comp Lhi - Llo.comp Dh) u =
    m (J a) (Qlo (Dh u)) + m (R (Dh u)) (D a) - Llo (Dh u) +
      (m (J a) (Qlo (Dh f₀)) + m (J (Qhi f₀)) (D a) + D b)
  calc
    _ = D (Lhi u) + D f - Llo (Dh u) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = _ := by rw [h]; abel

section

open MeasureTheory Filter Set
open scoped ENNReal
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem memLp_bilinear_of_bound_left
    {Ω A B C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (m : A →L[ℝ] B →L[ℝ] C) {μ : Measure Ω} {p : ℝ≥0∞}
    {a : Ω → A} {b : Ω → B} (ha : AEStronglyMeasurable a μ)
    (hb : MemLp b p μ) {R : ℝ} (hR : ∀ᵐ t ∂μ, ‖a t‖ ≤ R) :
    MemLp (fun t => m (a t) (b t)) p μ := by
  refine MemLp.of_le_mul (c := ‖m‖ * R) hb
    (m.aestronglyMeasurable_comp₂ ha hb.aestronglyMeasurable) ?_
  filter_upwards [hR] with t ht
  exact (m.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
      (norm_nonneg _))

private theorem memLp_nonlinear_parabolic_forcing
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {m : ℕ} (hm : 1 ≤ m) {T : ℝ}
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (a : ℝ → TensorHs g 0 0 (m : ℝ))
    (ha : AEStronglyMeasurable a (timeMeasure T))
    {C : ℝ} (haC : ∀ᵐ t ∂timeMeasure T, ‖a t‖ ≤ C)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T) :
    MemLp (fun t => WithLp.toLp 2 (fun i : ι =>
      scalarHsMul g m (by simpa using hm) (a t)
        (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i -
          tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (U t i)))
      2 (timeMeasure T) := by
  let mh := scalarHsMul g m (by simpa using hm)
  let Lh := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ)
  have hUi (i : ι) : MemLp (fun t => U t i) 2 (timeMeasure T) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)) i).comp_memLp' (Lp.memLp U)
  have hbi (i : ι) : MemLp (fun t => b t i) 2 (timeMeasure T) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ)) i).comp_memLp' (Lp.memLp b)
  apply MemLp.of_eval_piLp
  intro i
  have hv : MemLp (fun t => parameterSecondDerivativeHs g m (f₀ i + U t i)) 2
      (timeMeasure T) :=
    (parameterSecondDerivativeHs g m).comp_memLp' ((memLp_const (f₀ i)).add (hUi i))
  have hp : MemLp (fun t => mh (a t)
      (parameterSecondDerivativeHs g m (f₀ i + U t i))) 2 (timeMeasure T) :=
    memLp_bilinear_of_bound_left mh ha hv haC
  exact (hp.add (hbi i)).sub (Lh.comp_memLp' (hUi i))

theorem exists_timeL2_parabolic_forcing_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {T : ℝ}
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T)
    (a : ℝ → TensorHs g 0 0 (m : ℝ))
    (ha : AEStronglyMeasurable a (timeMeasure T))
    {C : ℝ} (haC : ∀ᵐ t ∂timeMeasure T, ‖a t‖ ≤ C)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hnm 2)
    let ml := scalarHsMul g n (by simpa using hn)
    let mh := scalarHsMul g m (by simpa using hn.trans hnm)
    let Ll := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
    let Lh := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ)
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      Ll (K (U t i)) + F t i =
        ml (J (a t)) (parameterSecondDerivativeHs g n (K (f₀ i + U t i))) + J (b t i)) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)).compLpL 2 (timeMeasure T) FH = F ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        Lh (U t i) + FH t i =
          mh (a t) (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i := by
  intro J K ml mh Ll Lh heq
  let H := fun t => WithLp.toLp 2 (fun i : ι =>
    mh (a t) (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i - Lh (U t i))
  have hmem : MemLp H 2 (timeMeasure T) :=
    memLp_nonlinear_parabolic_forcing g (hn.trans hnm) f₀ U a ha haC b
  let FH := hmem.toLp H
  have hFH : ∀ᵐ t ∂timeMeasure T, FH t = H t := MemLp.coeFn_toLp hmem
  have hL (v : TensorHs g 0 0 ((m : ℝ) + 2)) : J (Lh v) = Ll (K v) := by
    apply TensorHs.ext
    funext i
    simp only [J, K, Lh, Ll, tensorHsInclusion_coeff_apply, tensorScaleLaplacian_coeff]
  have hQ (v : TensorHs g 0 0 ((m : ℝ) + 2)) :
      J (parameterSecondDerivativeHs g m v) = parameterSecondDerivativeHs g n (K v) :=
    (parameterSecondDerivativeHs_tensorHsInclusion g hnm v).symm
  have hM (v w : TensorHs g 0 0 (m : ℝ)) : J (mh v w) = ml (J v) (J w) :=
    tensorHsInclusion_scalarHsMul g (by simpa using hn) hnm v w
  refine ⟨FH, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [(ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)).coeFn_compLpL FH,
      hFH, heq] with t hj hf he
    rw [hj, hf]
    apply PiLp.ext
    intro i
    change J (mh (a t) (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i -
      Lh (U t i)) = F t i
    rw [J.map_sub, J.map_add, hM, hQ, hL]
    exact (eq_sub_of_add_eq' (he i)).symm
  · filter_upwards [hFH] with t ht
    intro i
    rw [ht]
    change Lh (U t i) +
      (mh (a t) (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i - Lh (U t i)) = _
    abel

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

theorem exists_timeL2_parabolic_forcing_lift_of_continuousOn
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {T : ℝ} (hT : 0 < T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T)
    (a : ℝ → TensorHs g 0 0 (m : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ)))
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hnm 2)
    let ml := scalarHsMul g n (by simpa using hn)
    let mh := scalarHsMul g m (by simpa using hn.trans hnm)
    let Ll := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
    let Lh := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ)
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K)).compLpL 2 (timeMeasure T) U =
      maximalRegularityDuhamelVectorField hT 0 F →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      Ll (K (U t i)) + F t i =
        ml (J (a t)) (parameterSecondDerivativeHs g n (K (f₀ i + U t i))) + J (b t i)) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)).compLpL 2 (timeMeasure T) FH = F ∧
      U = maximalRegularityDuhamelVectorField hT 0 FH ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        Lh (U t i) + FH t i =
          mh (a t) (parameterSecondDerivativeHs g m (f₀ i + U t i)) + b t i := by
  intro J K ml mh Ll Lh hU heq
  have hbm : MemLp b 2 (timeMeasure T) := memLp_of_continuousOn hb
  let B := hbm.toLp b
  have hB : ∀ᵐ t ∂timeMeasure T, B t = b t := MemLp.coeFn_toLp hbm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have haC : ∀ᵐ t ∂timeMeasure T, ‖a t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hC t ht
  have heqB : ∀ᵐ t ∂timeMeasure T, ∀ i,
      Ll (K (U t i)) + F t i =
        ml (J (a t)) (parameterSecondDerivativeHs g n (K (f₀ i + U t i))) + J (B t i) := by
    filter_upwards [heq, hB] with t ht hb
    rw [hb]
    exact ht
  obtain ⟨FH, hFH, hhigh⟩ := exists_timeL2_parabolic_forcing_lift g hn hnm f₀ U F a
    (ha.aestronglyMeasurable measurableSet_Icc) haC B heqB
  refine ⟨FH, hFH, ?_, ?_⟩
  · apply eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm) hT
      (tensorResolventL2_isCompactOperator g 0 0) 0 F FH U hFH
    simpa only [map_zero] using hU
  · filter_upwards [hhigh, hB] with t ht hb
    rw [hb] at ht
    exact ht

end

end AddCircle


open MeasureTheory Filter Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem compLpL_add_apply_ae
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {T : ℝ}
    (A : X →L[ℝ] Z) (B : Y →L[ℝ] Z) (F : timeL2 X T) (U : timeL2 Y T) :
    ∀ᵐ t ∂timeMeasure T,
      (A.compLpL 2 (timeMeasure T) F + B.compLpL 2 (timeMeasure T) U) t =
        A (F t) + B (U t) := by
  filter_upwards [Lp.coeFn_add (A.compLpL 2 (timeMeasure T) F)
    (B.compLpL 2 (timeMeasure T) U), A.coeFn_compLpL F, B.coeFn_compLpL U]
    with t ha hA hB
  rw [ha, Pi.add_apply, hA, hB]

private theorem parameterDerivativeDuhamelForcing_apply_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let D : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ)))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ)))) :=
      (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) :=
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let L₁ : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ)))) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ))
    let L₀ : (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ)))) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
      parameterDerivativeDuhamelForcing g n hT F
    ∀ᵐ t ∂timeMeasure T, G t =
      D (F t) + (D.comp L₁ - L₀.comp Dh) (U t) := by
  intro D Dh U L₁ L₀ G
  unfold G parameterDerivativeDuhamelForcing
  exact compLpL_add_apply_ae D (D.comp L₁ - L₀.comp Dh) F U

private theorem parameterDerivative_duhamel_vector_field_apply_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let Dh : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) :=
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
      parameterDerivativeDuhamelForcing g n hT F
    let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
        (a := (n : ℝ)) hT 0 G
    ∀ᵐ t ∂timeMeasure T, Dh (U t) = V t := by
  intro Dh U G V
  have hV : Dh.compLpL 2 (timeMeasure T) U = V :=
    (parameterDerivative_duhamel_vector_eq g n hT F).1
  have h := Dh.coeFn_compLpL U
  rw [hV] at h
  exact h.symm

theorem parameterDerivativeDuhamelForcing_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) :
    let Z : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 0 :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let Q₁ := AddCircle.parameterSecondDerivativeHs g 1
    let L₁ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T :=
      parameterDerivativeDuhamelForcing g 0 hT F
    let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      L₁ (U t i) + F t i = scalarHsMul g 1 (by norm_num) (a t) (Q₁ (f₀ i + U t i)) + b t i) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      Z (G t i) = AddCircle.parameterDerivativeParabolicForcing g (a t) (b t i) (f₀ i) (V t i) := by
  intro Z Q₁ L₁ U G V heq
  let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
  let Dv : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) := (AddCircle.parameterDerivativeHsPi (ι := ι) g 0).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ))))
  let Dhv : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ)))).comp
    ((AddCircle.parameterDerivativeHsPi g 2).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))))
  let L₁v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) := ContinuousLinearMap.piLpMap 2 (fun _ : ι => L₁)
  let L₀v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) := ContinuousLinearMap.piLpMap 2 (fun _ : ι => L₀)
  have hVa : ∀ᵐ t ∂timeMeasure T, Dhv (U t) = V t :=
    parameterDerivative_duhamel_vector_field_apply_ae g 0 hT F
  have hG : ∀ᵐ t ∂timeMeasure T,
      G t = Dv (F t) + (Dv.comp L₁v - L₀v.comp Dhv) (U t) :=
    parameterDerivativeDuhamelForcing_apply_ae g 0 hT F
  filter_upwards [heq, hG, hVa] with t ht hgt hvt
  intro i
  have hvti : Dhv (U t) i = V t i := congrArg (fun v => v i) hvt
  rw [hgt, ← hvti]
  exact AddCircle.parameterDerivative_parabolic_equation g (f₀ i) (U t i) (a t) (b t i)
    (F t i) (ht i)

theorem parameterDerivativeDuhamelForcing_ae_eq_of_one_le
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)))
    (a : ℝ → TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) :
    let Qhi := AddCircle.parameterSecondDerivativeHs g (n + 1)
    let Lhi := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ)
    let U := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let G := parameterDerivativeDuhamelForcing g n hT F
    let V := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := (n : ℝ)) hT 0 G
    (∀ᵐ t ∂timeMeasure T, ∀ i, Lhi (U t i) + F t i =
      scalarHsMul g (n + 1) (by simp) (a t) (Qhi (f₀ i + U t i)) + b t i) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      G t i = AddCircle.parameterDerivativeParabolicForcingHs g n hn
        (a t) (b t i) (f₀ i) (V t i) := by
  intro Qhi Lhi U G V heq
  let D := (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)))
  let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num))).comp
    ((AddCircle.parameterDerivativeHsPi g (n + 2)).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
        (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by push_cast; linarith))))
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Lhi)
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
  let K := D.comp Lh - Ll.comp Dh
  have hVa : ∀ᵐ t ∂timeMeasure T, Dh (U t) = V t :=
    parameterDerivative_duhamel_vector_field_apply_ae g n hT F
  have hG : ∀ᵐ t ∂timeMeasure T, G t = D (F t) + K (U t) :=
    parameterDerivativeDuhamelForcing_apply_ae g n hT F
  filter_upwards [heq, hG, hVa] with t ht hgt hvt
  intro i
  have hvti : Dh (U t) i = V t i := congrArg (fun v => v i) hvt
  rw [hgt, ← hvti]
  exact AddCircle.parameterDerivative_parabolic_equation_of_one_le g hn
    (f₀ i) (U t i) (a t) (b t i) (F t i) (ht i)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
