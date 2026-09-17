import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleMultiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.MultiplicationInclusion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open scoped Manifold ContDiff
namespace AddCircle
open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

section
open scoped BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

theorem iteratedParameterDerivativeHs_scalarHsMul_succ
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (u v : TensorHs g 0 0 ((n + (k + 1) : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g (n + k)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + k : ℕ) : ℝ) + 1 ≤ ((n + (k + 1) : ℕ) : ℝ)))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast Nat.le_succ (n + k) :
        ((n + k : ℕ) : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ))
    let M := scalarHsMul g (n + k) (by simpa using (show 1 ≤ n + k by omega))
    iteratedParameterDerivativeHs g n (k + 1)
        (scalarHsMul g (n + (k + 1))
          (by simpa using (show 1 ≤ n + (k + 1) by omega)) u v) =
      iteratedParameterDerivativeHs g n k (M (J u) (D v)) +
        iteratedParameterDerivativeHs g n k (M (J v) (D u)) := by
  intro D J M
  have h := parameterDerivativeHs_scalarHsMul_of_one_le g
    (show 1 ≤ n + k by omega) u v
  change D (scalarHsMul g (n + (k + 1))
          (by simpa using (show 1 ≤ n + (k + 1) by omega)) u v) =
    M (J u) (D v) + M (J v) (D u) at h
  change iteratedParameterDerivativeHs g n k
    (D (scalarHsMul g (n + (k + 1))
          (by simpa using (show 1 ≤ n + (k + 1) by omega)) u v)) = _
  rw [h, map_add]


private theorem scalarH1ToContinuous_inclusion_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (u v : TensorHs g 0 0 (n : ℝ))
    (x : AddCircle (1 : ℝ)) :
    scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ))
          (scalarHsMul g n (by simpa using hn) u v)) x =
      scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) u) x *
      scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) v) x := by
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast hn : ((1 : ℕ) : ℝ) ≤ (n : ℝ))
  let E₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have hmul : J (scalarHsMul g n (by simpa using hn) u v) =
      scalarHsMul g 1 (by norm_num) (J u) (J v) :=
    tensorHsInclusion_scalarHsMul g
      (by norm_num : Module.finrank ℝ ℝ / 2 + 1 ≤ 1) hn u v
  have hprod := congrArg (fun w => scalarH1ToContinuous g (E₁ w) x) hmul
  have heval := scalarH1ToContinuous_scalarHsMul g (J u) (J v) x
  have h := hprod.trans heval
  simpa only [J, E₁, ← tensorHsInclusion_trans_apply] using h

theorem iteratedParameterDerivativeHs_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (u v : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) :
    let jet := fun (j : ℕ) (hj : j ≤ k) =>
      (iteratedParameterDerivativeHs g n j).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast Nat.add_le_add_left hj n :
            ((n + j : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ)))
    iteratedParameterDerivativeHs g n k
        (scalarHsMul g (n + k) (by simpa using (show 1 ≤ n + k by omega)) u v) =
      ∑ j : Fin (k + 1), (k.choose (j : ℕ) : ℝ) •
        scalarHsMul g n (by simpa using hn)
          (jet j.val (by omega) u) (jet (k - j.val) (Nat.sub_le _ _) v) := by
  classical
  intro jet
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)))
  let F := fun (w : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) (x : ℝ) =>
    scalarH1ToContinuous g (tensorHsInclusion
      (by exact_mod_cast (show 1 ≤ n + k by omega) :
        (1 : ℝ) ≤ ((n + k : ℕ) : ℝ)) w) (x : AddCircle (1 : ℝ))
  have hreg (w : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) : ContDiff ℝ k (F w) := by
    have h := contDiff_scalarH1ToContinuous g k (tensorHsInclusion
      (by push_cast; exact_mod_cast (show k + 1 ≤ n + k by omega) :
        (k : ℝ) + 1 ≤ ((n + k : ℕ) : ℝ)) w)
    simpa only [F, ← tensorHsInclusion_trans_apply] using h
  have hjet (j : ℕ) (hj : j ≤ k)
      (w : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) (x : ℝ) :
      C (jet j hj w) (x : AddCircle (1 : ℝ)) = iteratedDeriv j (F w) x := by
    have h := congrFun (scalarH1ToContinuous_iteratedParameterDerivativeHs g hn j
      (tensorHsInclusion (by exact_mod_cast Nat.add_le_add_left hj n :
        ((n + j : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ)) w)) x
    simpa only [jet, C, F, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using h
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ))
  apply scalarH1ToContinuous_injective g
  ext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  let E := (ContinuousMap.evalCLM ℝ (x : AddCircle (1 : ℝ))).comp C
  change E (iteratedParameterDerivativeHs g n k
    (scalarHsMul g (n + k) (by simpa using (show 1 ≤ n + k by omega)) u v)) = E _
  have hprod : F (scalarHsMul g (n + k)
      (by simpa using (show 1 ≤ n + k by omega)) u v) = F u * F v := by
    funext t
    exact scalarH1ToContinuous_inclusion_scalarHsMul g (by omega) u v t
  have hleft := congrFun (scalarH1ToContinuous_iteratedParameterDerivativeHs g hn k
    (scalarHsMul g (n + k) (by simpa using (show 1 ≤ n + k by omega)) u v)) x
  change E (iteratedParameterDerivativeHs g n k _) =
    iteratedDeriv k (F (scalarHsMul g (n + k)
      (by simpa using (show 1 ≤ n + k by omega)) u v)) x at hleft
  rw [hprod] at hleft
  rw [hleft, map_sum]
  rw [iteratedDeriv_mul (hreg u).contDiffAt (hreg v).contDiffAt,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val ≤ k := by omega
  rw [map_smul]
  change _ = (k.choose (j : ℕ) : ℝ) *
    C (scalarHsMul g n (by simpa using hn)
      (jet j.val hj u) (jet (k - j.val) (Nat.sub_le _ _) v)) x
  rw [show C (scalarHsMul g n (by simpa using hn)
        (jet j.val hj u) (jet (k - j.val) (Nat.sub_le _ _) v)) x =
      C (jet j.val hj u) x * C (jet (k - j.val) (Nat.sub_le _ _) v) x from
        scalarH1ToContinuous_inclusion_scalarHsMul g hn _ _ _]
  rw [hjet j.val hj u x, hjet (k - j.val) (Nat.sub_le _ _) v x]
  ring

end

section
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private def precompBilinear
    {A B C X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : A →L[ℝ] B →L[ℝ] C) (L : X →L[ℝ] A) (R : Y →L[ℝ] B) :
    X →L[ℝ] Y →L[ℝ] C :=
  ((ContinuousLinearMap.precompR Y M).flip R).comp L

private def postcompBilinear
    {A B C X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : A →L[ℝ] B →L[ℝ] C) (L : C →L[ℝ] X) :
    A →L[ℝ] B →L[ℝ] X :=
  (ContinuousLinearMap.compL ℝ B C X L).comp M

def iteratedParameterDerivativeMulRemainderCcTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ℕ → SmoothCcTensor g 0 0 → SmoothCcTensor g 0 0 → SmoothCcTensor g 0 0
  | 0, S, T =>
      ccOperatorFieldComp g 0 0 0
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) T
  | k + 1, S, T =>
      parameterDerivativeCcTensor g (iteratedParameterDerivativeMulRemainderCcTensor g k S T) +
        ((k + 2 : ℕ) : ℝ) • ccOperatorFieldComp g 0 0 0
          (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S))
          ((parameterDerivativeCcTensor g)^[k + 1] T)

def iteratedParameterDerivativeMulRemainderHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    (n : ℕ) → 1 ≤ n → (k : ℕ) →
      TensorHs g 0 0 ((n + k + 2 : ℕ) : ℝ) →L[ℝ]
        TensorHs g 0 0 ((n + k : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 (n : ℝ)
  | n, hn, 0 =>
      (scalarHsMul g n (by simpa using hn)).comp (iteratedParameterDerivativeHs g n 2)
  | n, hn, k + 1 =>
      let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + 1 + k + 2 : ℕ) : ℝ) ≤ ((n + (k + 1) + 2 : ℕ) : ℝ))
      let R := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + 1 + k : ℕ) : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ))
      let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show n + 2 ≤ n + (k + 1) + 2 by omega) :
          ((n + 2 : ℕ) : ℝ) ≤ ((n + (k + 1) + 2 : ℕ) : ℝ))
      postcompBilinear
        (precompBilinear
          (iteratedParameterDerivativeMulRemainderHs g (n + 1) (by omega) k) L R)
        (iteratedParameterDerivativeHs g n 1) +
      ((k + 2 : ℕ) : ℝ) •
        precompBilinear (scalarHsMul g n (by simpa using hn))
          ((iteratedParameterDerivativeHs g n 2).comp J)
          (iteratedParameterDerivativeHs g n (k + 1))

theorem iteratedParameterDerivativeMulRemainderHs_zero_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (a : TensorHs g 0 0 ((n + 2 : ℕ) : ℝ)) (w : TensorHs g 0 0 (n : ℝ)) :
    iteratedParameterDerivativeMulRemainderHs g n hn 0 a w =
      scalarHsMul g n (by simpa using hn) (iteratedParameterDerivativeHs g n 2 a) w := rfl

theorem iteratedParameterDerivativeMulRemainderHs_succ_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (a : TensorHs g 0 0 ((n + (k + 1) + 2 : ℕ) : ℝ))
    (w : TensorHs g 0 0 ((n + (k + 1) : ℕ) : ℝ)) :
    iteratedParameterDerivativeMulRemainderHs g n hn (k + 1) a w =
      iteratedParameterDerivativeHs g n 1
        (iteratedParameterDerivativeMulRemainderHs g (n + 1) (by omega) k
          (tensorHsInclusion (by push_cast; linarith :
            ((n + 1 + k + 2 : ℕ) : ℝ) ≤ ((n + (k + 1) + 2 : ℕ) : ℝ)) a)
          (tensorHsInclusion (by push_cast; linarith :
            ((n + 1 + k : ℕ) : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ)) w)) +
      ((k + 2 : ℕ) : ℝ) • scalarHsMul g n (by simpa using hn)
        (iteratedParameterDerivativeHs g n 2
          (tensorHsInclusion
            (by exact_mod_cast (show n + 2 ≤ n + (k + 1) + 2 by omega) :
              ((n + 2 : ℕ) : ℝ) ≤ ((n + (k + 1) + 2 : ℕ) : ℝ)) a))
        (iteratedParameterDerivativeHs g n (k + 1) w) := rfl

theorem iteratedParameterDerivativeMulRemainderHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (S T : SmoothCcTensor g 0 0) :
    iteratedParameterDerivativeMulRemainderHs g n hn k
        (ccTensorToHs g 0 ((n + k + 2 : ℕ) : ℝ) S)
        (ccTensorToHs g 0 ((n + k : ℕ) : ℝ) T) =
      ccTensorToHs g 0 (n : ℝ)
        (iteratedParameterDerivativeMulRemainderCcTensor g k S T) := by
  induction k generalizing n with
  | zero =>
      simp only [Nat.add_zero, iteratedParameterDerivativeMulRemainderHs_zero_apply,
        iteratedParameterDerivativeHs_apply_ccTensorToHs,
        scalarHsMul_apply_ccTensorToHs, iteratedParameterDerivativeMulRemainderCcTensor,
        Function.iterate_succ_apply, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [iteratedParameterDerivativeMulRemainderHs_succ_apply]
      simp only [tensorHsInclusion_ccTensorToHs, ih,
        iteratedParameterDerivativeHs_apply_ccTensorToHs,
        scalarHsMul_apply_ccTensorToHs, iteratedParameterDerivativeMulRemainderCcTensor,
        ccTensorToHs_add, ccTensorToHs_smul,
        Function.iterate_succ_apply, Function.iterate_zero, id_eq]

theorem norm_iteratedParameterDerivativeMulRemainderHs_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (a : TensorHs g 0 0 ((n + k + 2 : ℕ) : ℝ))
    (w : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) :
    ‖iteratedParameterDerivativeMulRemainderHs g n hn k a w‖ ≤
      ‖iteratedParameterDerivativeMulRemainderHs g n hn k‖ * ‖a‖ * ‖w‖ :=
  (iteratedParameterDerivativeMulRemainderHs g n hn k).le_opNorm₂ a w

end

section
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private theorem parameter_derivative_cc_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) :
    parameterDerivativeCcTensor g (S + T) =
      parameterDerivativeCcTensor g S + parameterDerivativeCcTensor g T := by
  simp only [parameterDerivativeCcTensor, covGrad_add,
    ← operatorFieldComposition_zero_eq_operatorFieldApply,
    operatorFieldComposition_add_right]

private theorem parameter_derivative_cc_smul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (c : ℝ) (S : SmoothCcTensor g 0 0) :
    parameterDerivativeCcTensor g (c • S) = c • parameterDerivativeCcTensor g S := by
  simp only [parameterDerivativeCcTensor, covGrad_smul,
    ← operatorFieldComposition_zero_eq_operatorFieldApply,
    operatorFieldComposition_smul_right]

private theorem scalar0_operator_comp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
    TensorRSField.scalar0 (ccOperatorFieldComp g 0 0 0 S T).toSection x =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  let f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  rw [← hS, operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc,
    scalar0_smul_cc, scalar0_scalarCc]

theorem iteratedParameterDerivativeMulRemainderCcTensor_add_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (S T : SmoothCcTensor g 0 0) :
    iteratedParameterDerivativeMulRemainderCcTensor g k S T +
        ccOperatorFieldComp g 0 0 0 S ((parameterDerivativeCcTensor g)^[k + 2] T) +
        ((k + 2 : ℕ) : ℝ) • ccOperatorFieldComp g 0 0 0
          (parameterDerivativeCcTensor g S) ((parameterDerivativeCcTensor g)^[k + 1] T) =
      (parameterDerivativeCcTensor g)^[k + 2] (ccOperatorFieldComp g 0 0 0 S T) := by
  induction k with
  | zero =>
      simp only [iteratedParameterDerivativeMulRemainderCcTensor,
        Nat.zero_add, Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp only [parameterDerivativeCcTensor_ccOperatorFieldComp,
        parameter_derivative_cc_add]
      apply SmoothCcTensor.ext_scalar0
      funext x
      simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
        TensorRSField.scalar0_add, TensorRSField.scalar0_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, scalar0_operator_comp]
      ring
  | succ k ih =>
      change parameterDerivativeCcTensor g
          (iteratedParameterDerivativeMulRemainderCcTensor g k S T) +
          ((k + 2 : ℕ) : ℝ) • ccOperatorFieldComp g 0 0 0
            (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S))
            ((parameterDerivativeCcTensor g)^[k + 1] T) +
          ccOperatorFieldComp g 0 0 0 S ((parameterDerivativeCcTensor g)^[k + 1 + 2] T) +
          ((k + 1 + 2 : ℕ) : ℝ) • ccOperatorFieldComp g 0 0 0
            (parameterDerivativeCcTensor g S)
            ((parameterDerivativeCcTensor g)^[k + 1 + 1] T) = _
      calc
        _ = parameterDerivativeCcTensor g
            (iteratedParameterDerivativeMulRemainderCcTensor g k S T +
              ccOperatorFieldComp g 0 0 0 S
                ((parameterDerivativeCcTensor g)^[k + 2] T) +
              ((k + 2 : ℕ) : ℝ) • ccOperatorFieldComp g 0 0 0
                (parameterDerivativeCcTensor g S)
                ((parameterDerivativeCcTensor g)^[k + 1] T)) := by
          have hnext : (parameterDerivativeCcTensor g)^[k + 1 + 2] T =
              parameterDerivativeCcTensor g ((parameterDerivativeCcTensor g)^[k + 2] T) :=
            Function.iterate_succ_apply' (parameterDerivativeCcTensor g) (k + 2) T
          have hmid : (parameterDerivativeCcTensor g)^[k + 1 + 1] T =
              parameterDerivativeCcTensor g ((parameterDerivativeCcTensor g)^[k + 1] T) :=
            Function.iterate_succ_apply' (parameterDerivativeCcTensor g) (k + 1) T
          simp only [hnext, hmid, parameter_derivative_cc_add, parameter_derivative_cc_smul,
            parameterDerivativeCcTensor_ccOperatorFieldComp]
          apply SmoothCcTensor.ext_scalar0
          funext x
          simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
            TensorRSField.scalar0_add, TensorRSField.scalar0_smul, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, scalar0_operator_comp]
          push_cast
          ring
        _ = parameterDerivativeCcTensor g
            ((parameterDerivativeCcTensor g)^[k + 2] (ccOperatorFieldComp g 0 0 0 S T)) :=
          congrArg (parameterDerivativeCcTensor g) ih
        _ = (parameterDerivativeCcTensor g)^[k + 1 + 2]
            (ccOperatorFieldComp g 0 0 0 S T) :=
          (Function.iterate_succ_apply' (parameterDerivativeCcTensor g) (k + 2)
            (ccOperatorFieldComp g 0 0 0 S T)).symm

end

section
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

theorem iteratedParameterDerivativeMulRemainderHs_add_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (a w : TensorHs g 0 0 ((n + k + 2 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show n ≤ n + k + 2 by omega) :
        (n : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ))
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show n + k ≤ n + k + 2 by omega) :
        ((n + k : ℕ) : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ))
    let D := (iteratedParameterDerivativeHs g n 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show n + 1 ≤ n + k + 2 by omega) :
          ((n + 1 : ℕ) : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ)))
    let Dk := (iteratedParameterDerivativeHs g n (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show n + (k + 1) ≤ n + k + 2 by omega) :
          ((n + (k + 1) : ℕ) : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ)))
    let Dk₂ := (iteratedParameterDerivativeHs g n (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show n + (k + 2) ≤ n + k + 2 by omega) :
          ((n + (k + 2) : ℕ) : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ)))
    let m := scalarHsMul g n (by simpa using hn)
    iteratedParameterDerivativeMulRemainderHs g n hn k a (K w) +
      m (J a) (Dk₂ w) + ((k + 2 : ℕ) : ℝ) • m (D a) (Dk w) =
      Dk₂ (scalarHsMul g (n + k + 2) (by simp) a w) := by
  intro J K D Dk Dk₂ m
  let R := iteratedParameterDerivativeMulRemainderHs g n hn k
  let M := scalarHsMul g (n + k + 2) (by simp)
  change R a (K w) + m (J a) (Dk₂ w) +
    ((k + 2 : ℕ) : ℝ) • m (D a) (Dk w) = Dk₂ (M a w)
  refine (ccToHsLin_dense g 0
    (by positivity : (0 : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ))).induction_on a ?_ ?_
  · apply isClosed_eq
    · exact ((R.continuous.clm_apply continuous_const).add
        ((m.continuous.comp J.continuous).clm_apply continuous_const)).add
          (((m.continuous.comp D.continuous).clm_apply continuous_const).const_smul
            ((k + 2 : ℕ) : ℝ))
    · exact Dk₂.continuous.comp (M.continuous.clm_apply continuous_const)
  intro S
  refine (ccToHsLin_dense g 0
    (by positivity : (0 : ℝ) ≤ ((n + k + 2 : ℕ) : ℝ))).induction_on w ?_ ?_
  · apply isClosed_eq
    · exact (((R _).continuous.comp K.continuous).add
        ((m (J _)).continuous.comp Dk₂.continuous)).add
          (((m (D _)).continuous.comp Dk.continuous).const_smul ((k + 2 : ℕ) : ℝ))
    · exact Dk₂.continuous.comp (M _).continuous
  intro T
  simp only [J, K, D, Dk, Dk₂, R, M, m, ccToHsLin_apply,
    ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
    iteratedParameterDerivativeMulRemainderHs_apply_ccTensorToHs,
    iteratedParameterDerivativeHs_apply_ccTensorToHs, scalarHsMul_apply_ccTensorToHs,
    Function.iterate_succ_apply, Function.iterate_zero, id_eq]
  have h := congrArg (ccToHsLin g 0 (n : ℝ))
    (iteratedParameterDerivativeMulRemainderCcTensor_add_eq g k S T)
  simpa only [map_add, map_smul, ccToHsLin_apply,
    Function.iterate_succ_apply, Function.iterate_zero, id_eq] using h

end

section
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private theorem scalarH0ContinuousMul_smooth_product
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) :
    scalarH0ContinuousMul g (scalarH1ToContinuous g (ccTensorToHs g 0 1 S))
        (ccTensorToHs g 0 0 T) =
      ccTensorToHs g 0 0 (ccOperatorFieldComp g 0 0 0 S T) := by
  have h := tensorHsInclusion_scalarHsMul_zero g
    (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S) (ccTensorToHs g 0 ((1 : ℕ) : ℝ) T)
  dsimp only at h
  simp only [scalarHsMul_apply_ccTensorToHs, ContinuousLinearMap.comp_apply,
    tensorHsInclusion_ccTensorToHs] at h
  exact h.symm

theorem iteratedParameterDerivativeHs_scalarHsMul_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (a : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (w : TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) :
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Rw := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
        ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let M := scalarHsMul g (k + 2) (by simp)
    let R := iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
    let m₀ := scalarH0ContinuousMul g
    D (M (J a) w) =
      Z (R (Ra a) (Rw w)) + m₀ (C (A a)) (D w) +
        ((k + 2 : ℕ) : ℝ) • m₀ (C (A₁ a)) (Z (W₁ w)) := by
  intro E₀ D J Ra Rw A A₁ W₁ Z C M R m₀
  refine (ccToHsLin_dense g 0 (by positivity :
    (0 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))).induction_on a ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp
        ((M.continuous.comp J.continuous).clm_apply continuous_const)
    · exact ((Z.continuous.comp
        ((R.continuous.comp Ra.continuous).clm_apply continuous_const)).add
          ((m₀.continuous.comp (C.continuous.comp A.continuous)).clm_apply
            continuous_const)).add
        (((m₀.continuous.comp (C.continuous.comp A₁.continuous)).clm_apply
          continuous_const).const_smul ((k + 2 : ℕ) : ℝ))
  intro S
  refine (ccToHsLin_dense g 0 (by positivity :
    (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ))).induction_on w ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp
        (M (J (ccToHsLin g 0 ((k + 3 : ℕ) : ℝ) S))).continuous
    · exact ((Z.continuous.comp
        ((R (Ra (ccToHsLin g 0 ((k + 3 : ℕ) : ℝ) S))).continuous.comp
          Rw.continuous)).add
        ((m₀ (C (A (ccToHsLin g 0 ((k + 3 : ℕ) : ℝ) S)))).continuous.comp
          D.continuous)).add
        (((m₀ (C (A₁ (ccToHsLin g 0 ((k + 3 : ℕ) : ℝ) S)))).continuous.comp
          (Z.continuous.comp W₁.continuous)).const_smul ((k + 2 : ℕ) : ℝ))
  intro T
  simp only [ccToHsLin_apply, E₀, D, J, Ra, Rw, A, A₁, W₁, Z, C, M, R, m₀,
    ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
    scalarHsMul_apply_ccTensorToHs, iteratedParameterDerivativeHs_apply_ccTensorToHs,
    iteratedParameterDerivativeMulRemainderHs_apply_ccTensorToHs,
    Function.iterate_one, scalarH0ContinuousMul_smooth_product]
  have h := congrArg (ccTensorToHs g 0 (0 : ℝ))
    (iteratedParameterDerivativeMulRemainderCcTensor_add_eq g k S T)
  simp only [ccTensorToHs_add, ccTensorToHs_smul] at h
  exact h.symm

end

end AddCircle
