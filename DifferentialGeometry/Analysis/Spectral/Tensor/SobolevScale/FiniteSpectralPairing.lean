import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Elliptic

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem cc_iter_coeff
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (U : SmoothCcTensor g 0 s)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
        (SmoothCcTensor.toL2
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U)) i =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ n *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (SmoothCcTensor.toL2 U) i := by
  induction n with
  | zero => simp only [oneMinusConnLapSmoothIter_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        oneMinus_coeff (I := I) (M := M) g s
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U) i,
        ih, pow_succ]
      ring

omit [BoundarylessManifold I M] in
theorem cc_l2_pair_tsum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 s A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 s,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
            (SmoothCcTensor.toL2 B) i := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s
  let b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc
  have hinner : tensorL2Inner (I := I) (M := M) g 0 s A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner]
  have hparseval := b.tsum_inner_mul_inner
    (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← hparseval]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) hc,
    tensorL2Coeff_eq_inner (I := I) (M := M) hc]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) =
      ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from real_inner_comm _ _]

theorem cc_pair_tsum
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (U A : SmoothCcTensor g 0 s) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s,
        tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 U) i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n U).toFun A.toFun := by
  classical
  rw [cc_l2_pair_tsum (I := I) (M := M) g s
    (oneMinusConnLapSmoothIter (I := I) g 0 s n U) A]
  refine tsum_congr (fun i => ?_)
  rw [cc_iter_coeff (I := I) (M := M) g s n U i]
  have hweight :
      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) =
        (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring

theorem cc_pair_tsum_split
    (g : SmoothRiemannianMetric I M) (s a b : ℕ)
    (U A : SmoothCcTensor g 0 s) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s,
        tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 U) i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s b U).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 s a A).toFun := by
  classical
  rw [cc_l2_pair_tsum (I := I) (M := M) g s
    (oneMinusConnLapSmoothIter (I := I) g 0 s b U)
    (oneMinusConnLapSmoothIter (I := I) g 0 s a A)]
  refine tsum_congr (fun i => ?_)
  rw [cc_iter_coeff (I := I) (M := M) g s b U i,
    cc_iter_coeff (I := I) (M := M) g s a A i]
  have hweight :
      tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) =
        (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ (a + b) := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight, pow_add]
  ring

theorem finite_pair_split
    (g : SmoothRiemannianMetric I M)
    (F : Finset
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2))
    (c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2 → ℝ)
    (A : SmoothCcTensor g 0 2) (a b : ℕ) :
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
        (c i * tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 b
          (finiteEigenCombo (I := I) (M := M) g F c)).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 a A).toFun := by
  classical
  have hcoeff
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2) :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (finiteEigenCombo (I := I) (M := M) g F c)) i =
        (if i ∈ F then c i else 0) := by
    rw [SmoothCcTensor.toL2_apply]
    exact finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i
  have hzero : ∀ i ∉ F,
      tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2
                (finiteEigenCombo (I := I) (M := M) g F c)) i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2 A) i) = 0 := by
    intro i hi
    rw [hcoeff i, if_neg hi, zero_mul, mul_zero]
  calc
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
          (c i * tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 A) i) =
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2
                (finiteEigenCombo (I := I) (M := M) g F c)) i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2 A) i) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hcoeff i, if_pos hi]
    _ = ∑' i,
          tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (SmoothCcTensor.toL2
                  (finiteEigenCombo (I := I) (M := M) g F c)) i *
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (SmoothCcTensor.toL2 A) i) := (tsum_eq_sum hzero).symm
    _ = _ := cc_pair_tsum_split (I := I) (M := M) g 2 a b
      (finiteEigenCombo (I := I) (M := M) g F c) A

omit [CompactSpace M] [I.Boundaryless] in
private theorem connIter_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (theta : ℝ)
    (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s k (theta • T) =
      theta • oneMinusConnLapSmoothIter (I := I) g r s k T := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ, ih, oneMinusConnLapSmoothIter_succ]
      unfold oneMinusConnLapSmooth
      have hraw :
          rawTensorConnLapSmooth (I := I) g r s
              (theta • oneMinusConnLapSmoothIter (I := I) g r s k T) =
            theta • rawTensorConnLapSmooth (I := I) g r s
              (oneMinusConnLapSmoothIter (I := I) g r s k T) := by
        change rawConnLapLin (I := I) g r s
              (theta • oneMinusConnLapSmoothIter (I := I) g r s k T) =
            theta • rawConnLapLin (I := I) g r s
              (oneMinusConnLapSmoothIter (I := I) g r s k T)
        exact map_smul (rawConnLapLin (I := I) g r s) theta
          (oneMinusConnLapSmoothIter (I := I) g r s k T)
      rw [hraw, smul_sub]

private theorem connIter_symmS
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2) :
    oneMinusConnLapSmoothIter (I := I) g 0 2 k
        (symmS (I := I) (M := M) g T) =
      symmS (I := I) (M := M) g
        (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
      have hraw :
          rawTensorConnLapSmooth (I := I) g 0 2
              (symmS (I := I) (M := M) g
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) =
            symmS (I := I) (M := M) g
              (rawTensorConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) := by
        unfold symmS ccTensor02Symm
        have hsmul :
            rawTensorConnLapSmooth (I := I) g 0 2
                ((1 / 2 : ℝ) •
                  (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                      (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))) =
              (1 / 2 : ℝ) • rawTensorConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) := by
          change rawConnLapLin (I := I) g 0 2
                ((1 / 2 : ℝ) •
                  (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                      (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))) =
              (1 / 2 : ℝ) • rawConnLapLin (I := I) g 0 2
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))
          exact map_smul (rawConnLapLin (I := I) g 0 2) (1 / 2 : ℝ) _
        have hadd :
            rawTensorConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) =
              rawTensorConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) +
                rawTensorConnLapSmooth (I := I) g 0 2
                  (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) := by
          change rawConnLapLin (I := I) g 0 2
                (oneMinusConnLapSmoothIter (I := I) g 0 2 k T +
                  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) =
              rawConnLapLin (I := I) g 0 2
                  (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) +
                rawConnLapLin (I := I) g 0 2
                  (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                    (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))
          exact map_add (rawConnLapLin (I := I) g 0 2) _ _
        rw [hsmul, hadd,
          rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g
            (Equiv.swap (0 : Fin 2) 1)]
      rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ, ih]
      unfold oneMinusConnLapSmooth
      rw [hraw]
      exact (symmS_sub (I := I) (M := M) g _ _).symm

theorem finite_symm_scale
    (g : SmoothRiemannianMetric I M)
    (F : Finset
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2))
    (c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2 → ℝ)
    (A : SmoothCcTensor g 0 2) (a b : ℕ) (theta : ℝ)
    (hA : symmS (I := I) (M := M) g A = A) :
    theta * (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (((a + b : ℕ) : ℝ)) *
          (c i * tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 A) i)) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 b
          (theta • symmS (I := I) (M := M) g
            (finiteEigenCombo (I := I) (M := M) g F c))).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 a A).toFun := by
  rw [finite_pair_split (I := I) (M := M) g F c A a b]
  have hsymmA :
      symmS (I := I) (M := M) g
          (oneMinusConnLapSmoothIter (I := I) g 0 2 a A) =
        oneMinusConnLapSmoothIter (I := I) g 0 2 a A := by
    rw [← connIter_symmS (I := I) (M := M) g a A, hA]
  have hsymm_pair (S T : SmoothCcTensor g 0 2) :
      tensorL2Inner (I := I) (M := M) g 0 2
          (symmS (I := I) (M := M) g S).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g 0 2
          S.toFun (symmS (I := I) (M := M) g T).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M),
      ← SmoothCcTensor.inner_def (I := I) (M := M)]
    unfold symmS ccTensor02Symm
    rw [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      inner_domDomCongrSection_swap (I := I) (M := M) g]
  rw [connIter_smul (I := I) (M := M),
    connIter_symmS (I := I) (M := M), SmoothCcTensor.toFun_smul,
    tensorL2Inner_smul_left, hsymm_pair, hsymmA]

theorem finite_repr_norm
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (T : tensorHs (I := I) (M := M) g 0 s 0)
    (hT : (Function.support T.coeff).Finite) :
    ‖ccTensorToHs (I := I) (M := M) g s (m : ℝ)
        (tensorHsSmoothRepr (I := I) (M := M) T hT)‖ ^ 2 =
      ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (T.coeff i) ^ 2 := by
  classical
  let U : SmoothCcTensor g 0 s :=
    tensorHsSmoothRepr (I := I) (M := M) T hT
  have hrepr
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s) :
      (ccTensorToHs (I := I) (M := M) g s (m : ℝ) U).coeff i =
        T.coeff i := by
    rw [ccTensorToHs_coeff, SmoothCcTensor.toL2_apply]
    dsimp only [U]
    rw [tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) T hT,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  rw [tensorHs.norm_sq_eq_tsum]
  change
    (∑' i,
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
        ((ccTensorToHs (I := I) (M := M) g s (m : ℝ) U).coeff i) ^ 2) = _
  calc
    _ = ∑' i,
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (T.coeff i) ^ 2 := by
      apply tsum_congr
      intro i
      rw [hrepr i]
    _ = _ := by
      rw [tsum_eq_sum (s := hT.toFinset)]
      intro i hi
      have hcoeff : T.coeff i = 0 := by
        by_contra hne
        exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
      norm_num [hcoeff]

theorem finite_cc_pair
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (T : tensorHs (I := I) (M := M) g 0 s 0)
    (hT : (Function.support T.coeff).Finite)
    (A : SmoothCcTensor g 0 s) :
    ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (T.coeff i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n
          (tensorHsSmoothRepr (I := I) (M := M) T hT)).toFun A.toFun := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s
  have hrepr
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s) :
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2
            (tensorHsSmoothRepr (I := I) (M := M) T hT)) i = T.coeff i := by
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) T hT,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  have hzero : ∀ i ∉ hT.toFinset,
      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 A) i) = 0 := by
    intro i hi
    have hcoeff : T.coeff i = 0 := by
      by_contra hne
      exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
    rw [hcoeff, zero_mul, mul_zero]
  calc
    ∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 A) i) =
        ∑' i,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 A) i) :=
      (tsum_eq_sum hzero).symm
    _ = tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n
            (tensorHsSmoothRepr (I := I) (M := M) T hT)).toFun A.toFun := by
      simpa only [hrepr] using
        (cc_pair_tsum (I := I) (M := M) g s n
          (tensorHsSmoothRepr (I := I) (M := M) T hT) A)

end DifferentialGeometry.Analysis.Spectral

end
