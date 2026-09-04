import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.AdjointBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.Polarization
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.LpProduct

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private local instance edgePartnerBiTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

private local instance edgePartnerBiTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

private local instance edgePartnerBiTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

private local instance edgePartnerBiTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma edge_app_le (g : SmoothRiemannianMetric I M)
    (r s : Nat) (Phi : SmoothCcTensor g r s)
    (W : SmoothCcTensor g 0 r) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((operatorFieldApply (I := I) (M := M) g r s Phi W).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x (Phi.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  rw [operatorFieldApplication_toSection]
  exact riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 0 r s x (Phi.toSection x) (W.toSection x)

omit [SigmaCompactSpace M] in
private lemma edge_extend2_one (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 5 x
        ((covGrad (I := I) (M := M) g 2 4
          (slotExtendIter (I := I) (M := M) g 0 2 2 T)).toSection x) =
      (Module.finrank Real E : Real) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T).toSection x) := by
  change riemannianFiberNormSq (I := I) (M := M) g 2 5 x
      ((covGrad (I := I) (M := M) g 2 4
        (slotExtend (I := I) (M := M) g 1 3
          (slotExtend (I := I) (M := M) g 0 2 T))).toSection x) = _
  rw [riemannianFiberNormSq_covGrad_slotExtend_scale (I := I) (M := M) g 1 3
    (slotExtend (I := I) (M := M) g 0 2 T) x]
  rw [riemannianFiberNormSq_covGrad_slotExtend_scale (I := I) (M := M) g 0 2 T x]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma edgeRaise_zero_mul (g gm : SmoothRiemannianMetric I M)
    (W P : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g W y v w)
    {delta : Real} (hdelta : delta ≤ 1 / 2) (hdelta0 : 0 ≤ delta)
    (hWbound : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P).toSection x) ≤
      ((2 * (Module.finrank Real E : Real)) ^ 2) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) := by
  let F : Real := (2 * (Module.finrank Real E : Real)) ^ 2
  let S0 : SmoothCcTensor g 0 2 :=
    secondSlotInsertionCoefficient (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 P
  have hS0 := slotInsertionCoefficient_norm_bound (I := I) (M := M) g gm W htie
    hdelta hdelta0 hWbound 0 P x
  have hS0' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (S0.toSection x) ≤ F *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) := by
    simpa only [S0, F] using hS0
  have hR0 := slotInsertionCoefficient_norm_bound (I := I) (M := M) g gm W htie
    hdelta hdelta0 hWbound 1 S0 x
  have hR0' : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      ((secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P).toSection x) ≤
        F * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (S0.toSection x) := by
    simpa only [secondSlotMetricComparisonCoefficient, S0, F] using hR0
  calc
    _ ≤ F * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (S0.toSection x) := hR0'
    _ ≤ F * (F * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (P.toSection x)) := mul_le_mul_of_nonneg_left hS0' (sq_nonneg _)
    _ = _ := by simp only [F]; ring

omit [SigmaCompactSpace M] in
private lemma edgeRaise_one_mul (g : SmoothRiemannianMetric I M) :
    ∃ D : Real, 0 ≤ D ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (W P : SmoothCcTensor g 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2
                (secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P)).toSection x) ≤
            D *
              (riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (P.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                  ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)) := by
  obtain ⟨K, hK0, hK⟩ := slotInsertionCoefficient_covariantDerivative_bound (I := I) (M := M) g
  let F : Real := (2 * (Module.finrank Real E : Real)) ^ 2
  let D : Real := K * (F + K)
  have hF0 : 0 ≤ F := sq_nonneg _
  have hD0 : 0 ≤ D := mul_nonneg hK0 (add_nonneg hF0 hK0)
  refine ⟨D, hD0, ?_⟩
  intro gm W P htie delta hdelta hdelta0 hWbound x
  let S0 : SmoothCcTensor g 0 2 :=
    secondSlotInsertionCoefficient (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 P
  let W1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x)
  let P0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (P.toSection x)
  let P1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
  have hS0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (S0.toSection x) ≤ F * P0 := by
    simpa only [S0, F, P0] using
      slotInsertionCoefficient_norm_bound (I := I) (M := M) g gm W htie
        hdelta hdelta0 hWbound 0 P x
  have hS1 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 S0).toSection x) ≤
        K * (W1 * P0 + P1) := by
    simpa only [S0, W1, P0, P1, iteratedCovGrad_succ,
      iteratedCovGrad_zero] using
      hK gm W htie hdelta hdelta0 hWbound 0 P x
  have hR1 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2
        (secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P)).toSection x) ≤
        K *
          (W1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (S0.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 S0).toSection x)) := by
    simpa only [secondSlotMetricComparisonCoefficient, S0, W1, iteratedCovGrad_succ,
      iteratedCovGrad_zero] using
      hK gm W htie hdelta hdelta0 hWbound 1 S0 x
  have hW10 : 0 ≤ W1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hP00 : 0 ≤ P0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hP10 : 0 ≤ P1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hKF : K ≤ F + K := by linarith
  calc
    _ ≤ K *
        (W1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (S0.toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 S0).toSection x)) := hR1
    _ ≤ K * (W1 * (F * P0) + K * (W1 * P0 + P1)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ hS1) hK0
      exact mul_le_mul_of_nonneg_left hS0 hW10
    _ = K * ((F + K) * (W1 * P0) + K * P1) := by ring
    _ ≤ K * ((F + K) * (W1 * P0) + (F + K) * P1) := by
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hK0
      exact mul_le_mul_of_nonneg_right hKF hP10
    _ = D * (W1 * P0 + P1) := by simp only [D]; ring
    _ = _ := rfl

omit [SigmaCompactSpace M] in
theorem topOrderBilinearPairingCoefficient_uniform_norm_bound :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (g gm : SmoothRiemannianMetric I M)
        (W P V : SmoothCcTensor g 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 4 x
              ((topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma).toSection x) ≤
            C * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (P.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (V.toSection x) := by
  classical
  let d : Real := Module.finrank Real E
  let F : Real := (2 * d) ^ 2
  let C : Real := d ^ 2 * F ^ 2
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg d) (sq_nonneg F)
  refine ⟨C, hC0, ?_⟩
  intro g gm W P V htie delta hdelta hdelta0 hWbound sigma x
  let A : SmoothCcTensor g 0 2 :=
    secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P
  let Phi : SmoothCcTensor g 2 4 :=
    slotExtendIter (I := I) (M := M) g 0 2 2 V
  have hA0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (A.toSection x) ≤ F ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) := by
    simpa only [A, F, d] using
      edgeRaise_zero_mul (I := I) (M := M) g gm W P htie
        hdelta hdelta0 hWbound x
  have hPhi0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (Phi.toSection x) = d ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (V.toSection x) := by
    simpa only [Phi, d] using
      riemannianFiberNormSq_slotExtendIter_eq (I := I) (M := M) g 0 2 2 V x
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g sigma.symm
    (fourTensorProductCoefficient (I := I) (M := M) g A V) 0 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          ((fourTensorProductCoefficient (I := I) (M := M) g A V).toSection x) := by
    simpa only [topOrderBilinearPairingAdjointCoefficient, A, iteratedCovGrad_zero] using hout
  rw [hout']
  refine (edge_app_le (I := I) (M := M) g 2 4 Phi A x).trans ?_
  rw [hPhi0]
  calc
    d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (V.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (A.toSection x) ≤
        d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (V.toSection x) *
          (F ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (P.toSection x)) :=
      mul_le_mul_of_nonneg_left hA0
        (mul_nonneg (sq_nonneg d)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _))
    _ = C * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (V.toSection x) := by simp only [C]; ring

private lemma quadratic_kernel_bound {A : Type*} [AddCommGroup A] [Module Real A]
    (N : A → Real) (Pair : Equiv.Perm (Fin 4) → A) (B : Real)
    (hNadd : ∀ Q R, N (Q + R) ≤ 2 * N Q + 2 * N R)
    (hNsub : ∀ Q R, N (Q - R) ≤ 2 * N Q + 2 * N R)
    (hNsmul : ∀ (a : Real) Q, N (a • Q) = a ^ 2 * N Q)
    (hpair : ∀ sigma, N (Pair sigma) ≤ B)
    (qq : Fin 4 → Equiv.Perm (Fin 4)) :
    N ((1 / 2 : Real) •
        (Pair (qq 0) + Pair (qq 1) - Pair (qq 2) - Pair (qq 3))) ≤ 4 * B := by
  let Q0 := Pair (qq 0)
  let Q1 := Pair (qq 1)
  let Q2 := Pair (qq 2)
  let Q3 := Pair (qq 3)
  have h01 : N (Q0 + Q1) ≤ 4 * B := by
    calc
      N (Q0 + Q1) ≤ 2 * N Q0 + 2 * N Q1 := hNadd Q0 Q1
      _ ≤ 2 * B + 2 * B := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [Q0] using hpair (qq 0)) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [Q1] using hpair (qq 1)) (by norm_num))
      _ = 4 * B := by ring
  have h23 : N (Q2 + Q3) ≤ 4 * B := by
    calc
      N (Q2 + Q3) ≤ 2 * N Q2 + 2 * N Q3 := hNadd Q2 Q3
      _ ≤ 2 * B + 2 * B := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [Q2] using hpair (qq 2)) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [Q3] using hpair (qq 3)) (by norm_num))
      _ = 4 * B := by ring
  have hdiff : N ((Q0 + Q1) - (Q2 + Q3)) ≤ 16 * B := by
    calc
      N ((Q0 + Q1) - (Q2 + Q3)) ≤ 2 * N (Q0 + Q1) + 2 * N (Q2 + Q3) :=
        hNsub _ _
      _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
        (mul_le_mul_of_nonneg_left h01 (by norm_num))
        (mul_le_mul_of_nonneg_left h23 (by norm_num))
      _ = 16 * B := by ring
  have heq : Q0 + Q1 - Q2 - Q3 = (Q0 + Q1) - (Q2 + Q3) := by abel
  change N ((1 / 2 : Real) • (Q0 + Q1 - Q2 - Q3)) ≤ _
  rw [hNsmul, heq]
  norm_num
  linarith

private lemma quadratic_riemannian_part_bound {A : Type*} [AddCommGroup A] [Module Real A]
    (N : A → Real) (Kern : (Fin 4 → Equiv.Perm (Fin 4)) → A) (B s : Real)
    (hNadd : ∀ Q R, N (Q + R) ≤ 2 * N Q + 2 * N R)
    (hNsmul : ∀ (a : Real) Q, N (a • Q) = a ^ 2 * N Q)
    (hkernel : ∀ qq, N (Kern qq) ≤ 4 * B) (hB0 : 0 ≤ B) (hs2 : s ^ 2 ≤ 1)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    N (s • ((1 / 2 : Real) • (Kern qA + Kern qB))) ≤ 4 * B := by
  let KA := Kern qA
  let KB := Kern qB
  have hab : N (KA + KB) ≤ 16 * B := by
    calc
      N (KA + KB) ≤ 2 * N KA + 2 * N KB := hNadd KA KB
      _ ≤ 2 * (4 * B) + 2 * (4 * B) := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [KA] using hkernel qA) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [KB] using hkernel qB) (by norm_num))
      _ = 16 * B := by ring
  change N (s • ((1 / 2 : Real) • (KA + KB))) ≤ _
  rw [hNsmul, hNsmul]
  norm_num
  nlinarith [sq_nonneg s]

private lemma quadratic_lie_term_bound {A : Type*} [AddCommGroup A] [Module Real A]
    (N : A → Real) (Pair : Equiv.Perm (Fin 4) → A) (B : Real)
    (hNadd : ∀ Q R, N (Q + R) ≤ 2 * N Q + 2 * N R)
    (hNsmul : ∀ (a : Real) Q, N (a • Q) = a ^ 2 * N Q)
    (hpair : ∀ sigma, N (Pair sigma) ≤ B)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (hepsilon : ∀ i, |epsilon i| ≤ 1) (hB0 : 0 ≤ B) (i : Fin 3) :
    N (epsilon i • ((1 / 2 : Real) •
        (Pair (q i) + Pair ((q i).trans (Equiv.swap (0 : Fin 4) 1))))) ≤ B := by
  let QA := Pair (q i)
  let QB := Pair ((q i).trans (Equiv.swap (0 : Fin 4) 1))
  have hab : N (QA + QB) ≤ 4 * B := by
    calc
      N (QA + QB) ≤ 2 * N QA + 2 * N QB := hNadd QA QB
      _ ≤ 2 * B + 2 * B := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [QA] using hpair (q i)) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (by simpa only [QB] using hpair ((q i).trans (Equiv.swap (0 : Fin 4) 1)))
          (by norm_num))
      _ = 4 * B := by ring
  have heps2 : (epsilon i) ^ 2 ≤ 1 := by
    have hi := abs_le.mp (hepsilon i)
    have hprod : 0 ≤ (1 - epsilon i) * (1 + epsilon i) :=
      mul_nonneg (sub_nonneg.mpr hi.2) (by linarith [hi.1])
    nlinarith
  change N (epsilon i • ((1 / 2 : Real) • (QA + QB))) ≤ B
  rw [hNsmul, hNsmul]
  norm_num
  nlinarith [sq_nonneg (epsilon i)]

private lemma quadratic_lie_part_bound {A : Type*} [AddCommGroup A] [Module Real A]
    (N : A → Real) (LieTerm : Fin 3 → A) (B s : Real)
    (hNadd : ∀ Q R, N (Q + R) ≤ 2 * N Q + 2 * N R)
    (hNsmul : ∀ (a : Real) Q, N (a • Q) = a ^ 2 * N Q)
    (hlieTerm : ∀ i, N (LieTerm i) ≤ B) (hB0 : 0 ≤ B) (hs2 : s ^ 2 ≤ 1) :
    N (s • (LieTerm 0 + LieTerm 1 + LieTerm 2)) ≤ 10 * B := by
  let L0 := LieTerm 0
  let L1 := LieTerm 1
  let L2 := LieTerm 2
  have h01 : N (L0 + L1) ≤ 4 * B := by
    calc
      N (L0 + L1) ≤ 2 * N L0 + 2 * N L1 := hNadd L0 L1
      _ ≤ 2 * B + 2 * B := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [L0] using hlieTerm 0) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [L1] using hlieTerm 1) (by norm_num))
      _ = 4 * B := by ring
  have h012 : N (L0 + L1 + L2) ≤ 10 * B := by
    calc
      N (L0 + L1 + L2) ≤ 2 * N (L0 + L1) + 2 * N L2 := hNadd _ _
      _ ≤ 2 * (4 * B) + 2 * B := add_le_add
        (mul_le_mul_of_nonneg_left h01 (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa only [L2] using hlieTerm 2) (by norm_num))
      _ = 10 * B := by ring
  change N (s • (L0 + L1 + L2)) ≤ _
  rw [hNsmul]
  exact (mul_le_mul_of_nonneg_left h012 (sq_nonneg s)).trans (by nlinarith [sq_nonneg s])

omit [SigmaCompactSpace M] in
theorem ricciDeTurckTopOrderBilinearPairingCoefficient_uniform_norm_bound :
    ∃ K : Real, 0 ≤ K ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (T P V : SmoothCcTensor g 0 2) {delta : Real},
        0 ≤ delta → delta ≤ 1 / 2 →
        (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) delta) →
        (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) delta) →
        ∀ (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
            fiberLpFun g 0 4
                (ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V
                  hdelta hdeltaZ qA qB q epsilon s) x ≤
              K * fiberLpFun g 0 2 P x * fiberLpFun g 0 2 V x := by
  classical
  obtain ⟨Cb, hCb0, hpair0⟩ := topOrderBilinearPairingCoefficient_uniform_norm_bound (I := I) (M := M)
  let K : Real := Real.sqrt (52 * Cb)
  have hcoef0 : 0 ≤ 52 * Cb := mul_nonneg (by norm_num) hCb0
  refine ⟨K, Real.sqrt_nonneg _, ?_⟩
  intro g T P V delta hdelta0 hdelta_half hdelta hdeltaZ
    qA qB q epsilon hepsilon s hs x
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half (by norm_num)
  have hsSmall : s ∈ metricPerturbationPathDomain (δ := delta) (δ' := delta) :=
    Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt hs
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
  let W : SmoothCcTensor g 0 2 := s • T
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g W y v w := by
    intro y v w
    have hpath := metricPerturbationPath_inner_of_mem (I := I) (M := M)
      g T 0 hdelta hdeltaZ hsSmall y v w
    simpa only [gm, W, convexPerturbation, smul_zero, zero_add] using hpath
  have hsabs : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs2 : s ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - s) * (1 + s) :=
      mul_nonneg (sub_nonneg.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hWraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s T hdelta
  have hrad : |s| * delta ≤ delta := by
    have hprod : 0 ≤ (1 - |s|) * delta :=
      mul_nonneg (sub_nonneg.mpr hsabs) hdelta0
    nlinarith
  have hWscaled : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) (|s| * delta) := by
    simpa only [W] using hWraw
  have hWbound : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta := by
    intro y v w
    exact (hWscaled y v w).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  let P0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (P.toSection x)
  let V0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (V.toSection x)
  let B : Real := Cb * P0 * V0
  have hP0 : 0 ≤ P0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hV0 : 0 ≤ V0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hCb0 hP0) hV0
  let N : SmoothCcTensor g 0 4 → Real := fun Q =>
    riemannianFiberNormSq (I := I) (M := M) g 0 4 x (Q.toSection x)
  let Pair : Equiv.Perm (Fin 4) → SmoothCcTensor g 0 4 := fun sigma =>
    topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma
  let Kern : (Fin 4 → Equiv.Perm (Fin 4)) → SmoothCcTensor g 0 4 := fun qq =>
    (1 / 2 : Real) •
      (Pair (qq 0) + Pair (qq 1) - Pair (qq 2) - Pair (qq 3))
  let Riem : SmoothCcTensor g 0 4 :=
    s • ((1 / 2 : Real) • (Kern qA + Kern qB))
  let LieTerm : Fin 3 → SmoothCcTensor g 0 4 := fun i =>
    epsilon i • ((1 / 2 : Real) •
      (Pair (q i) + Pair ((q i).trans (Equiv.swap (0 : Fin 4) 1))))
  let Lie : SmoothCcTensor g 0 4 :=
    s • (LieTerm 0 + LieTerm 1 + LieTerm 2)
  have hpair : ∀ sigma : Equiv.Perm (Fin 4), N (Pair sigma) ≤ B := by
    intro sigma
    simpa only [N, Pair, B, P0, V0, gm] using
      hpair0 g gm W P V htie hdelta_half hdelta0 hWbound sigma x
  have hNadd : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q + R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [SmoothCcTensor.toSection_add]
    exact riemannianFiberNormSq_add_le
      (I := I) (M := M) g 0 4 x _ _
  have hNsub : ∀ Q R : SmoothCcTensor g 0 4,
      N (Q - R) ≤ 2 * N Q + 2 * N R := by
    intro Q R
    dsimp only [N]
    rw [SmoothCcTensor.toSection_sub]
    exact riemannianFiberNormSq_sub_le
      (I := I) (M := M) g 0 4 x _ _
  have hNsmul : ∀ (a : Real) (Q : SmoothCcTensor g 0 4),
      N (a • Q) = a ^ 2 * N Q := by
    intro a Q
    dsimp only [N]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
  have hkernel : ∀ qq : Fin 4 → Equiv.Perm (Fin 4), N (Kern qq) ≤ 4 * B := by
    intro qq
    exact quadratic_kernel_bound N Pair B hNadd hNsub hNsmul hpair qq
  have hriem : N Riem ≤ 4 * B :=
    quadratic_riemannian_part_bound N Kern B s hNadd hNsmul hkernel hB0 hs2 qA qB
  have hlieTerm : ∀ i : Fin 3, N (LieTerm i) ≤ B := by
    intro i
    exact quadratic_lie_term_bound N Pair B hNadd hNsmul hpair q epsilon hepsilon hB0 i
  have hlie : N Lie ≤ 10 * B :=
    quadratic_lie_part_bound N LieTerm B s hNadd hNsmul hlieTerm hB0 hs2
  have hform :
      ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V hdelta hdeltaZ
          qA qB q epsilon s = (2 : Real) • Riem + Lie := by
    simp only [ricciDeTurckTopOrderBilinearPairingAdjoint, Riem, Lie, Kern, LieTerm, Pair, gm,
      Fin.sum_univ_three]
  have htop : N (ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V
      hdelta hdeltaZ qA qB q epsilon s) ≤ 52 * B := by
    rw [hform]
    have hadd := hNadd ((2 : Real) • Riem) Lie
    rw [hNsmul] at hadd
    norm_num at hadd
    calc
      _ ≤ 2 * (4 * N Riem) + 2 * N Lie := hadd
      _ ≤ 2 * (4 * (4 * B)) + 2 * (10 * B) := add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hriem (by norm_num)) (by norm_num))
        (mul_le_mul_of_nonneg_left hlie (by norm_num))
      _ = 52 * B := by ring
  have hsquare :
      (fiberLpFun g 0 4
          (ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V
            hdelta hdeltaZ qA qB q epsilon s) x) ^ 2 ≤
        (K * fiberLpFun g 0 2 P x * fiberLpFun g 0 2 V x) ^ 2 := by
    simp only [fiberLpFun, K]
    rw [Real.sq_sqrt (riemannianFiberNormSq_nonneg
        (I := I) (M := M) g 0 4 x _),
      mul_pow, mul_pow, Real.sq_sqrt hcoef0,
      Real.sq_sqrt hP0, Real.sq_sqrt hV0]
    simpa only [B, P0, V0, mul_assoc] using htop
  exact le_of_sq_le_sq hsquare
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))

omit [SigmaCompactSpace M] in
theorem topOrderBilinearPairingAdjoint_norm_bound (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (W P V : SmoothCcTensor g 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 4 x
              ((topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma).toSection x) ≤
            C * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (P.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (V.toSection x) := by
  obtain ⟨C, hC, hbound⟩ := topOrderBilinearPairingCoefficient_uniform_norm_bound (I := I) (M := M)
  exact ⟨C, hC, hbound g⟩

omit [SigmaCompactSpace M] in
theorem topOrderBilinearPairingAdjoint_covariantDerivative_bound (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (W P V : SmoothCcTensor g 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w)
        {delta : Real}, delta ≤ 1 / 2 → 0 ≤ delta →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta →
        ∀ (sigma : Equiv.Perm (Fin 4)) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 5 x
              ((covGrad (I := I) (M := M) g 0 4
                (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma)).toSection x) ≤
            C *
              (riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (P.toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                    ((iteratedCovGrad (I := I) g 0 2 1 V).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (V.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (P.toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (V.toSection x)) := by
  classical
  obtain ⟨D, hD0, hraise⟩ := edgeRaise_one_mul (I := I) (M := M) g
  let d : Real := Module.finrank Real E
  let F : Real := (2 * d) ^ 2
  let C : Real := 2 * (d ^ 2 * F ^ 2 + d ^ 2 * D)
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg (sq_nonneg d) (sq_nonneg F))
      (mul_nonneg (sq_nonneg d) hD0))
  refine ⟨C, hC0, ?_⟩
  intro gm W P V htie delta hdelta hdelta0 hWbound sigma x
  let A : SmoothCcTensor g 0 2 :=
    secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P
  let Phi : SmoothCcTensor g 2 4 :=
    slotExtendIter (I := I) (M := M) g 0 2 2 V
  let U : SmoothCcTensor g 0 5 :=
    operatorFieldApply (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) A
  let Q : SmoothCcTensor g 0 5 :=
    operatorFieldApply (I := I) (M := M) g 3 5
      (slotExtend (I := I) (M := M) g 2 4 Phi)
      (covGrad (I := I) (M := M) g 0 2 A)
  let P0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (P.toSection x)
  let P1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x)
  let W1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 W).toSection x)
  let V0 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 2 x
    (V.toSection x)
  let V1 : Real := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((iteratedCovGrad (I := I) g 0 2 1 V).toSection x)
  have hA0 : riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (A.toSection x) ≤ F ^ 2 * P0 := by
    simpa only [A, F, d, P0] using
      edgeRaise_zero_mul (I := I) (M := M) g gm W P htie
        hdelta hdelta0 hWbound x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 A).toSection x) ≤
        D * (W1 * P0 + P1) := by
    simpa only [A, W1, P0, P1] using
      hraise gm W P htie hdelta hdelta0 hWbound x
  have hPhi0 : riemannianFiberNormSq (I := I) (M := M) g 2 4 x
      (Phi.toSection x) = d ^ 2 * V0 := by
    simpa only [Phi, d, V0] using
      riemannianFiberNormSq_slotExtendIter_eq (I := I) (M := M) g 0 2 2 V x
  have hPhi1 : riemannianFiberNormSq (I := I) (M := M) g 2 5 x
      ((covGrad (I := I) (M := M) g 2 4 Phi).toSection x) =
        d ^ 2 * V1 := by
    simpa only [Phi, d, V1, iteratedCovGrad_succ, iteratedCovGrad_zero] using
      edge_extend2_one (I := I) (M := M) g V x
  have hprod : covGrad (I := I) (M := M) g 0 4
      (fourTensorProductCoefficient (I := I) (M := M) g A V) = U + Q := by
    simpa only [fourTensorProductCoefficient, Phi, U, Q] using
      covGrad_operatorFieldApplication_eq (I := I) (M := M) g 2 4 Phi A
  have hout := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g sigma.symm
    (fourTensorProductCoefficient (I := I) (M := M) g A V) 1 x
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V sigma)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4
            (fourTensorProductCoefficient (I := I) (M := M) g A V)).toSection x) := by
    simpa only [topOrderBilinearPairingAdjointCoefficient, A, iteratedCovGrad_succ,
      iteratedCovGrad_zero] using hout
  rw [hout', hprod]
  have hadd := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 0 5 x (U.toSection x) (Q.toSection x)
  have hP00 : 0 ≤ P0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hP10 : 0 ≤ P1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hW10 : 0 ≤ W1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hV00 : 0 ≤ V0 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 2 x _
  have hV10 : 0 ≤ V1 := riemannianFiberNormSq_nonneg
    (I := I) (M := M) g 0 3 x _
  have hU : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      (U.toSection x) ≤ d ^ 2 * F ^ 2 * (P0 * V1) := by
    refine (edge_app_le (I := I) (M := M) g 2 5
      (covGrad (I := I) (M := M) g 2 4 Phi) A x).trans ?_
    rw [hPhi1]
    calc
      d ^ 2 * V1 * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (A.toSection x) ≤ d ^ 2 * V1 * (F ^ 2 * P0) :=
        mul_le_mul_of_nonneg_left hA0 (mul_nonneg (sq_nonneg d) hV10)
      _ = d ^ 2 * F ^ 2 * (P0 * V1) := by ring
  have hQ : riemannianFiberNormSq (I := I) (M := M) g 0 5 x
      (Q.toSection x) ≤ d ^ 2 * D * (P1 * V0 + W1 * P0 * V0) := by
    refine (riemannianFiberNormSq_comp_slotExtend_le
      (I := I) (M := M) g 2 4 Phi
      (covGrad (I := I) (M := M) g 0 2 A) x).trans ?_
    rw [hPhi0]
    calc
      d ^ 2 * V0 * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 A).toSection x) ≤
          d ^ 2 * V0 * (D * (W1 * P0 + P1)) :=
        mul_le_mul_of_nonneg_left hA1 (mul_nonneg (sq_nonneg d) hV00)
      _ = d ^ 2 * D * (P1 * V0 + W1 * P0 * V0) := by ring
  let X : Real := P0 * V1
  let Y : Real := P1 * V0
  let Z : Real := W1 * P0 * V0
  have hX0 : 0 ≤ X := mul_nonneg hP00 hV10
  have hY0 : 0 ≤ Y := mul_nonneg hP10 hV00
  have hZ0 : 0 ≤ Z := mul_nonneg (mul_nonneg hW10 hP00) hV00
  have hAcoef0 : 0 ≤ d ^ 2 * F ^ 2 :=
    mul_nonneg (sq_nonneg d) (sq_nonneg F)
  have hBcoef0 : 0 ≤ d ^ 2 * D := mul_nonneg (sq_nonneg d) hD0
  have hAle : d ^ 2 * F ^ 2 ≤ d ^ 2 * F ^ 2 + d ^ 2 * D := by linarith
  have hBle : d ^ 2 * D ≤ d ^ 2 * F ^ 2 + d ^ 2 * D := by linarith
  calc
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          (U.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          (Q.toSection x) := hadd
    _ ≤ 2 * (d ^ 2 * F ^ 2 * X) + 2 * (d ^ 2 * D * (Y + Z)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [X] using hU) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (by simpa only [Y, Z] using hQ) (by norm_num))
    _ ≤ 2 * ((d ^ 2 * F ^ 2 + d ^ 2 * D) * X) +
        2 * ((d ^ 2 * F ^ 2 + d ^ 2 * D) * (Y + Z)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hAle hX0) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hBle (add_nonneg hY0 hZ0)) (by norm_num))
    _ = C * (X + Y + Z) := by simp only [C]; ring
    _ = _ := rfl

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
