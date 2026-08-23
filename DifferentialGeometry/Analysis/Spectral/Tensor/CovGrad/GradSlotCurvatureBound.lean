import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GradSlotCurvature
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframe_update_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) (k : Fin 2) (Q : TangentSpace I x)
    {C : ℝ} (hC : 0 ≤ C)
    (hQ : Real.sqrt (g.inner x Q Q) ≤ C) :
    |Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x 2 e K)
        (Function.update (fun l : Fin 2 ↦ e (J l)) k Q)| ≤ C := by
  have hinner : ∀ a : Fin n,
      |g.inner x (e a) Q| ≤ C := by
    intro a
    calc
      |g.inner x (e a) Q| ≤
          Real.sqrt (g.inner x (e a) (e a)) *
            Real.sqrt (g.inner x Q Q) :=
        abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g x (e a) Q
      _ = Real.sqrt (g.inner x Q Q) := by
        rw [horth a a, if_pos rfl, Real.sqrt_one, one_mul]
      _ ≤ C := hQ
  have hdelta : ∀ a b : Fin n,
      |g.inner x (e a) (e b)| ≤ 1 := by
    intro a b
    rw [horth a b]
    split <;> norm_num
  fin_cases k
  · change |Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g x 2 e K)
          (Function.update (fun l : Fin 2 ↦ e (J l)) 0 Q)| ≤ C
    rw [show Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g x 2 e K)
          (Function.update (fun l : Fin 2 ↦ e (J l)) 0 Q) =
        coframeS (I := I) (M := M) g x 2 e K
          (Function.update (fun l : Fin 2 ↦ e (J l)) 0 Q) from rfl,
      coframeS_apply, Fin.prod_univ_two, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), abs_mul]
    exact (mul_le_mul (hinner (K 0)) (hdelta (K 1) (J 1))
      (abs_nonneg _) hC).trans_eq (mul_one C)
  · change |Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g x 2 e K)
          (Function.update (fun l : Fin 2 ↦ e (J l)) 1 Q)| ≤ C
    rw [show Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g x 2 e K)
          (Function.update (fun l : Fin 2 ↦ e (J l)) 1 Q) =
        coframeS (I := I) (M := M) g x 2 e K
          (Function.update (fun l : Fin 2 ↦ e (J l)) 1 Q) from rfl,
      coframeS_apply, Fin.prod_univ_two,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Function.update_self, abs_mul]
    exact (mul_le_mul (hdelta (K 0) (J 0)) (hinner (K 1))
      (abs_nonneg _) zero_le_one).trans_eq (one_mul C)

omit [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gradSlot_comp0_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 2 → Fin n) (J : Fin 4 → Fin n)
    {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (v w u : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v w u)
          (riemannOp (LeviCivita (I := I) g) x v w u) ≤
        C ^ 2 * g.inner x v v * g.inner x w w * g.inner x u u) :
    |fiberNormSqComponent (I := I) (M := M) g x 2 4
        (show TensorRSSpace 2 4 I x from
          (gradSlotCurvCoeff (I := I) (M := M) g).toSection x)
        n e K J| ≤ 2 * C := by
  let A : Tensor0SSpace 2 I x := coframeS (I := I) (M := M) g x 2 e K
  let m : Fin 2 → TangentSpace I x := ![e (J 2), e (J 3)]
  have htuple : (fun a : Fin 4 ↦ e (J a)) =
      Fin.cons (e (J 0)) (Fin.cons (e (J 1)) m) := by
    funext a
    fin_cases a <;> rfl
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x 2 4
        (show TensorRSSpace 2 4 I x from
          (gradSlotCurvCoeff (I := I) (M := M) g).toSection x)
        n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (gradSlotCurvCoeff (I := I) (M := M) g).toSection x) A)
        (fun a : Fin 4 ↦ e (J a)) := by
    unfold fiberNormSqComponent A coframeS
    rfl
  rw [hcomp, htuple]
  change |Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (gradSlotCurvCoeff (I := I) (M := M) g).toSection x) A)
      (Fin.cons (e (J 0)) (Fin.cons (e (J 1)) m))| ≤ 2 * C
  rw [gradSlotCurv_eval (I := I) (M := M) g x A]
  rw [abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc
    ∑ k : Fin 2, |Tensor0SSpace.toModel A
        (Function.update m k
          (riemannOp (LeviCivita (I := I) g) x (e (J 0)) (e (J 1)) (m k)))| ≤
        ∑ _k : Fin 2, C := by
      refine Finset.sum_le_sum (fun k _ ↦ ?_)
      apply coframe_update_le (I := I) (M := M) g x e horth K
        ![J 2, J 3] k
      · exact hC
      · have hb := hR (e (J 0)) (e (J 1)) (m k)
        have hunit : ∀ a : Fin 4,
            g.inner x (e (J a)) (e (J a)) = 1 := by
          intro a
          rw [horth (J a) (J a), if_pos rfl]
        have hm : g.inner x (m k) (m k) = 1 := by
          fin_cases k <;> simp [m, hunit]
        rw [hunit 0, hunit 1, hm, mul_one, mul_one, mul_one] at hb
        calc
          Real.sqrt (g.inner x
              (riemannOp (LeviCivita (I := I) g) x
                (e (J 0)) (e (J 1)) (m k))
              (riemannOp (LeviCivita (I := I) g) x
                (e (J 0)) (e (J 1)) (m k))) ≤
              Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hb
          _ = C := Real.sqrt_sq hC
    _ = 2 * C := by simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma gradSlot_comp1_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 2 → Fin n) (J : Fin 5 → Fin n)
    {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x
          (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        C * Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z)) :
    |fiberNormSqComponent (I := I) (M := M) g x 2 5
        (show TensorRSSpace 2 5 I x from
          (covGrad (I := I) (M := M) g 2 4
            (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x)
        n e K J| ≤ 2 * C := by
  let A : Tensor0SSpace 2 I x := coframeS (I := I) (M := M) g x 2 e K
  let m : Fin 2 → TangentSpace I x := ![e (J 3), e (J 4)]
  have htuple : (fun a : Fin 5 ↦ e (J a)) =
      Fin.cons (e (J 0))
        (Fin.cons (e (J 1)) (Fin.cons (e (J 2)) m)) := by
    funext a
    fin_cases a <;> rfl
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x 2 5
        (show TensorRSSpace 2 5 I x from
          (covGrad (I := I) (M := M) g 2 4
            (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x)
        n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (covGrad (I := I) (M := M) g 2 4
            (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x) A)
        (fun a : Fin 5 ↦ e (J a)) := by
    unfold fiberNormSqComponent A coframeS
    rfl
  rw [hcomp, htuple]
  change |Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (covGrad (I := I) (M := M) g 2 4
          (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x) A)
      (Fin.cons (e (J 0))
        (Fin.cons (e (J 1)) (Fin.cons (e (J 2)) m)))| ≤ 2 * C
  rw [gradSlot_cov_eval (I := I) (M := M) g x A]
  rw [abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc
    ∑ k : Fin 2, |Tensor0SSpace.toModel A
        (Function.update m k
          (nablaRiemannOp (I := I) g x
            (e (J 0)) (e (J 1)) (e (J 2)) (m k)))| ≤
        ∑ _k : Fin 2, C := by
      refine Finset.sum_le_sum (fun k _ ↦ ?_)
      apply coframe_update_le (I := I) (M := M) g x e horth K
        ![J 3, J 4] k
      · exact hC
      · have hb := hR (e (J 0)) (e (J 1)) (e (J 2)) (m k)
        have hunit : ∀ a : Fin 5,
            g.inner x (e (J a)) (e (J a)) = 1 := by
          intro a
          rw [horth (J a) (J a), if_pos rfl]
        have hm : g.inner x (m k) (m k) = 1 := by
          fin_cases k <;> simp [m, hunit]
        simpa only [hunit 0, hunit 1, hunit 2, hm,
          Real.sqrt_one, mul_one] using hb
    _ = 2 * C := by simp

omit [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradSlot_riemannianFiberNormSq_zero
    (g : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (x : M) (v w u : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v w u)
          (riemannOp (LeviCivita (I := I) g) x v w u) ≤
        C ^ 2 * g.inner x v v * g.inner x w w * g.inner x u u) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 4 x
          ((gradSlotCurvCoeff (I := I) (M := M) g).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 6 * (2 * C) ^ 2 := by
  classical
  intro x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 2 4 x
    (show TensorRSSpace 2 4 I x from
      (gradSlotCurvCoeff (I := I) (M := M) g).toSection x)
    e bse hnE hbse horth]
  calc
    (∑ K : Fin 2 → Fin n, ∑ J : Fin 4 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 2 4
          (show TensorRSSpace 2 4 I x from
            (gradSlotCurvCoeff (I := I) (M := M) g).toSection x)
          n e K J) ^ 2) ≤
        ∑ _K : Fin 2 → Fin n, ∑ _J : Fin 4 → Fin n,
          (2 * C) ^ 2 := by
      refine Finset.sum_le_sum (fun K _ ↦ Finset.sum_le_sum (fun J _ ↦ ?_))
      have ha := gradSlot_comp0_le (I := I) (M := M) g x e horth K J hC
        (fun v w u ↦ hR x v w u)
      exact sq_le_sq' (neg_le_of_abs_le ha) (le_of_abs_le ha)
    _ = (Module.finrank ℝ E : ℝ) ^ 6 * (2 * C) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      simp only [hnE, Fintype.card_fin]
      push_cast
      ring

omit [NeZero (Module.finrank ℝ E)] in
theorem gradSlot_riemannianFiberNormSq_one
    (g : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x
          (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        C * Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z)) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 5 x
          ((covGrad (I := I) (M := M) g 2 4
            (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 7 * (2 * C) ^ 2 := by
  classical
  intro x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 2 5 x
    (show TensorRSSpace 2 5 I x from
      (covGrad (I := I) (M := M) g 2 4
        (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x)
    e bse hnE hbse horth]
  calc
    (∑ K : Fin 2 → Fin n, ∑ J : Fin 5 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 2 5
          (show TensorRSSpace 2 5 I x from
            (covGrad (I := I) (M := M) g 2 4
              (gradSlotCurvCoeff (I := I) (M := M) g)).toSection x)
          n e K J) ^ 2) ≤
        ∑ _K : Fin 2 → Fin n, ∑ _J : Fin 5 → Fin n,
          (2 * C) ^ 2 := by
      refine Finset.sum_le_sum (fun K _ ↦ Finset.sum_le_sum (fun J _ ↦ ?_))
      have ha := gradSlot_comp1_le (I := I) (M := M) g x e horth K J hC
        (fun D X Y Z ↦ hR x D X Y Z)
      exact sq_le_sq' (neg_le_of_abs_le ha) (le_of_abs_le ha)
    _ = (Module.finrank ℝ E : ℝ) ^ 7 * (2 * C) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      simp only [hnE, Fintype.card_fin]
      push_cast
      ring

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end
