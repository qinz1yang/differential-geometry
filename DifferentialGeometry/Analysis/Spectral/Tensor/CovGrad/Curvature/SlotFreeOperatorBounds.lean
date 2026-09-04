import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.SlotFree
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets

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
private lemma coframe_one_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (m : Fin 1 → TangentSpace I x)
    (Q : TangentSpace I x) {C : ℝ} (hC : 0 ≤ C)
    (hQ : Real.sqrt (g.inner x Q Q) ≤ C) :
    |Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x 1 e K)
        (Function.update m 0 Q)| ≤ C := by
  have hinner := abs_metric_inner_le_sqrt_metric_quadratic
    (I := I) (M := M) g x (e (K 0)) Q
  calc
    |Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x 1 e K)
        (Function.update m 0 Q)| = |g.inner x (e (K 0)) Q| := by
      rw [show Tensor0SSpace.toModel
            (coframeS (I := I) (M := M) g x 1 e K)
            (Function.update m 0 Q) =
          coframeS (I := I) (M := M) g x 1 e K
            (Function.update m 0 Q) from rfl,
        coframeS_apply, Fin.prod_univ_one, Function.update_self]
    _ ≤ Real.sqrt (g.inner x (e (K 0)) (e (K 0))) *
        Real.sqrt (g.inner x Q Q) := hinner
    _ = Real.sqrt (g.inner x Q Q) * 1 := by
      rw [mul_comm, horth (K 0) (K 0), if_pos rfl, Real.sqrt_one]
    _ ≤ C * 1 := mul_le_mul hQ le_rfl zero_le_one hC
    _ = C := mul_one C

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private lemma sfOne_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 1 I x) (u w : TangentSpace I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
        (Fin.cons u (Fin.cons w m)) =
      -Tensor0SSpace.toModel A
        (Function.update m 0
          (riemannOp (LeviCivita (I := I) g) x u w (m 0))) := by
  rw [slotFreeOpCc_apply]
  change Tensor0SSpace.toModel
      (curvatureOperatorOnTensorFib (I := I) (M := M) g 1 x A)
      (Fin.cons u (Fin.cons w m)) = _
  have h := slotFreeCurvOpFib_apply_eval (I := I) (M := M) g 1 x A u w m
  rw [Fin.sum_univ_one] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma sfOne_cov_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 1 I x) (d u w : TangentSpace I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) A)
        (Fin.cons d (Fin.cons u (Fin.cons w m))) =
      -Tensor0SSpace.toModel A
        (Function.update m 0
          (nablaRiemannOp (I := I) g x d u w (m 0))) := by
  have h := covGrad_toSection_apply_eval (I := I) (M := M) g 1 3
    (slotFreeOpCc (I := I) (M := M) g 1) x A
    (Fin.cons d (Fin.cons u (Fin.cons w m)))
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (covGrad (I := I) (M := M) g 1 3
          (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) A)
      (Fin.cons d (Fin.cons u (Fin.cons w m))) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorCovDerivAt (I := I) (M := M) g 1 3
          (slotFreeOpCc (I := I) (M := M) g 1) x d) A)
      (Fin.cons u (Fin.cons w m)) at h
  rw [h]
  change Tensor0SSpace.toModel
      (TensorRSSpace.toCLM
        (tensorCovDerivAt (I := I) (M := M) g 1 3
          (slotFreeOpCc (I := I) (M := M) g 1) x (show E from d)) A)
      (Fin.cons u (Fin.cons w m)) = _
  rw [tensorCovDerivAt_def]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 1 3
          (LeviCivita (I := I) g)
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x d) A)
      (Fin.cons u (Fin.cons w m)) = _
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 1 3
          (LeviCivita (I := I) g)
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x d) A)
      (Fin.cons u (Fin.cons w m)) =
    -Tensor0SSpace.eval A
      (Function.update m 0 (nablaRiemannOp (I := I) g x d u w (m 0)))
  simpa only [Fin.sum_univ_one] using
    slotFree_cov_eval (I := I) (M := M) g 1 x d A u w m

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma sfOne_comp0_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin 3 → Fin n)
    {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (v w u : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v w u)
          (riemannOp (LeviCivita (I := I) g) x v w u) ≤
        C ^ 2 * g.inner x v v * g.inner x w w * g.inner x u u) :
    |fiberNormSqComponent (I := I) (M := M) g x 1 3
        (show TensorRSSpace 1 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
        n e K J| ≤ C := by
  let A : Tensor0SSpace 1 I x := coframeS (I := I) (M := M) g x 1 e K
  let m : Fin 1 → TangentSpace I x := ![e (J 2)]
  have htuple : (fun a : Fin 3 ↦ e (J a)) =
      Fin.cons (e (J 0)) (Fin.cons (e (J 1)) m) := by
    funext a
    fin_cases a <;> rfl
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x 1 3
        (show TensorRSSpace 1 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
        n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
        (fun a : Fin 3 ↦ e (J a)) := by
    unfold fiberNormSqComponent A coframeS
    rfl
  rw [hcomp, htuple]
  change |Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
      (Fin.cons (e (J 0)) (Fin.cons (e (J 1)) m))| ≤ C
  rw [sfOne_eval, abs_neg]
  refine coframe_one_le (I := I) (M := M) g x e horth K m _ hC ?_
  have hb := hR (e (J 0)) (e (J 1)) (m 0)
  have hunit : ∀ a : Fin 3,
      g.inner x (e (J a)) (e (J a)) = 1 := by
    intro a
    rw [horth (J a) (J a), if_pos rfl]
  have hm : g.inner x (m 0) (m 0) = 1 := by
    simp [m, hunit]
  rw [hunit 0, hunit 1, hm, mul_one, mul_one, mul_one] at hb
  calc
    Real.sqrt (g.inner x
        (riemannOp (LeviCivita (I := I) g) x
          (e (J 0)) (e (J 1)) (m 0))
        (riemannOp (LeviCivita (I := I) g) x
          (e (J 0)) (e (J 1)) (m 0))) ≤
        Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hb
    _ = C := Real.sqrt_sq hC

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma sfOne_comp1_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n,
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin 4 → Fin n)
    {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x
          (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        C * Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z)) :
    |fiberNormSqComponent (I := I) (M := M) g x 1 4
        (show TensorRSSpace 1 4 I x from
          (covGrad (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x)
        n e K J| ≤ C := by
  let A : Tensor0SSpace 1 I x := coframeS (I := I) (M := M) g x 1 e K
  let m : Fin 1 → TangentSpace I x := ![e (J 3)]
  have htuple : (fun a : Fin 4 ↦ e (J a)) =
      Fin.cons (e (J 0))
        (Fin.cons (e (J 1)) (Fin.cons (e (J 2)) m)) := by
    funext a
    fin_cases a <;> rfl
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x 1 4
        (show TensorRSSpace 1 4 I x from
          (covGrad (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x)
        n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) A)
        (fun a : Fin 4 ↦ e (J a)) := by
    unfold fiberNormSqComponent A coframeS
    rfl
  rw [hcomp, htuple]
  change |Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (covGrad (I := I) (M := M) g 1 3
          (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) A)
      (Fin.cons (e (J 0))
        (Fin.cons (e (J 1)) (Fin.cons (e (J 2)) m)))| ≤ C
  rw [sfOne_cov_eval, abs_neg]
  refine coframe_one_le (I := I) (M := M) g x e horth K m _ hC ?_
  have hb := hR (e (J 0)) (e (J 1)) (e (J 2)) (m 0)
  have hunit : ∀ a : Fin 4,
      g.inner x (e (J a)) (e (J a)) = 1 := by
    intro a
    rw [horth (J a) (J a), if_pos rfl]
  have hm : g.inner x (m 0) (m 0) = 1 := by
    simp [m, hunit]
  simpa only [hunit 0, hunit 1, hunit 2, hm,
    Real.sqrt_one, mul_one] using hb

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem sfOne_riemannianFiberNormSq_zero
    (g : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ (x : M) (v w u : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v w u)
          (riemannOp (LeviCivita (I := I) g) x v w u) ≤
        C ^ 2 * g.inner x v v * g.inner x w w * g.inner x u u) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 1 3 x
          ((slotFreeOpCc (I := I) (M := M) g 1).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 4 * C ^ 2 := by
  classical
  intro x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 1 3 x
    (show TensorRSSpace 1 3 I x from
      (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
    e bse hnE hbse horth]
  calc
    (∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 1 3
          (show TensorRSSpace 1 3 I x from
            (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
          n e K J) ^ 2) ≤
        ∑ _K : Fin 1 → Fin n, ∑ _J : Fin 3 → Fin n, C ^ 2 := by
      refine Finset.sum_le_sum (fun K _ ↦ Finset.sum_le_sum (fun J _ ↦ ?_))
      have ha := sfOne_comp0_le (I := I) (M := M) g x e horth K J hC
        (fun v w u ↦ hR x v w u)
      exact sq_le_sq' (neg_le_of_abs_le ha) (le_of_abs_le ha)
    _ = (Module.finrank ℝ E : ℝ) ^ 4 * C ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      simp only [hnE, Fintype.card_fin]
      push_cast
      ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem sfOne_riemannianFiberNormSq_one
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
      riemannianFiberNormSq (I := I) (M := M) g 1 4 x
          ((covGrad (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 5 * C ^ 2 := by
  classical
  intro x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 1 4 x
    (show TensorRSSpace 1 4 I x from
      (covGrad (I := I) (M := M) g 1 3
        (slotFreeOpCc (I := I) (M := M) g 1)).toSection x)
    e bse hnE hbse horth]
  calc
    (∑ K : Fin 1 → Fin n, ∑ J : Fin 4 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 1 4
          (show TensorRSSpace 1 4 I x from
            (covGrad (I := I) (M := M) g 1 3
              (slotFreeOpCc (I := I) (M := M) g 1)).toSection x)
          n e K J) ^ 2) ≤
        ∑ _K : Fin 1 → Fin n, ∑ _J : Fin 4 → Fin n, C ^ 2 := by
      refine Finset.sum_le_sum (fun K _ ↦ Finset.sum_le_sum (fun J _ ↦ ?_))
      have ha := sfOne_comp1_le (I := I) (M := M) g x e horth K J hC
        (fun D X Y Z ↦ hR x D X Y Z)
      exact sq_le_sq' (neg_le_of_abs_le ha) (le_of_abs_le ha)
    _ = (Module.finrank ℝ E : ℝ) ^ 5 * C ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      simp only [hnE, Fintype.card_fin]
      push_cast
      ring

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end
