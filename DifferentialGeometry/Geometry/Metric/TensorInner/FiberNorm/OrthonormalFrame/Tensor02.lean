import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Components
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
noncomputable section


open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def tensor00Scalar (x : M) :
    Tensor0SSpace 0 I x →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.comp
    (Tensor0SSpace.toModelL (I := I) 0 x)

lemma tensor00Scalar_apply (x : M) (τ : Tensor0SSpace 0 I x)
    (m : Fin 0 → TangentSpace I x) :
    tensor00Scalar (I := I) (M := M) x τ = τ m := by
  unfold tensor00Scalar
  rw [ContinuousLinearMap.comp_apply]
  have h1 : (Tensor0SSpace.toModelL (I := I) 0 x) τ = Tensor0SSpace.toModel τ := rfl
  rw [h1]
  change (continuousMultilinearCurryFin0 ℝ E ℝ) (Tensor0SSpace.toModel τ) = _
  rw [continuousMultilinearCurryFin0_apply]
  change τ (0 : Fin 0 → TangentSpace I x) = τ m
  congr 1
  exact Subsingleton.elim _ _

noncomputable def coframePair
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
      (fun k : Fin 2 => g.inner x (e ((![a, b] : Fin 2 → Fin n) k))))

omit [FiniteDimensional ℝ E] in
abbrev coframe2
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    Tensor0SSpace 2 I x :=
  coframePair g x e a b

omit [FiniteDimensional ℝ E] in
lemma coframe2_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (u : Fin 2 → TangentSpace I x) :
    coframePair (I := I) (M := M) g x e a b u =
      g.inner x (e a) (u 0) * g.inner x (e b) (u 1) := by
  unfold coframePair
  change Tensor0SSpace.eval
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          (fun k : Fin 2 => g.inner x (e ((![a, b] : Fin 2 → Fin n) k))))) u = _
  rw [Tensor0SSpace.eval_fiber_equiv_symm]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

noncomputable def dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    TensorRSSpace 0 2 I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (coframePair (I := I) (M := M) g x e a b)

lemma dualTensorFrame_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (dualTensorFrame (I := I) (M := M) g x e a b :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • coframePair (I := I) (M := M) g x e a b := by
  unfold dualTensorFrame
  rw [ContinuousLinearMap.smulRight_apply]

lemma fiberNormSqComponent_dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (a b : Fin n) (K : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 2
        (dualTensorFrame (I := I) (M := M) g x e a b) n e K J =
      (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0) := by
  classical
  let ωK : Tensor0SSpace 0 I x :=
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k))))
  change Tensor0SSpace.eval
      ((dualTensorFrame (I := I) (M := M) g x e a b :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK)
      (fun k : Fin 2 => e (J k)) = _
  rw [dualTensorFrame_apply (I := I) (M := M) g x e a b ωK]
  have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x ωK (fun k : Fin 0 => k.elim0)]
    change Tensor0SSpace.eval
        ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K k))))) (fun k : Fin 0 => k.elim0) = 1
    rw [Tensor0SSpace.eval_fiber_equiv_symm,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    simp
  rw [hscalar, one_smul]
  rw [Tensor0SSpace.eval_eq]
  rw [coframe2_apply (I := I) (M := M) g x e a b (fun k : Fin 2 => e (J k))]
  rw [horth a (J 0), horth b (J 1)]

omit [FiniteDimensional ℝ E] in
lemma tensor02_coframe_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SSpace 2 I x) :
    A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 2 x
  intro u
  let Acmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ := A
  let Rcmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
    ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b
  suffices h : Acmm.toMultilinearMap = Rcmm.toMultilinearMap by
    exact congrArg
      (fun (T : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ) => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 2 => bse) ?_
  intro v
  have hbtuple : (fun i : Fin 2 => bse (v i)) = (fun i : Fin 2 => e (v i)) := by
    funext i; rw [hbse (v i)]
  change Acmm (fun i : Fin 2 => bse (v i)) = Rcmm (fun i : Fin 2 => bse (v i))
  rw [hbtuple]
  have hRHS_eval : Rcmm (fun i : Fin 2 => e (v i)) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) := by
    change (∑ a : Fin n, ∑ b : Fin n,
          (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
            coframePair (I := I) (M := M) g x e a b)
        (fun i : Fin 2 => e (v i)) = _
    rw [Tensor0SSpace.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Tensor0SSpace.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Tensor0SSpace.smul_apply, smul_eq_mul]
  change Acmm (fun i : Fin 2 => e (v i)) = _
  rw [hRHS_eval]
  have hcoframe : ∀ a b : Fin n,
      coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) =
        (if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0) := by
    intro a b
    rw [coframe2_apply (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))]
    rw [horth a (v 0), horth b (v 1)]
  rw [show (∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          ((if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0)) from by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcoframe a b]]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (v 1)]
  · rw [Finset.sum_eq_single (v 0)]
    · simp only [if_pos, mul_one]
      congr 1
      funext k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro a _ ha
      rw [if_neg ha, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (v 0)) h
  · intro b _ hb
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (v 1)) h

lemma tangent_orthonormalBasis_witness
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 2 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]
    exact hite
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right eob v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner x v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner x (eob i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (eob i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner x v v := hnorm_sq
  · intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i = v :=
      OrthonormalBasis.sum_repr' eob v
    have hcongr : (∑ i : Fin n, g.inner x (eob i) v • eob i) =
        ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (eob i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

lemma tensor_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    T = ∑ a : Fin n, ∑ b : Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
        dualTensorFrame (I := I) (M := M) g x e a b := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 2 x
  intro τ
  set c : ℝ := tensor00Scalar (I := I) (M := M) x τ with hc_def
  set ωK : Tensor0SSpace 0 I x :=
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k)))) with hωK_def
  have hτ : τ = c • ωK := by
    apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
    intro m
    rw [hc_def, tensor00Scalar_apply (I := I) (M := M) x τ m]
    rw [Tensor0SSpace.smul_apply, smul_eq_mul]
    have hωK1 : ωK m = 1 := by
      change Tensor0SSpace.eval ωK m = 1
      rw [hωK_def, Tensor0SSpace.eval_fiber_equiv_symm,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    rw [hωK1, mul_one]
  have hLHS : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      c • (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK := by
    rw [hτ, ContinuousLinearMap.map_smul]
  set A : Tensor0SSpace 2 I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK with hA_def
  have hA_expand : A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b :=
    tensor02_coframe_expansion (I := I) (M := M) g x e bse hbse horth A
  have hAeval : ∀ a b : Fin n,
      A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k)) =
        fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b]) := by
    intro a b
    rw [hA_def]
    rfl
  have hLHS' : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframePair (I := I) (M := M) g x e a b) := by
    rw [hLHS, hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hAeval a b, smul_comm]
  have hRHS' : (∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          dualTensorFrame (I := I) (M := M) g x e a b :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframePair (I := I) (M := M) g x e a b) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_apply,
      dualTensorFrame_apply (I := I) (M := M) g x e a b τ, ← hc_def]
  rw [hLHS', hRHS']

lemma riemannianFiberNormSq_eq_sum_component_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x T =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2 := by
  classical
  rw [hrepr T]
  rw [Finset.sum_eq_single K₀]
  · rw [show (∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 T n e K₀ J) =
        ∑ J : Fin 2 → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2 from by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [fiberNormSqSummand_eq_component_sq]]
    rw [← Fintype.sum_prod_type'
      (f := fun a b => (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2)]
    rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin n)).symm
      (fun J : Fin 2 → Fin n =>
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [finTwoArrowEquiv_symm_apply]
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

end Elliptic
end Analysis
end DifferentialGeometry

end
