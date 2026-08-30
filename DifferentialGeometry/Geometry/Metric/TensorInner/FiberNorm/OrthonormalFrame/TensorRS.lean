import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.OrthonormalFrame.Tensor02


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

noncomputable def coframeS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n) :
    Tensor0SSpace s I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin s) ℝ).compContinuousLinearMap
      (fun k : Fin s => g.inner x (e (J k))))

omit [FiniteDimensional ℝ E] in
lemma coframeS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n)
    (u : Fin s → TangentSpace I x) :
    coframeS (I := I) (M := M) g x s e J u =
      ∏ k : Fin s, g.inner x (e (J k)) (u k) := by
  unfold coframeS
  change Tensor0SSpace.eval
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin s) ℝ).compContinuousLinearMap
          (fun k : Fin s => g.inner x (e (J k))))) u = _
  rw [Tensor0SSpace.eval_fiber_equiv_symm,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

omit [FiniteDimensional ℝ E] in
theorem fiberNormSqComponent_eq_toModel_coframe
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s S n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S)
          (coframeS (I := I) (M := M) g x r e K))
        (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) := by
  unfold fiberNormSqComponent
  rw [Tensor0SSpace.toModel_apply_model_vector]
  unfold coframeS
  simp only [Tensor0SSpace.eval_eq, ContinuousLinearEquiv.symm_apply_apply]

noncomputable def dualTensorFrameS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (coframeS (I := I) (M := M) g x s e J)

lemma dualTensorFrameS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (dualTensorFrameS (I := I) (M := M) g x s e J :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • coframeS (I := I) (M := M) g x s e J := by
  unfold dualTensorFrameS
  rw [ContinuousLinearMap.smulRight_apply]

lemma fiberNormSqComponent_dualTensorFrameS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (J : Fin s → Fin n) (K : Fin 0 → Fin n) (J' : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s
        (dualTensorFrameS (I := I) (M := M) g x s e J) n e K J' =
      ∏ k : Fin s, (if J k = J' k then (1 : ℝ) else 0) := by
  classical
  let ωK : Tensor0SSpace 0 I x :=
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k))))
  change Tensor0SSpace.eval
      ((dualTensorFrameS (I := I) (M := M) g x s e J :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) ωK)
      (fun k : Fin s => e (J' k)) = _
  rw [dualTensorFrameS_apply (I := I) (M := M) g x s e J ωK]
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
  rw [coframeS_apply (I := I) (M := M) g x s e J (fun k : Fin s => e (J' k))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [horth (J k) (J' k)]

omit [FiniteDimensional ℝ E] in
lemma tensorS_coframe_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SSpace s I x) :
    A = ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro u
  let Acmm : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ := A
  let Rcmm : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ :=
    ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J
  suffices h : Acmm.toMultilinearMap = Rcmm.toMultilinearMap by
    exact congrArg
      (fun (T : MultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ) => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin s => bse) ?_
  intro v
  have hbtuple : (fun i : Fin s => bse (v i)) = (fun i : Fin s => e (v i)) := by
    funext i; rw [hbse (v i)]
  change Acmm (fun i : Fin s => bse (v i)) = Rcmm (fun i : Fin s => bse (v i))
  rw [hbtuple]
  have hRHS_eval : Rcmm (fun i : Fin s => e (v i)) =
      ∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i)) := by
    change (∑ J : Fin s → Fin n,
          (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J)
        (fun i : Fin s => e (v i)) = _
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [smul_apply, smul_eq_mul]
  change Acmm (fun i : Fin s => e (v i)) = _
  rw [hRHS_eval]
  have hcoframe : ∀ J : Fin s → Fin n,
      coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i)) =
        ∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0) := by
    intro J
    rw [coframeS_apply (I := I) (M := M) g x s e J (fun i : Fin s => e (v i))]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [horth (J k) (v k)]
  rw [show (∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i))) =
      ∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          ∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcoframe J]]
  rw [Finset.sum_eq_single v]
  · rw [show (∏ k : Fin s, (if v k = v k then (1 : ℝ) else 0)) = 1 from by
      refine Finset.prod_eq_one (fun k _ => ?_); rw [if_pos rfl]]
    rw [mul_one]
    change Tensor0SSpace.eval A (fun i : Fin s => e (v i)) =
      Tensor0SSpace.eval A (fun i : Fin s => e (v i))
    rfl
  · intro J _ hJ
    have hk : ∃ k : Fin s, J k ≠ v k := by
      by_contra hcon
      refine hJ (funext (fun k => ?_))
      by_contra hkne
      exact hcon ⟨k, hkne⟩
    obtain ⟨k, hkne⟩ := hk
    rw [show (∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0)) = 0 from by
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [if_neg hkne]]
    rw [mul_zero]
  · intro h; exact absurd (Finset.mem_univ v) h

lemma tensorS_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace 0 s I x) (K₀ : Fin 0 → Fin n) :
    T = ∑ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
        dualTensorFrameS (I := I) (M := M) g x s e J := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
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
    rw [smul_apply, smul_eq_mul]
    have hωK1 : ωK m = 1 := by
      change Tensor0SSpace.eval ωK m = 1
      rw [hωK_def, Tensor0SSpace.eval_fiber_equiv_symm,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    rw [hωK1, mul_one]
  have hLHS : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      c • (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) ωK := by
    rw [hτ, ContinuousLinearMap.map_smul]
  set A : Tensor0SSpace s I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) ωK with hA_def
  have hA_expand : A = ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J :=
    tensorS_coframe_expansion (I := I) (M := M) g x s e bse hbse horth A
  have hAeval : ∀ J : Fin s → Fin n,
      A (fun k : Fin s => e (J k)) =
        fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J := by
    intro J
    rw [hA_def]
    rfl
  have hLHS' : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          (c • coframeS (I := I) (M := M) g x s e J) := by
    rw [hLHS, hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hAeval J, smul_comm]
  have hRHS' : (∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          dualTensorFrameS (I := I) (M := M) g x s e J :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          (c • coframeS (I := I) (M := M) g x s e J) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [smul_apply,
      dualTensorFrameS_apply (I := I) (M := M) g x s e J τ, ← hc_def]
  rw [hLHS', hRHS']

lemma riemannianFiberNormSq_eq_sum_componentS_sq
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (T : TensorRSSpace 0 s I x) (K₀ : Fin 0 → Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x T =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) ^ 2 := by
  classical
  rw [hrepr T]
  rw [Finset.sum_eq_single K₀]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

lemma tangent_orthonormalBasisS_witness
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 s I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
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

private lemma clmFinsetSum {X Y : Type*}
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommMonoid Y] [Module ℝ Y]
    {ι : Type*} (f : X →L[ℝ] Y) (t : Finset ι) (u : ι → X) :
    f (∑ i ∈ t, u i) = ∑ i ∈ t, f (u i) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearMap.map_zero]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ContinuousLinearMap.map_add, ih]

noncomputable def tensorEvalAtFrame
    (x : M) (r : ℕ) {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) :
    Tensor0SSpace r I x →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap
      ({ toFun := fun f : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ =>
            f (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (K k)))
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →ₗ[ℝ] ℝ)).comp
    (Tensor0SSpace.toModelL (I := I) r x)

lemma tensorEvalAtFrame_apply
    (x : M) (r : ℕ) {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n)
    (τ : Tensor0SSpace r I x) :
    tensorEvalAtFrame (I := I) (M := M) x r e K τ = τ (fun k => e (K k)) := by
  unfold tensorEvalAtFrame
  rw [ContinuousLinearMap.comp_apply, Tensor0SSpace.toModelL_apply]
  change Tensor0SSpace.toModel τ
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (K k))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

noncomputable def dualTensorFrameRS
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n) :
    TensorRSSpace r s I x :=
  (tensorEvalAtFrame (I := I) (M := M) x r e K).smulRight
    (coframeS (I := I) (M := M) g x s e J)

lemma dualTensorFrameRS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n)
    (τ : Tensor0SSpace r I x) :
    (dualTensorFrameRS (I := I) (M := M) g x r s e K J :
        Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensorEvalAtFrame (I := I) (M := M) x r e K τ •
        coframeS (I := I) (M := M) g x s e J := by
  unfold dualTensorFrameRS
  rw [ContinuousLinearMap.smulRight_apply]

lemma fiberNormSqComponent_dualTensorFrameRS
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin r → Fin n) (J : Fin s → Fin n)
    (K' : Fin r → Fin n) (J' : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s
        (dualTensorFrameRS (I := I) (M := M) g x r s e K J) n e K' J' =
      (∏ k : Fin r, (if K' k = K k then (1 : ℝ) else 0)) *
        ∏ l : Fin s, (if J l = J' l then (1 : ℝ) else 0) := by
  classical
  let ωK : Tensor0SSpace r I x :=
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x).symm
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K' k))))
  change Tensor0SSpace.eval
      ((dualTensorFrameRS (I := I) (M := M) g x r s e K J :
        Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) ωK)
      (fun k : Fin s => e (J' k)) = _
  rw [dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J ωK]
  have hscalar : tensorEvalAtFrame (I := I) (M := M) x r e K ωK =
      ∏ k : Fin r, (if K' k = K k then (1 : ℝ) else 0) := by
    rw [tensorEvalAtFrame_apply (I := I) (M := M) x r e K]
    change Tensor0SSpace.eval
        ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x).symm
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K' k))))) (fun k => e (K k)) = _
    rw [Tensor0SSpace.eval_fiber_equiv_symm,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [horth (K' k) (K k)]
  rw [hscalar]
  rw [Tensor0SSpace.eval_smul, smul_eq_mul]
  rw [Tensor0SSpace.eval_eq]
  rw [coframeS_apply (I := I) (M := M) g x s e J (fun l : Fin s => e (J' l))]
  congr 1
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [horth (J l) (J' l)]

lemma tensorRS_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace r s I x) :
    T = ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
        dualTensorFrameRS (I := I) (M := M) g x r s e K J := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) r s x
  intro τ
  set Tclm : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x := T with hTclm
  have hτexp : τ = ∑ K : Fin r → Fin n,
      (τ (fun k : Fin r => e (K k))) • coframeS (I := I) (M := M) g x r e K :=
    tensorS_coframe_expansion (I := I) (M := M) g x r e bse hbse horth τ
  have hLHS : Tclm τ =
      ∑ K : Fin r → Fin n,
        (τ (fun k : Fin r => e (K k))) • Tclm (coframeS (I := I) (M := M) g x r e K) := by
    conv_lhs => rw [hτexp]
    rw [clmFinsetSum Tclm]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hTcoframe : ∀ K : Fin r → Fin n,
      Tclm (coframeS (I := I) (M := M) g x r e K) =
        ∑ J : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J := by
    intro K
    have hAexp := tensorS_coframe_expansion (I := I) (M := M) g x s e bse hbse horth
      (Tclm (coframeS (I := I) (M := M) g x r e K))
    rw [hAexp]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    congr 1
  have hLHS' : Tclm τ =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (τ (fun k : Fin r => e (K k))) •
          ((fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J) := by
    rw [hLHS]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [hTcoframe K, Finset.smul_sum]
  have hRHS' : (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
          dualTensorFrameRS (I := I) (M := M) g x r s e K J :
            Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (τ (fun k : Fin r => e (K k))) •
          ((fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [smul_apply,
      dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J τ,
      tensorEvalAtFrame_apply (I := I) (M := M) x r e K, smul_comm]
  change Tclm τ = _
  rw [hLHS', hRHS']

lemma riemannianFiberNormSq_eq_sum_componentRS_sq
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s S n e K J)
    (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x T =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) ^ 2 := by
  classical
  rw [hrepr T]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [fiberNormSqSummand_eq_component_sq]

lemma tangent_orthonormalBasisRS_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace r s I x,
        riemannianFiberNormSq (I := I) (M := M) g r s x S =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x r s S n e K J := by
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

end Elliptic
end Analysis
end DifferentialGeometry

end
