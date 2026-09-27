import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

namespace DirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}

def ofFiniteSupport (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ)
    (f : DirichletLaplacianEigenIndex g → ℝ)
    (hf : (Function.support f).Finite) :
    DirichletHs g σ where
  coeff := f
  weighted_summable := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset hf
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro hfi
    apply hi
    rw [hfi]
    ring

@[simp] lemma ofFiniteSupport_coeff (g : SmoothRiemannianMetric (I_half n) M)
    (σ : ℝ) (f : DirichletLaplacianEigenIndex g → ℝ)
    (hf : (Function.support f).Finite) :
    (ofFiniteSupport g σ f hf).coeff = f := rfl

open scoped Classical in
def basisVec (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ)
    (i : DirichletLaplacianEigenIndex g) :
    DirichletHs g σ :=
  ofFiniteSupport g σ
    (fun j => if j = i then (1 : ℝ) else 0)
    (by
      apply Set.Finite.subset (Set.finite_singleton i)
      intro j hj
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hj
      simpa using hj)

open scoped Classical in
@[simp] lemma basisVec_coeff (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ)
    (i j : DirichletLaplacianEigenIndex g) :
    (basisVec g σ i).coeff j =
      (if j = i then (1 : ℝ) else 0) := rfl

def finiteSupportSubmodule (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ) :
    Submodule ℝ (DirichletHs g σ) where
  carrier := {T | (Function.support T.coeff).Finite}
  add_mem' := by
    intro S T hS hT
    refine Set.Finite.subset (hS.union hT) ?_
    intro i hi
    simp only [Function.mem_support, add_coeff, ne_eq] at hi
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, ne_eq, not_or,
      not_not] at hcon
    exact hi (by rw [hcon.1, hcon.2, add_zero])
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, zero_coeff]
    refine Set.finite_empty.subset ?_
    intro i hi
    simp only [Function.mem_support, ne_eq, not_true_eq_false] at hi
  smul_mem' := by
    intro c T hT
    refine Set.Finite.subset hT ?_
    intro i hi
    simp only [Function.mem_support, smul_coeff, ne_eq] at hi
    simp only [Function.mem_support, ne_eq]
    intro hcon
    exact hi (by rw [hcon, mul_zero])

@[simp] lemma mem_finiteSupportSubmodule
    (T : DirichletHs g σ) :
    T ∈ finiteSupportSubmodule g σ ↔
      (Function.support T.coeff).Finite := Iff.rfl

theorem hasSum_smul_basisVec_of_finite
    (T : DirichletHs g σ)
    (hT : T ∈ finiteSupportSubmodule g σ) :
    T = ∑ i ∈ ((mem_finiteSupportSubmodule T).mp hT).toFinset,
      T.coeff i • basisVec g σ i := by
  classical
  set hT' := (mem_finiteSupportSubmodule T).mp hT
  refine DirichletHs.ext ?_
  funext j
  have h_sum : (∑ i ∈ hT'.toFinset,
        T.coeff i • basisVec g σ i).coeff j =
      ∑ i ∈ hT'.toFinset,
        (if j = i then T.coeff i else 0) := by
    induction hT'.toFinset using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
          DirichletHs.add_coeff]
        simp only [DirichletHs.smul_coeff, basisVec_coeff,
          mul_ite, mul_one, mul_zero]
  rw [h_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · intro hj
    have hzero : T.coeff j = 0 := by
      by_contra hne
      exact hj (hT'.mem_toFinset.mpr (Function.mem_support.mpr hne))
    simp [hzero]

open scoped Classical in
lemma rescaleEquivL2_smul_basisVec
    (T : DirichletHs g σ)
    (i : DirichletLaplacianEigenIndex g) :
    rescaleEquivL2 (g := g) (σ := σ)
        (T.coeff i • basisVec g σ i) =
      lp.single 2 i
        (Real.sqrt (dirichletSobolevWeight i σ) *
          T.coeff i) := by
  classical
  apply lp.ext
  funext j
  rw [rescaleEquivL2_apply, lp.single_apply]
  simp only [smul_coeff, basisVec_coeff]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem hasSum_smul_basisVec
    (T : DirichletHs g σ) :
    HasSum (fun i : DirichletLaplacianEigenIndex g =>
      T.coeff i • basisVec g σ i) T := by
  classical
  rw [← ContinuousLinearEquiv.hasSum'
    (e := (rescaleEquivL2
      (g := g) (σ := σ)).toContinuousLinearEquiv)]
  have h_l2 : HasSum
      (fun i : DirichletLaplacianEigenIndex g =>
        lp.single 2 i
          (Real.sqrt (dirichletSobolevWeight i σ) *
            T.coeff i))
      (rescaleEquivL2
        (g := g) (σ := σ) T) := by
    have h := lp.hasSum_single (α := DirichletLaplacianEigenIndex g)
      (E := fun _ => ℝ) (p := 2) (by norm_num)
      (rescaleEquivL2
        (g := g) (σ := σ) T)
    refine h.congr_fun (fun i => ?_)
    rw [rescaleEquivL2_apply]
  refine h_l2.congr_fun (fun i => ?_)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rescaleEquivL2_smul_basisVec]

theorem mem_closure_finiteSupportSubmodule
    (T : DirichletHs g σ) :
    T ∈ closure
      (finiteSupportSubmodule g σ :
        Set (DirichletHs g σ)) := by
  classical
  refine mem_closure_of_tendsto
    (hasSum_smul_basisVec T) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  rw [mem_finiteSupportSubmodule]
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro j hj
  simp only [Function.mem_support, basisVec_coeff, ne_eq,
    ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
  simpa using hj

end DirichletHs

theorem DirichletHs.finiteSupportSubmodule_topologicalClosure_eq_top
    {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ} :
    (DirichletHs.finiteSupportSubmodule g σ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro T _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact DirichletHs.mem_closure_finiteSupportSubmodule T

theorem DirichletHs.finiteSupportSubmodule_dense
    {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ} :
    Dense (DirichletHs.finiteSupportSubmodule g σ :
      Set (DirichletHs g σ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact DirichletHs.finiteSupportSubmodule_topologicalClosure_eq_top

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
