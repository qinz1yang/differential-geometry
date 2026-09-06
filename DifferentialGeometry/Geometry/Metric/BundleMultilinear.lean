import DifferentialGeometry.Geometry.Metric.BundleHom
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Bundle.Hom.Regularity
import DifferentialGeometry.Tensor.Multilinear.BundleCurry
import DifferentialGeometry.Tensor.Multilinear.Fiber
import Mathlib.Topology.VectorBundle.FiniteDimensional

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Bundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def multilinearRiemannianMetric : (k : ℕ) →
    RiemannianMetric (Bundle.continuousMultilinearMap ℝ k F V)
  | 0 => (RiemannianMetric.ofInnerProductSpace (fun _ : B => ℝ)).pullback id
      (fun x => Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) x)
  | k + 1 => by
    let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
      ⟨multilinearRiemannianMetric k⟩
    let tensorNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => (tensorNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) x
    exact (homRiemannianMetric V (Bundle.continuousMultilinearMap ℝ k F V)).pullback id
      (fun x => Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x)

@[simp]
theorem multilinearRiemannianMetric_inner_zero (x : B)
    (T S : Bundle.continuousMultilinearMap ℝ 0 F V x) :
    (multilinearRiemannianMetric (F := F) V 0).inner x T S = T Fin.elim0 * S Fin.elim0 := by
  change inner ℝ (Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) x T)
    (Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) x S) = _
  simp only [Bundle.continuousMultilinearMap.curryFin0Equiv_apply, Real.inner_apply]

theorem multilinearRiemannianMetric_inner_succ_eq_sum {ι : Type*} [Fintype ι]
    (k : ℕ) (x : B) (b : OrthonormalBasis ι ℝ (V x))
    (T S : Bundle.continuousMultilinearMap ℝ (k + 1) F V x) :
    (multilinearRiemannianMetric (F := F) V (k + 1)).inner x T S =
      ∑ i, (multilinearRiemannianMetric (F := F) V k).inner x
        (Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x T (b i))
        (Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x S (b i)) := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
    ⟨multilinearRiemannianMetric V k⟩
  let tensorNorm : ∀ y, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousMultilinearMap ℝ k F V) y
  let _ : ∀ y, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => (tensorNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) y
  change (homRiemannianMetric V (Bundle.continuousMultilinearMap ℝ k F V)).inner x
    (Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x T)
    (Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x S) = _
  exact homRiemannianMetric_inner_eq_sum V (Bundle.continuousMultilinearMap ℝ k F V) x b _ _

theorem multilinearRiemannianMetric_inner_eq_sum {ι : Type*} [Fintype ι]
    (k : ℕ) (x : B) (b : OrthonormalBasis ι ℝ (V x))
    (T S : Bundle.continuousMultilinearMap ℝ k F V x) :
    (multilinearRiemannianMetric (F := F) V k).inner x T S =
      ∑ j : Fin k → ι, T (fun i => b (j i)) * S (fun i => b (j i)) := by
  classical
  induction k with
  | zero =>
    rw [multilinearRiemannianMetric_inner_zero]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    congr 2 <;> funext i <;> exact Fin.elim0 i
  | succ k ih =>
    rw [multilinearRiemannianMetric_inner_succ_eq_sum V k x b]
    simp_rw [ih, Bundle.continuousMultilinearMap.curryLeftEquiv_apply]
    rw [← Fintype.sum_prod_type (fun j : ι × (Fin k → ι) =>
      T (Fin.cons (b j.1) (fun i => b (j.2 i))) *
        S (Fin.cons (b j.1) (fun i => b (j.2 i))))]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ι))
    intro j
    simp only [Fin.consEquiv_apply]
    congr 2 <;> funext i <;> refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end Bundle


namespace Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

local instance multilinearDualModelNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance multilinearDualModelNormedSpace (k : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance multilinearBilinearModelNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance multilinearBilinearModelNormedSpace (k : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem contMDiff_multilinearRiemannianMetric_inner (k : ℕ) :
    ContMDiff IB
      (IB.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ)) n
      (fun x => (⟨x, (multilinearRiemannianMetric (F := F) V k).inner x⟩ :
        TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ)
          (fun x => Bundle.continuousMultilinearMap ℝ k F V x →L[ℝ]
            Bundle.continuousMultilinearMap ℝ k F V x →L[ℝ] ℝ))) := by
  induction k with
  | zero =>
    let g : ContMDiffRiemannianMetric IB n ℝ (Bundle.Trivial B ℝ) := {
      RiemannianMetric.ofInnerProductSpace (Bundle.Trivial B ℝ) with
      contMDiff := by
        obtain ⟨h, hh, hi⟩ :=
          (inferInstance : IsContMDiffRiemannianBundle IB n ℝ (Bundle.Trivial B ℝ)).exists_contMDiff
        apply hh.congr
        intro x
        apply TotalSpace.mk_inj.mpr
        apply ContinuousLinearMap.ext
        intro v
        apply ContinuousLinearMap.ext
        intro w
        exact hi x v w }
    let q := g.pullbackFiberwiseContinuousLinearEquiv
      (fun x => Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) x)
      (ContMDiff.clm_bundle_of_map (ContMDiff.multilinear_bundle_curry_zero contMDiff_id))
    exact q.contMDiff
  | succ k ih =>
    let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
      ⟨multilinearRiemannianMetric V k⟩
    let tensorNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => (tensorNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : IsContMDiffRiemannianBundle IB n
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) :=
      ⟨(multilinearRiemannianMetric V k).inner, ih, fun _ _ _ => rfl⟩
    let g := homContMDiffRiemannianMetric (IB := IB) (n := n) (FU := F)
      (FV := ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
      V (Bundle.continuousMultilinearMap ℝ k F V)
    let q := g.pullbackFiberwiseContinuousLinearEquiv
      (fun x => Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x)
      (ContMDiff.clm_bundle_of_map (ContMDiff.multilinear_bundle_curry_left contMDiff_id))
    have hq : q.toRiemannianMetric = multilinearRiemannianMetric V (k + 1) := by
      rw [ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric,
        homContMDiffRiemannianMetric_toRiemannianMetric]
      rfl
    exact q.contMDiff.congr fun x =>
      congrArg (fun A => TotalSpace.mk x A) (congrArg (fun h => h.inner x) hq).symm

def multilinearContMDiffRiemannianMetric (k : ℕ) :
    ContMDiffRiemannianMetric IB n
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
      (Bundle.continuousMultilinearMap ℝ k F V) where
  inner := (multilinearRiemannianMetric V k).inner
  symm := (multilinearRiemannianMetric V k).symm
  pos := (multilinearRiemannianMetric V k).pos
  isVonNBounded := (multilinearRiemannianMetric V k).isVonNBounded
  contMDiff := contMDiff_multilinearRiemannianMetric_inner V k

@[simp]
theorem multilinearContMDiffRiemannianMetric_toRiemannianMetric (k : ℕ) :
    (multilinearContMDiffRiemannianMetric (IB := IB) (n := n) (F := F) V k).toRiemannianMetric =
      multilinearRiemannianMetric V k := rfl

end Bundle
