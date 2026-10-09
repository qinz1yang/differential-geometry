import DifferentialGeometry.Geometry.Metric.BundleMultilinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.Multilinear
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Hom
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Trivial
import DifferentialGeometry.Geometry.Connection.PullbackMetric

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem IsMetricCompatible.multilinear {cov : CovariantDerivative I F V}
    (hcov : cov.IsMetricCompatible) (k : ℕ) :
    letI : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
      ⟨(multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V k).toRiemannianMetric⟩
    let tensorNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => (tensorNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : IsContMDiffRiemannianBundle I 1
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) :=
      ⟨(multilinearRiemannianMetric (F := F) V k).inner,
        contMDiff_multilinearRiemannianMetric_inner (IB := I) (n := 1) V k, fun _ _ _ => rfl⟩
    (CovariantDerivative.multilinear cov k).IsMetricCompatible := by
  induction k with
  | zero =>
    let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ 0 F V) :=
      ⟨(multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V 0).toRiemannianMetric⟩
    let sourceNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ 0 F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ 0 F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ 0 F V x) :=
      fun x => (sourceNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ 0 F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ 0 F V) x
    dsimp only
    have he : ContMDiff (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ))
        (I.prod 𝓘(ℝ, ℝ)) 1
        (fun p : TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ 0 F V) =>
          (⟨p.proj, Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) p.proj p.snd⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
      ContMDiff.multilinear_bundle_curry_zero contMDiff_id
    apply (trivial_isMetricCompatible I M ℝ).pullbackFiberwiseLinearEquiv
      (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ)
      (V₁ := Bundle.continuousMultilinearMap ℝ 0 F V)
      (fun x => (Bundle.continuousMultilinearMap.curryFin0Equiv (F := F) (E := V) x).toLinearEquiv)
      he
    intro x A C
    rfl
  | succ k ih =>
    let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let gk := multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V k
    let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) := ⟨gk.toRiemannianMetric⟩
    let tensorNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ k F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => (tensorNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ k F V) x
    have hk : (CovariantDerivative.multilinear cov k).IsMetricCompatible := ih
    let gH := homContMDiffRiemannianMetric (IB := I) (n := 1) (FU := F)
      (FV := ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
      V (Bundle.continuousMultilinearMap ℝ k F V)
    let _ : RiemannianBundle (fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) :=
      ⟨gH.toRiemannianMetric⟩
    let homNorm : ∀ x, NormedAddCommGroup (V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) x
    let _ : ∀ x, SeminormedAddCommGroup (V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => (homNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) :=
      fun x => Bundle.instInnerProductSpaceReal
        (E := fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) x
    have hH := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isMetricCompatible
      cov hcov (CovariantDerivative.multilinear cov k) hk
    have he : ContMDiff (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ))
        (I.prod 𝓘(ℝ, F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)) 1
        (fun p : TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ (k + 1) F V) =>
          (⟨p.proj, Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k p.proj p.snd⟩ :
            TotalSpace (F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
              (fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x))) :=
      ContMDiff.multilinear_bundle_curry_left contMDiff_id
    let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ (k + 1) F V) :=
      ⟨(multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V (k + 1)).toRiemannianMetric⟩
    let sourceNorm : ∀ x, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ (k + 1) F V x) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousMultilinearMap ℝ (k + 1) F V) x
    let _ : ∀ x, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ (k + 1) F V x) :=
      fun x => (sourceNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ (k + 1) F V x) :=
      fun x => Bundle.instInnerProductSpaceReal (E := Bundle.continuousMultilinearMap ℝ (k + 1) F V) x
    dsimp only at hH ⊢
    apply hH.pullbackFiberwiseLinearEquiv
      (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)
      (V₁ := Bundle.continuousMultilinearMap ℝ (k + 1) F V)
      (fun x => (Bundle.continuousMultilinearMap.curryLeftEquiv (F := F) (E := V) k x).toLinearEquiv)
      he
    intro x A C
    change gH.inner x _ _ = (multilinearRiemannianMetric V (k + 1)).inner x A C
    rw [multilinearRiemannianMetric_inner_succ_eq_sum V k x (stdOrthonormalBasis ℝ (V x))]
    dsimp only [gH]
    rw [homContMDiffRiemannianMetric_inner,
      ContinuousLinearMap.hilbertSchmidtInner_eq_sum (stdOrthonormalBasis ℝ (V x))]
    apply Finset.sum_congr rfl
    intro i _
    change gk.inner x _ _ = (multilinearRiemannianMetric V k).inner x _ _
    rfl

theorem IsMetricCompatible.multilinear_mvfderiv_inner
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ)
    {T S : ∀ x, Bundle.continuousMultilinearMap ℝ k F V x} {x : M}
    (hT : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V))) x)
    (hS : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
      (fun y => (⟨y, S y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V))) x)
    (X : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y => (multilinearRiemannianMetric (F := F) V k).inner y (T y) (S y)) x (X) =
      (multilinearRiemannianMetric (F := F) V k).inner x
        ((CovariantDerivative.multilinear cov k) T x X) (S x) +
      (multilinearRiemannianMetric (F := F) V k).inner x (T x)
        ((CovariantDerivative.multilinear cov k) S x X) := by
  let _ : RiemannianBundle (Bundle.continuousMultilinearMap ℝ k F V) :=
    ⟨(multilinearContMDiffRiemannianMetric (IB := I) (n := 1)
      (F := F) V k).toRiemannianMetric⟩
  let tensorNorm : ∀ y, NormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousMultilinearMap ℝ k F V) y
  let _ : ∀ y, SeminormedAddCommGroup (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => (tensorNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (Bundle.continuousMultilinearMap ℝ k F V y) :=
    fun y => Bundle.instInnerProductSpaceReal
      (E := Bundle.continuousMultilinearMap ℝ k F V) y
  have hmc : (CovariantDerivative.multilinear cov k).IsMetricCompatible :=
    CovariantDerivative.IsMetricCompatible.multilinear hcov k
  have h := hmc.mvfderiv_inner_eq (X := fun y => X) hT hS
  change d% (fun y => (multilinearRiemannianMetric (F := F) V k).inner y (T y) (S y)) x X =
    (multilinearRiemannianMetric (F := F) V k).inner x
      ((CovariantDerivative.multilinear cov k) T x X) (S x) +
      (multilinearRiemannianMetric (F := F) V k).inner x (T x)
        ((CovariantDerivative.multilinear cov k) S x X) at h
  change d% (fun y => (multilinearRiemannianMetric (F := F) V k).inner y (T y) (S y)) x X = _
  simpa only [multilinearContMDiffRiemannianMetric_toRiemannianMetric] using h

end CovariantDerivative
