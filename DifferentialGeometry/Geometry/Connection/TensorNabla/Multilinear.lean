import DifferentialGeometry.Tensor.Multilinear.BundleCurry
import DifferentialGeometry.Geometry.Connection.Trivial
import DifferentialGeometry.Geometry.Connection.Pullback
import DifferentialGeometry.Geometry.Connection.HomBundle.Basic

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

private theorem contMDiff_curry_zero :
    ContMDiff (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ 0 F V) =>
        (⟨p.1, Bundle.continuousMultilinearMap.curryFin0Equiv
          (𝕜 := ℝ) (F := F) (E := V) p.1 p.2⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
  ContMDiff.multilinear_bundle_curry_zero contMDiff_id

private theorem contMDiff_uncurry_zero :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ)) ∞
      (fun p : TotalSpace ℝ (Bundle.Trivial M ℝ) =>
        (⟨p.1, (Bundle.continuousMultilinearMap.curryFin0Equiv
          (𝕜 := ℝ) (F := F) (E := V) p.1).symm p.2⟩ : TotalSpace
            (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) ℝ)
            (Bundle.continuousMultilinearMap ℝ 0 F V))) :=
  ContMDiff.multilinear_bundle_uncurry_zero contMDiff_id

private theorem contMDiff_curry_succ (k : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ))
      (I.prod 𝓘(ℝ, F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)) ∞
      (fun p : TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ (k + 1) F V) =>
        (⟨p.1, Bundle.continuousMultilinearMap.curryLeftEquiv
          (𝕜 := ℝ) (F := F) (E := V) k p.1 p.2⟩ : TotalSpace
            (F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
            (fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x))) :=
  ContMDiff.multilinear_bundle_curry_left contMDiff_id

private theorem contMDiff_uncurry_succ (k : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (fun x => V x →L[ℝ] Bundle.continuousMultilinearMap ℝ k F V x) =>
        (⟨p.1, (Bundle.continuousMultilinearMap.curryLeftEquiv
          (𝕜 := ℝ) (F := F) (E := V) k p.1).symm p.2⟩ : TotalSpace
            (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)
            (Bundle.continuousMultilinearMap ℝ (k + 1) F V))) :=
  ContMDiff.multilinear_bundle_uncurry_left contMDiff_id

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

def multilinear (cov : CovariantDerivative I F V) : (k : ℕ) →
    CovariantDerivative I (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
      (Bundle.continuousMultilinearMap ℝ k F V)
  | 0 =>
    pullbackFiberwiseLinearEquiv
      (fun x => (Bundle.continuousMultilinearMap.curryFin0Equiv
        (𝕜 := ℝ) (F := F) (E := V) x).toLinearEquiv)
      (contMDiff_curry_zero.of_le (by norm_num)) (trivial I M ℝ)
  | k + 1 => by
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    letI : CompleteSpace F := FiniteDimensional.complete ℝ F
    exact pullbackFiberwiseLinearEquiv
      (fun x => (Bundle.continuousMultilinearMap.curryLeftEquiv
        (𝕜 := ℝ) (F := F) (E := V) k x).toLinearEquiv)
      ((contMDiff_curry_succ k).of_le (by norm_num))
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) cov (multilinear cov k))

private theorem multilinear_succ_contMDiff (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (k : ℕ)
    (ih : ContMDiffCovariantDerivative (multilinear cov k) ∞) :
    ContMDiffCovariantDerivative (multilinear cov (k + 1)) ∞ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let := ih
  let covH := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
    I M F V (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
    (Bundle.continuousMultilinearMap ℝ k F V) cov (multilinear cov k)
  have hH : ContMDiffCovariantDerivative covH ∞ := inferInstance
  exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun x => (Bundle.continuousMultilinearMap.curryLeftEquiv
      (𝕜 := ℝ) (F := F) (E := V) k x).toLinearEquiv)
    (contMDiff_curry_succ (I := I) (F := F) (V := V) k)
    (contMDiff_uncurry_succ (I := I) (F := F) (V := V) k) covH

instance multilinear_contMDiff (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (k : ℕ) :
    ContMDiffCovariantDerivative (multilinear cov k) ∞ := by
  induction k with
  | zero =>
    exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv _
      contMDiff_curry_zero contMDiff_uncurry_zero (trivial I M ℝ)
  | succ k ih => exact multilinear_succ_contMDiff cov k ih

theorem multilinear_apply_zero (cov : CovariantDerivative I F V)
    (T : ∀ x, Bundle.continuousMultilinearMap ℝ 0 F V x)
    (x : M) (X : TangentSpace I x) (v : Fin 0 → V x) :
    multilinear cov 0 T x X v = mvfderiv (I := I) (fun y => T y Fin.elim0) x X := by
  change (Bundle.continuousMultilinearMap.curryFin0Equiv (𝕜 := ℝ) (F := F) (E := V) x).symm
    (trivial I M ℝ (fun y => Bundle.continuousMultilinearMap.curryFin0Equiv
      (𝕜 := ℝ) (F := F) (E := V) y (T y)) x X) v = _
  simp only [Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply, trivial_apply,
    Bundle.continuousMultilinearMap.curryFin0Equiv_apply]

theorem multilinear_apply_succ (cov : CovariantDerivative I F V) (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ (k + 1) F V x}
    {Y : ∀ x, V x} {x : M}
    (hT : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ (k + 1) F V))) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y y⟩ : TotalSpace F V)) x)
    (X : TangentSpace I x) (v : Fin k → V x) :
    multilinear cov (k + 1) T x X (Fin.cons (Y x) v) =
      multilinear cov k (fun y => Bundle.continuousMultilinearMap.curryLeftEquiv
        (𝕜 := ℝ) (F := F) (E := V) k y (T y) (Y y)) x X v -
      T x (Fin.cons (cov Y x X) v) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let A (y : M) := Bundle.continuousMultilinearMap.curryLeftEquiv
    (𝕜 := ℝ) (F := F) (E := V) k y (T y)
  obtain ⟨W, hWx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x X
  have h := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M F V (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
    (Bundle.continuousMultilinearMap ℝ k F V) cov (multilinear cov k) A
    hT.multilinear_bundle_curry_left W.mdifferentiableAt hY
  rw [hWx] at h
  change (Bundle.continuousMultilinearMap.curryLeftEquiv
    (𝕜 := ℝ) (F := F) (E := V) k x).symm
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) cov (multilinear cov k) A x X)
      (Fin.cons (Y x) v) = _
  simp only [Bundle.continuousMultilinearMap.curryLeftEquiv_symm_apply,
    Fin.cons_zero, Fin.tail_cons]
  simpa only [A, sub_apply,
    Bundle.continuousMultilinearMap.curryLeftEquiv_apply] using
      congrArg (fun S : Bundle.continuousMultilinearMap ℝ k F V x => S v) h

theorem multilinear_apply (cov : CovariantDerivative I F V) (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F V x}
    (Y : Fin k → ∀ x, V x) {x : M}
    (hT : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V))) x)
    (hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : TotalSpace F V)) x)
    (X : TangentSpace I x) :
    multilinear cov k T x X (fun i => Y i x) =
      mvfderiv (I := I) (fun y => T y (fun i => Y i y)) x X -
        ∑ i, T x (Function.update (fun j => Y j x) i (cov (Y i) x X)) := by
  classical
  induction k with
  | zero =>
    rw [multilinear_apply_zero]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    congr 2
    funext y
    exact congrArg (T y) (Subsingleton.elim _ _)
  | succ k ih =>
    let S (y : M) := Bundle.continuousMultilinearMap.curryLeftEquiv
      (𝕜 := ℝ) (F := F) (E := V) k y (T y) (Y 0 y)
    have hS : MDifferentiableAt I
        (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
        (fun y => (⟨y, S y⟩ : TotalSpace
          (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ k F V))) x :=
      hT.multilinear_bundle_curry_left.clm_bundle_apply (hY 0)
    have hrec := ih (fun i => Y i.succ) hS (fun i => hY i.succ)
    have hcons (y : M) :
        Fin.cons (Y 0 y) (fun i => Y i.succ y) = (fun i => Y i y) :=
      Fin.cons_self_tail (fun i => Y i y)
    have hscalar : (fun y => S y (fun i => Y i.succ y)) =
        (fun y => T y (fun i => Y i y)) := by
      funext y
      simp only [S, Bundle.continuousMultilinearMap.curryLeftEquiv_apply, hcons]
    have hsum :
        (∑ i : Fin k, S x (Function.update (fun j => Y j.succ x) i
          (cov (Y i.succ) x X))) =
        ∑ i : Fin k, T x (Function.update (fun j => Y j x) i.succ
          (cov (Y i.succ) x X)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [S, Bundle.continuousMultilinearMap.curryLeftEquiv_apply,
        Fin.cons_update, hcons]
    have hhead : T x (Fin.cons (cov (Y 0) x X) (fun i => Y i.succ x)) =
        T x (Function.update (fun j => Y j x) 0 (cov (Y 0) x X)) := by
      rw [← hcons x, Fin.update_cons_zero]
    have hsuc := multilinear_apply_succ cov k hT (hY 0) X (fun i => Y i.succ x)
    rw [hcons] at hsuc
    rw [hsuc]
    change multilinear cov k S x X (fun i => Y i.succ x) - _ = _
    rw [hrec, hscalar, hsum, hhead, Fin.sum_univ_succ]
    ring

end CovariantDerivative
