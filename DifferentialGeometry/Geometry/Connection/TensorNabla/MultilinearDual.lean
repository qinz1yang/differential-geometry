import DifferentialGeometry.Tensor.Multilinear.Dual
import DifferentialGeometry.Geometry.Connection.TensorNabla.Multilinear
import DifferentialGeometry.Geometry.Connection.Trivial

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_finset_prod_apply {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → M → ℝ) {x : M}
    (h : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) (X : TangentSpace I x) :
    mvfderiv (I := I) (∏ i ∈ s, f i) x X =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * mvfderiv (I := I) (f i) x X := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact congrArg (fun L => L X) (mvfderiv_const (I := I) (1 : ℝ))
  | @insert i s hi ih =>
    have hi' := h i (Finset.mem_insert_self i s)
    have hs (j : ι) (hj : j ∈ s) := h j (Finset.mem_insert_of_mem hj)
    have hprod : MDifferentiableAt I 𝓘(ℝ, ℝ) (∏ j ∈ s, f j) x :=
      MDifferentiableAt.prod (t := s) (f := f) hs
    rw [Finset.prod_insert hi, mvfderiv_mul hi' hprod]
    simp only [add_apply, smul_apply, smul_eq_mul, Finset.prod_apply]
    rw [ih hs, Finset.mul_sum, Finset.sum_insert hi, Finset.erase_insert hi]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.erase_insert_of_ne (by intro hij; exact hi (hij ▸ hj)),
      Finset.prod_insert (by simp [hi])]
    ring

theorem multilinear_tensorOfDualLinearForms
    (cov : CovariantDerivative I F V) (k : ℕ)
    (α : Fin k → ∀ x, V x →L[ℝ] ℝ) {x : M}
    (hα : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun y => (⟨y, α i y⟩ : TotalSpace (F →L[ℝ] ℝ) (Bundle.dual ℝ V))) x)
    (X : TangentSpace I x) :
    cov.multilinear k
        (fun y => ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V y) k (fun i => α i y)) x X =
      ∑ i, ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) k
        (Function.update (fun j => α j x) i
          (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i) x X)) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  choose Y hY using fun i => ContMDiffSection.exists_eq_at (I := I) (F := F) (V := V)
    (n := (⊤ : ℕ∞)) x (v i)
  have hvec : (fun i => Y i x) = v := funext hY
  rw [← hvec, cov.multilinear_apply k (fun i y => Y i y)
    (MDifferentiableAt.tensorOfDualLinearForms_bundle k α hα)
    (fun i => (Y i).mdifferentiableAt) X]
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x X
  have hdual (i : Fin k) :
      DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i) x X (Y i x) =
        mvfderiv (I := I) (fun y => α i y (Y i y)) x X - α i x (cov (Y i) x X) := by
    rw [← hZ]
    exact DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i)
      (hα i) Z.mdifferentiableAt (Y i).mdifferentiableAt
  have hscalar (i : Fin k) : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => α i y (Y i y)) x := by
    have h := (hα i).clm_bundle_apply (Y i).mdifferentiableAt
    rw [mdifferentiableAt_totalSpace] at h
    exact h.2
  have hprod : mvfderiv (I := I) (fun y => ∏ i, α i y (Y i y)) x X =
      ∑ i, (∏ j ∈ Finset.univ.erase i, α j x (Y j x)) *
        mvfderiv (I := I) (fun y => α i y (Y i y)) x X := by
    simpa only [Finset.prod_fn] using mvfderiv_finset_prod_apply Finset.univ
      (fun i y => α i y (Y i y)) (fun i _ => hscalar i) X
  simp only [sum_apply, ContinuousMultilinearMap.tensorOfDualLinearForms_apply]
  rw [hprod, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hleft : (fun j => α j x (Function.update (fun j => Y j x) i (cov (Y i) x X) j)) =
      Function.update (fun j => α j x (Y j x)) i (α i x (cov (Y i) x X)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  have hright : (fun j => Function.update (fun j => α j x) i
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i) x X) j (Y j x)) =
      Function.update (fun j => α j x (Y j x)) i
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i) x X (Y i x)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hleft, hright, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i), hdual, Finset.sdiff_singleton_eq_erase]
  ring

theorem dualMultilinearFiberwiseEquiv_covariantDerivative
    (cov : CovariantDerivative I F V) (k : ℕ)
    (φ : ∀ y, Bundle.continuousMultilinearMap ℝ k F V y →L[ℝ] ℝ) {x : M}
    (hφ : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ))
      (fun y => (⟨y, φ y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ)
        (Bundle.dual ℝ (Bundle.continuousMultilinearMap ℝ k F V)))) x)
    (X : TangentSpace I x) :
    Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv (F := F) (E := V) k x
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) ℝ (Bundle.Trivial M ℝ)
        (cov.multilinear k) (trivial I M ℝ) φ x X) =
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ)).multilinear k
          (fun y => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv
            (F := F) (E := V) k y (φ y)) x X := by
  classical
  let D := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
    I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ)
  let T := Bundle.continuousMultilinearMap ℝ k F V
  let G := ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ
  let Ψ := fun y => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv
    (F := F) (E := V) k y (φ y)
  have hΨ : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F →L[ℝ] ℝ) ℝ))
      (fun y => (⟨y, Ψ y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F →L[ℝ] ℝ) ℝ)
        (Bundle.continuousMultilinearMap ℝ k (F →L[ℝ] ℝ) (Bundle.dual ℝ V)))) x :=
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth
      (IB := I) (n := ∞) (F := F) (E := V) k).mdifferentiableAt (by simp) |>.comp x hφ
  apply ContinuousMultilinearMap.ext
  intro α
  choose A hA using fun i => ContMDiffSection.exists_eq_at (I := I)
    (F := F →L[ℝ] ℝ) (V := Bundle.dual ℝ V) (n := (⊤ : ℕ∞)) x (α i)
  have hα : (fun i => A i x) = α := funext hA
  rw [← hα]
  rw [Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply]
  change DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
    I M G T ℝ (Bundle.Trivial M ℝ) (cov.multilinear k) (trivial I M ℝ) φ x X
      (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) k (fun i => A i x)) =
    D.multilinear k Ψ x X (fun i => A i x)
  rw [D.multilinear_apply k (fun i y => A i y) hΨ (fun i => (A i).mdifferentiableAt) X]
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x X
  have htensor := MDifferentiableAt.tensorOfDualLinearForms_bundle k
    (fun i y => A i y) (fun i => (A i).mdifferentiableAt (x := x))
  have hdual := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M G T ℝ (Bundle.Trivial M ℝ) (cov.multilinear k) (trivial I M ℝ) φ hφ
    (Z.mdifferentiableAt (x := x)) htensor
  rw [hZ] at hdual
  change _ = mvfderiv (I := I)
    (fun y => φ y (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V y) k
      (fun i => A i y))) x X -
    φ x (cov.multilinear k
      (fun y => ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V y) k
        (fun i => A i y)) x X) at hdual
  rw [hdual, cov.multilinear_tensorOfDualLinearForms k
    (fun i y => A i y) (fun i => (A i).mdifferentiableAt) X, map_sum]
  simp only [Ψ, Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_apply]
  rfl

theorem dualMultilinearFiberwiseEquiv_symm_covariantDerivative
    (cov : CovariantDerivative I F V) (k : ℕ)
    (Ψ : ∀ y, Bundle.continuousMultilinearMap ℝ k (F →L[ℝ] ℝ) (Bundle.dual ℝ V) y) {x : M}
    (hΨ : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F →L[ℝ] ℝ) ℝ))
      (fun y => (⟨y, Ψ y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F →L[ℝ] ℝ) ℝ)
        (Bundle.continuousMultilinearMap ℝ k (F →L[ℝ] ℝ) (Bundle.dual ℝ V)))) x)
    (X : TangentSpace I x) :
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv (F := F) (E := V) k x).symm
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ)).multilinear k Ψ x X) =
      DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V) ℝ (Bundle.Trivial M ℝ)
        (cov.multilinear k) (trivial I M ℝ)
        (fun y => (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv
          (F := F) (E := V) k y).symm (Ψ y)) x X := by
  let φ := fun y => (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv
    (F := F) (E := V) k y).symm (Ψ y)
  have hφ : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ))
      (fun y => (⟨y, φ y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ →L[ℝ] ℝ)
        (Bundle.dual ℝ (Bundle.continuousMultilinearMap ℝ k F V)))) x :=
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth
      (IB := I) (n := ∞) (F := F) (E := V) k).mdifferentiableAt (by simp) |>.comp x hΨ
  apply (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv
    (F := F) (E := V) k x).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := cov.dualMultilinearFiberwiseEquiv_covariantDerivative k φ hφ X
  simpa only [φ, LinearEquiv.apply_symm_apply] using h.symm

theorem hom_multilinear_apply_tensorOfDualLinearForms
    (cov : CovariantDerivative I F V) (r s : ℕ)
    (A : ∀ y, Bundle.continuousMultilinearMap ℝ r F V y →L[ℝ]
      Bundle.continuousMultilinearMap ℝ s F V y)
    (α : Fin r → ∀ y, V y →L[ℝ] ℝ) (Y : Fin s → ∀ y, V y) {x : M}
    (hA : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ))
      (fun y => (⟨y, A y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
        (fun y => Bundle.continuousMultilinearMap ℝ r F V y →L[ℝ]
          Bundle.continuousMultilinearMap ℝ s F V y))) x)
    (hα : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun y => (⟨y, α i y⟩ : TotalSpace (F →L[ℝ] ℝ) (Bundle.dual ℝ V))) x)
    (hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : TotalSpace F V)) x)
    (X : TangentSpace I x) :
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ)
      (Bundle.continuousMultilinearMap ℝ r F V)
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
      (Bundle.continuousMultilinearMap ℝ s F V)
      (cov.multilinear r) (cov.multilinear s) A x X
        (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r (fun i => α i x))
        (fun i => Y i x) =
      mvfderiv (I := I) (fun y =>
        A y (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V y) r (fun i => α i y))
          (fun j => Y j y)) x X -
      ∑ j, A x (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r
        (fun i => α i x)) (Function.update (fun i => Y i x) j (cov (Y j) x X)) -
      ∑ i, A x (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r
        (Function.update (fun j => α j x) i
          (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V ℝ (Bundle.Trivial M ℝ) cov (trivial I M ℝ) (α i) x X)))
        (fun j => Y j x) := by
  classical
  have hT := MDifferentiableAt.tensorOfDualLinearForms_bundle r α hα
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x X
  have h :=
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ)
    (Bundle.continuousMultilinearMap ℝ r F V)
    (ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
    (Bundle.continuousMultilinearMap ℝ s F V)
    (cov.multilinear r) (cov.multilinear s) A hA (Z.mdifferentiableAt (x := x)) hT
  rw [hZ] at h
  rw [h]
  simp only [sub_apply]
  rw [cov.multilinear_apply s Y (hA.clm_bundle_apply hT) hY X,
    cov.multilinear_tensorOfDualLinearForms r α hα X, map_sum]
  simp only [sum_apply]

end CovariantDerivative
