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

end CovariantDerivative
