import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {D D' : RealTimeInterval}

private theorem lRegularizedLagrangian_eq_of_localPullMetric_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (Q : SolutionOn (I := I) (M := N) D')
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f) (T s : ℝ)
    (hmetric : g = localPullMetric (Q.base.metric (T - s ^ 2)) f hf)
    {α : ℝ → M} {β : ℝ → N} (hα : MDifferentiableAt 𝓘(ℝ, ℝ) I α s)
    (hmatch : β =ᶠ[𝓝 s] f ∘ α) :
    (1 / 2 : ℝ) * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) +
      2 * s ^ 2 * metricScalarAt g (α s) = lRegularizedLagrangian Q T β s := by
  have hpoint := hmatch.self_of_nhds
  have hvel : lVelocity (I := I) β s = mfderiv I I f (α s) (lVelocity (I := I) α s) := by
    unfold lVelocity
    rw [hmatch.mfderiv_eq, mfderiv_comp s ((hf _).contMDiffAt.mdifferentiableAt (by simp)) hα]
    rfl
  unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
  rw [hmetric, localPullMetric_inner, metricScalarAt_localPull, hpoint, hvel]
  rfl

private theorem sum_boundary_of_matching {n : ℕ} (left right : Fin (n + 1) → ℝ)
    (hmatch : ∀ i : Fin n, right i.castSucc = left i.succ) :
    (∑ i, (right i - left i)) = right (Fin.last n) - left 0 := by
  rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc right, Fin.sum_univ_succ left]
  have hs : (∑ i : Fin n, right i.castSucc) = ∑ i : Fin n, left i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    exact hmatch i
  rw [hs]
  ring

theorem sum_integral_lHamSq_eq_boundary_of_local_isometries
    {n : ℕ} (M : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (D : Fin (n + 1) → RealTimeInterval)
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (t : Fin (n + 2) → ℝ) (ht : Monotone t)
    (α : (i : Fin (n + 1)) → ℝ → M i)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (α i) (Ioo (t i.castSucc) (t i.succ)))
    (hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (α i)) (Icc (t i.castSucc) (t i.succ)))
    (hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (α i)) volume (t i.castSucc) (t i.succ))
    (X : Fin n → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (X i)]
    (g : (i : Fin n) → SmoothRiemannianMetric I (X i))
    (η : (i : Fin n) → ℝ → X i)
    (leftMap : (i : Fin n) → X i → M i.castSucc)
    (rightMap : (i : Fin n) → X i → M i.succ)
    (hleft : ∀ i, IsLocalDiffeomorph I I ∞ (leftMap i))
    (hright : ∀ i, IsLocalDiffeomorph I I ∞ (rightMap i))
    (hmetricLeft : ∀ i : Fin n,
      g i =
        localPullMetric ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)) (leftMap i) (hleft i))
    (hmetricRight : ∀ i : Fin n,
      g i =
        localPullMetric ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2)) (rightMap i) (hright i))
    (hη : ∀ i : Fin n, MDifferentiableAt 𝓘(ℝ, ℝ) I (η i) (t i.castSucc.succ))
    (hmatchLeft : ∀ i : Fin n, α i.castSucc =ᶠ[𝓝 (t i.castSucc.succ)] (leftMap i) ∘ η i)
    (hmatchRight : ∀ i : Fin n, α i.succ =ᶠ[𝓝 (t i.castSucc.succ)] (rightMap i) ∘ η i) :
    4 * (∑ i : Fin (n + 1), ∫ r in t i.castSucc..t i.succ, lHamSq (S i) T (α i) r) =
      (∑ i : Fin (n + 1), lRegularizedAction (S i) T (α i) (t i.castSucc) (t i.succ)) -
        (t (Fin.last (n + 1)) * lRegularizedLagrangian (S (Fin.last n)) T (α (Fin.last n)) (t (Fin.last (n + 1))) -
          t 0 * lRegularizedLagrangian (S 0) T (α 0) (t 0)) := by
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_lHamSq_eq_boundary_of_geodesic (S i) (hS i) T (α i)
      (ht i.castSucc_le_succ) (hgeo i) (hLag i) (hHam i))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hboundary := sum_boundary_of_matching
    (fun i : Fin (n + 1) => t i.castSucc * lRegularizedLagrangian (S i) T (α i) (t i.castSucc))
    (fun i : Fin (n + 1) => t i.succ * lRegularizedLagrangian (S i) T (α i) (t i.succ)) (by
      intro i
      have hclock : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hclock]
      congr 1
      exact (lRegularizedLagrangian_eq_of_localPullMetric_of_eventuallyEq
        (g i) (S i.castSucc) (leftMap i) (hleft i) T (t i.castSucc.succ)
        (hmetricLeft i) (hη i) (hmatchLeft i)).symm.trans
          (lRegularizedLagrangian_eq_of_localPullMetric_of_eventuallyEq
            (g i) (S i.succ) (rightMap i) (hright i) T (t i.castSucc.succ)
            (hmetricRight i) (hη i) (hmatchRight i)))
  rw [hboundary] at hsum
  exact hsum

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
