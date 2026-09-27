import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Geometry.Metric.Pullback.Local

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [I.Boundaryless] [T2Space N] in
private theorem first_variation_pair_of_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hmetric : g = localPullMetric h f hf)
    {η : ℝ → ℝ → M} {β : ℝ → ℝ → N} {r : ℝ}
    (hη : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (fun z : ℝ × ℝ => η z.1 z.2) (0, r))
    (heq : (fun z : ℝ × ℝ => β z.1 z.2) =ᶠ[𝓝 (0, r)]
      f ∘ (fun z => η z.1 z.2)) :
    h.inner (β 0 r) (lVelocity (I := I) (fun z => β z r) 0) (lVelocity (I := I) (β 0) r) =
      g.inner (η 0 r) (lVelocity (I := I) (fun z => η z r) 0) (lVelocity (I := I) (η 0) r) := by
  have hpoint : β 0 r = f (η 0 r) := heq.self_of_nhds
  have hηvar : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => η z r) 0 :=
    hη.comp 0 (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hηtime : MDifferentiableAt 𝓘(ℝ, ℝ) I (η 0) r :=
    hη.comp r (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have heqvar : (fun z => β z r) =ᶠ[𝓝 0] f ∘ (fun z => η z r) :=
    heq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have heqtime : β 0 =ᶠ[𝓝 r] f ∘ η 0 :=
    heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hvar : lVelocity (I := I) (fun z => β z r) 0 =
      mfderiv I I f (η 0 r) (lVelocity (I := I) (fun z => η z r) 0) := by
    unfold lVelocity
    rw [heqvar.mfderiv_eq, mfderiv_comp 0 ((hf _).contMDiffAt.mdifferentiableAt (by simp)) hηvar]
    rfl
  have htime : lVelocity (I := I) (β 0) r =
      mfderiv I I f (η 0 r) (lVelocity (I := I) (η 0) r) := by
    unfold lVelocity
    rw [heqtime.mfderiv_eq, mfderiv_comp r ((hf _).contMDiffAt.mdifferentiableAt (by simp)) hηtime]
    rfl
  rw [hmetric, localPullMetric_inner, hpoint, hvar, htime]

theorem hasDerivAt_sum_lRegularizedAction_of_local_isometries
    {n : ℕ} (M : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (D : Fin (n + 1) → RealTimeInterval)
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (t : Fin (n + 2) → ℝ)
    (α : (i : Fin (n + 1)) → ℝ → ℝ → M i)
    (hα : ∀ i, IsSmoothVariation (I := I) (α i))
    (hclock : ∀ i, ∀ s ∈ uIcc (t i.castSucc) (t i.succ), T - s ^ 2 ∈ (D i).regular)
    (X : Fin n → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (X i)]
    (g : (i : Fin n) → SmoothRiemannianMetric I (X i))
    (η : (i : Fin n) → ℝ → ℝ → X i)
    (leftMap : (i : Fin n) → X i → M i.castSucc)
    (rightMap : (i : Fin n) → X i → M i.succ)
    (hleft : ∀ i, IsLocalDiffeomorph I I ∞ (leftMap i))
    (hright : ∀ i, IsLocalDiffeomorph I I ∞ (rightMap i))
    (hmetricLeft : ∀ i : Fin n, g i = localPullMetric
      ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)) (leftMap i) (hleft i))
    (hmetricRight : ∀ i : Fin n, g i = localPullMetric
      ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2)) (rightMap i) (hright i))
    (hη : ∀ i : Fin n, MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I
      (fun z : ℝ × ℝ => η i z.1 z.2) (0, t i.castSucc.succ))
    (hmatchLeft : ∀ i : Fin n,
      (fun z : ℝ × ℝ => α i.castSucc z.1 z.2) =ᶠ[𝓝 (0, t i.castSucc.succ)]
        (leftMap i) ∘ (fun z => η i z.1 z.2))
    (hmatchRight : ∀ i : Fin n,
      (fun z : ℝ × ℝ => α i.succ z.1 z.2) =ᶠ[𝓝 (0, t i.castSucc.succ)]
        (rightMap i) ∘ (fun z => η i z.1 z.2)) :
    HasDerivAt (fun z : ℝ => ∑ i : Fin (n + 1),
      lRegularizedAction (S i) T (α i z) (t i.castSucc) (t i.succ))
      (((S (Fin.last n)).base.metric (T - (t (Fin.last (n + 1))) ^ 2)).inner
        (α (Fin.last n) 0 (t (Fin.last (n + 1))))
        (lVelocity (I := I) (fun z => α (Fin.last n) z (t (Fin.last (n + 1)))) 0)
        (lVelocity (I := I) (α (Fin.last n) 0) (t (Fin.last (n + 1)))) -
      ((S 0).base.metric (T - (t 0) ^ 2)).inner (α 0 0 (t 0))
        (lVelocity (I := I) (fun z => α 0 z (t 0)) 0) (lVelocity (I := I) (α 0 0) (t 0)) -
      ∑ i : Fin (n + 1), ∫ s in t i.castSucc..t i.succ,
        lRegularizedEulerPair (S i) T (α i 0) s
          (lVelocity (I := I) (fun z => α i z s) 0)) 0 := by
  let pair (i : Fin (n + 1)) (r : ℝ) := ((S i).base.metric (T - r ^ 2)).inner (α i 0 r)
    (lVelocity (I := I) (fun z => α i z r) 0) (lVelocity (I := I) (α i 0) r)
  have hmatch (i : Fin n) : pair i.castSucc (t i.castSucc.succ) = pair i.succ (t i.succ.castSucc) := by
    have htime : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    rw [htime]
    exact (first_variation_pair_of_local_isometry (g i) _ (leftMap i) (hleft i)
      (hmetricLeft i) (hη i) (hmatchLeft i)).trans
      (first_variation_pair_of_local_isometry (g i) _ (rightMap i) (hright i)
        (hmetricRight i) (hη i) (hmatchRight i)).symm
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    lRegularizedAction_first_variation (S i) (hS i) T (α i) (hα i)
      (t i.castSucc) (t i.succ) (hclock i))
  apply hsum.congr_deriv
  change (∑ i : Fin (n + 1), (pair i (t i.succ) - pair i (t i.castSucc) - _)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun i => pair i (t i.succ)),
    Fin.sum_univ_succ (fun i => pair i (t i.castSucc))]
  have hs : (∑ i : Fin n, pair i.castSucc (t i.castSucc.succ)) =
      ∑ i : Fin n, pair i.succ (t i.succ.castSucc) := Finset.sum_congr rfl (fun i _ => hmatch i)
  rw [hs]
  change ((∑ i : Fin n, pair i.succ (t i.succ.castSucc)) + pair (Fin.last n) (t (Fin.last (n + 1))) -
    (pair 0 (t 0) + ∑ i : Fin n, pair i.succ (t i.succ.castSucc))) - _ =
    pair (Fin.last n) (t (Fin.last (n + 1))) - pair 0 (t 0) - _
  abel

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
