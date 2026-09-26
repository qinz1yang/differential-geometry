import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.MovingEndpointSecondVariation
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private theorem second_variation_pair_of_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hmetric : g = localPullMetric h f hf)
    {η : ℝ → ℝ → M} {β : ℝ → ℝ → N} {r : ℝ}
    (hη : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => η z.1 z.2) (0, r))
    (heq : (fun z : ℝ × ℝ => β z.1 z.2) =ᶠ[𝓝 (0, r)]
      f ∘ (fun z => η z.1 z.2)) :
    h.inner (β 0 r)
      (covDerivAlong h (fun u => β u r)
        (fun u => lVelocity (I := I) (fun v => β v r) u) 0)
      (lVelocity (I := I) (β 0) r) =
      g.inner (η 0 r)
        (covDerivAlong g (fun u => η u r)
          (fun u => lVelocity (I := I) (fun v => η v r) u) 0)
        (lVelocity (I := I) (η 0) r) := by
  have hpoint : β 0 r = f (η 0 r) := heq.self_of_nhds
  have hηvar : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun u => η u r) 0 :=
    hη.comp 0 (contMDiffAt_id.prodMk contMDiffAt_const)
  have hηtime : MDifferentiableAt 𝓘(ℝ, ℝ) I (η 0) r :=
    (hη.comp r (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have heqvar : (fun u => β u r) =ᶠ[𝓝 0] f ∘ (fun u => η u r) :=
    heq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have heqtime : β 0 =ᶠ[𝓝 r] f ∘ η 0 :=
    heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have htime : lVelocity (I := I) (β 0) r =
      mfderiv I I f (η 0 r) (lVelocity (I := I) (η 0) r) := by
    unfold lVelocity
    rw [heqtime.mfderiv_eq,
      mfderiv_comp r ((hf _).contMDiffAt.mdifferentiableAt (by simp)) hηtime]
    rfl
  have hvel : ∀ᶠ u in 𝓝 0,
      lVelocity (I := I) (fun v => β v r) u =
        lVelocity (I := I) (fun v => f (η v r)) u := by
    filter_upwards [heqvar.eventuallyEq_nhds] with u hu
    unfold lVelocity
    rw [hu.mfderiv_eq]
    rfl
  have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve h
    (fun u => lVelocity (I := I) (fun v => β v r) u)
    (fun u => lVelocity (I := I) (fun v => f (η v r)) u) heqvar hvel
  have hnat := covDerivAlong_velocity_map_of_local_isometry_on g h isOpen_univ
    (fun x => hf x)
    (fun x _ v w => by rw [hmetric, localPullMetric_inner])
    (fun u => η u r) (mem_univ _) hηvar
  change mfderiv I I f (η 0 r)
      (covDerivAlong g (fun u => η u r)
        (fun u => lVelocity (I := I) (fun v => η v r) u) 0) =
    covDerivAlong h (fun u => f (η u r))
      (fun u => lVelocity (I := I) (fun v => f (η v r)) u) 0 at hnat
  rw [hcov, ← hnat, hpoint, htime, hmetric, localPullMetric_inner]


theorem hasDerivAt_deriv_sum_lRegularizedAction_of_local_isometries
    {n : ℕ} (M : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (D : Fin (n + 1) → RealTimeInterval)
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (t : Fin (n + 2) → ℝ)
    (α : (i : Fin (n + 1)) → ℝ → ℝ → M i)
    (hα : ∀ i, IsSmoothVariation (I := I) (α i))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (α i 0)
      (uIcc (t i.castSucc) (t i.succ)))
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
    (hη : ∀ i : Fin n, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => η i z.1 z.2) (0, t i.castSucc.succ))
    (hmatchLeft : ∀ i : Fin n,
      (fun z : ℝ × ℝ => α i.castSucc z.1 z.2) =ᶠ[𝓝 (0, t i.castSucc.succ)]
        (leftMap i) ∘ (fun z => η i z.1 z.2))
    (hmatchRight : ∀ i : Fin n,
      (fun z : ℝ × ℝ => α i.succ z.1 z.2) =ᶠ[𝓝 (0, t i.castSucc.succ)]
        (rightMap i) ∘ (fun z => η i z.1 z.2)) :
    HasDerivAt
      (fun z : ℝ => deriv (fun y : ℝ => ∑ i : Fin (n + 1),
        lRegularizedAction (S i) T (α i y) (t i.castSucc) (t i.succ)) z)
      (2 * (∑ i : Fin (n + 1), lRegularizedIndex (S i) T (α i 0)
          (fun s => lVelocity (I := I) (fun z => α i z s) 0)
          (fun s => lVelocity (I := I) (fun z => α i z s) 0) (t i.castSucc) (t i.succ)) +
        ((S (Fin.last n)).base.metric (T - (t (Fin.last (n + 1))) ^ 2)).inner
          (α (Fin.last n) 0 (t (Fin.last (n + 1))))
          (covDerivAlong (I := I) ((S (Fin.last n)).base.metric (T - (t (Fin.last (n + 1))) ^ 2))
            (fun z => α (Fin.last n) z (t (Fin.last (n + 1))))
            (fun z => lVelocity (I := I) (fun y => α (Fin.last n) y (t (Fin.last (n + 1)))) z) 0)
          (lVelocity (I := I) (α (Fin.last n) 0) (t (Fin.last (n + 1)))) -
        ((S 0).base.metric (T - (t 0) ^ 2)).inner (α 0 0 (t 0))
          (covDerivAlong (I := I) ((S 0).base.metric (T - (t 0) ^ 2))
            (fun z => α 0 z (t 0)) (fun z => lVelocity (I := I) (fun y => α 0 y (t 0)) z) 0)
          (lVelocity (I := I) (α 0 0) (t 0))) 0 := by
  let pair (i : Fin (n + 1)) (r : ℝ) := ((S i).base.metric (T - r ^ 2)).inner (α i 0 r)
    (covDerivAlong (I := I) ((S i).base.metric (T - r ^ 2))
      (fun z => α i z r) (fun z => lVelocity (I := I) (fun y => α i y r) z) 0)
    (lVelocity (I := I) (α i 0) r)
  let index (i : Fin (n + 1)) := lRegularizedIndex (S i) T (α i 0)
    (fun s => lVelocity (I := I) (fun z => α i z s) 0)
    (fun s => lVelocity (I := I) (fun z => α i z s) 0) (t i.castSucc) (t i.succ)
  have hmatch (i : Fin n) : pair i.castSucc (t i.castSucc.succ) = pair i.succ (t i.succ.castSucc) := by
    have htime : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    rw [htime]
    exact (second_variation_pair_of_local_isometry (g i) _ (leftMap i) (hleft i)
      (hmetricLeft i) (hη i) (hmatchLeft i)).trans
      (second_variation_pair_of_local_isometry (g i) _ (rightMap i) (hright i)
        (hmetricRight i) (hη i) (hmatchRight i)).symm
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    lRegularizedAction_second_variation_moving_endpoints (S i) (hS i) T (α i) (hα i)
      (t i.castSucc) (t i.succ) (hgeo i))
  have hderiv (z : ℝ) :
      deriv (fun y : ℝ => ∑ i : Fin (n + 1),
        lRegularizedAction (S i) T (α i y) (t i.castSucc) (t i.succ)) z =
      ∑ i : Fin (n + 1), deriv (fun y : ℝ =>
        lRegularizedAction (S i) T (α i y) (t i.castSucc) (t i.succ)) z := by
    apply deriv_fun_sum
    intro i _
    exact (contDiff_lRegularizedAction (S i) (hS i) T (α i) (hα i)
      (t i.castSucc) (t i.succ) (fun s hs => (hgeo i s hs).1)).differentiable
        (by norm_num) z
  have heq : (fun z : ℝ => deriv (fun y : ℝ => ∑ i : Fin (n + 1),
      lRegularizedAction (S i) T (α i y) (t i.castSucc) (t i.succ)) z) =
      (fun z : ℝ => ∑ i : Fin (n + 1), deriv (fun y : ℝ =>
        lRegularizedAction (S i) T (α i y) (t i.castSucc) (t i.succ)) z) := funext hderiv
  rw [heq]
  apply hsum.congr_deriv
  change (∑ i : Fin (n + 1), (2 * index i + pair i (t i.succ) - pair i (t i.castSucc))) =
    2 * (∑ i, index i) + pair (Fin.last n) (t (Fin.last (n + 1))) - pair 0 (t 0)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Fin.sum_univ_castSucc (fun i => pair i (t i.succ)),
    Fin.sum_univ_succ (fun i => pair i (t i.castSucc))]
  have hs : (∑ i : Fin n, pair i.castSucc (t i.castSucc.succ)) =
      ∑ i : Fin n, pair i.succ (t i.succ.castSucc) := Finset.sum_congr rfl (fun i _ => hmatch i)
  rw [hs]
  change 2 * (∑ i, index i) +
    ((∑ i : Fin n, pair i.succ (t i.succ.castSucc)) + pair (Fin.last n) (t (Fin.last (n + 1)))) -
      (pair 0 (t 0) + ∑ i : Fin n, pair i.succ (t i.succ.castSucc)) = _
  abel

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
