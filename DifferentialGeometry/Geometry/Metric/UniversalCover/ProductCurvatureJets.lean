import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Tensor.Metric.LocalIsometry


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

section CrossDiffeomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]


local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local instance : CompleteSpace F := FiniteDimensional.complete ℝ F

local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

local instance : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

private theorem curvCovDerivStep_eq_covStep
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (A : DifferentialGeometry.Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4)) :
    curvCovDerivStep (I := I) (M := M) g k A = covStep (I := I) g (k + 4) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply]
  rfl

private theorem curvCovDeriv_pullbackMetricCross_apply
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) :
    ∀ (m : ℕ) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Phi) m x v =
        curvCovDeriv (I := J) (M := N) g m (Phi x)
          (fun i => mfderiv I J (Phi : M → N) x (v i)) := by
  intro m
  induction m with
  | zero =>
      intro x v
      exact metricRm04_cross (I := I) (J := J) g Phi x v
  | succ m ih =>
      intro x v
      rw [curvCovDeriv_succ (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Phi) m,
        curvCovDeriv_succ (I := J) (M := N) g m,
        curvCovDerivStep_eq_covStep (I := I) (M := M)
          (Diffeomorph.pullbackMetricCross g Phi) m,
        curvCovDerivStep_eq_covStep (I := J) (M := N) g m]
      exact DifferentialGeometry.Geometry.Tensor.cov_step_pullback g Phi
        (curvCovDeriv (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Phi) m)
        (curvCovDeriv (I := J) (M := N) g m) ih x v

omit [T2Space N] in
private theorem normSq0S_pullbackMetricCross_eval
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) (s : ℕ)
    (basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x))
    (hON : ∀ i j,
      (Diffeomorph.pullbackMetricCross g Phi).inner x (basis i) (basis j) =
        if i = j then (1 : ℝ) else 0)
    (Tpb : DifferentialGeometry.Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) s x)
    (T : DifferentialGeometry.Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := F) (H := G)
      (I := J) (M := N) s (Phi x))
    (hT : ∀ slots : Fin s → TangentSpace I x,
      Tpb slots = T (fun q : Fin s => mfderiv I J (Phi : M → N) x (slots q))) :
    DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetricCross g Phi) x s Tpb =
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := J) g (Phi x) s T := by
  classical
  let dPhi : TangentSpace I x ≃L[ℝ] TangentSpace J (Phi x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Phi (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  let basis' : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace J (Phi x)) :=
    basis.map dPhi.toLinearEquiv
  have hdPhi_apply : ∀ v : TangentSpace I x, dPhi v = mfderiv I J (Phi : M → N) x v := by
    intro v
    have h := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Phi) (x := x)
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Phi x) => f v) h
  have hbasis'_apply : ∀ i, basis' i = mfderiv I J (Phi : M → N) x (basis i) := by
    intro i
    have hmap : basis' i = dPhi (basis i) := by
      change (basis.map dPhi.toLinearEquiv) i = dPhi (basis i)
      rw [Module.Basis.map_apply]
      rfl
    rw [hmap, hdPhi_apply (basis i)]
  have hON' : ∀ i j,
      g.inner (Phi x) (basis' i) (basis' j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have hsrc := hON i j
    rw [Diffeomorph.pullbackMetricCross_inner] at hsrc
    simpa [hbasis'_apply i, hbasis'_apply j] using hsrc
  have hinv : DifferentialGeometry.Tensor0SBundle.MetricInverseInBasis (I := I)
      (Diffeomorph.pullbackMetricCross g Phi) x basis
      (DifferentialGeometry.Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := I) (Diffeomorph.pullbackMetricCross g Phi) basis hON
    intro i j
    simpa [DifferentialGeometry.Tensor0SBundle.identityInvMetric,
      DifferentialGeometry.Tensor0SBundle.diagonalInvMetric] using h i j
  have hinv' : DifferentialGeometry.Tensor0SBundle.MetricInverseInBasis (I := J) g (Phi x)
      basis' (DifferentialGeometry.Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := J) g basis' hON'
    intro i j
    simpa [DifferentialGeometry.Tensor0SBundle.identityInvMetric,
      DifferentialGeometry.Tensor0SBundle.diagonalInvMetric] using h i j
  rw [DifferentialGeometry.Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I)
      (Diffeomorph.pullbackMetricCross g Phi) x s basis hinv Tpb,
    DifferentialGeometry.Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := J) g (Phi x) s
      basis' hinv' T]
  apply Finset.sum_congr rfl
  intro slots _
  congr 1
  rw [DifferentialGeometry.Tensor0SBundle.component0S_apply,
    DifferentialGeometry.Tensor0SBundle.component0S_apply, hT]
  exact congrArg T (funext fun q => (hbasis'_apply (slots q)).symm)


theorem curvDerivNorm_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (m : ℕ) (x : M) :
    curvDerivNorm (I := I) m (Diffeomorph.pullbackMetricCross g Phi) x =
      curvDerivNorm (I := J) m g (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (Diffeomorph.pullbackMetricCross g Phi) x
  unfold curvDerivNorm curvDerivNormSq
  rw [normSq0S_pullbackMetricCross_eval (g := g) (Phi := Phi) (x := x) (s := m + 4)
    (basis := basis) hON
    (Tpb := curvCovDeriv (I := I) (M := M)
      (Diffeomorph.pullbackMetricCross g Phi) m x)
    (T := curvCovDeriv (I := J) (M := N) g m (Phi x))
    (fun slots => curvCovDeriv_pullbackMetricCross_apply g Phi m x slots)]

end CrossDiffeomorphism

section RealProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


theorem curvDerivNorm_le_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (b : ℝ) (hb : 0 < b)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + b * (a * c))
    (m : ℕ) (y : M) (s : ℝ) :
    curvDerivNorm (I := I) m h y ≤
      curvDerivNorm (I := I.prod 𝓘(ℝ, ℝ)) m gP (y, s) := by
  sorry

end RealProduct

section UniversalCoverLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]


theorem curvDerivNorm_liftedMetric
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x' : UniversalCover M) :
    curvDerivNorm (I := I) m (UniversalCover.liftedMetric (I := I) g) x' =
      curvDerivNorm (I := I) m g (UniversalCover.proj x') := by
  sorry

end UniversalCoverLift

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
