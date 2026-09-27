import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Product
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Tensor.Metric.IsometryNorm
import DifferentialGeometry.Tensor.Metric.LocalIsometry
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.VectorField
open DifferentialGeometry.Tensor0SBundle
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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem mfderiv_fst_apply (y : M) (s : ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
    (mfderiv (I := I.prod 𝓘(ℝ, ℝ)) (I' := I) (fun p : M × ℝ => p.1) (y, s)) v = v.1 := by
  rw [mfderiv_fst]
  rfl

omit [I.Boundaryless] in
theorem covStep_prod_horizontal
    (h : SmoothRiemannianMetric I M) (gR : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ)
    {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (B : Tensor0SField (𝕜 := ℝ) (E := E × ℝ)
      (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (n := (∞ : WithTop ℕ∞)) r)
    (hAB : ∀ (y : M) (s : ℝ)
      (u : Fin r → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)),
      B (y, s) u = A y (fun i => (u i).1))
    (y : M) (s : ℝ)
    (u : Fin (r + 1) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
    covStep (I := I) h r A y (fun i => (u i).1) =
      covStep (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) r B (y, s) u := by
  classical
  obtain ⟨X0, hX0⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y (u 0).1
  choose W hW using fun q : Fin r => ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y (u q.succ).1
  obtain ⟨cX, hcX⟩ := ContMDiffSection.exists_eq_at (I := 𝓘(ℝ, ℝ)) (F := ℝ)
    (V := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) (n := (⊤ : ℕ∞)) s (u 0).2
  choose cW hcW using fun q : Fin r => ContMDiffSection.exists_eq_at (I := 𝓘(ℝ, ℝ)) (F := ℝ)
    (V := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) (n := (⊤ : ℕ∞)) s (u q.succ).2
  let Xl : ContMDiffSection (I.prod 𝓘(ℝ, ℝ)) (E × ℝ) ∞
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : M × ℝ → Type _) := productVectorField X0 cX
  let Wl : Fin r → ContMDiffSection (I.prod 𝓘(ℝ, ℝ)) (E × ℝ) ∞
      (TangentSpace (I.prod 𝓘(ℝ, ℝ)) : M × ℝ → Type _) :=
    fun q => productVectorField (W q) (cW q)
  have hXlpoint : Xl (y, s) = u 0 := by
    change (X0 y, cX s) = ((u 0).1, (u 0).2)
    rw [hX0, hcX]
    rfl
  have hWlpoint : ∀ q : Fin r, Wl q (y, s) = u q.succ := by
    intro q
    change ((W q) y, (cW q) s) = ((u q.succ).1, (u q.succ).2)
    rw [hW q, hcW q]
    rfl
  have hconsL : Fin.cons (X0 y) (fun q : Fin r => W q y) = fun i => (u i).1 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hX0
    · exact hW j
  have hconsR : Fin.cons (Xl (y, s)) (fun q : Fin r => Wl q (y, s)) = u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hXlpoint
    · exact hWlpoint j
  have hL := covStep_eval_smooth_slots (I := I) h r A X0 W y
  have hR := covStep_eval_smooth_slots (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) r B Xl Wl (y, s)
  have hgoalL := congrArg (fun w => covStep (I := I) h r A y w) hconsL
  have hgoalR := congrArg (fun w => covStep (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) r B (y, s) w) hconsR
  have hL' := hgoalL.symm.trans hL
  have hR' := hgoalR.symm.trans hR
  have hderiv :
      mvfderiv (I := I.prod 𝓘(ℝ, ℝ)) (fun p : M × ℝ => B p (fun q => Wl q p))
          (y, s) (Xl (y, s)) =
        mvfderiv (I := I) (fun y' : M => A y' (fun q => W q y')) y (X0 y) := by
    have hfun : (fun p : M × ℝ => B p (fun q => Wl q p)) =
        (fun y' : M => A y' (fun q => W q y')) ∘ Prod.fst := by
      funext p
      obtain ⟨y', s'⟩ := p
      rw [hAB y' s' (fun q => Wl q (y', s'))]
      congr 1
    have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y' : M => A y' (fun q => W q y')) y :=
      (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) A W y).mdifferentiableAt (by simp)
    rw [hfun]
    rw [mvfderiv_comp_apply (I := I) (I' := I.prod 𝓘(ℝ, ℝ)) (y, s)
      (f := fun p : M × ℝ => p.1) (g := fun y' : M => A y' (fun q => W q y'))
      hf mdifferentiableAt_fst (Xl (y, s))]
    rw [mfderiv_fst_apply (I := I) y s (Xl (y, s))]
    congr 1
  have hcorr :
      (∑ q : Fin r, A y (Function.update (fun b : Fin r => W b y) q
          (((leviCivitaConnectionOfMetric (I := I) h) (fun y' : M => W q y') y) (X0 y)))) =
        ∑ q : Fin r, B (y, s) (Function.update (fun b : Fin r => Wl b (y, s)) q
          (((leviCivitaConnectionOfMetric (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR))
            (fun p : M × ℝ => Wl q p) (y, s)) (Xl (y, s)))) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hAB y s (Function.update (fun b : Fin r => Wl b (y, s)) q
      (((leviCivitaConnectionOfMetric (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR))
        (fun p : M × ℝ => Wl q p) (y, s)) (Xl (y, s))))]
    have h1 : ∀ q : Fin r, (((leviCivitaConnectionOfMetric (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR))
          (fun p : M × ℝ => Wl q p) (y, s)) (Xl (y, s))).1 =
        ((leviCivitaConnectionOfMetric (I := I) h) (fun y' : M => W q y') y) (X0 y) := by
      intro q
      change (((leviCivitaConnectionOfMetric (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR))
          (productVectorField (W q) (cW q)) (y, s)) (Xl (y, s))).1 =
        ((leviCivitaConnectionOfMetric (I := I) h) (fun y' : M => W q y') y) (X0 y)
      rw [leviCivita_productVectorField_apply (I := I) (J := 𝓘(ℝ, ℝ)) h gR
        (W q) (cW q) (y, s) (Xl (y, s))]
      rfl
    refine congrArg (A y) (funext fun b => ?_)
    by_cases hb : b = q
    · rw [hb, Function.update_self, Function.update_self]
      exact (h1 q).symm
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
      rfl
  refine hL'.trans ?_
  refine Eq.trans ?_ hR'.symm
  rw [hderiv, hcorr]

theorem metricRm04At_prod_real_strong
    (h : SmoothRiemannianMetric I M) (gR : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ)
    (y : M) (s : ℝ)
    (u : Fin 4 → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) (y, s) u =
      metricRm04At (I := I) h y (fun i => (u i).1) := by
  rw [metricRm04At_productMetric_apply (I := I) (J := 𝓘(ℝ, ℝ)) h gR (y, s) u]
  rw [metricRm04At_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) gR (by simp) s]
  change ((metricRm04At (I := I) h y) (fun k => (u k).1)) + (0 : ℝ) =
    (metricRm04At (I := I) h y) (fun i => (u i).1)
  rw [add_zero]

theorem curvCovDeriv_prod_horizontal
    (h : SmoothRiemannianMetric I M) (gR : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ)
    (m : ℕ) (y : M) (s : ℝ)
    (u : Fin (m + 4) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, s)) :
    curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m (y, s) u =
      curvCovDeriv (I := I) (M := M) h m y (fun i => (u i).1) := by
  induction m generalizing y s with
  | zero =>
      exact metricRm04At_prod_real_strong (I := I) h gR y s u
  | succ m ih =>
      have hstep := covStep_prod_horizontal (I := I) h gR
        (curvCovDeriv (I := I) (M := M) h m)
        (curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m)
        (fun y s u => ih y s u) y s u
      calc
        curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) (m + 1) (y, s) u =
            curvCovDerivStep (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) m
              (curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m) (y, s) u :=
          rfl
        _ = covStep (I := I.prod 𝓘(ℝ, ℝ)) (h.prod gR) (m + 4)
              (curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m) (y, s) u := by
          rw [curvCovDerivStep_eq_covStep]
        _ = covStep (I := I) h (m + 4) (curvCovDeriv (I := I) (M := M) h m) y
              (fun i => (u i).1) := hstep.symm
        _ = curvCovDerivStep (I := I) h m (curvCovDeriv (I := I) (M := M) h m) y
              (fun i => (u i).1) := by
          rw [curvCovDerivStep_eq_covStep]
        _ = curvCovDeriv (I := I) (M := M) h (m + 1) y (fun i => (u i).1) := rfl


set_option backward.isDefEq.respectTransparency false in
theorem curvDerivNorm_le_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (b : ℝ) (hb : 0 < b)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + b * (a * c))
    (m : ℕ) (y : M) (s : ℝ) :
    curvDerivNorm (I := I) m h y ≤
      curvDerivNorm (I := I.prod 𝓘(ℝ, ℝ)) m gP (y, s) := by
  classical
  let gR : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ :=
    scaleMetric b hb (euclideanMetric (E := ℝ))
  have hgR : ∀ (t : ℝ) (a c : ℝ), gR.inner t a c = b * (a * c) := by
    intro t a c
    change (scaleMetric b hb (euclideanMetric (E := ℝ))).inner t a c = b * (a * c)
    rw [scaleMetric_inner, euclideanMetric_inner, Real.inner_apply]
  have heq : gP = h.prod gR := by
    refine SmoothRiemannianMetric.ext_inner (I := I.prod 𝓘(ℝ, ℝ)) ?_
    intro x u w
    obtain ⟨y', s'⟩ := x
    rw [SmoothRiemannianMetric.prod_inner]
    change gP.inner (y', s') u w = h.inner y' u.1 w.1 + gR.inner s' u.2 w.2
    have hu : u = ((u.1, u.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    have hw : w = ((w.1, w.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    rw [hu, hw]
    change gP.inner (y', s') (u.1, u.2) (w.1, w.2) =
      h.inner y' u.1 w.1 + gR.inner s' u.2 w.2
    rw [hproduct y' s' u.1 w.1 u.2 w.2, hgR s' u.2 w.2]
  rw [heq]
  unfold curvDerivNorm curvDerivNormSq
  apply Real.sqrt_le_sqrt
  rw [normSq0S_prod_of_forall_fst (I := I) (J := 𝓘(ℝ, ℝ)) h gR (y, s) (m + 4)
    ((curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m) (y, s))
    ((curvCovDeriv (I := I) (M := M) h m) y)
    (fun slots => curvCovDeriv_prod_horizontal (I := I) h gR m y s slots)]

end RealProduct

section JetTowerBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def curvEquiv : (m : ℕ) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => Tensor0SBundle.frontExtendEquiv (curvEquiv m)

private theorem curv_apply_iterCov (g : SmoothRiemannianMetric I M) :
    ∀ (m : ℕ) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (curvEquiv m)
              (iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I) g m
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I) (M := M) g m)
        _ = covStep (I := I) g (m + 4)
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDerivStep_eq_covStep (I := I) (M := M) g m _)
        _ = covStep (I := I) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
                (∞ : WithTop ℕ∞) (curvEquiv m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (Tensor0SBundle.frontExtendEquiv (curvEquiv m))
              (covStep (I := I) g (4 + m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I) (M := M) g (curvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (curvEquiv (m + 1))
              ((iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) (m + 1)) x)) v := by
          rfl

private theorem curvCovDeriv_normSq_eq (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    DifferentialGeometry.Tensor0SBundle.normSq0S (I := I) g x (m + 4)
        (curvCovDeriv (I := I) (M := M) g m x) =
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I) g x (4 + m)
        ((iterCov (I := I) g 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04
            (I := I) (M := M) g) m) x) := by
  classical
  have hfiber :
      curvCovDeriv (I := I) (M := M) g m x =
        ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact curv_apply_iterCov g m x v
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (I := I) g x
  have hinv :
      DifferentialGeometry.Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
        (DifferentialGeometry.Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    intro i j
    simpa [DifferentialGeometry.Tensor0SBundle.identityInvMetric,
      DifferentialGeometry.Tensor0SBundle.diagonalInvMetric] using h' i j
  rw [hfiber]
  exact DifferentialGeometry.Tensor0SBundle.normSq0S_domDomCongr (I := I) g x basis hinv
    (curvEquiv m)
    ((iterCov (I := I) g 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04
        (I := I) (M := M) g) m) x)

end JetTowerBridge

section UniversalCoverLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem curvDerivNorm_liftedMetric
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x' : UniversalCover M) :
    curvDerivNorm (I := I) m (UniversalCover.liftedMetric (I := I) g) x' =
      curvDerivNorm (I := I) m g (UniversalCover.proj x') := by
  classical
  let hf : IsLocalDiffeomorph I I ∞ (UniversalCover.proj : UniversalCover M → M) :=
    UniversalCover.proj_localDiffeo (I := I) (M := M)
  obtain ⟨Phi, hx, hagrees⟩ := hf x'
  let U : TopologicalSpace.Opens (UniversalCover M) := ⟨Phi.source, Phi.open_source⟩
  have hU : (U : Set (UniversalCover M)) ⊆ Phi.source := Set.Subset.rfl
  let V : TopologicalSpace.Opens M :=
    ⟨(Phi : UniversalCover M → M) '' (U : Set (UniversalCover M)),
      image_opens_isOpen Phi hU⟩
  let Psi : U ≃ₘ⟮I, I⟯ V := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  have hpoint (y : U) : (Psi y : M) = UniversalCover.proj (y : UniversalCover M) := by
    change (Phi : UniversalCover M → M) (y : UniversalCover M) = _
    exact (hagrees (hU y.property)).symm
  have hderiv (y : U) : mfderiv I I (Psi : U → V) y = ContinuousLinearMap.id ℝ E := by
    have hnear : (UniversalCover.proj : UniversalCover M → M)
        =ᶠ[nhds (y : UniversalCover M)] (Phi : UniversalCover M → M) :=
      Filter.eventuallyEq_of_mem (Phi.open_source.mem_nhds (hU y.property)) hagrees
    have hdf : mfderiv I I (UniversalCover.proj : UniversalCover M → M)
          (y : UniversalCover M) =
        mfderiv I I (Phi : UniversalCover M → M) (y : UniversalCover M) :=
      hnear.mfderiv_eq
    have hproj : mfderiv I I (UniversalCover.proj : UniversalCover M → M)
          (y : UniversalCover M) = ContinuousLinearMap.id ℝ E :=
      (UniversalCover.hasMFDerivAt_proj (I := I) (M := M) (y : UniversalCover M)).mfderiv
    ext v
    exact (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v).trans
      ((congrArg (fun L => L v) hdf.symm).trans (congrArg (fun L => L v) hproj))
  have hmetric (y : U) (v w : TangentSpace I y) :
      (UniversalCover.liftedMetric (I := I) g).inner (y : UniversalCover M) v w =
        g.inner (Psi y : M) (mfderiv I I (Psi : U → V) y v)
          (mfderiv I I (Psi : U → V) y w) := by
    have hv : mfderiv I I (Psi : U → V) y v = v :=
      congrArg (fun L => L v) (hderiv y)
    have hw : mfderiv I I (Psi : U → V) y w = w :=
      congrArg (fun L => L w) (hderiv y)
    exact (UniversalCover.liftedMetric_inner_eq (I := I) g
      (y : UniversalCover M) v w).symm.trans
      ((congrArg (fun p : M => g.inner p v w) (hpoint y)).symm.trans
        (congrArg₂ (fun a b => g.inner (Psi y : M) a b) hv hw).symm)
  have hAB (y : U) (v : Fin 4 → TangentSpace I y) :
      (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I)
          (M := UniversalCover M) (UniversalCover.liftedMetric (I := I) g))
          (y : UniversalCover M) v =
        (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g)
          (Psi y : M) (fun i => mfderiv I I (Psi : U → V) y (v i)) := by
    have hv : (fun i => mfderiv I I (Psi : U → V) y (v i)) = v := by
      funext i
      exact congrArg (fun L => L (v i)) (hderiv y)
    rw [hv]
    simp only [DifferentialGeometry.Geometry.Curvature.metricRm04_apply]
    exact (UniversalCover.metricRm04At_liftedMetric_apply (I := I) (M := M) g
        (y : UniversalCover M) v).trans
      ((congrArg (fun p : M =>
        (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I) (M := M) g) p v)
        (hpoint y)).symm)
  have hiter := DifferentialGeometry.Geometry.Tensor.normSq0S_iterCov_of_metric_isometry_on_opens
    (I := I) (M := UniversalCover M) (N := M)
    (UniversalCover.liftedMetric (I := I) g) g U V Psi hmetric
    (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := UniversalCover M)
      (UniversalCover.liftedMetric (I := I) g))
    (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g)
    hAB m ⟨x', hx⟩
  have hpx : (Psi ⟨x', hx⟩ : M) = UniversalCover.proj x' := hpoint ⟨x', hx⟩
  have hsq : curvDerivNormSq (I := I) m (UniversalCover.liftedMetric (I := I) g) x' =
      curvDerivNormSq (I := I) m g (UniversalCover.proj x') := by
    rw [curvDerivNormSq, curvDerivNormSq,
      curvCovDeriv_normSq_eq (UniversalCover.liftedMetric (I := I) g) m x',
      curvCovDeriv_normSq_eq g m (UniversalCover.proj x')]
    exact hpx ▸ hiter
  simp only [curvDerivNorm]
  rw [hsq]

end UniversalCoverLift

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
