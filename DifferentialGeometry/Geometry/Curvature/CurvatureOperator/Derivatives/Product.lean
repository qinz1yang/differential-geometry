import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Product
import DifferentialGeometry.Geometry.Metric.Euclidean

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.VectorField
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

section RealProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


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
    exact mvfderiv_comp_fst (I := I) (J := 𝓘(ℝ, ℝ)) (N := ℝ)
      (fun y' : M => A y' (fun q => W q y')) (y, s) (Xl (y, s)) hf
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

theorem metricRm04At_prod_real_apply
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
      exact metricRm04At_prod_real_apply (I := I) h gR y s u
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
          rw [curvStep_eq_covStep]
        _ = covStep (I := I) h (m + 4) (curvCovDeriv (I := I) (M := M) h m) y
              (fun i => (u i).1) := hstep.symm
        _ = curvCovDerivStep (I := I) h m (curvCovDeriv (I := I) (M := M) h m) y
              (fun i => (u i).1) := by
          rw [curvStep_eq_covStep]
        _ = curvCovDeriv (I := I) (M := M) h (m + 1) y (fun i => (u i).1) := rfl


theorem curvDerivNorm_prod_real
    (h : SmoothRiemannianMetric I M) (gR : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ)
    (m : ℕ) (y : M) (s : ℝ) :
    curvDerivNorm (I := I.prod 𝓘(ℝ, ℝ)) m (h.prod gR) (y, s) =
      curvDerivNorm (I := I) m h y := by
  unfold curvDerivNorm curvDerivNormSq
  congr 1
  exact normSq0S_prod_of_forall_fst (I := I) (J := 𝓘(ℝ, ℝ)) h gR (y, s) (m + 4)
    ((curvCovDeriv (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) (h.prod gR) m) (y, s))
    ((curvCovDeriv (I := I) (M := M) h m) y)
    (fun slots => curvCovDeriv_prod_horizontal (I := I) h gR m y s slots)

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
  rw [heq, curvDerivNorm_prod_real]

end RealProduct

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
