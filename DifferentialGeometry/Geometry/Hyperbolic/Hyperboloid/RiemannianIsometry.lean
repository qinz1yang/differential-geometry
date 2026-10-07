import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometrySmooth
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem mvfderiv_clm_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {f : Hyperboloid E → V} {x : Hyperboloid E}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, V) f x) (u : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (L ∘ f) x u = L (mvfderiv 𝓘(ℝ, E) f x u) := by
  rw [mvfderiv_comp_apply x L.differentiableAt.mdifferentiableAt hf,
    mvfderiv_eq_fderiv, L.fderiv]
  rfl

private theorem mvfderiv_ambient_fst (x : Hyperboloid E) (u : TangentSpace 𝓘(ℝ, E) x) :
    (mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => (y.time, y.space)) x u).1 =
      inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u) / x.time := by
  have h := mvfderiv_clm_comp (ContinuousLinearMap.fst ℝ ℝ E)
    ((contMDiff_time_space (E := E) (n := ∞)).mdifferentiableAt (x := x) (by simp)) u
  have ht : mvfderiv 𝓘(ℝ, E) time x u =
      inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u) / x.time :=
    mfderiv_time_apply x u
  exact h.symm.trans ht

private theorem mvfderiv_ambient_snd (x : Hyperboloid E) (u : TangentSpace 𝓘(ℝ, E) x) :
    (mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => (y.time, y.space)) x u).2 =
      mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u := by
  exact (mvfderiv_clm_comp (ContinuousLinearMap.snd ℝ ℝ E)
    ((contMDiff_time_space (E := E) (n := ∞)).mdifferentiableAt (x := x) (by simp)) u).symm

private theorem lorentzForm_mvfderiv_ambient (x : Hyperboloid E)
    (u v : TangentSpace 𝓘(ℝ, E) x) :
    lorentzForm E
      (mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => (y.time, y.space)) x u)
      (mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => (y.time, y.space)) x v) =
        riemannianMetric.inner x u v := by
  rw [lorentzForm_apply, mvfderiv_ambient_fst, mvfderiv_ambient_fst,
    mvfderiv_ambient_snd, mvfderiv_ambient_snd, riemannianMetric_inner]
  change inner ℝ (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u)
      (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x v) -
      (inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u) / x.time) *
        (inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x v) / x.time) =
    inner ℝ (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u)
      (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x v) -
      inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x u) *
        inner ℝ x.space (mvfderiv 𝓘(ℝ, E) spaceDiffeomorph x v) / (1 + ‖x.space‖ ^ 2)
  rw [← x.time_sq]
  ring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem mvfderiv_ambient_isometryEquiv (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (x : Hyperboloid E) (u : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, F) (fun y : Hyperboloid F => (y.time, y.space)) (f x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x u) =
        lorentzExtension f (mvfderiv 𝓘(ℝ, E)
          (fun y : Hyperboloid E => (y.time, y.space)) x u) := by
  let L := (lorentzIsometryContinuousLinearEquiv (lorentzExtension f)).toContinuousLinearMap
  have he : (fun y : Hyperboloid F => (y.time, y.space)) ∘ f =
      L ∘ (fun y : Hyperboloid E => (y.time, y.space)) := by
    funext y
    exact (lorentzExtension_apply f y).symm
  rw [← mvfderiv_comp_apply x
    ((contMDiff_time_space (E := F) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_isometryEquiv (n := ∞) f).mdifferentiableAt (by simp)), he]
  exact mvfderiv_clm_comp L
    ((contMDiff_time_space (E := E) (n := ∞)).mdifferentiableAt (by simp)) u

theorem riemannianMetric_inner_mfderiv_isometryEquiv
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (x : Hyperboloid E)
    (u v : TangentSpace 𝓘(ℝ, E) x) :
    riemannianMetric.inner (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x u)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v) = riemannianMetric.inner x u v := by
  rw [← lorentzForm_mvfderiv_ambient, mvfderiv_ambient_isometryEquiv,
    mvfderiv_ambient_isometryEquiv, (lorentzExtension f).map_app,
    lorentzForm_mvfderiv_ambient]

end DifferentialGeometry.Hyperboloid
