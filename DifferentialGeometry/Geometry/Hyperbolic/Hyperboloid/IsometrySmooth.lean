import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Manifold
import DifferentialGeometry.Geometry.Lorentz.Isometry

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem contMDiff_isometryEquiv {n : ℕ∞ω} (e : Hyperboloid E ≃ᵢ Hyperboloid F) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n e := by
  let L : (ℝ × E) →L[ℝ] F := (ContinuousLinearMap.snd ℝ ℝ F).comp
    (lorentzIsometryContinuousLinearEquiv (lorentzExtension e)).toContinuousLinearMap
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n
      (fun x : Hyperboloid E => L (x.time, x.space)) :=
    L.contMDiff.comp (contMDiff_time_space (n := n))
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n
      (fun x : Hyperboloid E => ofSpace (L (x.time, x.space))) :=
    (contMDiff_ofSpace (E := F) (n := n)).comp hL
  have he : (fun x : Hyperboloid E => ofSpace (L (x.time, x.space))) =
      (e : Hyperboloid E → Hyperboloid F) := by
    funext x
    change ofSpace (lorentzExtension e (x.time, x.space)).2 = e x
    rw [lorentzExtension_apply, ofSpace_space]
  rwa [he] at h

def isometryDiffeomorph (e : Hyperboloid E ≃ᵢ Hyperboloid F) (n : ℕ∞ω := ∞) :
    Hyperboloid E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ Hyperboloid F where
  toEquiv := e.toEquiv
  contMDiff_toFun := contMDiff_isometryEquiv e
  contMDiff_invFun := contMDiff_isometryEquiv e.symm

@[simp] theorem isometryDiffeomorph_toEquiv (e : Hyperboloid E ≃ᵢ Hyperboloid F) (n : ℕ∞ω) :
    (isometryDiffeomorph e n).toEquiv = e.toEquiv := rfl

@[simp] theorem isometryDiffeomorph_apply (e : Hyperboloid E ≃ᵢ Hyperboloid F)
    (n : ℕ∞ω) (x : Hyperboloid E) : isometryDiffeomorph e n x = e x := rfl

@[simp] theorem isometryDiffeomorph_symm_apply (e : Hyperboloid E ≃ᵢ Hyperboloid F)
    (n : ℕ∞ω) (y : Hyperboloid F) : (isometryDiffeomorph e n).symm y = e.symm y := rfl

@[simp] theorem isometryDiffeomorph_symm (e : Hyperboloid E ≃ᵢ Hyperboloid F) (n : ℕ∞ω) :
    isometryDiffeomorph e.symm n = (isometryDiffeomorph e n).symm := by
  apply Diffeomorph.ext
  intro x
  rfl

@[simp] theorem isometryDiffeomorph_refl (n : ℕ∞ω) :
    isometryDiffeomorph (IsometryEquiv.refl (Hyperboloid E)) n =
      Diffeomorph.refl 𝓘(ℝ, E) (Hyperboloid E) n := by
  apply Diffeomorph.ext
  intro x
  rfl

@[simp] theorem isometryDiffeomorph_trans {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : Hyperboloid E ≃ᵢ Hyperboloid F) (f : Hyperboloid F ≃ᵢ Hyperboloid G) (n : ℕ∞ω) :
    isometryDiffeomorph (e.trans f) n = (isometryDiffeomorph e n).trans (isometryDiffeomorph f n) := by
  apply Diffeomorph.ext
  intro x
  rfl

end DifferentialGeometry.Hyperboloid
