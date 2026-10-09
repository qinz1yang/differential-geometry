import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem IsLocalFrameOn.pushforward
    {ι : Type*} {frame : ι → (x : M) → TangentSpace I x} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (Φ : M ≃ₘ⟮I, J⟯ N) :
    IsLocalFrameOn (V := (TangentSpace J : N → Type _)) J F (∞ : WithTop ℕ∞)
      (fun i (y : N) => mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) where
  linearIndependent {y} hy := by
    have hsymm : Φ.symm y ∈ u := by
      obtain ⟨x, hx, hxy⟩ := hy; rw [← hxy, Φ.symm_apply_apply]; exact hx
    have hb : (fun i => mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
        = ⇑((hframe.toBasisAt hsymm).map
            (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm y)).toLinearEquiv) := by
      funext i
      rw [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe]
    change LinearIndependent ℝ (fun i => mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
    rw [hb]
    exact Module.Basis.linearIndependent _
  generating {y} hy := by
    have hsymm : Φ.symm y ∈ u := by
      obtain ⟨x, hx, hxy⟩ := hy; rw [← hxy, Φ.symm_apply_apply]; exact hx
    have hb : (fun i => mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
        = ⇑((hframe.toBasisAt hsymm).map
            (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm y)).toLinearEquiv) := by
      funext i
      rw [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe]
    change ⊤ ≤ Submodule.span ℝ (Set.range
      (fun i => mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))))
    rw [hb]
    exact (Module.Basis.span_eq _).ge
  contMDiffOn i := by
    have hmaps : Set.MapsTo (Φ.symm : N → M) (Φ '' u) u := by
      rintro y ⟨x, hx, rfl⟩; rw [Φ.symm_apply_apply]; exact hx
    have h1 : ContMDiffOn J (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (fun y : N => TotalSpace.mk' E (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) :=
      (hframe.contMDiffOn i).comp (Φ.symm.contMDiff.contMDiffOn) hmaps
    have h2 := (Φ.contMDiff.contMDiff_tangentMap (by simp)).comp_contMDiffOn h1
    refine h2.congr ?_
    intro y _hy
    change TotalSpace.mk' F y (mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
       = tangentMap I J (Φ : M → N) (TotalSpace.mk' E (Φ.symm y) (frame i (Φ.symm y)))
    exact (congrArg
      (fun b : N => TotalSpace.mk' F (E := fun z : N => TangentSpace J z) b
        (mfderiv I J (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))))
      (Φ.apply_symm_apply y)).symm
