import DifferentialGeometry.Bundle.SmoothSubbundle.Basic

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

universe u uE uH uM uF₁ uF₂ uV₁ uV₂

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {V₁ : M → Type uV₁} [TopologicalSpace (TotalSpace F₁ V₁)]
variable [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
variable [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
variable {V₂ : M → Type uV₂} [TopologicalSpace (TotalSpace F₂ V₂)]
variable [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
variable [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
variable {n : WithTop ℕ∞}

namespace ContMDiffVectorSubbundle

variable [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ I]
variable [VectorBundle 𝕜 F₂ V₂] [ContMDiffVectorBundle n F₂ V₂ I]

def map
    (S : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n))
    (e : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (he : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ =>
        (⟨p.1, e p.1 p.2⟩ : TotalSpace F₂ V₂))) :
    ContMDiffVectorSubbundle (I := I) (F := F₂) (V := V₂) (n := n) where
  fiber x := Submodule.map (e x).toLinearMap (S.fiber x)
  rank := S.rank
  exists_isSubbundleFrameOn x := by
    obtain ⟨U, s, hU, hxU, hs⟩ := S.exists_frame x
    refine ⟨U, fun i y => e y (s i y), hU, hxU, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      exact (hs.linearIndependent hy).map' (e y).toLinearMap
        (LinearMap.ker_eq_bot.mpr (e y).injective)
    · intro y hy
      calc
        Submodule.span 𝕜 (Set.range fun i => e y (s i y)) =
            Submodule.span 𝕜 ((e y).toLinearMap '' Set.range (s · y)) := by
              congr 1
              ext v
              simp
        _ = Submodule.map (e y).toLinearMap
            (Submodule.span 𝕜 (Set.range (s · y))) := by
              rw [Submodule.map_span]
        _ = Submodule.map (e y).toLinearMap (S.fiber y) := by
              rw [hs.spans hy]
    · intro i
      exact (he.comp_contMDiffOn (hs.contMDiffOn i)).congr fun y hy => rfl

@[simp]
theorem map_fiber
    (S : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n))
    (e : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (he : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ =>
        (⟨p.1, e p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (x : M) :
    (map S e he).fiber x = Submodule.map (e x).toLinearMap (S.fiber x) :=
  rfl

@[simp]
theorem map_rank
    (S : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n))
    (e : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (he : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ =>
        (⟨p.1, e p.1 p.2⟩ : TotalSpace F₂ V₂))) :
    (map S e he).rank = S.rank :=
  rfl

end ContMDiffVectorSubbundle
