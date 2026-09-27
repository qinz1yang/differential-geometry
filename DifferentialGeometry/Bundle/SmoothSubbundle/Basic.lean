import DifferentialGeometry.Bundle.SmoothSubbundle.Defs

set_option autoImplicit false

noncomputable section

open Bundle Module Set
open scoped Manifold

universe u uE uH uM uF uV uI

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type uV} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable {n : WithTop ℕ∞}

namespace IsSubbundleFrameOn

variable {S : ∀ x, Submodule 𝕜 (V x)}
variable {ι : Type uI} {s : ι → (x : M) → V x} {U U' : Set M}

theorem mem_fiber (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U)
    {x : M} (hx : x ∈ U) (i : ι) : s i x ∈ S x := by
  rw [← hs.spans hx]
  exact Submodule.subset_span (Set.mem_range_self i)

theorem mono (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U)
    (hU : U' ⊆ U) : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U' where
  linearIndependent hx := hs.linearIndependent (hU hx)
  spans hx := hs.spans (hU hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hU

end IsSubbundleFrameOn

namespace ContMDiffVectorSubbundle

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]

theorem exists_frame (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (x : M) :
    ∃ (U : Set M) (s : Fin S.rank → (y : M) → V y),
      IsOpen U ∧ x ∈ U ∧ IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber s U :=
  S.exists_isSubbundleFrameOn x

theorem finrank_fiber (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (x : M) : Module.finrank 𝕜 (S.fiber x) = S.rank := by
  obtain ⟨U, s, hU, hx, hs⟩ := S.exists_frame x
  let t : Fin S.rank → S.fiber x := fun i => ⟨s i x, hs.mem_fiber hx i⟩
  have htli : LinearIndependent 𝕜 t := by
    apply LinearIndependent.of_comp (S.fiber x).subtype
    have hcomp : (S.fiber x).subtype ∘ t = fun i => s i x := by
      funext i
      rfl
    rw [hcomp]
    exact hs.linearIndependent hx
  have htspan : Submodule.span 𝕜 (Set.range t) = ⊤ := by
    apply (Submodule.map_injective_of_injective (S.fiber x).injective_subtype)
    have hrange : (S.fiber x).subtype '' Set.range t = Set.range (fun i => s i x) := by
      ext v
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨t i, ⟨i, rfl⟩, rfl⟩
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, hrange, hs.spans hx]
  let b : Basis (Fin S.rank) 𝕜 (S.fiber x) := Basis.mk htli (by rw [htspan])
  simpa using Module.finrank_eq_card_basis b

end ContMDiffVectorSubbundle
