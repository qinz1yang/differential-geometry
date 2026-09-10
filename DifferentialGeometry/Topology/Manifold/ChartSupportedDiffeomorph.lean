import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Support

noncomputable section
open Set Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H}

theorem exists_compactly_supported_chart_representative
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (f : Diffeomorph I I M M ∞) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hfix : ∀ x, x ∉ K → f x = x) :
    ∃ g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ z, g z = e (f (e.symm z))) ∧
      (∀ z, g.symm z = e (f.symm (e.symm z))) ∧
      HasCompactSupport (fun z ↦ g z - z) ∧
      ∀ x ∈ e.source, e.symm (g (e x)) = f x := by
  have hfixi (x : M) (hx : x ∉ K) : f.symm x = x := by
    apply f.injective
    exact (f.apply_symm_apply x).trans (hfix x hx).symm
  have hmaps (x : M) (hx : x ∈ e.source) : f x ∈ e.source := by
    by_contra h
    have hfx : f x ∉ K := fun hk ↦ h (hKs hk)
    have heq : f x = x := f.injective (hfix (f x) hfx)
    exact h (heq.symm ▸ hx)
  have hmapsi (x : M) (hx : x ∈ e.source) : f.symm x ∈ e.source := by
    by_contra h
    have hfx : f.symm x ∉ K := fun hk ↦ h (hKs hk)
    have heq : f.symm x = x := f.symm.injective (hfixi (f.symm x) hfx)
    exact h (heq.symm ▸ hx)
  have hes (z : E) : e.symm z ∈ e.source := e.map_target (htarget ▸ mem_univ z)
  have hi : ContMDiff 𝓘(ℝ, E) I ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z ↦ e (f (e.symm z))) := by
    intro z
    exact (he.contMDiffAt (e.open_source.mem_nhds (hmaps _ (hes z)))).comp z
      (f.contMDiff.contMDiffAt.comp z hi.contMDiffAt)
  have hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z ↦ e (f.symm (e.symm z))) := by
    intro z
    exact (he.contMDiffAt (e.open_source.mem_nhds (hmapsi _ (hes z)))).comp z
      (f.symm.contMDiff.contMDiffAt.comp z hi.contMDiffAt)
  let g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toEquiv :=
        { toFun := fun z ↦ e (f (e.symm z))
          invFun := fun z ↦ e (f.symm (e.symm z))
          left_inv := fun z ↦ by
            change e (f.symm (e.symm (e (f (e.symm z))))) = z
            rw [e.left_inv (hmaps _ (hes z)), f.symm_apply_apply,
              e.right_inv (htarget ▸ mem_univ z)]
          right_inv := fun z ↦ by
            change e (f (e.symm (e (f.symm (e.symm z))))) = z
            rw [e.left_inv (hmapsi _ (hes z)), f.apply_symm_apply,
              e.right_inv (htarget ▸ mem_univ z)] }
      contMDiff_toFun := hF
      contMDiff_invFun := hG }
  refine ⟨g, fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_⟩
  · apply HasCompactSupport.intro (K := e '' K)
      (hK.image_of_continuousOn (he.continuousOn.mono hKs))
    intro z hz
    have hzK : e.symm z ∉ K := fun h ↦ hz ⟨e.symm z, h, e.right_inv (htarget ▸ mem_univ z)⟩
    change e (f (e.symm z)) - z = 0
    rw [hfix _ hzK, e.right_inv (htarget ▸ mem_univ z), sub_self]
  · intro x hx
    change e.symm (e (f (e.symm (e x)))) = f x
    rw [e.left_inv hx, e.left_inv (hmaps x hx)]

end Poincare.Topology.Manifold
