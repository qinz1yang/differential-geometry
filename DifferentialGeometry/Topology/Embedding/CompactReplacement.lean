import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace Topology.IsEmbedding

variable {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]

theorem exists_replacement_of_isClosed
    {e g : X → Y} (he : IsEmbedding e) {D : Set X} (hD : IsClosed D)
    (hg : ContinuousOn g D) (hginj : InjOn g D)
    (hboundary : EqOn g e (frontier D))
    (hdisj : Disjoint (g '' D) (e '' Dᶜ)) :
    ∃ f : X → Y, IsEmbedding f ∧ EqOn f g D ∧ EqOn f e Dᶜ ∧
      range f = g '' D ∪ e '' Dᶜ := by
  classical
  let f := D.piecewise g e
  have hf : Continuous f := continuous_piecewise hboundary
    (hD.closure_eq.symm ▸ hg) he.continuous.continuousOn
  have hfinj : Function.Injective f := (injective_piecewise_iff D).mpr
    ⟨hginj, he.injective.injOn, fun x hx y hy hxy =>
      disjoint_left.mp hdisj (mem_image_of_mem g hx) ⟨y, hy, hxy.symm⟩⟩
  exact ⟨f, (hf.isClosedEmbedding hfinj).isEmbedding,
    piecewise_eqOn D g e, piecewise_eqOn_compl D g e, range_piecewise D g e⟩

theorem exists_replacement_of_openPartialHomeomorph
    {e : X → Y} (he : IsEmbedding e)
    (φ : OpenPartialHomeomorph Z X) {K : Set Z} (hK : IsCompact K)
    (hKφ : K ⊆ φ.source) {g : Z → Y}
    (hg : ContinuousOn g K) (hginj : InjOn g K)
    (hboundary : ∀ x ∈ frontier K, g x = e (φ x))
    (hdisj : Disjoint (g '' K) (e '' (φ '' K)ᶜ)) :
    ∃ f : X → Y, IsEmbedding f ∧ (∀ x ∈ K, f (φ x) = g x) ∧
      EqOn f e (φ '' K)ᶜ ∧ range f = g '' K ∪ e '' (φ '' K)ᶜ := by
  let _ : T2Space X := he.t2Space
  let D := φ '' K
  have hDc : IsClosed D := (hK.image_of_continuousOn (φ.continuousOn.mono hKφ)).isClosed
  have hDφ : D ⊆ φ.target := fun _ hx => by
    obtain ⟨x, hx, rfl⟩ := hx
    exact φ.map_source (hKφ hx)
  have hφD : φ.IsImage K D := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (φ.injOn (hKφ hy) hx hyx) ▸ hy
    · exact mem_image_of_mem φ
  have hmaps : MapsTo φ.symm D K := by
    intro y hy
    exact (hφD.symm (hDφ hy)).mpr hy
  have hboundary' : EqOn (g ∘ φ.symm) e (frontier D) := by
    intro y hy
    have hyD : y ∈ D := hDc.closure_eq ▸ frontier_subset_closure hy
    have hx := (hφD.symm.frontier (hDφ hyD)).mpr hy
    change g (φ.symm y) = e y
    rw [hboundary (φ.symm y) hx, φ.right_inv (hDφ hyD)]
  have himage : (g ∘ φ.symm) '' D = g '' K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_image_of_mem g (hmaps hx)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, mem_image_of_mem φ hx, congrArg g (φ.left_inv (hKφ hx))⟩
  obtain ⟨f, hf, hformula, hfix, hrange⟩ := he.exists_replacement_of_isClosed hDc
    (hg.comp (φ.symm.continuousOn.mono hDφ) hmaps)
    (hginj.comp (φ.symm.injOn.mono hDφ) hmaps)
    hboundary' (himage.symm ▸ hdisj)
  refine ⟨f, hf, ?_, hfix, hrange.trans ?_⟩
  · intro x hx
    exact (hformula (mem_image_of_mem φ hx)).trans (congrArg g (φ.left_inv (hKφ hx)))
  · rw [himage]

end Topology.IsEmbedding
