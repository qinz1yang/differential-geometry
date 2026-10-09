import DifferentialGeometry.Topology.Maps.SaturatedFaces
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

/-!
# EDP05/EDP06 kernels: saturation by connected fibres and equality of fibre circles

Frozen blueprint master207B, proposition `prop:fibration-actual-edge-horizontal-faces` (EDP05,
lines 7040–7090) and proposition `prop:fibration-actual-vertical-circle-agreement` (EDP06, lines
7092–7133).

Both saturation statements consume lane W4-GAF's ZSP03 kernels
(`DifferentialGeometry/Topology/Maps/SaturatedFaces.lean`):
`isPreconnected_subset_interior_or_subset_compl_closure` and `isClosed_image_and_preimage_image_eq`.

* `preimage_singleton_subset_of_frontier`: EDP05's "a disk fibre meeting `∂M₂` lies in it;
  connectedness of the disk then implies saturation of `M₂ ∩ X₂`". If every fibre of `f` is
  preconnected and every fibre through a frontier point of `S` lies in `S`, then every fibre meeting
  `S` lies in `S`.
* `saturated_closed_image_of_frontier`: with a proper `f` and closed `S`, `S = f⁻¹(f S)` and its
  image `C₂ = f(S)` is closed (EDP05: "properness of `f₂` implies that its image `C₂` is closed").
  The same lemma with `f = E` on `X₁` is EDP06's saturation of `M₂ ∩ X₁`.
* `range_eq_of_range_subset_of_isEmbedding`: EDP06's "this inclusion of a compact connected smooth
  circle into the disk's connected smooth boundary circle is open ... and closed by compactness. It
  is the entire boundary circle." For a continuous injective `c : P → X` from a compact nonempty
  `F`-charted space and an embedding `d : Q → X` of a connected Hausdorff `F`-charted space with
  `range c ⊆ range d`, the ranges agree. Openness comes from invariance of domain
  (`DifferentialGeometry.Topology.surjective_of_continuous_injective`), so no smoothness is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

/-- **EDP05 kernel (saturation).** If every fibre of `f` is preconnected and every fibre through a
frontier point of `S` lies in `S`, then every fibre meeting `S` lies in `S`. -/
theorem preimage_singleton_subset_of_frontier {X B : Type*} [TopologicalSpace X] (f : X → B)
    {S : Set X} (hconn : ∀ x : X, IsPreconnected (f ⁻¹' {f x}))
    (hfront : ∀ x ∈ frontier S, f ⁻¹' {f x} ⊆ S) :
    ∀ x ∈ S, f ⁻¹' {f x} ⊆ S := by
  intro x hx y hy
  by_cases hmeet : (f ⁻¹' {f x} ∩ frontier S).Nonempty
  · obtain ⟨z, hzD, hzF⟩ := hmeet
    have h := hfront z hzF
    rw [show f z = f x from hzD] at h
    exact h hy
  · have hdisj : Disjoint (f ⁻¹' {f x}) (frontier S) :=
      disjoint_left.mpr fun z hz hzF => hmeet ⟨z, hz, hzF⟩
    rcases DifferentialGeometry.Topology.isPreconnected_subset_interior_or_subset_compl_closure
      (hconn x) hdisj with h | h
    · exact interior_subset (h hy)
    · exact absurd (subset_closure hx) (h (mem_preimage.mpr rfl))

/-- **EDP05 kernel (saturated restriction with closed base).** For a proper map with preconnected
fibres and a closed set `S` whose frontier points carry their whole fibres, `S` is the full preimage
of its image and the image is closed. -/
theorem saturated_closed_image_of_frontier {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    {f : X → B} (hf : IsProperMap f) {S : Set X} (hS : IsClosed S)
    (hconn : ∀ x : X, IsPreconnected (f ⁻¹' {f x}))
    (hfront : ∀ x ∈ frontier S, f ⁻¹' {f x} ⊆ S) :
    f ⁻¹' (f '' S) = S ∧ IsClosed (f '' S) := by
  obtain ⟨hcl, hpre⟩ := DifferentialGeometry.Topology.isClosed_image_and_preimage_image_eq f hf S hS
    fun x y hxy hx => preimage_singleton_subset_of_frontier f hconn hfront x hx
      (mem_preimage.mpr hxy.symm)
  exact ⟨hpre, hcl⟩

/-- **EDP06 kernel (equality of the circles).** A compact nonempty `F`-charted space injected
continuously into the image of an embedded connected Hausdorff `F`-charted space fills that image. -/
theorem range_eq_of_range_subset_of_isEmbedding {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {P Q X : Type*} [TopologicalSpace P]
    [ChartedSpace F P] [CompactSpace P] [Nonempty P] [TopologicalSpace Q] [ChartedSpace F Q]
    [T2Space Q] [ConnectedSpace Q] [TopologicalSpace X] {c : P → X} {d : Q → X}
    (hc : Continuous c) (hcinj : Injective c) (hd : Topology.IsEmbedding d)
    (hsub : range c ⊆ range d) : range c = range d := by
  let e := hd.toHomeomorph
  let h : P → Q := fun x => e.symm ⟨c x, hsub (mem_range_self x)⟩
  have hcont : Continuous h :=
    e.symm.continuous.comp (hc.subtype_mk fun x => hsub (mem_range_self x))
  have hinj : Injective h := by
    intro x y hxy
    have := congrArg (fun z => (e z : X)) hxy
    simp only [h, Homeomorph.apply_symm_apply] at this
    exact hcinj this
  have hsurj := DifferentialGeometry.Topology.surjective_of_continuous_injective (E := F) hcont hinj
  apply Subset.antisymm hsub
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨x, ?_⟩
  have h1 := congrArg (fun z => (e z : X)) hx
  have h2 : ((e y : range d) : X) = d y := rfl
  simp only [h, Homeomorph.apply_symm_apply] at h1
  rw [h1, h2]

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
