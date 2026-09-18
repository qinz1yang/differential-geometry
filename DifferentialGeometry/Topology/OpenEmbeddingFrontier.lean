import DifferentialGeometry.Topology.FixedPoint.Brouwer

open Set

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem isOpen_range_of_isOpen_subtype {V : Set E} (hV : IsOpen V) (g : V → E)
    (hg : Continuous g) (hginj : Function.Injective g) : IsOpen (range g) :=
  isOpen_range_of_isOpen_of_continuous_injective (modelWithCornersSelf ℝ E) hV g hg hginj

theorem isOpen_image_of_subset_of_injOn {f : E → E} {U : Set E}
    (hf : ContinuousOn f U) (hinj : InjOn f U) {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) :
    IsOpen (f '' V) :=
  invariance_of_domain_open_map f V hV (hf.mono hVU) (hinj.mono hVU)

theorem interior_image_eq_image_interior {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) {P : Set E} (hPU : P ⊆ U) :
    interior (f '' P) = f '' interior P := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hxP, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hW : IsOpen (U ∩ f ⁻¹' interior (f '' P)) :=
      hf.isOpen_inter_preimage hU isOpen_interior
    have hxW : x ∈ U ∩ f ⁻¹' interior (f '' P) := ⟨hPU hxP, hy⟩
    have hWP : U ∩ f ⁻¹' interior (f '' P) ⊆ P := by
      rintro z ⟨hzU, hzf⟩
      obtain ⟨p, hpP, hpz⟩ := interior_subset hzf
      exact (hinj (hPU hpP) hzU hpz) ▸ hpP
    exact mem_interior.mpr ⟨_, hWP, hW, hxW⟩
  · exact interior_maximal (image_mono interior_subset)
      (isOpen_image_of_subset_of_injOn hf hinj isOpen_interior (interior_subset.trans hPU))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem image_sdiff_interior {f : E → E} {U : Set E} (hinj : InjOn f U) {P : Set E}
    (hPU : P ⊆ U) : f '' (P \ interior P) = f '' P \ f '' interior P := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨hxP, hxI⟩, rfl⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    exact hxI ((hinj (hPU (interior_subset hz)) (hPU hxP) hzx) ▸ hz)
  · rintro _ ⟨⟨x, hxP, rfl⟩, hy⟩
    exact ⟨x, ⟨hxP, fun hxI => hy ⟨x, hxI, rfl⟩⟩, rfl⟩

theorem frontier_image_eq_image_frontier {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) {P : Set E} (hPU : P ⊆ U)
    (hP : IsCompact P) : frontier (f '' P) = f '' frontier P := by
  have himg : IsClosed (f '' P) := (hP.image_of_continuousOn (hf.mono hPU)).isClosed
  rw [himg.frontier_eq, hP.isClosed.frontier_eq,
    interior_image_eq_image_interior hU hf hinj hPU, image_sdiff_interior hinj hPU]

theorem closure_interior_image_eq_image {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) {P : Set E} (hPU : P ⊆ U)
    (hP : IsCompact P) (hreg : closure (interior P) = P) :
    closure (interior (f '' P)) = f '' P := by
  rw [interior_image_eq_image_interior hU hf hinj hPU]
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset)
      (hP.image_of_continuousOn (hf.mono hPU)).isClosed
  · have hmap : MapsTo f (interior P) (f '' interior P) := fun x hx => ⟨x, hx, rfl⟩
    have hcont : ContinuousOn f (closure (interior P)) := by
      rw [hreg]; exact hf.mono hPU
    have hcl := hmap.closure_of_continuousOn hcont
    rw [hreg] at hcl
    rintro _ ⟨x, hxP, rfl⟩
    exact hcl hxP

theorem interior_range_eq_image_preimage_interior {A : Set E} (hA : IsCompact A)
    (g : A → E) (hg : Continuous g) (hginj : Function.Injective g) :
    interior (range g) = g '' ((Subtype.val : A → E) ⁻¹' interior A) := by
  have _ : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hemb : Topology.IsEmbedding g := (hg.isClosedEmbedding hginj).isEmbedding
  have hopen : IsOpen (g '' ((Subtype.val : A → E) ⁻¹' interior A)) := by
    have hkcont : Continuous (fun v : interior A => g ⟨v.1, interior_subset v.2⟩) :=
      hg.comp (continuous_subtype_val.subtype_mk _)
    have hkinj : Function.Injective (fun v : interior A => g ⟨v.1, interior_subset v.2⟩) := by
      intro v w hvw
      exact Subtype.ext (congrArg (Subtype.val : A → E) (hginj hvw))
    have hrange : range (fun v : interior A => g ⟨v.1, interior_subset v.2⟩) =
        g '' ((Subtype.val : A → E) ⁻¹' interior A) := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨⟨v.1, interior_subset v.2⟩, v.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a.1, ha⟩, rfl⟩
    rw [← hrange]
    exact isOpen_range_of_isOpen_subtype isOpen_interior _ hkcont hkinj
  apply Subset.antisymm
  · intro y hy
    obtain ⟨a, rfl⟩ := interior_subset hy
    refine ⟨a, ?_, rfl⟩
    have hFcont : Continuous
        (fun w : interior (range g) =>
          (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩ : E)) :=
      continuous_subtype_val.comp
        (hemb.toHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
    have hFinj : Function.Injective
        (fun w : interior (range g) =>
          (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩ : E)) := by
      intro v w hvw
      have h1 := hemb.toHomeomorph.symm.injective (Subtype.ext hvw)
      exact Subtype.ext (congrArg (Subtype.val : range g → E) h1)
    have hFopen : IsOpen (range
        (fun w : interior (range g) =>
          (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩ : E))) :=
      isOpen_range_of_isOpen_subtype isOpen_interior _ hFcont hFinj
    have hFsub : range
        (fun w : interior (range g) =>
          (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩ : E)) ⊆ A := by
      rintro _ ⟨w, rfl⟩
      exact (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩).2
    have hval : hemb.toHomeomorph a = ⟨g a, interior_subset hy⟩ :=
      Subtype.ext (hemb.toHomeomorph_apply_coe a)
    have hmem : (a : E) ∈ range
        (fun w : interior (range g) =>
          (hemb.toHomeomorph.symm ⟨w.1, interior_subset w.2⟩ : E)) := by
      refine ⟨⟨g a, hy⟩, ?_⟩
      change (hemb.toHomeomorph.symm ⟨g a, interior_subset hy⟩ : E) = (a : E)
      rw [← hval, hemb.toHomeomorph.symm_apply_apply]
    exact mem_interior.mpr ⟨_, hFsub, hFopen, hmem⟩
  · exact interior_maximal (by rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩) hopen

end DifferentialGeometry.Topology
