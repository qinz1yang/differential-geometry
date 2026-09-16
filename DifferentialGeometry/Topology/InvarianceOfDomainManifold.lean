import DifferentialGeometry.Topology.FixedPoint.Brouwer

open Set
open scoped Topology

namespace DifferentialGeometry.Topology

theorem invariance_of_domain_isOpen_image {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → E} (hf : ContinuousOn f U)
    (hinj : Set.InjOn f U) : IsOpen (f '' U) :=
  invariance_of_domain_open_map f U hU hf hinj

theorem invariance_of_domain_isOpen_image_of_finrank_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContinuousOn f U)
    (hinj : Set.InjOn f U) : IsOpen (f '' U) := by
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simp [H])
  let d : F ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simpa [H] using hdim.symm)
  let V := e.symm ⁻¹' U
  let g : H → H := d ∘ f ∘ e.symm
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have hg : ContinuousOn g V := d.continuous.comp_continuousOn
    (hf.comp e.symm.continuous.continuousOn (fun _ hx => hx))
  have hinjg : InjOn g V := by
    intro x hx y hy hxy
    exact e.symm.injective (hinj hx hy (d.injective hxy))
  have hopen := invariance_of_domain_isOpen_image hV hg hinjg
  have himage : g '' V = d '' (f '' U) := by
    change (d ∘ f ∘ e.symm) '' (e.symm ⁻¹' U) = _
    rw [image_comp, image_comp, e.symm.surjective.image_preimage]
  rw [himage] at hopen
  have hpre := hopen.preimage d.continuous
  simpa only [d.injective.preimage_image] using hpre

theorem isOpen_image_of_continuousOn_injOn {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E M₁]
    [TopologicalSpace M₂] [ChartedSpace E M₂]
    {U : Set M₁} (hU : IsOpen U) {f : M₁ → M₂}
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  let c : OpenPartialHomeomorph M₁ E := chartAt E x
  let W : Set E := c.target ∩ c.symm ⁻¹' U
  have hWopen : IsOpen W := c.isOpen_inter_preimage_symm hU
  let g : W → M₂ := fun z ↦ f (c.symm z.1)
  have hgcont : Continuous g := by
    have hcomp : ContinuousOn (f ∘ c.symm) W :=
      hf.comp (c.continuousOn_symm.mono inter_subset_left) (fun z hz ↦ hz.2)
    exact hcomp.domRestrict
  have hginj : Function.Injective g := by
    intro z w hzw
    apply Subtype.ext
    exact c.symm.injOn z.2.1 w.2.1 (hinj z.2.2 w.2.2 hzw)
  have hopen : IsOpen (range g) :=
    isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersSelf ℝ E) hWopen g hgcont hginj
  have hxsource : x ∈ c.source := mem_chart_source E x
  have hcxW : c x ∈ W := by
    refine ⟨c.map_source hxsource, ?_⟩
    change c.symm (c x) ∈ U
    rwa [c.left_inv hxsource]
  have hpoint : f x ∈ range g :=
    ⟨⟨c x, hcxW⟩, congrArg f (c.left_inv hxsource)⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hpoint)
  rintro z ⟨w, rfl⟩
  exact ⟨c.symm w.1, w.2.2, rfl⟩

theorem isOpenMap_of_continuous_injective {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E M₁]
    [TopologicalSpace M₂] [ChartedSpace E M₂] {f : M₁ → M₂}
    (hf : Continuous f) (hinj : Function.Injective f) : IsOpenMap f := by
  intro U hU
  exact isOpen_image_of_continuousOn_injOn (E := E) hU hf.continuousOn hinj.injOn

theorem surjective_of_continuous_injective {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E M₁] [CompactSpace M₁] [Nonempty M₁]
    [TopologicalSpace M₂] [ChartedSpace E M₂] [T2Space M₂] [ConnectedSpace M₂]
    {f : M₁ → M₂} (hf : Continuous f) (hinj : Function.Injective f) : Function.Surjective f := by
  have hopen : IsOpen (range f) := by
    rw [← image_univ]
    exact isOpenMap_of_continuous_injective (E := E) hf hinj univ isOpen_univ
  have hclopen : IsClopen (range f) := ⟨(isCompact_range hf).isClosed, hopen⟩
  exact range_eq_univ.mp (hclopen.eq_univ (range_nonempty f))

theorem isOpen_range_of_isOpen_of_continuous_injective_real {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hf : Continuous f) (hinj : Function.Injective f) : IsOpen (range f) :=
  isOpen_range_of_isOpen_of_continuous_injective I hU f hf hinj

theorem isOpen_range_of_isOpen_of_isEmbedding_real {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hf : _root_.Topology.IsEmbedding f) : IsOpen (range f) :=
  isOpen_range_of_isOpen_of_continuous_injective_real I hU f hf.continuous hf.injective

theorem isInteriorPoint_iff_any_chart_real {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {x : M} {f : OpenPartialHomeomorph M H} (hf : x ∈ f.source) :
    I.IsInteriorPoint x ↔ I (f x) ∈ interior (range I) :=
  isInteriorPoint_iff_any_chart I hf

theorem isBoundaryPoint_iff_any_chart_real {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {x : M} {f : OpenPartialHomeomorph M H} (hf : x ∈ f.source) :
    I.IsBoundaryPoint x ↔ I (f x) ∈ frontier (range I) :=
  isBoundaryPoint_iff_any_chart I hf

end DifferentialGeometry.Topology
