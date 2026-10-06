import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Geometry.Hyperbolic.Truncation

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

section Open

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DifferentialGeometry.Topology.HasInvarianceOfDomain E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

/-- A continuous injective map from a `3`-manifold with boundary into a `3`-manifold is open at
interior points: the image of the interior is a neighbourhood of the image of every interior point. -/
theorem image_interior_mem_nhds_CPA2 (hE : Module.finrank ℝ E = 3) {e : M → N}
    (he : Continuous e) (hinj : Injective e) {x : M} (hx : I.IsInteriorPoint x) :
    e '' (I.interior M) ∈ 𝓝 (e x) := by
  let φ := chartAt H x
  have hxφ : x ∈ φ.source := mem_chart_source H x
  have hy₀ : I (φ x) ∈ interior (range I) :=
    (DifferentialGeometry.Topology.isInteriorPoint_iff_any_chart I hxφ).mp hx
  let U₀ : Set E := interior (range I) ∩ I.symm ⁻¹' φ.target
  have hU₀ : IsOpen U₀ :=
    isOpen_interior.inter (φ.open_target.preimage I.continuous_symm)
  have hy₀U : I (φ x) ∈ U₀ := ⟨hy₀, by simpa using φ.map_source hxφ⟩
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hE])
  let U'' : Set (EuclideanSpace ℝ (Fin 3)) := L.symm ⁻¹' U₀
  have hU'' : IsOpen U'' := hU₀.preimage L.symm.continuous
  let ρ : E → M := fun z => φ.symm (I.symm z)
  have hρc : ContinuousOn ρ U₀ := by
    refine φ.continuousOn_symm.comp I.continuous_symm.continuousOn ?_
    intro z hz
    exact hz.2
  have hρi : InjOn ρ U₀ := by
    intro z hz z' hz' h
    have h1 : I (φ (ρ z)) = z := by
      have : φ (ρ z) = I.symm z := φ.right_inv hz.2
      rw [this]; exact I.right_inv (interior_subset hz.1)
    have h2 : I (φ (ρ z')) = z' := by
      have : φ (ρ z') = I.symm z' := φ.right_inv hz'.2
      rw [this]; exact I.right_inv (interior_subset hz'.1)
    rw [← h1, ← h2, h]
  let f : U'' → N := fun z => e (ρ (L.symm z.1))
  have hfc : Continuous f := by
    refine he.comp ?_
    have : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 3) => ρ (L.symm z)) U'' :=
      hρc.comp L.symm.continuous.continuousOn (fun z hz => hz)
    exact this.comp_continuous continuous_subtype_val (fun z => z.2)
  have hfi : Injective f := by
    intro z z' h
    have := hρi (show L.symm z.1 ∈ U₀ from z.2) (show L.symm z'.1 ∈ U₀ from z'.2) (hinj h)
    exact Subtype.ext (L.symm.injective this)
  have hopen : IsOpen (range f) :=
    DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      (𝓡 3) hU'' f hfc hfi
  have hrange : range f ⊆ e '' (I.interior M) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨ρ (L.symm z.1), ?_, rfl⟩
    have hz : L.symm z.1 ∈ U₀ := z.2
    have hmem : ρ (L.symm z.1) ∈ φ.source := φ.map_target hz.2
    have : I.IsInteriorPoint (ρ (L.symm z.1)) := by
      refine (DifferentialGeometry.Topology.isInteriorPoint_iff_any_chart I hmem).mpr ?_
      have h1 : φ (ρ (L.symm z.1)) = I.symm (L.symm z.1) := φ.right_inv hz.2
      rw [h1, I.right_inv (interior_subset hz.1)]
      exact hz.1
    exact this
  have hxmem : e x ∈ range f := by
    refine ⟨⟨L (I (φ x)), by simpa [U''] using hy₀U⟩, ?_⟩
    change e (ρ (L.symm (L (I (φ x))))) = e x
    simp only [ContinuousLinearEquiv.symm_apply_apply, ρ]
    rw [I.left_inv, φ.left_inv hxφ]
  exact Filter.mem_of_superset (hopen.mem_nhds hxmem) hrange

theorem isOpen_image_interior_CPA2 (hE : Module.finrank ℝ E = 3) {e : M → N}
    (he : Continuous e) (hinj : Injective e) : IsOpen (e '' (I.interior M)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  exact image_interior_mem_nhds_CPA2 I hE he hinj hx

end Open

/-- Invariance of domain transfers along a continuous linear equivalence. -/
theorem hasInvarianceOfDomain_of_equiv_CPA2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [DifferentialGeometry.Topology.HasInvarianceOfDomain F]
    (L : E ≃L[ℝ] F) : DifferentialGeometry.Topology.HasInvarianceOfDomain E := by
  refine ⟨fun {x s f} hCont hs hsub => ?_⟩
  let g : PartialEquiv F F :=
    { toFun := fun z => L (f (L.symm z))
      invFun := fun z => L (f.symm (L.symm z))
      source := L.symm ⁻¹' f.source
      target := L.symm ⁻¹' f.target
      map_source' := fun z hz => by simpa using f.map_source hz
      map_target' := fun z hz => by simpa using f.map_target hz
      left_inv' := fun z hz => by simp [f.left_inv hz]
      right_inv' := fun z hz => by simp [f.right_inv hz] }
  have hgc : ContinuousOn g g.source := by
    have h1 : ContinuousOn (fun z : F => f (L.symm z)) (L.symm ⁻¹' f.source) :=
      hCont.comp L.symm.continuous.continuousOn (fun z hz => hz)
    exact L.continuous.comp_continuousOn h1
  have hs' : L '' s ∈ nhds (L x) := L.toHomeomorph.isOpenMap.image_mem_nhds hs
  have hsub' : L '' s ⊆ g.source := by
    rintro _ ⟨y, hy, rfl⟩
    show L.symm (L y) ∈ f.source
    simpa using hsub hy
  have h := DifferentialGeometry.Topology.HasInvarianceOfDomain.invariance_of_domain hgc hs' hsub'
  have himg : g '' (L '' s) = L '' (f '' s) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨f y, ⟨y, hy, rfl⟩, by simp [g]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨L y, ⟨y, hy, rfl⟩, by simp [g]⟩
  have hgx : g (L x) = L (f x) := by simp [g]
  rw [himg, hgx] at h
  have h2 := L.symm.toHomeomorph.isOpenMap.image_mem_nhds h
  have h3 : (L.symm '' (L '' (f '' s))) = f '' s := by
    ext w; simp
  have h4 : L.symm (L (f x)) = f x := by simp
  simpa [h3, h4] using h2

end GC.LongTime.CuspP1
