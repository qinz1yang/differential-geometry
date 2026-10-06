import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology

/-- Model space of `Torus × ℝ` (used only to run invariance of domain). -/
abbrev TorusLineModel_LTP1 := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ

instance instChartedTorusLine_LTP1 : ChartedSpace TorusLineModel_LTP1 (Torus × ℝ) :=
  inferInstanceAs (ChartedSpace (ModelProd (ModelProd (EuclideanSpace ℝ (Fin 1))
    (EuclideanSpace ℝ (Fin 1))) ℝ) (Torus × ℝ))

/-- Invariance of domain between a `3`-dimensional charted space `X` and a `3`-manifold `M`:
a continuous injection on an open set is an open map. -/
theorem isOpen_image_of_injOn_LTP1 {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] (hdim : Module.finrank ℝ E₁ = 3)
    {X M : Type*} [TopologicalSpace X] [ChartedSpace E₁ X]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set X} (hU : IsOpen U) {f : X → M} (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  let c := chartAt E₁ x
  let d := chartAt (EuclideanSpace ℝ (Fin 3)) (f x)
  let V : Set X := U ∩ f ⁻¹' d.source
  have hV : IsOpen V := hf.isOpen_inter_preimage hU d.open_source
  let W : Set E₁ := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.isOpen_inter_preimage_symm hV
  let g : E₁ → EuclideanSpace ℝ (Fin 3) := fun z => d (f (c.symm z))
  have hfcs : ContinuousOn (f ∘ c.symm) W :=
    hf.comp (c.continuousOn_symm.mono inter_subset_left) (fun z hz => hz.2.1)
  have hgc : ContinuousOn g W := d.continuousOn.comp hfcs (fun z hz => hz.2.2)
  have hginj : InjOn g W := by
    intro z hz z' hz' h
    have h1 : f (c.symm z) = f (c.symm z') := d.injOn hz.2.2 hz'.2.2 h
    have h2 : c.symm z = c.symm z' := hinj hz.2.1 hz'.2.1 h1
    exact c.symm.injOn hz.1 hz'.1 h2
  have hopen : IsOpen (g '' W) :=
    invariance_of_domain_isOpen_image_of_finrank_eq (by simpa using hdim) hW hgc hginj
  have hsub : g '' W ⊆ d.symm.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.map_source hz.2.2
  have hT : IsOpen (d.symm '' (g '' W)) := d.symm.isOpen_image_of_subset_source hopen hsub
  have hxW : c x ∈ W := by
    refine ⟨c.map_source (mem_chart_source E₁ x), ?_⟩
    change c.symm (c x) ∈ V
    rw [c.left_inv (mem_chart_source E₁ x)]
    exact ⟨hx, mem_chart_source _ _⟩
  have hfx : f x ∈ d.symm '' (g '' W) := by
    refine ⟨g (c x), ⟨c x, hxW, rfl⟩, ?_⟩
    change d.symm (d (f (c.symm (c x)))) = f x
    rw [c.left_inv (mem_chart_source E₁ x)]
    exact d.left_inv (mem_chart_source _ _)
  refine Filter.mem_of_superset (hT.mem_nhds hfx) ?_
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨c.symm z, hz.2.1, ?_⟩
  exact (d.left_inv hz.2.2).symm ▸ rfl

/-- Open partial homeomorphism with prescribed open source from an open continuous injection. -/
def ofInjOn_LTP1 {X M : Type*} [TopologicalSpace X] [TopologicalSpace M] [Nonempty X]
    (f : X → M) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hopen : ∀ V, V ⊆ U → IsOpen V → IsOpen (f '' V)) : OpenPartialHomeomorph X M :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U) hf
    (by
      intro V hV
      have h1 : IsOpen (Subtype.val '' V : Set X) := hU.isOpenMap_subtype_val V hV
      have h2 := hopen _ (by rintro _ ⟨v, _, rfl⟩; exact v.2) h1
      have : (U.domRestrict f) '' V = f '' (Subtype.val '' V) := by
        rw [← image_comp]; rfl
      change IsOpen ((U.domRestrict f) '' V)
      rwa [this])
    hU

@[simp] theorem ofInjOn_apply_LTP1 {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Nonempty X] (f : X → M) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (hopen : ∀ V, V ⊆ U → IsOpen V → IsOpen (f '' V)) :
    ⇑(ofInjOn_LTP1 f U hU hf hinj hopen) = f := rfl

@[simp] theorem ofInjOn_source_LTP1 {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Nonempty X] (f : X → M) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (hopen : ∀ V, V ⊆ U → IsOpen V → IsOpen (f '' V)) :
    (ofInjOn_LTP1 f U hU hf hinj hopen).source = U := rfl

/-- Single-slice version: `Torus × ℝ` into a `3`-manifold. -/
def ofInjOnTorusLine_LTP1 {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (f : Torus × ℝ → M) (U : Set (Torus × ℝ)) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) : OpenPartialHomeomorph (Torus × ℝ) M :=
  haveI : Nonempty (Torus × ℝ) := ⟨((1, 1), 0)⟩
  ofInjOn_LTP1 f U hU hf hinj (fun V hVU hV =>
    isOpen_image_of_injOn_LTP1 (E₁ := TorusLineModel_LTP1) (by simp) hV
      (hf.mono hVU) (hinj.mono hVU))

/-- Multi-slice version: `(ι × Torus) × ℝ` into a `3`-manifold. -/
def ofInjOnSigma_LTP1 {ι : Type*} [TopologicalSpace ι] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Nonempty ι]
    (f : (ι × Torus) × ℝ → M) (U : Set ((ι × Torus) × ℝ)) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : OpenPartialHomeomorph ((ι × Torus) × ℝ) M :=
  haveI : Nonempty ((ι × Torus) × ℝ) := ⟨((Classical.arbitrary ι, (1, 1)), 0)⟩
  ofInjOn_LTP1 f U hU hf hinj (fun V hVU hV => by
    have : f '' V = ⋃ j : ι, (fun p : Torus × ℝ => f ((j, p.1), p.2)) ''
        ((fun p : Torus × ℝ => ((j, p.1), p.2)) ⁻¹' V) := by
      ext y
      simp only [mem_image, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨⟨j, t⟩, s⟩, hp, rfl⟩
        exact ⟨j, (t, s), hp, rfl⟩
      · rintro ⟨j, p, hp, rfl⟩
        exact ⟨_, hp, rfl⟩
    rw [this]
    refine isOpen_iUnion fun j => ?_
    let emb : Torus × ℝ → (ι × Torus) × ℝ := fun p => ((j, p.1), p.2)
    have hemb : Continuous emb := by fun_prop
    refine isOpen_image_of_injOn_LTP1 (E₁ := TorusLineModel_LTP1) (by simp)
      (hV.preimage hemb) (f := fun p => f (emb p)) ?_ ?_
    · exact (hf.mono hVU).comp hemb.continuousOn (fun p hp => hp)
    · intro p hp p' hp' h
      have := (hinj.mono hVU) hp hp' h
      have h2 : p.1 = p'.1 ∧ p.2 = p'.2 := by simpa [emb] using this
      exact Prod.ext h2.1 h2.2)

end GC.LongTime.CuspP1
