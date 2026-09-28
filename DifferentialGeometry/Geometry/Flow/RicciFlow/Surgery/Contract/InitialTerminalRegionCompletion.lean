import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialTerminalRegionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmoothCutCapTransitionInstance

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialTerminalRegion

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (R : InitialTerminalRegion D ε Λ)

theorem core_eq_component_of_isEmpty_boundary (c : {c // c ∈ R.component})
    [IsEmpty (R.core c).Boundary] :
    (Subtype.val ⁻¹' (R.core c).region : Set D.slab.terminalRegularOpen) =
      {x | ConnectedComponents.mk x = c.val} := by
  have hregion : (R.core c).region = (R.core c).interiorImage := by
    simpa only [iUnion_of_empty, union_empty] using
      (R.core c).region_eq_interiorImage_union_spheres
  have hopen : IsOpen (R.core c).region := hregion ▸ (R.core c).isOpen_interiorImage
  have hclopen : IsClopen (Subtype.val ⁻¹' (R.core c).region :
      Set D.slab.terminalRegularOpen) :=
    ⟨(R.core c).compact.isClosed.preimage continuous_subtype_val,
      hopen.preimage continuous_subtype_val⟩
  obtain ⟨y, hyc, hyR⟩ := (R.component_iff_meets_low c.val).mp c.property
  have hy : y.val ∈ (R.core c).region :=
    interior_subset (R.low_mem_interior c y hyc hyR)
  ext x
  constructor
  · intro hx
    exact R.core_component c ⟨x.val, hx⟩
  · intro hx
    apply hclopen.connectedComponent_subset hy
    exact ConnectedComponents.coe_eq_coe'.mp (hx.trans hyc.symm)

theorem exists_terminalCorePresentation_of_isEmpty_boundary
    (hboundary : ∀ c : {c // c ∈ R.component}, IsEmpty (R.core c).Boundary) :
    ∃ P : TerminalCorePresentation D ε Λ,
      P.component = R.component ∧ P.coreRadius = R.coreRadius ∧
      (∀ c (hc : c ∈ R.component), P.core c =
        (Subtype.val ⁻¹' (R.core ⟨c, hc⟩).region : Set D.slab.terminalRegularOpen)) ∧
      ∀ c, IsEmpty (P.hornIndex c) := by
  classical
  let core : ConnectedComponents D.slab.terminalRegularOpen → Set D.slab.terminalRegularOpen :=
    fun c => if hc : c ∈ R.component then Subtype.val ⁻¹' (R.core ⟨c, hc⟩).region else ∅
  have hcore (c) (hc : c ∈ R.component) : core c =
      (Subtype.val ⁻¹' (R.core ⟨c, hc⟩).region : Set D.slab.terminalRegularOpen) := by
    simp only [core, dite_eq_left hc]
  have hempty (c) (hc : c ∉ R.component) : core c = ∅ := by
    simp only [core, dite_eq_right hc]
  have hcomp (c) (hc : c ∈ R.component) :
      core c = {x | ConnectedComponents.mk x = c} := by
    let _ := hboundary ⟨c, hc⟩
    exact (hcore c hc).trans (R.core_eq_component_of_isEmpty_boundary ⟨c, hc⟩)
  have hopen (c) : IsOpen (core c) := by
    by_cases hc : c ∈ R.component
    · rw [hcore c hc]
      let _ := hboundary ⟨c, hc⟩
      have heq : (R.core ⟨c, hc⟩).region = (R.core ⟨c, hc⟩).interiorImage := by
        simpa only [iUnion_of_empty, union_empty] using
          (R.core ⟨c, hc⟩).region_eq_interiorImage_union_spheres
      rw [heq]
      exact (R.core ⟨c, hc⟩).isOpen_interiorImage.preimage continuous_subtype_val
    · rw [hempty c hc]
      exact isOpen_empty
  have hcompact (c) (hc : c ∈ R.component) : IsCompact (core c) := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ D.slab.terminalRegularOpen))]
    have himage : Subtype.val '' core c = (R.core ⟨c, hc⟩).region := by
      rw [hcore c hc]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, R.core_terminal ⟨c, hc⟩ hx⟩, hx, rfl⟩
    rw [himage]
    exact (R.core ⟨c, hc⟩).compact
  have hconnected (c) (hc : c ∈ R.component) : IsConnected (core c) := by
    obtain ⟨x, hx, _⟩ := (R.component_iff_meets_low c).mp hc
    have heq : core c = connectedComponent x := by
      rw [hcomp c hc]
      ext y
      exact ⟨fun hy => ConnectedComponents.coe_eq_coe'.mp (hy.trans hx.symm),
        fun hy => (ConnectedComponents.coe_eq_coe'.mpr hy).trans hx⟩
    rw [heq]
    exact isConnected_connectedComponent
  have hinterior (c) :
      let _ := subsetChartedSpace (core c) (hopen c)
      (Subtype.val : core c → D.slab.terminalRegularOpen) ''
        (𝓡∂ 3).interior (core c) = interior (core c) := by
    let _ := subsetChartedSpace (core c) (hopen c)
    have hb := subset_boundary_eq_empty (core c) (hopen c)
    have hi : (𝓡∂ 3).interior (core c) = (univ : Set (core c)) := by
      simpa only [hb, union_empty] using
        (ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 3) (M := core c))
    change (Subtype.val : core c → D.slab.terminalRegularOpen) '' (𝓡∂ 3).interior (core c) = interior (core c)
    rw [hi, image_univ, Subtype.range_coe, (hopen c).interior_eq]
  have hfrontier (c) (hc : c ∈ R.component) : frontier (core c) = ∅ :=
    IsClopen.frontier_eq ⟨(hcompact c hc).isClosed, hopen c⟩
  let P : TerminalCorePresentation D ε Λ :=
    { epsilon_pos := R.epsilon_pos
      Lambda_ge_one := R.Lambda_ge_one
      coreRadius := R.coreRadius
      coreRadius_pos := R.coreRadius_pos
      coreRadius_eq := R.coreRadius_eq
      component := R.component
      component_finite := R.component_finite
      core := core
      core_isCompact := hcompact
      core_isConnected := hconnected
      core_empty := hempty
      coreCharts := fun c _ => subsetChartedSpace (core c) (hopen c)
      core_smooth := fun c _ => subsetIsManifold (core c) (hopen c)
      core_induced := fun c _ => subset_inclusion_isSmoothEmbedding (core c) (hopen c)
      core_interior_eq := fun c _ => hinterior c
      core_boundary_eq := fun c hc => by
        rw [subset_boundary_eq_empty (core c) (hopen c), image_empty, hfrontier c hc]
      component_iff_meets_low := R.component_iff_meets_low
      low_mem_interior_core := fun c hc x hx _ => by
        rw [(hopen c).interior_eq, hcomp c hc]
        exact hx
      hornIndex := fun _ => PEmpty
      hornIndex_finite := fun _ => inferInstance
      hornIndex_empty := fun _ _ => inferInstance
      horn := fun _ e => isEmptyElim e
      horn_smooth := fun _ e => isEmptyElim e
      horn_interior_embedding := fun _ e => isEmptyElim e
      horn_injOn := fun _ e => isEmptyElim e
      horn_proper := fun _ e => isEmptyElim e
      horn_range_disjoint := fun _ e => isEmptyElim e
      horn_meets_core := fun _ e => isEmptyElim e
      horn_base_covers_boundary := fun c hc => by
        rw [iUnion_of_empty, hfrontier c hc]
      hornCollar := fun _ e => isEmptyElim e
      horn_collar_core_side := fun _ e => isEmptyElim e
      horn_collar_eq := fun _ e => isEmptyElim e
      horn_covers_component := fun c hc => by
        rw [iUnion_of_empty, union_empty, hcomp c hc]
      horn_scalar_large := fun _ e => isEmptyElim e
      horn_base_scalar := fun _ e => isEmptyElim e
      horn_scalar_diverges := fun _ e => isEmptyElim e
      horn_spatial_neck := fun _ e => isEmptyElim e }
  exact ⟨P, rfl, rfl, hcore, fun _ => inferInstance⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialTerminalRegion
