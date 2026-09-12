import Mathlib.Geometry.Manifold.HasGroupoid

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {H X : Type*} [TopologicalSpace H] [TopologicalSpace X]

theorem ofSet_mem_of_closedUnderRestriction (G : StructureGroupoid H) [ClosedUnderRestriction G]
    {s : Set H} (hs : IsOpen s) : OpenPartialHomeomorph.ofSet s hs ∈ G :=
  StructureGroupoid.le_iff.mp ((closedUnderRestriction_iff_id_le G).mp inferInstance) _
    (idRestrGroupoid_mem hs)

structure AtlasOn (G : StructureGroupoid H) (U : Set X) where
  charts : Set (OpenPartialHomeomorph X H)
  source_subset : ∀ e ∈ charts, e.source ⊆ U
  exists_mem_source : ∀ x ∈ U, ∃ e ∈ charts, x ∈ e.source
  compatible : ∀ e ∈ charts, ∀ e' ∈ charts, e.symm ≫ₕ e' ∈ G

namespace AtlasOn

variable {G : StructureGroupoid H} {U V : Set X}

def congr (A : AtlasOn G U) (h : U = V) : AtlasOn G V where
  charts := A.charts
  source_subset e he := h ▸ A.source_subset e he
  exists_mem_source x hx := A.exists_mem_source x (h ▸ hx)
  compatible := A.compatible

def empty (G : StructureGroupoid H) : AtlasOn G (∅ : Set X) where
  charts := ∅
  source_subset _ he := absurd he (notMem_empty _)
  exists_mem_source _ hx := absurd hx (notMem_empty _)
  compatible _ he := absurd he (notMem_empty _)

def ofOpenPartialHomeomorph [ClosedUnderRestriction G] (e : OpenPartialHomeomorph X H) :
    AtlasOn G e.source where
  charts := {e}
  source_subset e' he' := by
    rw [mem_singleton_iff] at he'
    rw [he']
  exists_mem_source x hx := ⟨e, rfl, hx⟩
  compatible e₁ he₁ e₂ he₂ := by
    rw [mem_singleton_iff] at he₁ he₂
    rw [he₁, he₂]
    exact G.mem_of_eqOnSource (ofSet_mem_of_closedUnderRestriction G e.open_target)
      e.symm_trans_self

theorem restrOpen_target (e : OpenPartialHomeomorph X H) (hV : IsOpen V) :
    (e.restrOpen V hV).target = e.target ∩ e.symm ⁻¹' V := rfl

def restrict [ClosedUnderRestriction G] (A : AtlasOn G U) (hV : IsOpen V) :
    AtlasOn G (U ∩ V) where
  charts := (fun e => e.restrOpen V hV) '' A.charts
  source_subset := by
    rintro _ ⟨e, he, rfl⟩
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_subset_inter_left _ (A.source_subset e he)
  exists_mem_source x hx := by
    obtain ⟨e, he, hxe⟩ := A.exists_mem_source x hx.1
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hxe, hx.2⟩
  compatible := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' V) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hV
    refine G.mem_of_eqOnSource (closedUnderRestriction' (A.compatible e he e' he') hopen) ?_
    change (e.restrOpen V hV).symm ≫ₕ e'.restrOpen V hV ≈
      (e.symm ≫ₕ e').restr (e.target ∩ e.symm ⁻¹' V)
    refine ⟨?_, fun _ _ => rfl⟩
    rw [OpenPartialHomeomorph.restr_source' _ _ hopen, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_source, restrOpen_target, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.coe_restrOpen_symm]
    ext y
    simp only [mem_inter_iff, mem_preimage]
    tauto

private theorem trans_cancel (F : X ≃ₜ X) (e e' : OpenPartialHomeomorph X H) :
    (F.toOpenPartialHomeomorph.trans e).symm.trans (F.toOpenPartialHomeomorph.trans e') =
      e.symm.trans e' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc F.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self]
  simp

def transport (A : AtlasOn G U) (F : X ≃ₜ X) : AtlasOn G (F '' U) where
  charts := (fun e => F.symm.toOpenPartialHomeomorph.trans e) '' A.charts
  source_subset := by
    rintro _ ⟨e, he, rfl⟩ x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact ⟨F.symm x, A.source_subset e he hx.2, F.apply_symm_apply x⟩
  exists_mem_source := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, hxe⟩ := A.exists_mem_source x hx
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    simp [hxe]
  compatible := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [trans_cancel]
    exact A.compatible e he e' he'

theorem mem_charts_transport_iff {A : AtlasOn G U} {F : X ≃ₜ X}
    {e₀ : OpenPartialHomeomorph X H} :
    e₀ ∈ (A.transport F).charts ↔
      ∃ e ∈ A.charts, F.symm.toOpenPartialHomeomorph.trans e = e₀ :=
  Iff.rfl

def union (A : AtlasOn G U) (B : AtlasOn G V)
    (h : ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ e' ∈ G) : AtlasOn G (U ∪ V) where
  charts := A.charts ∪ B.charts
  source_subset e he := he.elim (fun he => (A.source_subset e he).trans subset_union_left)
    fun he => (B.source_subset e he).trans subset_union_right
  exists_mem_source x hx := hx.elim
    (fun hx => let ⟨e, he, hxe⟩ := A.exists_mem_source x hx; ⟨e, Or.inl he, hxe⟩)
    fun hx => let ⟨e, he, hxe⟩ := B.exists_mem_source x hx; ⟨e, Or.inr he, hxe⟩
  compatible e he e' he' := by
    rcases he with he | he <;> rcases he' with he' | he'
    · exact A.compatible e he e' he'
    · exact h e he e' he'
    · have hG := G.symm (h e' he' e he)
      rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] at hG
    · exact B.compatible e he e' he'

@[instance_reducible] noncomputable def chartedSpace (A : AtlasOn G (univ : Set X)) :
    ChartedSpace H X where
  atlas := A.charts
  chartAt x := (A.exists_mem_source x (mem_univ x)).choose
  mem_chart_source x := (A.exists_mem_source x (mem_univ x)).choose_spec.2
  chart_mem_atlas x := (A.exists_mem_source x (mem_univ x)).choose_spec.1

theorem hasGroupoid (A : AtlasOn G (univ : Set X)) :
    letI := A.chartedSpace
    HasGroupoid X G := by
  let _ := A.chartedSpace
  exact ⟨fun he he' => A.compatible _ he _ he'⟩

end AtlasOn

end DifferentialGeometry.Topology.Manifold
