import Mathlib.Topology.PartialHomeomorph.Defs
import Mathlib.Topology.Separation.Regular


namespace PartialHomeomorph

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace Y] [RegularSpace Y]

theorem exists_open_image_isCompact_closure
    (e : PartialHomeomorph X Y) (htarget : IsOpen e.target)
    {C : Set X} (hC : IsCompact C) (hCs : C ⊆ e.source) :
    ∃ W : Set Y, IsOpen W ∧ e '' C ⊆ W ∧ closure W ⊆ e.target ∧
      IsCompact (closure W) ∧ IsCompact (e.symm '' closure W) ∧
      e.symm '' closure W ⊆ e.source ∧
      MapsTo e.symm W (e.symm '' closure W) := by
  have hImage : IsCompact (e '' C) :=
    hC.image_of_continuousOn (e.continuousOn.mono hCs)
  have hImageTarget : e '' C ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hCs hx)
  obtain ⟨W, hW, hCW, hWt, hWc⟩ :=
    exists_open_between_and_isCompact_closure hImage htarget hImageTarget
  refine ⟨W, hW, hCW, hWt, hWc,
    hWc.image_of_continuousOn (e.continuousOn_symm.mono hWt), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hWt hy)
  · intro y hy
    exact mem_image_of_mem e.symm (subset_closure hy)

end PartialHomeomorph
