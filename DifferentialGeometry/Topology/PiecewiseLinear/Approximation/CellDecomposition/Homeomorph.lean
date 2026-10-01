import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Extension

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_isPLHomeomorphInto_of_graph_cut_cells (hK : K.faces.Finite)
    (hK' : K'.faces.Finite)
    (hsc : ∀ l, IsPLCellOn (section34BoundedDim l) (src l) (srcBd l))
    (hsbd : ∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m)
    (hsinter : ∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k)
    (hsdim : ∀ l m, src m ⊆ src l → m = l ∨ section34BoundedDim m < section34BoundedDim l)
    {tc tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (htcell : ∀ l, IsPLCellOn (section34BoundedDim l) (tc l) (tcBd l))
    (htbd : ∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m)
    (htinter : ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k) :
    ∃ F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphInto 3 F (⋃ l, src l) ∧ ∀ l, F '' src l = tc l := by
  have hfin := finite_section34CompactLabelOf hK hK'
  choose Pp rr uu hrr huu hsceq hsbdeq using hsc
  choose Qq ss vv hss hvv htceq htbdeq using htcell
  refine exists_isPLHomeomorphInto_of_labelledCells section34BoundedDim (section34Face src) Pp Qq
    rr ss uu vv src tc section34BoundedDim_le_three hrr hss huu hvv hsceq htceq
    (fun l m hm => hsdim l m hm) ?_ ?_ hsinter htinter ?_ ?_
  · intro l
    rw [← hsbdeq l]
    exact hsbd l
  · intro l
    rw [← htbdeq l]
    exact htbd l
  · intro x _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩
  · intro y _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩

end Extension

end DifferentialGeometry.Topology.PiecewiseLinear
