import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactness.LocallyCompact

namespace MulAction

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X]
  [WeaklyLocallyCompactSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X]

theorem exists_compact_representatives
    {K : Set (orbitRel.Quotient Γ X)} (hK : IsCompact K) :
    ∃ S : Set X, IsCompact S ∧
      ∀ x : X, Quotient.mk (orbitRel Γ X) x ∈ K → ∃ γ : Γ, γ • x ∈ S := by
  classical
  choose C hC hmem using fun x : X => exists_compact_mem_nhds x
  let π : X → orbitRel.Quotient Γ X := Quotient.mk (orbitRel Γ X)
  have hopen : IsOpenMap π := isOpenQuotientMap_quotientMk.isOpenMap
  have hcover : K ⊆ ⋃ x : X, π '' interior (C x) := by
    intro q _
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hmem x), rfl⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : X => π '' interior (C x))
    (fun _ => hopen _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ I, C x, I.isCompact_biUnion (fun x _ => hC x), ?_⟩
  intro x hx
  obtain ⟨y, hyI, z, hz, hzx⟩ := Set.mem_iUnion₂.mp (hI hx)
  obtain ⟨γ, hγ⟩ := Quotient.exact hzx
  change γ • x = z at hγ
  refine ⟨γ, Set.mem_iUnion₂.mpr ⟨y, hyI, ?_⟩⟩
  rw [hγ]
  exact interior_subset hz

end MulAction
