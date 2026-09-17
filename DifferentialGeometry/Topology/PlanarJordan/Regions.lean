import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_regions_of_simple_closed_curve
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hclose : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (γ '' Icc 0 1)ᶜ ∧
      frontier U = γ '' Icc 0 1 ∧ frontier V = γ '' Icc 0 1 ∧
      IsCompact (closure U) ∧ ¬ IsCompact (closure V) := by
  let e : ℂ ≃ₜ Schoenflies.Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph
  let C : Set Schoenflies.Plane := (fun t ↦ e (γ t)) '' Icc 0 1
  have hC : Schoenflies.IsJordanCurve C :=
    ⟨fun t ↦ e (γ t), ⟨e.continuous.comp_continuousOn hγ,
      congrArg e hclose, fun _ hx _ hy he ↦ hinj hx hy (e.injective he)⟩, rfl⟩
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hpre : e ⁻¹' C = γ '' Icc 0 1 := by
    ext z
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, e.injective he⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  let U := e ⁻¹' Schoenflies.inside C
  let V := e ⁻¹' Schoenflies.outside C
  have hU : IsOpen U := hsep.isOpen_inside.preimage e.continuous
  have hV : IsOpen V := hsep.isOpen_outside.preimage e.continuous
  have hUi : IsConnected U := e.isConnected_preimage.mpr hsep.isConnected_inside
  have hVi : IsConnected V := e.isConnected_preimage.mpr hsep.isConnected_outside
  have hUfr : frontier U = γ '' Icc 0 1 := by
    rw [← e.preimage_frontier, hsep.frontier_inside, hpre]
  have hVfr : frontier V = γ '' Icc 0 1 := by
    rw [← e.preimage_frontier, hsep.frontier_outside, hpre]
  refine ⟨U, V, hU, hV, hUi, hVi, ?_, ?_, hUfr, hVfr, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    exact fun z hz hz' ↦ hz'.2 hz.2
  · change (e ⁻¹' Schoenflies.inside C) ∪ (e ⁻¹' Schoenflies.outside C) = _
    rw [← preimage_union, Schoenflies.inside_union_outside, preimage_compl, hpre]
  · have hcompact : IsCompact (closure (Schoenflies.inside C)) :=
      hsep.isBounded_inside.isCompact_closure
    have he := e.isCompact_preimage.mpr hcompact
    simpa only [e.preimage_closure] using he
  · intro hcompact
    have he : IsCompact (closure (Schoenflies.outside C)) :=
      e.isCompact_preimage.mp (by simpa only [e.preimage_closure] using hcompact)
    exact hsep.not_isBounded_outside (he.isBounded.subset subset_closure)

end DifferentialGeometry.Topology.PlanarJordan

namespace Schoenflies.IsSeparating

theorem inside_eq_compl_closure_outside {C : Set Plane} (hC : IsSeparating C) :
    inside C = (closure (outside C))ᶜ := by
  rw [(IsRegionOf.outside C).closure_eq hC]
  ext p
  constructor
  · intro hp
    rintro (ho | hc)
    · exact disjoint_left.mp disjoint_inside_outside hp ho
    · exact hp.1 hc
  · intro hp
    have hpc : p ∉ C := fun hc => hp (Or.inr hc)
    have hm : p ∈ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hpc
    exact hm.resolve_right (fun ho => hp (Or.inl ho))

theorem outside_eq_compl_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    outside C = (closure (inside C))ᶜ := by
  rw [(IsRegionOf.inside C).closure_eq hC]
  ext p
  constructor
  · intro hp
    rintro (hi | hc)
    · exact disjoint_left.mp disjoint_inside_outside hi hp
    · exact hp.1 hc
  · intro hp
    have hpc : p ∉ C := fun hc => hp (Or.inr hc)
    have hm : p ∈ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hpc
    exact hm.resolve_left (fun hi => hp (Or.inl hi))

theorem frontier_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    frontier (closure (inside C)) = C := by
  rw [← frontier_compl, ← hC.outside_eq_compl_closure_inside, hC.frontier_outside]

end Schoenflies.IsSeparating

namespace DifferentialGeometry.Topology.PlanarJordan

theorem eq_closure_inside_of_isCompact_of_frontier_subset
    {K C : Set Schoenflies.Plane} (hK : IsCompact K)
    (hC : Schoenflies.IsJordanCurve C) (hne : (interior K).Nonempty)
    (hfront : frontier K ⊆ C) : K = closure (Schoenflies.inside C) := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hdisj : Disjoint (Schoenflies.outside C) (frontier K) :=
    disjoint_left.mpr (fun x hx hxf => hx.1 (hfront hxf))
  have hKout : Disjoint K (Schoenflies.outside C) := by
    apply disjoint_left.mpr
    intro x hxK hxo
    have hxi : x ∈ interior K := (mem_interior_iff_notMem_frontier hxK).mpr
      (fun hxf => hxo.1 (hfront hxf))
    have hsub :=
      DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hsep.isConnected_outside.isPreconnected hdisj ⟨x, hxo, hxi⟩
    exact hsep.not_isBounded_outside (hK.isBounded.subset (hsub.trans interior_subset))
  have hsub : K ⊆ closure (Schoenflies.inside C) := by
    intro x hx
    by_contra hn
    have hout : x ∈ Schoenflies.outside C := by
      rw [hsep.outside_eq_compl_closure_inside]
      exact hn
    exact disjoint_left.mp hKout hx hout
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyK, hyinside⟩ := mem_closure_iff.mp (hsub (interior_subset hx))
    (interior K) isOpen_interior hx
  have hinside : Schoenflies.inside C ⊆ interior K :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hsep.isConnected_inside.isPreconnected
      (disjoint_left.mpr (fun z hz hzf => hz.1 (hfront hzf))) ⟨y, hyinside, hyK⟩
  exact subset_antisymm hsub (closure_minimal (hinside.trans interior_subset) hK.isClosed)

end DifferentialGeometry.Topology.PlanarJordan
