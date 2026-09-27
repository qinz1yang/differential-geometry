/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellSphereCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem Section34CutFrame.exists_facet_above_of_source_subset
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {m l : Section34CutLabelOf 𝒦 𝒦'} (hml : src m ⊆ src l) (hne : m ≠ l) :
    ∃ k : Section34CutLabelOf 𝒦 𝒦',
      section34Dim k + 1 = section34Dim l ∧ src m ⊆ src k ∧ src k ⊆ src l := by
  classical
  obtain ⟨_, _, _, hcell, hboundary, hinter, hdim, hLF, hcover, _⟩ := hcut
  have hsrcU (i : Section34CutLabelOf 𝒦 𝒦') : src i ⊆ U :=
    (subset_iUnion src i).trans hcover.subset
  have hfin : (section34Face src l).Finite := finite_face_of_locallyFinite U src l
    (fun i => (hcell i).nonempty) (hcell l).isCompact hsrcU hLF
  let F := section34Face src l \ {l}
  let _ : Finite F := (hfin.sdiff (t := {l})).to_subtype
  have hmlt := (hdim l m hml).resolve_left hne
  obtain ⟨n, hln⟩ : ∃ n, section34Dim l = n + 1 := ⟨section34Dim l - 1, by omega⟩
  have hlcell : IsPLCellOn (n + 1) (src l) (srcBd l) := hln ▸ hcell l
  obtain ⟨P, r, u, hr, hu, hlP, hlBd⟩ := hlcell
  let g : M → E3 := Function.invFunOn u P
  have hginj : InjOn g (src l) := by
    rw [hlP]
    exact Function.invFunOn_injOn_image u P
  have hmodelbd : r '' stdSimplexBoundary (n + 1) ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr.bijOn.mapsTo hx.1
  have hgbd : g '' srcBd l = r '' stdSimplexBoundary (n + 1) := by
    rw [hlBd]
    exact hu.injOn.invFunOn_image hmodelbd
  have hBsphere : IsPLSphere n (g '' srcBd l) := by
    rw [hgbd]
    exact hr.isPLSphere_image_stdSimplexBoundary
  have hFcover : g '' srcBd l = ⋃ i : F, g '' src i.1 := by
    rw [hboundary l]
    simp only [F, image_iUnion, iUnion_subtype]
  have hFball : ∀ i : F, IsPLBall (section34Dim i.1) (g '' src i.1) := by
    intro i
    obtain ⟨q, hq, _⟩ := (hcell i.1).exists_isPLHomeomorphOn_invFunOn hu
      (i.2.1.trans hlP.subset)
    exact ⟨q, hq⟩
  have hFdim : ∀ i : F, section34Dim i.1 ≤ n := by
    intro i
    have hil : i.1 ≠ l := i.2.2
    have hlt := (hdim l i.1 i.2.1).resolve_left hil
    omega
  obtain ⟨x, hxm, hxbd⟩ := (hcell m).sdiff_boundary_nonempty
  have hxB : x ∈ srcBd l := by
    rw [hboundary l]
    exact mem_iUnion₂.mpr ⟨m, ⟨hml, hne⟩, hxm⟩
  obtain ⟨k, hkdim, hxk⟩ := exists_cell_dim_eq_of_sphere_cover
    (fun i : F => section34Dim i.1) (fun i : F => g '' src i.1)
    hFball hFcover hBsphere hFdim (mem_image_of_mem g hxB)
  obtain ⟨y, hyk, hyx⟩ := hxk
  have hyxeq : y = x := hginj (k.2.1 hyk) (hml hxm) hyx
  have hxinter : x ∈ src m ∩ src k.1 := ⟨hxm, hyxeq ▸ hyk⟩
  rw [hinter m k.1] at hxinter
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxinter
  have hjm : j = m := by
    by_contra hjne
    apply hxbd
    rw [hboundary m]
    exact mem_iUnion₂.mpr ⟨j, ⟨hj.1, hjne⟩, hxj⟩
  refine ⟨k.1, by omega, ?_, k.2.1⟩
  exact hjm ▸ hj.2

end DifferentialGeometry.Topology.PiecewiseLinear
