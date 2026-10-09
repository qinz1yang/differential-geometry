/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellSphereCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFacePoset
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace CompactSourceFaceProbe

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem exists_facet_above_of_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : src m ⊆ src l) (hne : m ≠ l) :
    ∃ k : Section34CompactLabelOf K K',
      section34BoundedDim k + 1 = section34BoundedDim l ∧
        src m ⊆ src k ∧ src k ⊆ src l := by
  classical
  obtain ⟨_, hKfin, hK'fin, _, _, _, hcell, hboundary, hinter, hdim, _⟩ := hcut
  let : Finite (Section34CompactLabelOf K K') :=
    finite_section34CompactLabelOf hKfin hK'fin
  have hmlt := (hdim l m hml).resolve_left hne
  obtain ⟨n, hln⟩ : ∃ n, section34BoundedDim l = n + 1 :=
    ⟨section34BoundedDim l - 1, by omega⟩
  have hlcell : IsPLCellOn (n + 1) (src l) (srcBd l) := hln ▸ hcell l
  obtain ⟨q, hq, hqboundary⟩ := hlcell.exists_isPLHomeomorphOn_stdSimplex
  have hlsphere : IsPLSphere n (srcBd l) := by
    rw [hqboundary]
    exact hq.isPLSphere_image_stdSimplexBoundary
  let F := section34Face src l \ {l}
  have hcover : srcBd l = ⋃ i : F, src i.1 := by
    simpa only [F, iUnion_subtype] using hboundary l
  have hFball : ∀ i : F, IsPLBall (section34BoundedDim i.1) (src i.1) := by
    intro i
    obtain ⟨r, hr, _⟩ := (hcell i.1).exists_isPLHomeomorphOn_stdSimplex
    exact ⟨r, hr⟩
  have hFdim : ∀ i : F, section34BoundedDim i.1 ≤ n := by
    intro i
    have hneil : i.1 ≠ l := i.2.2
    have hlt := (hdim l i.1 i.2.1).resolve_left hneil
    omega
  obtain ⟨x, hxm, hxbd⟩ := (hcell m).sdiff_boundary_nonempty
  have hxB : x ∈ srcBd l := by
    rw [hboundary l]
    exact mem_iUnion₂.mpr ⟨m, ⟨hml, hne⟩, hxm⟩
  obtain ⟨k, hkdim, hxk⟩ := exists_cell_dim_eq_of_sphere_cover
    (fun i : F => section34BoundedDim i.1) (fun i : F => src i.1)
    hFball hcover hlsphere hFdim hxB
  have hxinter : x ∈ src m ∩ src k.1 := ⟨hxm, hxk⟩
  rw [hinter m k.1] at hxinter
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxinter
  have hjm : j = m := by
    by_contra hjne
    apply hxbd
    rw [hboundary m]
    exact mem_iUnion₂.mpr ⟨j, ⟨hj.1, hjne⟩, hxj⟩
  refine ⟨k.1, by omega, ?_, k.2.1⟩
  exact hjm ▸ hj.2

end CompactSourceFaceProbe

end DifferentialGeometry.Topology.PiecewiseLinear
