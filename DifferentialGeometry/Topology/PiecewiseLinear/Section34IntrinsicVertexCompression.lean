/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryCircleFilling
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryInnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MouthConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentFacesFinite

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

open Classical in
theorem exists_section34_vertex_disk_avoiding_all_split_disks
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint J (section34SplitDiskImage src f₁ e))
    (hfill : ∀ t : Section34SimplexIndex 𝒦 3, Section34Incident w.1 t.1 →
      Disjoint J (fblBd t) →
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint J (section34SplitDiskImage srcBd f₁ e)) →
      ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
        ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
          Disjoint D (section34SplitDiskImage src f₁ e)) :
    ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint D (section34SplitDiskImage src f₁ e) := by
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hJS : J ⊆ section34VertexBallImage srcBd f₁ w := by
    rw [hV.boundary_eq_frontier]
    exact fun x hx => ⟨subset_closure (hJV hx), fun hi =>
      (hJN hx).2 (interior_mono (subset_iUnion _ w) hi)⟩
  have hws : Section34Incident w.1 s.1 := by
    by_contra hnot
    obtain ⟨x, hx⟩ := hJ.isConnected.nonempty
    exact notMem_empty x (hinv.2.2.1 s w hnot ▸
      ⟨(hinv.1 s).boundary_subset (hJP hx), hJV hx⟩)
  obtain ⟨Y, hY, hYS, hEY⟩ := exists_section34_connected_set_containing_split_disks
    hcut hf₁ hinv s w hws hJP hJN hJE hfill
  obtain ⟨D, hD, hDS, hYD⟩ := hV.exists_boundary_disk_disjoint_of_isPreconnected
    hY.isPreconnected (hYS.trans sdiff_subset) hJ hJS
      (disjoint_left.mpr fun x hx hxJ => (hYS hx).2 hxJ)
  refine ⟨D, hD, hDS, fun e => ?_⟩
  by_cases hwe : w.1 ⊆ e.1
  · exact (hYD.mono_left (hEY e hwe)).symm
  · apply disjoint_left.mpr
    intro x hxD hxE
    exact hwe (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE
      (hV.boundary_subset (hDS hxD)))

open Classical in
theorem exists_section34_compression_of_vertex_trace_circle
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hfamily : ∀ t : Section34SimplexIndex 𝒦 3,
      ∃ (ι : Type) (_ : Finite ι) (F : ι → Set M₂),
        (∀ i, IsPolyhedralSphere (n := 3) 1 (F i)) ∧
        (Pairwise fun i j => Disjoint (F i) (F j)) ∧
        fblBd t ∩ frontier (⋃ v, section34VertexBallImage src f₁ v) = ⋃ i, F i)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint J (section34SplitDiskImage src f₁ e))
    (hfill : ∀ t : Section34SimplexIndex 𝒦 3, Section34Incident w.1 t.1 →
      Disjoint J (fblBd t) →
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint J (section34SplitDiskImage srcBd f₁ e)) →
      ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
        ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
          Disjoint D (section34SplitDiskImage src f₁ e)) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) fbl fblBd t := by
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  let T := frontier (⋃ v, section34VertexBallImage src f₁ v)
  obtain ⟨D₀, hD₀, hD₀S, hD₀E⟩ := exists_section34_vertex_disk_avoiding_all_split_disks
    hinv hcut hf₁ s w hJ hJP hJV hJN hJE hfill
  have hlocal : ∀ x ∈ D₀, ∀ᶠ y in 𝓝 x, y ∈ T ↔
      y ∈ section34VertexBallImage srcBd f₁ w := by
    intro x hx
    exact hcut.frontier_eventually_eq_vertexBallBoundary hf₁ w
      (hV.boundary_subset (hD₀S hx)) fun e hxe => disjoint_left.mp (hD₀E e) hx hxe
  have hD₀T : D₀ ⊆ T := fun x hx => (hlocal x hx).self_of_nhds.mpr (hD₀S hx)
  have hws : Section34Incident w.1 s.1 := by
    by_contra hnot
    obtain ⟨x, hx⟩ := hJ.isConnected.nonempty
    exact notMem_empty x (hinv.2.2.1 s w hnot ▸
      ⟨(hinv.1 s).boundary_subset (hJP hx), hJV hx⟩)
  let A := {t : Section34SimplexIndex 𝒦 3 // Section34Incident w.1 t.1}
  let _ : Finite A := (finite_setOf_section34Faces_incident_vertex hcut.2.1 w 3).to_subtype
  choose I hI F hF hdis htrace using fun t : A => hfamily t
  let _ : ∀ t : A, Finite (I t) := hI
  let B := Σ t : A, I t
  let G : B → Set M₂ := fun i => F i.1 i.2
  have hG : ∀ i, IsPolyhedralSphere (n := 3) 1 (G i) := fun i => hF i.1 i.2
  have hGP : ∀ i, G i ⊆ fblBd i.1.1 := fun i x hx =>
    (htrace i.1).symm.subset (mem_iUnion.mpr ⟨i.2, hx⟩) |>.1
  have hGT : ∀ i, G i ⊆ T := fun i x hx =>
    (htrace i.1).symm.subset (mem_iUnion.mpr ⟨i.2, hx⟩) |>.2
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    rintro ⟨t, i⟩ ⟨v, j⟩ hne
    by_cases htv : t = v
    · subst v
      exact hdis t (fun hij => hne (by cases hij; rfl))
    · apply disjoint_left.mpr
      intro x hxi hxj
      exact (hGT ⟨t, i⟩ hxi).2 (hinv.2.2.2.1 t v
        (fun heq => htv (Subtype.ext heq))
        ⟨(hinv.1 t).boundary_subset (hGP ⟨t, i⟩ hxi),
          (hinv.1 v).boundary_subset (hGP ⟨v, j⟩ hxj)⟩)
  have hJU : J ⊆ ⋃ i, G i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp ((htrace ⟨s, hws⟩).subset ⟨hJP hx, hJN hx⟩)
    exact mem_iUnion.mpr ⟨⟨⟨s, hws⟩, i⟩, hxi⟩
  have hpair : (range G).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hGdis (fun hij => hne (congrArg G hij))
  have hmem : J ∈ range G :=
    (setOf_isPolyhedralSphere_one_subset_sUnion_eq (finite_range G)
      (by rintro _ ⟨i, rfl⟩; exact hG i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJU⟩
  obtain ⟨i₀, hi₀⟩ := hmem
  obtain ⟨i, D, hD, hDD₀, hclean⟩ :=
    hV.exists_innermost_disk_subset_of_eventually_eq hG hGT hGdis i₀
      (hi₀.symm ▸ hD₀) hD₀S hlocal
  have hDT : D ⊆ T := hDD₀.trans hD₀T
  have hDV : D ⊆ section34VertexBallImage src f₁ w :=
    (hDD₀.trans hD₀S).trans hV.boundary_subset
  have hDG : D ∩ fblBd i.1.1 = G i := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxP⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp ((htrace i.1).subset ⟨hxP, hDT hxD⟩)
      by_cases hji : (⟨i.1, j⟩ : B) = i
      · exact hji ▸ hxj
      · exact (disjoint_left.mp (hclean ⟨i.1, j⟩ hji) hxD hxj).elim
    · exact fun x hx => ⟨hD.boundary_subset hx, hGP i hx⟩
  have hball : ∀ t : Section34SimplexIndex 𝒦 3, t ≠ i.1.1 → Disjoint D (fbl t) := by
    intro t hti
    by_cases hwt : Section34Incident w.1 t.1
    · have hbd : Disjoint D (fblBd t) := by
        apply disjoint_left.mpr
        intro x hxD hxP
        obtain ⟨j, hxj⟩ := mem_iUnion.mp ((htrace ⟨t, hwt⟩).subset ⟨hxP, hDT hxD⟩)
        exact disjoint_left.mp (hclean ⟨⟨t, hwt⟩, j⟩
          (fun heq => hti (congrArg (fun k : B => k.1.1) heq))) hxD hxj
      have hfr : Disjoint D (frontier (fbl t)ᶜ) := by
        rw [frontier_compl, ← (hinv.1 t).boundary_eq_frontier]
        exact hbd
      obtain ⟨x, hx⟩ := (hG i).isConnected.nonempty
      have hnot : x ∉ fbl t := fun hxt => (hGT i hx).2
        (hinv.2.2.2.1 i.1.1 t hti.symm
          ⟨(hinv.1 i.1.1).boundary_subset (hGP i hx), hxt⟩)
      have hsub : D ⊆ (fbl t)ᶜ := IsPreconnected.subset_of_disjoint_frontier
        hD.isConnected.isPreconnected ⟨x, hD.boundary_subset hx, hnot⟩ hfr
      exact disjoint_left.mpr fun y hy hyt => hsub hy hyt
    · exact disjoint_left.mpr fun x hxD hxF =>
        notMem_empty x (hinv.2.2.1 t w hwt ▸ ⟨hxF, hDV hxD⟩)
  exact ⟨i.1.1, w, D, G i, hD, hDD₀.trans hD₀S, hGP i, hDG,
    fun e => (hD₀E e).mono_left hDD₀, fun t hti => (hball t hti).mono_left sdiff_subset⟩

end DifferentialGeometry.Topology.PiecewiseLinear
