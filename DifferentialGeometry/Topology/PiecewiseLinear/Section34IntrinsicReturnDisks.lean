/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MouthConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.SphereReturnDisk

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

theorem exists_section34_model_return_disk_avoiding_split_disks
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e₀ : Section34EdgeIndex 𝒦 𝒦') {P B : Set E3} {u : E3 → M₂} {η : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P)
    (hVP : section34VertexBallImage src f₁ w ⊆ u '' P)
    (hη : IsPLHomeomorphOn η (Icc 0 1) B) (hBP : B ⊆ P)
    (hBF : B ⊆ u ⁻¹' fblBd s) (hBS : B ⊆ u ⁻¹' section34VertexBallImage srcBd f₁ w)
    (hBN : B ⊆ u ⁻¹' frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hends : ({η 0, η 1} : Set E3) ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e₀)
    (hmeet : B ∩ u ⁻¹' (⋃ e, section34SplitDiskImage src f₁ e) = {η 0, η 1})
    (hfill : ∀ J : Set M₂,
      (∃ (J₀ : Set E3) (v : E3 → M₂), IsPLSphere 1 J₀ ∧
        IsPLHomeomorphInto 3 v J₀ ∧ J = v '' J₀) →
      J ⊆ section34VertexBallImage src f₁ w →
      J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v) →
      ∀ t : Section34SimplexIndex 𝒦 3, Section34Incident w.1 t.1 →
        Disjoint J (fblBd t) →
        (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
          Disjoint J (section34SplitDiskImage srcBd f₁ e)) →
        ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
          ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
            Disjoint D (section34SplitDiskImage src f₁ e)) :
    ∃ (R D : Set E3) (q : (Fin 3 → ℝ) → E3) (δ : ℝ → E3),
      IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
      R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e₀ ∧ B ∩ R = {η 0, η 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      q '' stdSimplexBoundary 2 = B ∪ R ∧ D ⊆ P ∧
      D ⊆ u ⁻¹' (section34VertexBallImage srcBd f₁ w ∩
        frontier (⋃ v, section34VertexBallImage src f₁ v)) ∧
      D ∩ u ⁻¹' section34SplitDiskImage src f₁ e₀ = R ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', e ≠ e₀ →
        Disjoint D (u ⁻¹' section34SplitDiskImage src f₁ e) := by
  classical
  let g := Function.invFunOn u P
  let S := g '' section34VertexBallImage srcBd f₁ w
  let L := g '' section34SplitDiskImage src f₁ e₀
  let Lb := g '' section34SplitDiskImage srcBd f₁ e₀
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e₀
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn g u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hmap : MapsTo g (u '' P) P := hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hSmap : MapsTo u S (section34VertexBallImage srcBd f₁ w) := by
    rintro x ⟨y, hy, rfl⟩
    rwa [hright (hVP (hV.boundary_subset hy))]
  have hSP : S ⊆ P := image_subset_iff.mpr fun y hy => hmap (hVP (hV.boundary_subset hy))
  have hBS' : B ⊆ S := fun x hx => ⟨u x, hBS hx, hleft (hBP hx)⟩
  have hη0 : η 0 ∈ B := hη.bijOn.mapsTo (by norm_num)
  have hwe₀ := hcut.subset_of_mem_splitDiskImage hf₁.injOn
    (hE.boundary_subset (hends (by simp))) (hV.boundary_subset (hBS hη0))
  have he₀s : Section34Incident e₀.1 s.1 := by
    by_contra he
    exact disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s e₀ he)
      ((hinv.1 s).boundary_subset (hBF hη0)) (hE.boundary_subset (hends (by simp)))
  have hEV := hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e₀ hwe₀
  have hEP : section34SplitDiskImage src f₁ e₀ ⊆ u '' P :=
    hEV.trans (hV.boundary_subset.trans hVP)
  have hLbP : section34SplitDiskImage srcBd f₁ e₀ ⊆ u '' P := hE.boundary_subset.trans hEP
  obtain ⟨r, hr, hrS⟩ := hV.exists_isPLHomeomorphOn_invFunOn hu hVP
  have hS : IsPLSphere 2 S := by
    change IsPLSphere 2 (g '' section34VertexBallImage srcBd f₁ w)
    rw [hrS]
    exact hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨p, hp, hpLb⟩ := hE.exists_isPLHomeomorphOn_invFunOn hu hEP
  have hLS : L ⊆ S := image_mono hEV
  have hLbL : Lb ⊆ L := image_mono hE.boundary_subset
  have hLbmap : MapsTo u Lb (section34SplitDiskImage srcBd f₁ e₀) := by
    rintro x ⟨y, hy, rfl⟩
    rwa [hright (hLbP hy)]
  have hends' : ({η 0, η 1} : Set E3) ⊆ Lb := by
    intro x hx
    have hxB : x ∈ B := (pair_subset hη0 (hη.bijOn.mapsTo (by norm_num))) hx
    exact ⟨u x, hends hx, hleft (hBP hxB)⟩
  have hBL : B ∩ L = {η 0, η 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, y, hy, hyx⟩
      apply hmeet.subset
      refine ⟨hxB, mem_iUnion.mpr ⟨e₀, ?_⟩⟩
      rw [← hyx, hright (hEP hy)]
      exact hy
    · intro x hx
      exact ⟨(pair_subset hη0 (hη.bijOn.mapsTo (by norm_num))) hx, hLbL (hends' hx)⟩
  let F : {e : Section34EdgeIndex 𝒦 𝒦' // e ≠ e₀} → Set E3 :=
    fun e => u ⁻¹' section34SplitDiskImage src f₁ e.1
  have hconnect : ∀ R : Set E3, IsPLSphere 1 (B ∪ R) → R ⊆ Lb →
      ∃ Y : Set E3, IsConnected Y ∧ Y ⊆ S \ (B ∪ R) ∧ ∀ e, F e ∩ S ⊆ Y := by
    intro R hJ hRLb
    have hRP : R ⊆ P := hRLb.trans (hLbL.trans (hLS.trans hSP))
    have hJP : B ∪ R ⊆ P := union_subset hBP hRP
    have hJV : u '' (B ∪ R) ⊆ section34VertexBallImage src f₁ w :=
      image_subset_iff.mpr fun x hx => hV.boundary_subset
        (hSmap ((union_subset hBS' (hRLb.trans (hLbL.trans hLS))) hx))
    have hRγ : R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e₀ :=
      fun x hx => hLbmap (hRLb hx)
    have hJN : u '' (B ∪ R) ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v) := by
      apply image_subset_iff.mpr
      exact union_subset hBN fun x hx =>
        hcut.splitDiskBoundary_subset_frontier_vertexBallImages hf₁ e₀ (hRγ hx)
    have hJF : u '' (B ∪ R) ⊆ fblBd s ∪ section34SplitDiskImage srcBd f₁ e₀ :=
      image_subset_iff.mpr (union_subset (fun x hx => Or.inl (hBF hx))
        (fun x hx => Or.inr (hRγ hx)))
    have hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', e ≠ e₀ →
        Disjoint (u '' (B ∪ R)) (section34SplitDiskImage src f₁ e) := by
      intro e he
      apply disjoint_left.mpr
      rintro y ⟨x, hx, rfl⟩ hxE
      have hxE₀ : u x ∈ section34SplitDiskImage src f₁ e₀ := by
        rcases hx with hxB | hxR
        · exact hE.boundary_subset (hends (hmeet.subset
            ⟨hxB, mem_iUnion.mpr ⟨e, hxE⟩⟩))
        · exact hE.boundary_subset (hRγ hxR)
      exact disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁.injOn he) hxE hxE₀
    obtain ⟨Y, hY, hYS, hEY⟩ := exists_section34_connected_set_containing_other_split_disks
      hcut hf₁ hinv s w e₀ hwe₀ he₀s hJF hJN hJE
      (hfill (u '' (B ∪ R))
        ⟨B ∪ R, u, hJ, hu.mono_of_polyhedron hJ.isPolyhedron hJP, rfl⟩ hJV hJN)
    have hYP : Y ⊆ u '' P := hYS.trans (sdiff_subset.trans (hV.boundary_subset.trans hVP))
    have hg : ContinuousOn g Y := fun y hy =>
      (hu.isPLOn_inverse hleft y (hYP hy)).continuousWithinAt.mono hYP
    refine ⟨g '' Y, hY.image g hg, ?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨⟨y, (hYS hy).1, rfl⟩, ?_⟩
      intro hyJ
      exact (hYS hy).2 ⟨g y, hyJ, hright (hYP hy)⟩
    · intro e x hx
      have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hx.1
        (hV.boundary_subset (hSmap hx.2))
      exact ⟨u x, hEY e.1 hwe e.2 hx.1, hleft (hSP hx.2)⟩
  obtain ⟨R, D, q, δ, hδ, hδ0, hδ1, hRLb, hBR, hq, hqB, hDS, hDL, hDF⟩ :=
    hS.exists_return_disk_avoiding_family hp hpLb.symm hLS hη hBS' hends' hBL F hconnect
  have hDP : D ⊆ P := hDS.trans hSP
  have hRγ : R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e₀ := fun x hx => hLbmap (hRLb hx)
  have hDE : D ∩ u ⁻¹' section34SplitDiskImage src f₁ e₀ = R := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxE⟩
      exact hDL.subset ⟨hxD, u x, hxE, hleft (hDP hxD)⟩
    · intro x hx
      have hxD := (hDL.symm.subset hx).1
      exact ⟨hxD, hE.boundary_subset (hRγ hx)⟩
  have hother : ∀ e : Section34EdgeIndex 𝒦 𝒦', e ≠ e₀ →
      Disjoint D (u ⁻¹' section34SplitDiskImage src f₁ e) := fun e he => hDF ⟨e, he⟩
  refine ⟨R, D, q, δ, hδ, hδ0, hδ1, hRγ, hBR, hq, hqB, hDP, ?_, hDE, hother⟩
  intro x hxD
  have hxS := hSmap (hDS hxD)
  refine ⟨hxS, ?_⟩
  by_cases hxE : u x ∈ section34SplitDiskImage src f₁ e₀
  · exact hcut.splitDiskBoundary_subset_frontier_vertexBallImages hf₁ e₀
      (hRγ (hDE.subset ⟨hxD, hxE⟩))
  · apply (hcut.frontier_eventually_eq_vertexBallBoundary hf₁ w
      (hV.boundary_subset hxS) ?_).self_of_nhds.mpr hxS
    intro e hxe
    by_cases he : e = e₀
    · exact hxE (he ▸ hxe)
    · exact disjoint_left.mp (hother e he) hxD hxe

end DifferentialGeometry.Topology.PiecewiseLinear
