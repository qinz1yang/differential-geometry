/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section FaceArc

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] {M₁ : Type u}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}

theorem section34_faceDisk_inter_interior_cutNeighborhood_eq_empty
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3) :
    src (Section34Label.faceDisk s) ∩ interior (section34CutNeighborhood src) = ∅ := by
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, harc, -, -, -, hfar, -⟩ := id hcut
  have hsubU : ∀ l, src l ⊆ U := fun l => (subset_iUnion src l).trans hcover.subset
  have hface : (section34Face src (Section34Label.faceDisk s)).Finite :=
    finite_face_of_locallyFinite U src (Section34Label.faceDisk s)
      (fun l => (hcell l).nonempty) (hcell _).isCompact hsubU hLF
  have hAfin : {a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s}.Finite := by
    refine Set.Finite.of_finite_image (f := fun a : Section34ArcIndex 𝒦 𝒦' =>
      (Section34Label.faceArc a : Section34CutLabelOf 𝒦 𝒦')) (hface.subset ?_)
      (fun a _ b _ hab => by simpa using hab)
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a.1.1 = s := ha
    change src (Section34Label.faceArc a) ⊆ src (Section34Label.faceDisk s)
    rw [harc a, ha']
    exact inter_subset_right
  have := hAfin.to_subtype
  have hS : IsPLCellOn 2 (src (Section34Label.faceDisk s))
      (srcBd (Section34Label.faceDisk s)) := hcell (Section34Label.faceDisk s)
  have hC : ∀ a : ↥{a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s},
      ∃ B : Set M₁, IsPLCellOn 1 (src (Section34Label.faceArc a.1)) B :=
    fun a => ⟨srcBd (Section34Label.faceArc a.1), hcell (Section34Label.faceArc a.1)⟩
  have hCS : ∀ a : ↥{a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s},
      src (Section34Label.faceArc a.1) ⊆ src (Section34Label.faceDisk s) := by
    intro a
    have ha' : a.1.1.1 = s := a.2
    rw [harc a.1, ha']
    exact inter_subset_right
  have hcov : interior (section34CutNeighborhood src) ∩ src (Section34Label.faceDisk s) ⊆
      ⋃ a : ↥{a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s},
        src (Section34Label.faceArc a.1) := by
    intro x hx
    have hxN : x ∈ ⋃ w : Section34VertexIndex 𝒦 𝒦', src (Section34Label.vertexBall w) :=
      interior_subset hx.1
    obtain ⟨w, hw⟩ := mem_iUnion.mp hxN
    have hinc : Section34Incident w.1 s.1 := by
      by_contra hcon
      have hx' : x ∈ src (Section34Label.faceDisk s) ∩ src (Section34Label.vertexBall w) :=
        ⟨hx.2, hw⟩
      rw [hfar s w hcon] at hx'
      exact hx'
    have hmem : (⟨(s, w), hinc⟩ : Section34ArcIndex 𝒦 𝒦') ∈
        {a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s} := rfl
    have hxarc : x ∈ src (Section34Label.faceArc (⟨(s, w), hinc⟩ :
        Section34ArcIndex 𝒦 𝒦')) := by
      rw [harc ⟨(s, w), hinc⟩]
      exact ⟨hw, hx.2⟩
    exact mem_iUnion.mpr ⟨⟨⟨(s, w), hinc⟩, hmem⟩, hxarc⟩
  exact (inter_comm _ _).trans
    (hS.inter_eq_empty_of_subset_iUnion
      (n := fun _ : ↥{a : Section34ArcIndex 𝒦 𝒦' | a.1.1 = s} => 1)
      (C := fun a => src (Section34Label.faceArc a.1)) hC (fun _ => le_rfl) hCS
      isOpen_interior hcov)

theorem section34_faceDisk_disjoint_graphSkeleton
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hnbhd : section34CutNeighborhood src ∈ nhdsSet (graphSkeletonSpace 𝒦))
    (s : Section34SimplexIndex 𝒦 3) :
    Disjoint (src (Section34Label.faceDisk s)) (graphSkeletonSpace 𝒦) := by
  have hint : graphSkeletonSpace 𝒦 ⊆ interior (section34CutNeighborhood src) :=
    subset_interior_iff_mem_nhdsSet.mpr hnbhd
  refine Set.disjoint_left.mpr fun x hxd hxΓ => ?_
  have hx : x ∈ src (Section34Label.faceDisk s) ∩ interior (section34CutNeighborhood src) :=
    ⟨hxd, hint hxΓ⟩
  rw [section34_faceDisk_inter_interior_cutNeighborhood_eq_empty hcut s] at hx
  exact hx

theorem section34_faceDisk_disjoint_of_ne
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hnbhd : section34CutNeighborhood src ∈ nhdsSet (graphSkeletonSpace 𝒦))
    {s s' : Section34SimplexIndex 𝒦 3} (hss : s ≠ s') :
    Disjoint (src (Section34Label.faceDisk s)) (src (Section34Label.faceDisk s')) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbody, -⟩ := id hcut
  refine Set.disjoint_left.mpr fun x hxs hxs' => ?_
  obtain ⟨p, hp, hpx⟩ : ∃ p ∈ convexHull ℝ (s.1 : Set Ea), 𝒦.map p = x := hbody s hxs
  obtain ⟨q, hq, hqx⟩ : ∃ q ∈ convexHull ℝ (s'.1 : Set Ea), 𝒦.map q = x := hbody s' hxs'
  have hpq : p = q :=
    𝒦.bijOn.injOn (Geometry.SimplicialComplex.convexHull_subset_space s.2.1 hp)
      (Geometry.SimplicialComplex.convexHull_subset_space s'.2.1 hq) (by rw [hpx, hqx])
  have hp' : p ∈ convexHull ℝ (s'.1 : Set Ea) := by rw [hpq]; exact hq
  have hpu : p ∈ convexHull ℝ ((s.1 ∩ s'.1 : Finset Ea) : Set Ea) := by
    rw [Finset.coe_inter]
    exact 𝒦.complex.inter_subset_convexHull s.2.1 s'.2.1 ⟨hp, hp'⟩
  have hune : (s.1 ∩ s'.1).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p, hpu⟩)
  have huface : s.1 ∩ s'.1 ∈ 𝒦.complex.faces :=
    Geometry.SimplicialComplex.down_closed s.2.1 Finset.inter_subset_left hune
  have hproper : s.1 ∩ s'.1 ≠ s.1 := by
    intro hcon
    refine hss (Subtype.ext ?_)
    have h1 : s.1 ⊆ s'.1 := by
      rw [← hcon]
      exact Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le h1 (le_of_eq (by rw [s.2.2, s'.2.2]))
  have hcard : (s.1 ∩ s'.1).card ≤ 2 := by
    have hlt : (s.1 ∩ s'.1).card < s.1.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hproper⟩)
    rw [s.2.2] at hlt
    omega
  have hxbody : x ∈ simplexBody 𝒦 (s.1 ∩ s'.1) := by
    have hmem : 𝒦.map p ∈ 𝒦.map '' convexHull ℝ ((s.1 ∩ s'.1 : Finset Ea) : Set Ea) :=
      mem_image_of_mem _ hpu
    rw [hpx] at hmem
    exact hmem
  have hxΓ : x ∈ graphSkeletonSpace 𝒦 :=
    Set.mem_biUnion (t := fun t => simplexBody 𝒦 t)
      (show s.1 ∩ s'.1 ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2} from
        ⟨huface, hcard⟩) hxbody
  exact Set.disjoint_left.mp (section34_faceDisk_disjoint_graphSkeleton hcut hnbhd s) hxs hxΓ

theorem section34_faceArc_subset_faceDisk_iff
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hnbhd : section34CutNeighborhood src ∈ nhdsSet (graphSkeletonSpace 𝒦))
    (a : Section34ArcIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3) :
    src (Section34Label.faceArc a) ⊆ src (Section34Label.faceDisk s) ↔ a.1.1 = s := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, -⟩ := id hcut
  have hown : src (Section34Label.faceArc a) ⊆ src (Section34Label.faceDisk a.1.1) := by
    rw [harc a]
    exact inter_subset_right
  refine ⟨fun hsub => ?_, fun hEq => ?_⟩
  · by_contra hne
    obtain ⟨x, hx⟩ := (hcell (Section34Label.faceArc a)).nonempty
    exact Set.disjoint_left.mp (section34_faceDisk_disjoint_of_ne hcut hnbhd hne)
      (hown hx) (hsub hx)
  · rw [harc a, hEq]
    exact inter_subset_right

end FaceArc

end DifferentialGeometry.Topology.PiecewiseLinear
