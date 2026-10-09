/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleDisk
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellBridgeDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskCenter
import DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_centered_graphDualCell_caps_triangle
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) (s : Section34CompactSimplexIndex K 3)
    (v : Fin 3 → E3) (hv : ∀ i, v i ∈ s.1) (hinj : Function.Injective v) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let C := fun i => (graphDualCell M L (v i)).space
    ∃ r : Fin 3 → (Fin 3 → ℝ) → E3, ∀ i,
      IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C i ∩ C (i + 1)) ∧
      r i (stdCenter 1) = ({v i, v (i + 1)} : Finset E3).centroid ℝ id ∧
      IsBridgeDisk (C i) (section34CompactSimplexRim s.1 ∩ C i)
        (convexHull ℝ (s.1 : Set E3) ∩ C i)
        (r (i + 2) (stdCenter 1)) (r i (stdCenter 1)) := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  let C := fun i => (graphDualCell M L (v i)).space
  have hLK : L.faces ⊆ K.faces := restrict_faces_subset K _
  have hLM : L.faces ⊆ M.faces := hLK.trans hKM
  have hdim : ∀ e ∈ L.faces, e.card ≤ 2 :=
    fun _ he => card_le_two_of_mem_restrict_section34CompactGraphSkeleton he
  have hpair (i j : Fin 3) : ({v i, v j} : Finset E3) ⊆ s.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv i
    · exact hv j
  have heK (i j : Fin 3) : ({v i, v j} : Finset E3) ∈ K.faces :=
    K.down_closed s.2.1 (hpair i j) (Finset.insert_nonempty _ _)
  have heL (i j : Fin 3) (hij : i ≠ j) : ({v i, v j} : Finset E3) ∈ L.faces := by
    refine ⟨heK i j, convexHull_subset_section34CompactGraphSkeleton (heK i j) ?_⟩
    rw [Finset.card_pair (fun h => hij (hinj h))]
  have hnext (i : Fin 3) : i ≠ i + 1 := by decide +revert
  have hprev (i : Fin 3) : i + 2 ≠ i := by decide +revert
  have hprevnext (i : Fin 3) : i + 2 ≠ i + 1 := by decide +revert
  have hcyc (i : Fin 3) : (i + 2) + 1 = i := by decide +revert
  have ht := isTube_graphDualCell (Set.toFinite M.faces) hM hLM hdim
    ⟨{v 0, v 1}, heL 0 1 (by decide), Finset.card_pair (fun h =>
      (by decide : (0 : Fin 3) ≠ 1) (hinj h))⟩
    (fun w hw => hKint (K.convexHull_subset_space (hLK hw) (by simp)))
  have hvL (i : Fin 3) : v i ∈ L.vertices := L.down_closed (heL i (i + 1) (hnext i))
    (by simp) (Finset.singleton_nonempty _)
  have hcoords (i : Fin 3) : ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C i ∩ C (i + 1)) ∧
      r (stdCenter 1) = ({v i, v (i + 1)} : Finset E3).centroid ℝ id := by
    obtain ⟨r, hr, -, hrc⟩ := ht.exists_centered_splitDisk_parametrization
      (heL i (i + 1) (hnext i)) (Finset.card_pair (fun h => hnext i (hinj h)))
    refine ⟨r, ?_, hrc⟩
    rw [ht.interEdge (hvL i) (hvL (i + 1)) (fun h => hnext i (hinj h))
      (heL i (i + 1) (hnext i))]
    exact hr
  choose r hr hrc using hcoords
  obtain ⟨F, hFfin, hFK, hF, hFspace, hFrim, hFL⟩ :=
    exists_triangle_subcomplex_with_rim K s
  let _ : Finite F.faces := hFfin.to_subtype
  have hF_eq : F = simplexComplex s.1 (K.indep s.2.1) :=
    eq_of_faces_subset_of_space_eq F _ K hFK
      (fun _ he => K.down_closed s.2.1 he.2 he.1)
      (hFspace.trans (simplexComplex_space s.1 (K.indep s.2.1)
        (K.nonempty_of_mem_faces s.2.1)).symm)
  have heF (i j : Fin 3) (hij : i ≠ j) :
      ({v i, v j} : Finset E3) ∈ (boundaryComplex 2 F).faces := by
    rw [hF_eq, boundaryComplex_simplexComplex (K.indep s.2.1) s.2.2]
    refine ⟨hpair i j, Finset.insert_nonempty _ _, ?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [Finset.card_pair (fun h => hij (hinj h)), s.2.2] at hc
    omega
  have hFint : F.space ⊆ interior M.space := by
    rw [hFspace]
    exact (K.convexHull_subset_space s.2.1).trans hKint
  refine ⟨r, fun i => ⟨hr i, hrc i, ?_⟩⟩
  have hb := isBridgeDisk_graphDualCell M L F hM hLM hdim (hFK.trans hKM) hF hFint hFL
    (fun h => hprev i (hinj h)) (fun h => hnext i (hinj h))
    (fun h => hprevnext i (hinj h)) (heF (i + 2) i (hprev i))
    (heF i (i + 1) (hnext i))
  rw [hFrim, hFspace] at hb
  rw [hrc (i + 2), hrc i, hcyc]
  exact hb

theorem section34CompactSimplexRim_subset_iUnion_graphDualCells
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (s : Section34CompactSimplexIndex K 3) :
    section34CompactSimplexRim s.1 ⊆ ⋃ v ∈ (s.1 : Set E3),
      (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  obtain ⟨F, hFfin, hFK, -, hFspace, hFrim, hFL⟩ :=
    exists_triangle_subcomplex_with_rim K s
  let _ : Finite F.faces := hFfin.to_subtype
  let H := boundaryComplex 2 F
  let _ : Finite H.faces := (boundaryComplex_faces_finite 2 F).to_subtype
  have hHF : H.faces ⊆ F.faces := boundaryComplex_faces_subset 2 F
  intro x hx
  have hxH : x ∈ H.space := hFrim.symm ▸ hx
  rw [← iUnion_dualCell_singleton_space H] at hxH
  obtain ⟨v, hxv⟩ := mem_iUnion.mp hxH
  have hvK := hFK (hHF v.property)
  have hvF : v.val ∈ F.space := F.subset_space (hHF v.property) (by simp)
  have hvs : v.val ∈ s.1 := mem_of_mem_convexHull_of_singleton_mem K hvK s.2.1
    (hFspace ▸ hvF)
  have htrace := graphDualCell_inter_subcomplex_eq_dualCell M H L
    (hHF.trans (hFK.trans hKM)) hLM hFL v.property
  exact mem_iUnion₂.mpr ⟨v.val, hvs, (htrace.symm ▸ hxv).1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
