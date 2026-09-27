/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceCutOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraClaws

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

def section34ClawBall (V : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (x y x' y' : Ea) : Set M₂ :=
  ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : ∃ p, w.1 = {p} ∧ (p ∈ segment ℝ x y ∨
    (p ∈ segment ℝ x x' ∧ p ≠ x') ∨ (p ∈ segment ℝ y y' ∧ p ≠ y'))), V w

theorem Section34CutFrame.splitDiskImage_subset_frontier
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {e : Section34EdgeIndex 𝒦 𝒦'} {w : Section34VertexIndex 𝒦 𝒦'}
    (hwe : w.1 ⊆ e.1) :
    section34SplitDiskImage src f₁ e ⊆
      frontier (section34VertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, hcell, hbd, -⟩ := id hcut
  have hG := hf₁.mono_of_isPLCellOn (hcell (.vertexBall w))
    (subset_iUnion (fun v => src (.vertexBall v)) w)
  have hsub : src (.splitDisk e) ⊆ src (.vertexBall w) :=
    hcut.src_subset_of_cutStep (show Section34CutStep (.splitDisk e) (.vertexBall w) from hwe)
  have hbdv : src (.splitDisk e) ⊆ srcBd (.vertexBall w) := by
    intro x hx
    rw [hbd (.vertexBall w)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hx⟩
  change f₁ '' src (.splitDisk e) ⊆ frontier (f₁ '' src (.vertexBall w))
  rw [← ((hcell (.vertexBall w)).image_boundary_interior hG).1]
  exact image_mono hbdv

theorem Section34CutFrame.vertexBallImage_inter_eq_splitDiskImage
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {e : Section34EdgeIndex 𝒦 𝒦'} {w w' : Section34VertexIndex 𝒦 𝒦'}
    (hww : w ≠ w') (hw : w.1 ⊆ e.1) (hw' : w'.1 ⊆ e.1) :
    section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ w' =
      section34SplitDiskImage src f₁ e := by
  obtain ⟨a, b, -, hab, hE⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  rcases eq_or_eq_of_section34VertexIndex_subset e hab hw with rfl | rfl <;>
    rcases eq_or_eq_of_section34VertexIndex_subset e hab hw' with rfl | rfl
  · exact absurd rfl hww
  · exact hE.symm
  · rw [inter_comm]
    exact hE.symm
  · exact absurd rfl hww

theorem Section34CutFrame.disjoint_vertexBallImage_of_forall_not_subset
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww : w ≠ w')
    (hnot : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → w'.1 ⊆ e.1 → False) :
    Disjoint (section34VertexBallImage src f₁ w)
      (section34VertexBallImage src f₁ w') := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hww hx hx'
  exact hnot e (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hx)
    (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hx')

open Classical in
theorem Section34CutFrame.path_attach_meet
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {n k : ℕ} (hk : k ≤ n) {w : ℕ → Section34VertexIndex 𝒦 𝒦'}
    {e : ℕ → Section34EdgeIndex 𝒦 𝒦'}
    (he : ∀ i < n, (e i).1 = (w i).1 ∪ (w (i + 1)).1)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, w i = w j → i = j)
    (hfar : ∀ i ≤ n, ∀ j ≤ n, i + 1 < j → ∀ e' : Section34EdgeIndex 𝒦 𝒦',
      (w i).1 ⊆ e'.1 → (w j).1 ⊆ e'.1 → False)
    {B : Set M₂} (hB : ∀ z ∈ B ∩ section34VertexBallImage src f₁ (w 1),
      z ∈ section34VertexBallImage src f₁ (w 0))
    (hB' : ∀ j, 0 < j → j < k →
      Disjoint B (section34VertexBallImage src f₁ (w (j + 1))))
    (hB0 : section34VertexBallImage src f₁ (w 0) ⊆ B) {j : ℕ} (hj : j < k) :
    (B ∪ ⋃ m ∈ Finset.range j, section34VertexBallImage src f₁ (w (m + 1))) ∩
      section34VertexBallImage src f₁ (w (j + 1)) =
        section34SplitDiskImage src f₁ (e j) := by
  have hcons : ∀ i < n, section34VertexBallImage src f₁ (w i) ∩
      section34VertexBallImage src f₁ (w (i + 1)) =
        section34SplitDiskImage src f₁ (e i) := by
    intro i hi
    refine hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ (fun h => ?_) ?_ ?_
    · exact absurd (hinj i hi.le (i + 1) hi h) (by omega)
    · rw [he i hi]
      exact Finset.subset_union_left
    · rw [he i hi]
      exact Finset.subset_union_right
  have hdisj : ∀ i ≤ n, ∀ l ≤ n, i + 1 < l → Disjoint
      (section34VertexBallImage src f₁ (w i))
      (section34VertexBallImage src f₁ (w l)) :=
    fun i hi l hl hil => hcut.disjoint_vertexBallImage_of_forall_not_subset hf₁
      (fun h => absurd (hinj i hi l hl h) (by omega)) (hfar i hi l hl hil)
  apply Subset.antisymm
  · rintro z ⟨hz | hz, hzj⟩
    · by_cases hj0 : j = 0
      · subst hj0
        rw [← hcons 0 (by omega)]
        exact ⟨hB z ⟨hz, hzj⟩, hzj⟩
      · exact absurd hzj (Set.disjoint_left.mp (hB' j (Nat.pos_of_ne_zero hj0) hj) hz)
    · obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
      have hm' : m < j := Finset.mem_range.mp hm
      by_cases hmj : m + 1 = j
      · rw [← hcons j (by omega)]
        rw [hmj] at hzm
        exact ⟨hzm, hzj⟩
      · exact absurd hzj (Set.disjoint_left.mp (hdisj (m + 1) (by omega) (j + 1) (by omega)
          (by omega)) hzm)
  · rw [← hcons j (by omega)]
    rintro z ⟨hz, hzj⟩
    refine ⟨?_, hzj⟩
    by_cases hj0 : j = 0
    · subst hj0
      exact mem_union_left _ (hB0 hz)
    · refine mem_union_right _ (mem_iUnion₂.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
      exact hz

theorem Section34CutFrame.disjoint_interior_vertexBallImage
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {w u : Section34VertexIndex 𝒦 𝒦'} (hwu : w ≠ u) :
    Disjoint (interior (section34VertexBallImage src f₁ w))
      (section34VertexBallImage src f₁ u) := by
  refine Set.disjoint_left.mpr fun z hz hzu => ?_
  obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hwu (interior_subset hz) hzu
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze (interior_subset hz)
  exact (hcut.splitDiskImage_subset_frontier hf₁ hwe hze).2 hz

end DifferentialGeometry.Topology.PiecewiseLinear
