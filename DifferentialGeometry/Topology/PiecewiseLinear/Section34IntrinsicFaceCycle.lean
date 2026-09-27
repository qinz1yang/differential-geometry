/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceVertexCycle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceVertexAdjacency
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.splitDiskImage_subset_faceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦')
    (he : Section34Incident e.1 s.1) :
    section34SplitDiskImage src f₁ e ⊆
      section34FaceTorus (section34VertexBallImage src f₁) s := by
  obtain ⟨a, b, -, heab, hD⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have ha : Section34Incident a.1 s.1 := by
    apply Subset.trans ?_ he
    rw [heab]
    exact subset_union_left
  intro x hx
  exact mem_iUnion₂.mpr ⟨⟨(s, a), ha⟩, rfl, (hD.subset hx).1⟩

theorem exists_cycle_order_intrinsic_face_vertex_balls
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P : Set E3} {u : E3 → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s) :
    ∃ (n : ℕ) (v : Fin (n + 3) → Section34VertexIndex 𝒦 𝒦'),
      Function.Injective v ∧ (∀ w, Section34Incident w.1 s.1 ↔ ∃ i, v i = w) ∧
      let B := fun i => Function.invFunOn u P '' section34VertexBallImage src f₁ (v i)
      (∀ i, IsPLBall 3 (B i)) ∧
      (∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j →
        ∃ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 ∧
          Function.invFunOn u P '' section34SplitDiskImage src f₁ e = B i ∩ B j) ∧
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
        ∃ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j ∧
          Function.invFunOn u P '' section34SplitDiskImage src f₁ e = B i ∩ B j) ∧
      (∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
        Disjoint (B i) (B j)) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → B i ∩ B j ∩ B k = ∅) ∧
      (⋃ i, B i) = P := by
  classical
  obtain ⟨-, hsubdiv, hmap, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hends, -, -⟩ := id hcut
  choose a b hab he hsplit using hends
  let ends := fun e => (a e, b e)
  have hends' : ∀ e, (e.1 : Set Ea) =
      (((ends e).1).1 : Set Ea) ∪ (((ends e).2).1 : Set Ea) := he
  obtain ⟨n, v, hv, hvinc, hadj⟩ :=
    exists_section34Face_vertex_cycle hsubdiv hmap ends hends' s
  let g := Function.invFunOn u P
  let B := fun i => g '' section34VertexBallImage src f₁ (v i)
  have hVT (w : Section34VertexIndex 𝒦 𝒦') (hw : Section34Incident w.1 s.1) :
      section34VertexBallImage src f₁ w ⊆ u '' P := by
    rw [hUP]
    exact fun x hx => mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hx⟩
  have hVi (i : Fin (n + 3)) : section34VertexBallImage src f₁ (v i) ⊆ u '' P :=
    hVT (v i) ((hvinc _).mpr ⟨i, rfl⟩)
  have hginj : InjOn g (u '' P) := Function.invFunOn_injOn_image u P
  have hN (w : Section34VertexIndex 𝒦 𝒦') :
      src (.vertexBall w) ⊆ section34CutNeighborhood src :=
    subset_iUnion (fun w => src (.vertexBall w)) w
  have hmeet (i j : Fin (n + 3)) : B i ∩ B j =
      g '' (f₁ '' (src (.vertexBall (v i)) ∩ src (.vertexBall (v j)))) := by
    rw [hf₁.injOn.image_inter (hN _) (hN _)]
    exact (hginj.image_inter (hVi i) (hVi j)).symm
  have hpair (e : Section34EdgeIndex 𝒦 𝒦') (i j : Fin (n + 3))
      (hij : (v i = (ends e).1 ∧ v j = (ends e).2) ∨
        (v i = (ends e).2 ∧ v j = (ends e).1)) :
      g '' section34SplitDiskImage src f₁ e = B i ∩ B j := by
    rw [hmeet]
    change g '' (f₁ '' src (.splitDisk e)) = _
    congr 2
    rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [hi, hj]
      exact hsplit e
    · rw [hi, hj, inter_comm]
      exact hsplit e
  have heinc (e : Section34EdgeIndex 𝒦 𝒦') (i j : Fin (n + 3))
      (hij : (v i = (ends e).1 ∧ v j = (ends e).2) ∨
        (v i = (ends e).2 ∧ v j = (ends e).1)) : Section34Incident e.1 s.1 := by
    change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [hends' e]
    rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [← hi, ← hj]
      exact union_subset ((hvinc _).mpr ⟨i, rfl⟩) ((hvinc _).mpr ⟨j, rfl⟩)
    · rw [← hi, ← hj]
      exact union_subset ((hvinc _).mpr ⟨j, rfl⟩) ((hvinc _).mpr ⟨i, rfl⟩)
  refine ⟨n, v, hv, hvinc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hcell := hcut.isPLCellOn_vertexBallImage hf₁ (v i)
    obtain ⟨q, hq, -⟩ := hcell.exists_isPLHomeomorphOn_invFunOn hu (hVi i)
    exact ⟨q, hq⟩
  · intro i j hij
    obtain ⟨e, heij⟩ := (hadj i j hij.ne).mp hij
    exact ⟨e, heinc e i j heij, hpair e i j heij⟩
  · intro e hes
    have ha : Section34Incident (a e).1 s.1 := by
      apply Subset.trans ?_ hes
      rw [he e]
      exact subset_union_left
    have hb : Section34Incident (b e).1 s.1 := by
      apply Subset.trans ?_ hes
      rw [he e]
      exact subset_union_right
    obtain ⟨i, hi⟩ := (hvinc _).mp ha
    obtain ⟨j, hj⟩ := (hvinc _).mp hb
    have hij : i ≠ j := fun h => hab e (hi.symm.trans ((congrArg v h).trans hj))
    have hp : (v i = (ends e).1 ∧ v j = (ends e).2) ∨
        (v i = (ends e).2 ∧ v j = (ends e).1) := Or.inl ⟨hi, hj⟩
    exact ⟨i, j, (hadj i j hij).mpr ⟨e, hp⟩, hpair e i j hp⟩
  · intro i j hij hnot
    apply disjoint_left.mpr
    intro x hxi hxj
    have hx : x ∈ g '' (f₁ ''
        (src (.vertexBall (v i)) ∩ src (.vertexBall (v j)))) :=
      (hmeet i j).subset ⟨hxi, hxj⟩
    obtain ⟨y, ⟨z, hz, -⟩, -⟩ := hx
    obtain ⟨e, -, heij⟩ := exists_section34Edge_of_vertex_inter_nonempty hcut ends hends'
      (fun heq => hij (hv heq)) ⟨z, hz⟩
    exact hnot ((hadj i j hij).mpr ⟨e, heij⟩)
  · intro i j k hij hik hjk
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxi, hxj⟩, hxk⟩
    obtain ⟨y, hiy, hyx⟩ := hxi
    obtain ⟨z, hjz, hzx⟩ := hxj
    obtain ⟨w, hkw, hwx⟩ := hxk
    have hzy : z = y := hginj (hVi j hjz) (hVi i hiy) (hzx.trans hyx.symm)
    have hwy : w = y := hginj (hVi k hkw) (hVi i hiy) (hwx.trans hyx.symm)
    subst z
    subst w
    obtain ⟨e, hye⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn (hv.ne hij) hiy hjz
    obtain ⟨w, w', -, hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
    have hcases (l : Fin (n + 3)) (hyl : y ∈ section34VertexBallImage src f₁ (v l)) :
        v l = w ∨ v l = w' := eq_or_eq_of_section34VertexIndex_subset e hew
      (hcut.subset_of_mem_splitDiskImage hf₁.injOn hye hyl)
    rcases hcases i hiy with hi | hi <;> rcases hcases j hjz with hj | hj <;>
      rcases hcases k hkw with hk | hk
    all_goals first
      | exact hij (hv (hi.trans hj.symm))
      | exact hik (hv (hi.trans hk.symm))
      | exact hjk (hv (hj.trans hk.symm))
  · have hcover : (⋃ i, section34VertexBallImage src f₁ (v i)) = u '' P := by
      rw [hUP]
      ext x
      constructor
      · rintro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion₂.mpr ⟨⟨(s, v i), (hvinc _).mpr ⟨i, rfl⟩⟩, rfl, hi⟩
      · rintro hx
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
        have hia : Section34Incident a.1.2.1 s.1 := ha ▸ a.2
        obtain ⟨i, hi⟩ := (hvinc _).mp hia
        exact mem_iUnion.mpr ⟨i, hi.symm ▸ hxa⟩
    change (⋃ i, g '' section34VertexBallImage src f₁ (v i)) = P
    rw [← image_iUnion, hcover]
    exact hu.injOn.invFunOn_image (Subset.refl P)

end DifferentialGeometry.Topology.PiecewiseLinear
