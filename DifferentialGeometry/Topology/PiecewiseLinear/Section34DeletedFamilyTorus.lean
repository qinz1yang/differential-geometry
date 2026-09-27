/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceVertexCycle
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [TopologicalSpace M₂] [ChartedSpace E3 M₂] {U : Set M₁}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}

theorem isCombinatorialSolidTorus_image_face_of_deleted_family
    (hsubdiv : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty →
      ∃ e : Section34EdgeIndex 𝒦 𝒦',
        (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (s : Section34SimplexIndex 𝒦 3) {c : OpenPartialHomeomorph M₂ E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hTc : section34FaceTorus Dv s ⊆ c.source) :
    IsCombinatorialSolidTorus (c '' section34FaceTorus Dv s) := by
  classical
  obtain ⟨n, v, hvi, hvcover, hvadj⟩ := exists_section34Face_vertex_cycle hsubdiv hmap ends hends s
  have hVc (i : Fin (n + 3)) : Dv (v i) ⊆ c.source := fun x hx =>
    hTc (mem_section34FaceTorus_iff.mpr ⟨v i, (hvcover _).mpr ⟨i, rfl⟩, hx⟩)
  let B := fun i : Fin (n + 3) => c '' Dv (v i)
  have hB (i : Fin (n + 3)) : IsPLBall 3 (B i) :=
    ((hDv (v i)).isPLBall_image_chart hc (hVc i)).1
  have hne (i j : Fin (n + 3)) (hij : i ≠ j) : v i ≠ v j := fun he => hij (hvi he)
  have hnext (i j : Fin (n + 3)) (hij : (SimpleGraph.cycleGraph (n + 3)).Adj i j) :
      IsPLBall 2 (B i ∩ B j) := by
    obtain ⟨e, he⟩ := (hvadj i j hij.ne).mp hij
    have hDc : Dd e ⊆ c.source := by
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [← hDmeet e, ← h₁, ← h₂]
        exact inter_subset_left.trans (hVc i)
      · rw [← hDmeet e, ← h₂, ← h₁]
        exact inter_subset_left.trans (hVc j)
    obtain ⟨q, hq, -⟩ := (hDd e).exists_isPLHomeomorphOn_image_chart hc hDc
    have hball : IsPLBall 2 (c '' Dd e) := ⟨q, hq⟩
    change IsPLBall 2 (c '' Dv (v i) ∩ c '' Dv (v j))
    rw [← c.injOn.image_inter (hVc i) (hVc j)]
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rwa [h₁, h₂, hDmeet e]
    · rw [h₁, h₂, inter_comm, hDmeet e]
      exact hball
  have hdis (i j : Fin (n + 3)) (hij : i ≠ j)
      (hnot : ¬ (SimpleGraph.cycleGraph (n + 3)).Adj i j) : Disjoint (B i) (B j) := by
    have hempty : ¬ (Dv (v i) ∩ Dv (v j)).Nonempty := fun ht =>
      hnot ((hvadj i j hij).mpr (hDadj _ _ (hne i j hij) ht))
    rw [disjoint_iff_inter_eq_empty]
    change c '' Dv (v i) ∩ c '' Dv (v j) = ∅
    rw [← c.injOn.image_inter (hVc i) (hVc j), not_nonempty_iff_eq_empty.mp hempty, image_empty]
  have htripleV (w₁ w₂ w₃ : Section34VertexIndex 𝒦 𝒦')
      (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) :
      Dv w₁ ∩ Dv w₂ ∩ Dv w₃ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hx₁, hx₂⟩, hx₃⟩
    obtain ⟨e, he⟩ := hDadj w₁ w₂ h12 ⟨x, hx₁, hx₂⟩
    obtain ⟨d, hd⟩ := hDadj w₁ w₃ h13 ⟨x, hx₁, hx₃⟩
    have hxd : x ∈ Dd d := by
      rw [← hDmeet d]
      rcases hd with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
      · exact ⟨h₁ ▸ hx₁, h₃ ▸ hx₃⟩
      · exact ⟨h₃ ▸ hx₃, h₁ ▸ hx₁⟩
    have hxe : x ∈ Dd e := by
      rw [← hDmeet e]
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁ ▸ hx₁, h₂ ▸ hx₂⟩
      · exact ⟨h₂ ▸ hx₂, h₁ ▸ hx₁⟩
    have hed : e ≠ d := by
      intro hed
      subst d
      rcases he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩ <;>
        rcases hd with ⟨hd₁, hd₃⟩ | ⟨hd₁, hd₃⟩
      · exact h23 (he₂.trans hd₃.symm)
      · exact h12 (hd₁.trans he₂.symm)
      · exact h12 (hd₁.trans he₂.symm)
      · exact h23 (he₂.trans hd₃.symm)
    exact disjoint_left.mp (hDddisj e d hed) hxe hxd
  have htriple (i j k : Fin (n + 3)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      B i ∩ B j ∩ B k = ∅ := by
    change (c '' Dv (v i) ∩ c '' Dv (v j)) ∩ c '' Dv (v k) = ∅
    rw [← c.injOn.image_inter (hVc i) (hVc j),
      ← c.injOn.image_inter (inter_subset_left.trans (hVc i)) (hVc k),
      htripleV _ _ _ (hne i j hij) (hne i k hik) (hne j k hjk), image_empty]
  have hunion : (⋃ i, B i) = c '' section34FaceTorus Dv s := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hz
      exact ⟨y, mem_section34FaceTorus_iff.mpr ⟨v i, (hvcover _).mpr ⟨i, rfl⟩, hy⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, hw, hyw⟩ := mem_section34FaceTorus_iff.mp hy
      obtain ⟨i, rfl⟩ := (hvcover w).mp hw
      exact mem_iUnion.mpr ⟨i, y, hyw, rfl⟩
  rw [← hunion]
  exact isCombinatorialSolidTorus_iUnion_of_cycle B hB hnext hdis htriple

end DifferentialGeometry.Topology.PiecewiseLinear
