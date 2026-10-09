/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem Section34CutStep.dim_succ {m l : Section34CutLabelOf 𝒦 𝒦'}
    (h : Section34CutStep m l) : section34Dim l = section34Dim m + 1 := by
  cases m <;> cases l <;> simp_all [Section34CutStep, section34Dim]

theorem Section34CutFrame.src_subset_of_cutStep
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {m l : Section34CutLabelOf 𝒦 𝒦'} (hstep : Section34CutStep m l) :
    src m ⊆ src l := by
  obtain ⟨-, -, -, -, -, -, -, -, -, harc, hmark, hpatch, hedge, -, -, -, -, -, -, -, -, -,
    hends, hfaceTet, -⟩ := hcut
  have hsplit (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦')
      (hw : w.1 ⊆ e.1) : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    obtain ⟨a, b, -, hab, he⟩ := hends e
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
    have hvw : v ∈ w.1 := hv.symm ▸ Finset.mem_singleton_self v
    have hve : v ∈ (e.1 : Set Ea) := hw hvw
    rw [hab] at hve
    have heq (w' : Section34VertexIndex 𝒦 𝒦') (hvw' : v ∈ w'.1) : w = w' := by
      apply Subtype.ext
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · rw [hv]
        exact Finset.singleton_subset_iff.mpr hvw'
      · exact le_of_eq (w'.2.2.1.trans w.2.2.1.symm)
    rcases hve.elim (fun h => Or.inl (heq a h)) (fun h => Or.inr (heq b h)) with rfl | rfl
    · rw [he]
      exact inter_subset_left
    · rw [he]
      exact inter_subset_right
  cases m <;> cases l <;> simp only [Section34CutStep] at hstep
  · rename_i e w
    exact hsplit e w hstep
  · rename_i s t
    exact hfaceTet t s hstep
  · rename_i x w
    rw [hpatch x, hstep]
    exact inter_subset_right
  · rename_i x t
    rw [hpatch x, hstep]
    exact inter_subset_left
  · rename_i a s
    rw [harc a, hstep]
    exact inter_subset_right
  · rename_i a x
    obtain ⟨hw, hst⟩ := hstep
    rw [harc a, hpatch x]
    exact fun y hy => ⟨hfaceTet x.1.1 a.1.1 hst hy.2, hw ▸ hy.1⟩
  · rename_i i e
    rw [hedge i, hstep]
    exact inter_subset_right
  · rename_i i x
    obtain ⟨ht, hw⟩ := hstep
    rw [hedge i, hpatch x]
    exact fun y hy => ⟨ht ▸ hy.1, hsplit i.1.2 x.1.2 hw hy.2⟩
  · rename_i p a
    obtain ⟨hs, hw⟩ := hstep
    rw [hmark p, harc a]
    exact fun y hy => ⟨hsplit p.1.2 a.1.2 hw hy.1, hs ▸ hy.2⟩
  · rename_i p i
    obtain ⟨he, hst⟩ := hstep
    rw [hmark p, hedge i]
    exact fun y hy => ⟨hfaceTet i.1.1 p.1.1 hst hy.2, he ▸ hy.1⟩

theorem Section34CutFrame.src_subset_of_cutLe
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {m l : Section34CutLabelOf 𝒦 𝒦'} (hml : Section34CutLe m l) : src m ⊆ src l := by
  induction hml using Relation.ReflTransGen.head_induction_on with
  | refl => exact subset_rfl
  | @head b c hab hbc ih => exact (hcut.src_subset_of_cutStep hab).trans ih

end DifferentialGeometry.Topology.PiecewiseLinear
