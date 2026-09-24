import DifferentialGeometry.Topology.Manifold.CollarFamily

set_option autoImplicit false

noncomputable section

open Set Topology

namespace DifferentialGeometry.Topology.Collar

def twoPointCollarCore (i : Fin 2) : Unit → ℝ := fun _ => ((i : ℕ) : ℝ)

def twoPointCollarHeight (i : Fin 2) : Unit × ℝ → ℝ := fun q => ((i : ℕ) : ℝ) + q.2

theorem isOpenEmbedding_twoPointCollarHeight (i : Fin 2) :
    Topology.IsOpenEmbedding (twoPointCollarHeight i) :=
  Topology.IsOpenEmbedding.comp (Homeomorph.addLeft ((i : ℕ) : ℝ)).isOpenEmbedding
    (Homeomorph.uniqueProd Unit ℝ).isOpenEmbedding

theorem twoPointCollarHeight_apply_zero (i : Fin 2) (s : Unit) :
    twoPointCollarHeight i (s, 0) = twoPointCollarCore i s := by
  simp [twoPointCollarHeight, twoPointCollarCore]

theorem pairwise_disjoint_range_twoPointCollarCore :
    Pairwise fun i j : Fin 2 =>
      Disjoint (range (twoPointCollarCore i)) (range (twoPointCollarCore j)) := by
  intro i j hij
  rw [disjoint_left]
  intro a ha hb
  simp only [twoPointCollarCore, mem_range] at ha hb
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  exact hij (Fin.ext (Nat.cast_inj.mp (ht.trans hs.symm))).symm

theorem twoPointCollarFamily_hypotheses :
    (∀ i : Fin 2, Topology.IsOpenEmbedding (twoPointCollarHeight i)) ∧
      (∀ (i : Fin 2) (s : Unit), twoPointCollarHeight i (s, 0) = twoPointCollarCore i s) ∧
      (Pairwise fun i j : Fin 2 =>
        Disjoint (range (twoPointCollarCore i)) (range (twoPointCollarCore j))) :=
  ⟨isOpenEmbedding_twoPointCollarHeight, twoPointCollarHeight_apply_zero,
    pairwise_disjoint_range_twoPointCollarCore⟩

theorem exists_pos_disjoint_twoPointCollarImages :
    ∃ δ : ℝ, 0 < δ ∧
      Pairwise fun i j : Fin 2 =>
        Disjoint (twoPointCollarHeight i '' {q : Unit × ℝ | |q.2| < δ})
          (twoPointCollarHeight j '' {q : Unit × ℝ | |q.2| < δ}) :=
  disjointBoundaryCollarFamily (X := ℝ) (ι := Fin 2) (S := fun _ : Fin 2 => Unit)
    (e := twoPointCollarCore) (c := twoPointCollarHeight)
    isOpenEmbedding_twoPointCollarHeight twoPointCollarHeight_apply_zero
    pairwise_disjoint_range_twoPointCollarCore

theorem not_disjoint_twoPointCollarImages_two :
    ¬ Disjoint (twoPointCollarHeight 0 '' {q : Unit × ℝ | |q.2| < 2})
      (twoPointCollarHeight 1 '' {q : Unit × ℝ | |q.2| < 2}) := by
  intro h
  have hm0 : (0 : ℝ) ∈ twoPointCollarHeight 0 '' {q : Unit × ℝ | |q.2| < 2} := by
    have hq : (Unit.unit, (0 : ℝ)) ∈ {q : Unit × ℝ | |q.2| < 2} := by norm_num
    have himg := mem_image_of_mem (twoPointCollarHeight 0) hq
    rw [show twoPointCollarHeight 0 (Unit.unit, (0 : ℝ)) = 0 by
      norm_num [twoPointCollarHeight]] at himg
    exact himg
  have hm1 : (0 : ℝ) ∈ twoPointCollarHeight 1 '' {q : Unit × ℝ | |q.2| < 2} := by
    have hq : (Unit.unit, (-1 : ℝ)) ∈ {q : Unit × ℝ | |q.2| < 2} := by norm_num
    have himg := mem_image_of_mem (twoPointCollarHeight 1) hq
    rw [show twoPointCollarHeight 1 (Unit.unit, (-1 : ℝ)) = 0 by
      norm_num [twoPointCollarHeight]] at himg
    exact himg
  exact (disjoint_left.mp h hm0) hm1

end DifferentialGeometry.Topology.Collar
