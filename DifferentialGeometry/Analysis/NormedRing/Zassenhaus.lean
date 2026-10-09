import DifferentialGeometry.Analysis.NormedRing.Units
import DifferentialGeometry.Topology.Algebra.Group.Nilpotent
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.Constructions

namespace Units

open scoped commutatorElement

variable {A : Type*} [SeminormedRing A]

private theorem norm_inv_sub_one_le_twice (u : Aˣ) (hu : ‖(↑u : A) - 1‖ ≤ 1 / 2) :
    ‖(↑u⁻¹ : A) - 1‖ ≤ 2 * ‖(↑u : A) - 1‖ := by
  have hu1 : ‖(↑u : A) - 1‖ < 1 := hu.trans_lt (by norm_num)
  calc
    ‖(↑u⁻¹ : A) - 1‖ = ‖((↑u : A) - 1) * (↑u⁻¹ : A)‖ := by
      rw [sub_mul, Units.mul_inv, one_mul, norm_sub_rev]
    _ ≤ ‖(↑u : A) - 1‖ / (1 - ‖(↑u : A) - 1‖) :=
      norm_mul_inv_le_of_norm_sub_one_lt_one u _ hu1
    _ ≤ 2 * ‖(↑u : A) - 1‖ := by
      apply (div_le_iff₀ (sub_pos.mpr hu1)).2
      calc
        ‖(↑u : A) - 1‖ = 2 * ‖(↑u : A) - 1‖ * (1 - (1 / 2 : ℝ)) := by ring
        _ ≤ 2 * ‖(↑u : A) - 1‖ * (1 - ‖(↑u : A) - 1‖) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left hu 1)
            (mul_nonneg (by norm_num) (norm_nonneg _))

private theorem exists_pos_norm_sub_one_lt_imp_eq_one (Γ : Subgroup Aˣ) [DiscreteTopology Γ] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : Γ, ‖((g : Aˣ) : A) - 1‖ < δ → g = 1 := by
  let e : Γ → A × Aᵐᵒᵖ := fun g => Units.embedProduct A (g : Aˣ)
  have he : Topology.IsEmbedding e :=
    Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  obtain ⟨V, hV, hpre⟩ := he.isInducing.isOpen_iff.mp (isOpen_discrete ({1} : Set Γ))
  have hone : e 1 ∈ V := by
    change (1 : Γ) ∈ e ⁻¹' V
    rw [hpre]
    exact Set.mem_singleton _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV (e 1) hone
  refine ⟨min (r / 2) (1 / 2), lt_min (half_pos hr) (by norm_num), ?_⟩
  intro g hg
  have hgR : ‖((g : Aˣ) : A) - 1‖ < r / 2 := hg.trans_le (min_le_left _ _)
  have hghalf : ‖((g : Aˣ) : A) - 1‖ ≤ 1 / 2 :=
    (hg.trans_le (min_le_right _ _)).le
  have hginv : ‖(↑((g : Aˣ)⁻¹) : A) - 1‖ < r :=
    (norm_inv_sub_one_le_twice (g : Aˣ) hghalf).trans_lt (by linarith)
  have hmem : e g ∈ Metric.ball (e 1) r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    change max (dist ((g : Aˣ) : A) 1)
      (dist (MulOpposite.op (↑((g : Aˣ)⁻¹) : A)) (MulOpposite.op (1 : A))) < r
    rw [MulOpposite.dist_op, dist_eq_norm, dist_eq_norm]
    exact max_lt (by linarith) hginv
  have : g ∈ ({1} : Set Γ) := by
    rw [← hpre]
    exact hball hmem
  exact Set.mem_singleton_iff.mp this

private theorem norm_foldl_commutator_le (Γ : Subgroup Aˣ) (s : Γ)
    (hs : ‖((s : Aˣ) : A) - 1‖ ≤ 1 / 32) (l : List Γ)
    (hl : ∀ t ∈ l, ‖((t : Aˣ) : A) - 1‖ ≤ 1 / 32) :
    ‖(((l.foldl (fun c t : Γ => ⁅c, t⁆) s : Γ) : Aˣ) : A) - 1‖ ≤
      (1 / 4 : ℝ) ^ l.length * ‖((s : Aˣ) : A) - 1‖ := by
  induction l generalizing s with
  | nil => simp
  | cons t l ih =>
    have ht := hl t (List.mem_cons_self ..)
    have hct : ‖(((⁅s, t⁆ : Γ) : Aˣ) : A) - 1‖ ≤
        (1 / 4 : ℝ) * ‖((s : Aˣ) : A) - 1‖ := by
      calc
        _ ≤ 8 * ‖((s : Aˣ) : A) - 1‖ * ‖((t : Aˣ) : A) - 1‖ :=
          norm_commutator_sub_one_le_of_norm_sub_one_le_half (s : Aˣ) (t : Aˣ)
            (hs.trans (by norm_num)) (ht.trans (by norm_num))
        _ ≤ 8 * ‖((s : Aˣ) : A) - 1‖ * (1 / 32) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) (norm_nonneg _))
        _ = _ := by ring
    have hsmall : ‖(((⁅s, t⁆ : Γ) : Aˣ) : A) - 1‖ ≤ 1 / 32 := by
      refine hct.trans ?_
      exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans (by norm_num)
    have htail : ∀ u ∈ l, ‖((u : Aˣ) : A) - 1‖ ≤ 1 / 32 :=
      fun u hu => hl u (List.mem_cons_of_mem t hu)
    rw [List.foldl_cons, List.length_cons]
    calc
      _ ≤ (1 / 4 : ℝ) ^ l.length * ‖(((⁅s, t⁆ : Γ) : Aˣ) : A) - 1‖ :=
        ih ⁅s, t⁆ hsmall htail
      _ ≤ (1 / 4 : ℝ) ^ l.length * ((1 / 4 : ℝ) * ‖((s : Aˣ) : A) - 1‖) :=
        mul_le_mul_of_nonneg_left hct (pow_nonneg (by norm_num) _)
      _ = (1 / 4 : ℝ) ^ (l.length + 1) * ‖((s : Aˣ) : A) - 1‖ := by
        rw [pow_succ]
        ring

theorem zassenhaus_lemma :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup Aˣ) [DiscreteTopology Γ],
      Group.IsNilpotent (Subgroup.closure {g : Γ | ‖((g : Aˣ) : A) - 1‖ < ε}) := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro Γ _
  obtain ⟨δ, hδ, hdiscrete⟩ := exists_pos_norm_sub_one_lt_imp_eq_one Γ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ * 32 from mul_pos hδ (by norm_num)) (by norm_num : (1 / 4 : ℝ) < 1)
  apply Subgroup.isNilpotent_closure_of_iterated_commutator_eq_one _ n
  intro s hs l hl hmem
  apply hdiscrete
  calc
    ‖(((l.foldl (fun c t : Γ => ⁅c, t⁆) s : Γ) : Aˣ) : A) - 1‖ ≤
        (1 / 4 : ℝ) ^ l.length * ‖((s : Aˣ) : A) - 1‖ :=
      norm_foldl_commutator_le Γ s hs.le l (fun t ht => (hmem t ht).le)
    _ ≤ (1 / 4 : ℝ) ^ n * (1 / 32) := by
      rw [hl]
      exact mul_le_mul_of_nonneg_left hs.le (pow_nonneg (by norm_num) _)
    _ < δ := by nlinarith

end Units
