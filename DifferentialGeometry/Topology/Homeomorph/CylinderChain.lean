import DifferentialGeometry.Topology.ClosedCover
import DifferentialGeometry.Topology.LocallyFinite.Superlevel
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology

private def cylinderStripHomeomorph (N : Type*) [TopologicalSpace N] (n : ℕ) :
    N × Icc (0 : ℝ) 1 ≃ₜ
      {x : N × Ici (0 : ℝ) | (x.2 : ℝ) ∈ Icc (n : ℝ) (n + 1)} where
  toFun x := ⟨(x.1, ⟨n + (x.2 : ℝ), add_nonneg (Nat.cast_nonneg n) x.2.property.1⟩),
    ⟨by linarith [x.2.property.1], by linarith [x.2.property.2]⟩⟩
  invFun x := (x.1.1, ⟨(x.1.2 : ℝ) - n,
    ⟨sub_nonneg.mpr x.property.1, by linarith [x.property.2]⟩⟩)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk ((continuous_const.add
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  continuous_invFun := by
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).sub
        continuous_const).subtype_mk _)

private theorem exists_homeomorph_iUnion_of_matching_cylinders
    {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
    (A : ℕ → Set M) (e : ∀ n, N × Icc (0 : ℝ) 1 ≃ₜ A n)
    (hclosed : ∀ n, IsClosed (A n)) (hfinite : LocallyFinite A)
    (hseam : ∀ n p, (e n (p, ⟨1, by simp⟩) : M) =
      e (n + 1) (p, ⟨0, by simp⟩))
    (hinter : ∀ n, A n ∩ A (n + 1) =
      range (fun p => (e n (p, ⟨1, by simp⟩) : M)))
    (hsep : ∀ i j, i + 1 < j → Disjoint (A i) (A j)) :
    ∃ E : N × Ici (0 : ℝ) ≃ₜ (⋃ n, A n),
      ∀ (n : ℕ) (p : N) (s : Icc (0 : ℝ) 1),
        (E (p, ⟨n + (s : ℝ), add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : M) =
          e n (p, s) := by
  let S (n : ℕ) : Set (N × Ici (0 : ℝ)) :=
    {x | (x.2 : ℝ) ∈ Icc (n : ℝ) (n + 1)}
  let T (n : ℕ) : Set (⋃ n, A n) := {y | (y : M) ∈ A n}
  have hS : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨Nat.floor (x.2 : ℝ), Nat.floor_le x.2.property,
      (Nat.lt_floor_add_one (x.2 : ℝ)).le⟩
  have hSc (n : ℕ) : IsClosed (S n) :=
    isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)
  have hSf : LocallyFinite S := by
    apply (continuous_subtype_val.comp continuous_snd).upperSemicontinuous.locallyFinite_of_tendsto_lower_bound
      (a := fun n : ℕ => (n : ℝ)) _ S (fun _ _ hx => hx.1)
    simpa only [Nat.cofinite_eq_atTop] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hT : ⋃ n, T n = univ := by
    apply eq_univ_of_forall
    intro y
    exact mem_iUnion.mp y.property |>.elim fun n hn => mem_iUnion.mpr ⟨n, hn⟩
  have hTc (n : ℕ) : IsClosed (T n) := (hclosed n).preimage continuous_subtype_val
  have hTf : LocallyFinite T := hfinite.preimage_continuous continuous_subtype_val
  let h (n : ℕ) : T n ≃ₜ A n :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun y hy => ⟨⟨y, mem_iUnion.mpr ⟨n, hy⟩⟩, rfl⟩)
  have hh (n : ℕ) (y : A n) : (((h n).symm y : T n) : (⋃ n, A n)) =
      ⟨y, mem_iUnion.mpr ⟨n, y.property⟩⟩ := by
    apply Subtype.ext
    have hc (z : T n) : ((h n) z : M) = (z.1 : M) :=
      Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
        (f := (Subtype.val : (⋃ n, A n) → M)) Topology.IsEmbedding.subtypeVal
        (fun y hy => ⟨⟨y, mem_iUnion.mpr ⟨n, hy⟩⟩, rfl⟩) z
    exact (hc _).symm.trans (congrArg (fun z : A n => (z : M)) ((h n).apply_symm_apply y))
  let d (n : ℕ) : S n ≃ₜ T n :=
    (cylinderStripHomeomorph N n).symm.trans ((e n).trans (h n).symm)
  have hd (n : ℕ) (x : S n) : ((d n x : T n) : (⋃ n, A n)) =
      ⟨e n (x.1.1, ⟨(x.1.2 : ℝ) - n,
        ⟨sub_nonneg.mpr x.property.1, by linarith [x.property.2]⟩⟩),
        mem_iUnion.mpr ⟨n, (e n _).property⟩⟩ := hh n _
  have hforward_le (i j : ℕ) (hij : i ≤ j) (x : N × Ici (0 : ℝ))
      (hxi : x ∈ S i) (hxj : x ∈ S j) :
      (d i ⟨x, hxi⟩ : (⋃ n, A n)) = d j ⟨x, hxj⟩ := by
    rcases eq_or_lt_of_le hij with rfl | hij
    · rfl
    have hji : j ≤ i + 1 := by exact_mod_cast hxj.1.trans hxi.2
    have hjeq : j = i + 1 := by omega
    subst j
    have hx : (x.2 : ℝ) = i + 1 := by
      have hj := hxj.1
      simp only [Nat.cast_add, Nat.cast_one] at hj
      exact le_antisymm hxi.2 hj
    apply Subtype.ext
    rw [hd, hd]
    change (e i (x.1, _) : M) = e (i + 1) (x.1, _)
    have hi : (x.2 : ℝ) - i = 1 := by rw [hx]; ring
    have hj : (x.2 : ℝ) - (i + 1 : ℕ) = 0 := by simp [hx]
    simpa only [hi, hj] using hseam i x.1
  have hforward (i j : ℕ) (x : N × Ici (0 : ℝ)) (hxi : x ∈ S i) (hxj : x ∈ S j) :
      (d i ⟨x, hxi⟩ : (⋃ n, A n)) = d j ⟨x, hxj⟩ := by
    rcases le_total i j with hij | hji
    · exact hforward_le i j hij x hxi hxj
    · exact (hforward_le j i hji x hxj hxi).symm
  have hbackward_le (i j : ℕ) (hij : i ≤ j) (y : (⋃ n, A n))
      (hyi : y ∈ T i) (hyj : y ∈ T j) :
      ((d i).symm ⟨y, hyi⟩ : N × Ici (0 : ℝ)) = (d j).symm ⟨y, hyj⟩ := by
    rcases eq_or_lt_of_le hij with rfl | hij
    · rfl
    have hji : j ≤ i + 1 := by
      by_contra hh'
      exact Set.disjoint_left.mp (hsep i j (by omega)) hyi hyj
    have hjeq : j = i + 1 := by omega
    subst j
    obtain ⟨p, hp⟩ := mem_range.mp ((hinter i) ▸ (show (y : M) ∈ A i ∩ A (i + 1) from ⟨hyi, hyj⟩))
    have hpi : (h i) ⟨y, hyi⟩ = e i (p, ⟨1, by simp⟩) := Subtype.ext hp.symm
    have hpj : (h (i + 1)) ⟨y, hyj⟩ = e (i + 1) (p, ⟨0, by simp⟩) :=
      Subtype.ext (hp.symm.trans (hseam i p))
    change (cylinderStripHomeomorph N i ((e i).symm ((h i) ⟨y, hyi⟩)) :
      N × Ici (0 : ℝ)) =
        (cylinderStripHomeomorph N (i + 1) ((e (i + 1)).symm ((h (i + 1)) ⟨y, hyj⟩)) :
          N × Ici (0 : ℝ))
    rw [hpi, hpj, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    ext <;> simp [cylinderStripHomeomorph]
  have hbackward (i j : ℕ) (y : (⋃ n, A n)) (hyi : y ∈ T i) (hyj : y ∈ T j) :
      ((d i).symm ⟨y, hyi⟩ : N × Ici (0 : ℝ)) = (d j).symm ⟨y, hyj⟩ := by
    rcases le_total i j with hij | hji
    · exact hbackward_le i j hij y hyi hyj
    · exact (hbackward_le j i hji y hyj hyi).symm
  refine ⟨Homeomorph.liftClosedCover S T d hforward hbackward hS hSc hSf hT hTc hTf, ?_⟩
  intro n p s
  let hx := (cylinderStripHomeomorph N n) (p, s)
  have heq := Homeomorph.liftClosedCover_coe (e := d) (he := hforward) (he' := hbackward)
    (hS := hS) (hSc := hSc) (hSf := hSf) (hT := hT) (hTc := hTc) (hTf := hTf) hx
  have hdeq := hh n (e n (p, s))
  have hd' : (d n hx : (⋃ n, A n)) =
      ⟨e n (p, s), mem_iUnion.mpr ⟨n, (e n (p, s)).property⟩⟩ := by
    simpa only [d, hx, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using hdeq
  exact congrArg Subtype.val (heq.trans hd')

theorem exists_homeomorph_iUnion_of_cylinder_chain
    {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
    (A : ℕ → Set M) (e : ∀ n, N × Icc (0 : ℝ) 1 ≃ₜ A n)
    (eta : ℕ → N ≃ₜ N) (hclosed : ∀ n, IsClosed (A n)) (hfinite : LocallyFinite A)
    (hseam : ∀ n p, (e n (p, ⟨1, by simp⟩) : M) =
      e (n + 1) (eta n p, ⟨0, by simp⟩))
    (hinter : ∀ n, A n ∩ A (n + 1) =
      range (fun p => (e n (p, ⟨1, by simp⟩) : M)))
    (hsep : ∀ i j, i + 1 < j → Disjoint (A i) (A j)) :
    ∃ E : N × Ici (0 : ℝ) ≃ₜ (⋃ n, A n), ∃ theta : ℕ → N ≃ₜ N,
      theta 0 = Homeomorph.refl N ∧ (∀ n, theta (n + 1) = (theta n).trans (eta n)) ∧
      ∀ (n : ℕ) (p : N) (s : Icc (0 : ℝ) 1),
        (E (p, ⟨n + (s : ℝ), add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : M) =
          e n (theta n p, s) := by
  let theta : ℕ → N ≃ₜ N := Nat.rec (Homeomorph.refl N) (fun n z => z.trans (eta n))
  let e' (n : ℕ) : N × Icc (0 : ℝ) 1 ≃ₜ A n :=
    ((theta n).prodCongr (Homeomorph.refl _)).trans (e n)
  have hseam' (n : ℕ) (p : N) : (e' n (p, ⟨1, by simp⟩) : M) =
      e' (n + 1) (p, ⟨0, by simp⟩) := hseam n (theta n p)
  have hinter' (n : ℕ) : A n ∩ A (n + 1) =
      range (fun p => (e' n (p, ⟨1, by simp⟩) : M)) := by
    rw [hinter]
    ext y
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨q, rfl⟩ := (theta n).surjective p
      exact ⟨q, hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨theta n p, hp⟩
  obtain ⟨E, hE⟩ := exists_homeomorph_iUnion_of_matching_cylinders
    A e' hclosed hfinite hseam' hinter' hsep
  exact ⟨E, theta, rfl, fun _ => rfl, hE⟩

end DifferentialGeometry.Topology
