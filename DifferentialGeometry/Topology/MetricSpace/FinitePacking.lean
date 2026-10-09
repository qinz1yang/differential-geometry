import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

noncomputable def finitePackingNumber (ε : ℝ) (S : Set X) : ℕ∞ :=
  ⨆ (A : Finset X) (_ : (A : Set X) ⊆ S) (_ : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)),
    (A.card : ℕ∞)

theorem card_le_finitePackingNumber {ε : ℝ} {S : Set X} (A : Finset X)
    (hA : (A : Set X) ⊆ S) (hsep : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)) :
    (A.card : ℕ∞) ≤ finitePackingNumber ε S :=
  le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hsep le_rfl))

theorem finitePackingNumber_le_iff {ε : ℝ} {S : Set X} {N : ℕ∞} :
    finitePackingNumber ε S ≤ N ↔
      ∀ A : Finset X, (A : Set X) ⊆ S →
        (A : Set X).Pairwise (fun x y => ε ≤ dist x y) → (A.card : ℕ∞) ≤ N := by
  simp only [finitePackingNumber, iSup_le_iff]

theorem finitePackingNumber_le_of_finite_images {ε δ : ℝ} {S : Set X} {T : Set Y}
    (himages : ∀ A : Finset X, (A : Set X) ⊆ S →
      (A : Set X).Pairwise (fun x y => ε ≤ dist x y) →
      ∃ B : Finset Y, (B : Set Y) ⊆ T ∧ A.card ≤ B.card ∧
        (B : Set Y).Pairwise (fun x y => δ ≤ dist x y)) :
    finitePackingNumber ε S ≤ finitePackingNumber δ T := by
  apply finitePackingNumber_le_iff.mpr
  intro A hA hsep
  obtain ⟨B, hB, hcard, hsepB⟩ := himages A hA hsep
  exact (by exact_mod_cast hcard : (A.card : ℕ∞) ≤ B.card).trans
    (card_le_finitePackingNumber B hB hsepB)

theorem exists_finset_image_of_lower_dist {S : Set X} {T : Set Y} {f : S → T}
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hlower : ∀ x y, ε ≤ dist x y → K * dist x y ≤ dist (f x) (f y))
    (A : Finset X) (hA : (A : Set X) ⊆ S)
    (hsep : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)) :
    ∃ B : Finset Y, (B : Set Y) ⊆ T ∧ B.card = A.card ∧
      (B : Set Y).Pairwise (fun x y => K * ε ≤ dist x y) := by
  classical
  let g : A → Y := fun x => f ⟨x, hA x.property⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hs := hsep x.property y.property hne
    have hl := hlower ⟨x, hA x.property⟩ ⟨y, hA y.property⟩ hs
    change K * dist (x : X) (y : X) ≤ dist (g x) (g y) at hl
    rw [hxy, dist_self] at hl
    exact (not_le_of_gt (mul_pos hK (hε.trans_le hs))) hl
  refine ⟨A.attach.image g, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (f ⟨x, hA x.property⟩).property
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  · intro u hu v hv huv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hv
    have hxy : (x : X) ≠ (y : X) := fun h => huv (congrArg g (Subtype.ext h))
    have hs := hsep x.property y.property hxy
    have hl := hlower ⟨x, hA x.property⟩ ⟨y, hA y.property⟩ hs
    exact (mul_le_mul_of_nonneg_left hs hK.le).trans hl

end Metric
