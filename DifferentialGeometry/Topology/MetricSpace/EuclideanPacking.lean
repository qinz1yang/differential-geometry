import DifferentialGeometry.Analysis.InnerProductSpace.FiniteBoxPacking
import DifferentialGeometry.Topology.MetricSpace.FinitePacking

set_option autoImplicit false

open Set Real

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem card_le_of_bounded_lower_dist_map {S : Set X} {m : ℕ} (hm : 0 < m)
    {f : S → PiLp 2 (fun _ : Fin m => ℝ)} {B K ε : ℝ}
    (hB : 0 ≤ B) (hK : 0 < K) (hε : 0 < ε) (hnorm : ∀ x, ‖f x‖ ≤ B)
    (hlower : ∀ x y, K * dist x y ≤ dist (f x) (f y))
    (A : Finset X) (hA : (A : Set X) ⊆ S)
    (hsep : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)) :
    (A.card : ℝ) ≤ (1 + 4 * B * sqrt m / (K * ε)) ^ m := by
  let g : A → PiLp 2 (fun _ : Fin m => ℝ) := fun x => f ⟨x, hA x.property⟩
  have hgsep (x y : A) (hxy : x ≠ y) : K * ε ≤ dist (g x) (g y) := by
    have hne : (x : X) ≠ (y : X) := fun h => hxy (Subtype.ext h)
    have hs := hsep x.property y.property hne
    exact (mul_le_mul_of_nonneg_left hs hK.le).trans (hlower ⟨x, hA x.property⟩ ⟨y, hA y.property⟩)
  have h := PiLp.card_le_of_bounded_separated_family hm g hB (mul_pos hK hε)
    (fun x => hnorm ⟨x, hA x.property⟩) hgsep
  simpa only [Fintype.card_coe] using h

theorem finitePackingNumber_le_floor_of_bounded_lower_dist_map {S : Set X} {m : ℕ} (hm : 0 < m)
    {f : S → PiLp 2 (fun _ : Fin m => ℝ)} {B K ε : ℝ}
    (hB : 0 ≤ B) (hK : 0 < K) (hε : 0 < ε) (hnorm : ∀ x, ‖f x‖ ≤ B)
    (hlower : ∀ x y, K * dist x y ≤ dist (f x) (f y)) :
    finitePackingNumber ε S ≤ (⌊(1 + 4 * B * sqrt m / (K * ε)) ^ m⌋₊ : ℕ∞) := by
  apply finitePackingNumber_le_iff.mpr
  intro A hA hsep
  have h := card_le_of_bounded_lower_dist_map hm hB hK hε hnorm hlower A hA hsep
  exact_mod_cast Nat.le_floor h

end Metric
