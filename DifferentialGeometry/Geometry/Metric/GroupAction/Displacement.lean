import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped ENNReal

namespace MulAction

variable {G X : Type*} [Group G] [PseudoEMetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

private theorem forall_le_edist_smul (r : ℝ≥0∞) {x : X}
    (hx : ∀ g : G, g ≠ 1 → r ≤ edist x (g • x)) (a : G) :
    ∀ g : G, g ≠ 1 → r ≤ edist (a • x) (g • (a • x)) := by
  intro g hg
  have hne : a⁻¹ * g * a ≠ 1 := by
    intro h
    have h' := congrArg (fun k : G => a * k * a⁻¹) h
    apply hg
    simpa [mul_assoc] using h'
  have h := hx (a⁻¹ * g * a) hne
  have hd : edist (a • x) (g • (a • x)) = edist x ((a⁻¹ * g * a) • x) := calc
    _ = edist (a • x) (a • ((a⁻¹ * g * a) • x)) := by
      simp only [mul_smul, smul_inv_smul]
    _ = _ := edist_smul_left a _ _
  rwa [hd]

private theorem isClosed_setOf_forall_le_edist_smul (G : Type*) [Group G]
    [MulAction G X] [IsIsometricSMul G X] (r : ℝ≥0∞) :
    IsClosed {x : X | ∀ g : G, g ≠ 1 → r ≤ edist x (g • x)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun g => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_id.edist (isometry_smul X g).continuous)

theorem isClosed_image_setOf_forall_le_edist_smul (G : Type*) [Group G]
    [MulAction G X] [IsIsometricSMul G X] (r : ℝ≥0∞) :
    IsClosed ((Quotient.mk (orbitRel G X)) ''
      {x : X | ∀ g : G, g ≠ 1 → r ≤ edist x (g • x)}) := by
  let S : Set X := {x | ∀ g : G, g ≠ 1 → r ≤ edist x (g • x)}
  have hsat : Quotient.mk (orbitRel G X) ⁻¹' (Quotient.mk (orbitRel G X) '' S) = S := by
    have heq : Quotient.mk (orbitRel G X) ⁻¹' (Quotient.mk (orbitRel G X) '' S) =
        ⋃ a : G, (a • ·) '' S := quotient_preimage_image_eq_union_mul S
    rw [heq]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact forall_le_edist_smul r hy a
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨1, x, hx, one_smul G x⟩
  apply (isOpenQuotientMap_quotientMk (Γ := G) (T := X)).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [hsat]
  exact isClosed_setOf_forall_le_edist_smul G r

end MulAction

namespace MulAction

variable {X : Type*} [PseudoMetricSpace X]

theorem injOn_quotientMk_ball_of_le_dist_smul (G : Type*) [Group G]
    [MulAction G X] [IsIsometricSMul G X] (x : X) (r : ℝ)
    (hx : ∀ g : G, g ≠ 1 → 2 * r ≤ dist x (g • x)) :
    Set.InjOn (Quotient.mk (orbitRel G X)) (Metric.ball x r) := by
  intro y hy z hz heq
  obtain ⟨g, hg⟩ := Quotient.exact heq
  by_cases h : g = 1
  · simpa only [h, one_smul] using hg.symm
  · have hbound : dist x (g • x) < 2 * r := calc
      dist x (g • x) ≤ dist x y + dist y (g • x) := dist_triangle _ _ _
      _ = dist x y + dist z x := by rw [← hg, dist_smul]
      _ < 2 * r := by
        have hy' : dist x y < r := Metric.mem_ball'.mp hy
        have hz' : dist z x < r := hz
        exact (add_lt_add hy' hz').trans_eq (two_mul r).symm
    exact (not_lt_of_ge (hx g h) hbound).elim

end MulAction
