import DifferentialGeometry.Topology.Planar.CornerRounding
import DifferentialGeometry.Topology.Planar.CornerReanchoring
import DifferentialGeometry.Topology.Compactness.FiniteReplacement

open Set Metric

namespace Schoenflies

theorem eq_affine_corner_replacement_of_local_profiles
    {ι : Type*} (e : ι → Plane ≃ᵃ[ℝ] Plane) (U : ι → Set Plane)
    (ε R d σ : ι → ℝ) {D E : Set Plane}
    (hε : ∀ i, 0 < ε i) (hR : ∀ i, 3 * ε i < R i)
    (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hraw : ∀ i, ∀ p ∈ U i, p ∈ D ↔
      0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0))
    (hsmooth : ∀ i, ∀ p ∈ U i, p ∈ E ↔
      0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0))
    (houtside : ∀ p ∉ ⋃ i, U i, p ∈ E ↔ p ∈ D) :
    E = (D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
      ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
        {p | 0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)} := by
  apply Set.eq_iUnion_replacement_of_local_eq D E
    (fun i => e i ⁻¹' ball (0 : Plane) (R i))
    (fun i => e i ⁻¹' closedBall (0 : Plane) (R i)) U
    (fun i => {p | 0 ≤ σ i * ((e i p) 1 -
      d i * Real.smoothMax (ε i) ((e i p) 0) 0)})
    (fun _ => preimage_mono ball_subset_closedBall) hKU hsmooth ?_ houtside
  intro i p hp
  have hnorm : R i ≤ ‖e i p‖ := by
    simpa only [mem_preimage, mem_ball, dist_zero_right, not_lt] using hp.2
  exact (smooth_corner_signs_eq_outside_ball (σ := σ i) (hε i) (hd i)
    ((hR i).trans_le hnorm)).1.trans (hraw i p hp.1).symm

private theorem exists_corner_orientation {c : ℝ} (hc : c ≠ 0) :
    ∃ s : ℝ, (s = -1 ∨ s = 1) ∧ ∀ t : ℝ, (0 ≤ c * t ↔ 0 ≤ s * t) := by
  rcases lt_or_gt_of_ne hc with h | h
  · refine ⟨-1, Or.inl rfl, fun t => ?_⟩
    rw [neg_one_mul, neg_nonneg]
    exact ⟨fun ht => nonpos_of_mul_nonneg_right ht h,
      fun ht => mul_nonneg_of_nonpos_of_nonpos h.le ht⟩
  · refine ⟨1, Or.inr rfl, fun t => ?_⟩
    rw [mul_nonneg_iff_of_pos_left h, one_mul]

theorem PrePolygon.exists_finite_corner_replacement_of_local_graphs
    {m : ℕ} (P : PrePolygon m) {ι : Type*} [Finite ι]
    (p : ι → Plane) (hp : Function.Injective p) (O : ι → Set Plane)
    (e₀ : ι → Plane ≃ᵃ[ℝ] Plane) (u v c : ι → ℝ)
    (hO : ∀ i, IsOpen (O i)) (hpO : ∀ i, p i ∈ O i)
    (he₀ : ∀ i, e₀ i (p i) = 0) (hc : ∀ i, c i ≠ 0)
    (hgraph : ∀ i, ∀ x ∈ O i, x ∈ P.carrier ↔
      (e₀ i x) 1 = u i * (e₀ i x) 0 + (v i - u i) * max ((e₀ i x) 0) 0) :
    ∃ (e : ι → Plane ≃ᵃ[ℝ] Plane) (V : ι → Set Plane) (d s κ R δ : ι → ℝ),
      (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ O i ∧
        e i (p i) = 0 ∧ (d i = 0 ∨ d i = 1) ∧ (d i = 0 ↔ u i = v i) ∧
        (s i = -1 ∨ s i = 1) ∧ 0 < κ i ∧ 0 < R i ∧ 0 < δ i ∧
        e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ V i ∧
        (∀ a ∈ Ioc (0 : ℝ) (δ i), 3 * (κ i * a) < R i) ∧
        (d i = 1 → ∃ (j : ZMod (m + 3)) (r : ℝ),
          P.vertex j = p i ∧ 0 < r ∧
          e i (P.vertex (j - 1)) = Plane.mk (-1) 0 ∧
          e i (P.vertex (j + 1)) = Plane.mk r r)) ∧
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧
      (∀ i x, (0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
          (v i - u i) * max ((e₀ i x) 0) 0) ↔
        0 ≤ s i * ((e i x) 1 - d i * max ((e i x) 0) 0))) ∧
      (∀ i, ∀ x ∈ O i, x ∈ P.carrier ↔
        (e i x) 1 = d i * max ((e i x) 0) 0) ∧
      ∀ (a : ι → ℝ), (∀ i, a i ∈ Ioc (0 : ℝ) (δ i)) →
        (∀ i x, (0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
            (v i - u i) * Real.smoothMax (a i) ((e₀ i x) 0) 0) ↔
          0 ≤ s i * ((e i x) 1 - d i * Real.smoothMax (κ i * a i) ((e i x) 0) 0))) ∧
        ∀ (D E : Set Plane),
          (∀ i, ∀ x ∈ O i, x ∈ D ↔
            0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
              (v i - u i) * max ((e₀ i x) 0) 0)) →
          (∀ i, ∀ x ∈ O i, x ∈ E ↔
            0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
              (v i - u i) * Real.smoothMax (a i) ((e₀ i x) 0) 0)) →
          (∀ x ∉ ⋃ i, O i, x ∈ E ↔ x ∈ D) →
          E = (D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
            ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
              {x | 0 ≤ s i * ((e i x) 1 - d i *
                Real.smoothMax (κ i * a i) ((e i x) 0) 0)} := by
  classical
  choose e d κ L hd hstraight hκ hL hep hraw hsmooth hvertex using
    fun i => P.exists_normalized_smooth_corner_of_local_graph (e₀ i)
      (hO i) (hpO i) (he₀ i) (hgraph i)
  obtain ⟨V, hV, hdisj⟩ := exists_pairwise_disjoint_open_neighborhoods p hp O hO hpO
  have hR i : ∃ R : ℝ, 0 < R ∧ e i ⁻¹' closedBall (0 : Plane) R ⊆ V i := by
    have hei : Continuous (e i).symm :=
      (e i).symm.toAffineMap.continuous_of_finiteDimensional
    have hz : (0 : Plane) ∈ (e i).symm ⁻¹' V i := by
      change (e i).symm 0 ∈ V i
      rw [← hep i, (e i).symm_apply_apply]
      exact (hV i).2.1
    obtain ⟨R, hR, hRV⟩ := nhds_basis_closedBall.mem_iff.mp
      (((hV i).1.preimage hei).mem_nhds hz)
    refine ⟨R, hR, fun x hx => ?_⟩
    simpa only [mem_preimage, (e i).symm_apply_apply] using hRV hx
  choose R hR hRV using hR
  choose δ hδ hδR using fun i => exists_pos_mul_lt (hR i) (3 * κ i)
  have hbound i a (ha : a ∈ Ioc (0 : ℝ) (δ i)) : 3 * (κ i * a) < R i := by
    calc
      3 * (κ i * a) = (3 * κ i) * a := (mul_assoc _ _ _).symm
      _ ≤ (3 * κ i) * δ i := mul_le_mul_of_nonneg_left ha.2 (mul_nonneg (by norm_num) (hκ i).le)
      _ < R i := hδR i
  choose s hs hsign using fun i => exists_corner_orientation (mul_ne_zero (hc i) (hL i))
  have hrawsign i x :
      (0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
          (v i - u i) * max ((e₀ i x) 0) 0) ↔
        0 ≤ s i * ((e i x) 1 - d i * max ((e i x) 0) 0)) := by
    rw [hraw i, ← mul_assoc]
    exact hsign i _
  have hcarrier i x (hx : x ∈ O i) : x ∈ P.carrier ↔
      (e i x) 1 = d i * max ((e i x) 0) 0 := by
    constructor
    · intro hxc
      have hz : (e₀ i x) 1 - u i * (e₀ i x) 0 -
          (v i - u i) * max ((e₀ i x) 0) 0 = 0 := by
        linarith only [(hgraph i x hx).mp hxc]
      exact sub_eq_zero.mp ((mul_eq_zero.mp ((hraw i x).symm.trans hz)).resolve_left (hL i))
    · intro heq
      have hz := hraw i x
      rw [heq, sub_self, mul_zero] at hz
      apply (hgraph i x hx).mpr
      linarith only [hz]
  refine ⟨e, V, d, s, κ, R, δ, ?_, hdisj, hrawsign, hcarrier, ?_⟩
  · intro i
    exact ⟨(hV i).1, (hV i).2.1, (hV i).2.2, hep i, hd i, hstraight i,
      hs i, hκ i, hR i, hδ i, hRV i, hbound i, hvertex i⟩
  · intro a ha
    have hsm i x :
        (0 ≤ c i * ((e₀ i x) 1 - u i * (e₀ i x) 0 -
            (v i - u i) * Real.smoothMax (a i) ((e₀ i x) 0) 0) ↔
          0 ≤ s i * ((e i x) 1 - d i * Real.smoothMax (κ i * a i) ((e i x) 0) 0)) := by
      rw [hsmooth i (a i) (ha i).1, ← mul_assoc]
      exact hsign i _
    refine ⟨hsm, fun D E hD hE houtside => ?_⟩
    exact eq_affine_corner_replacement_of_local_profiles e O (fun i => κ i * a i) R d s
      (fun i => mul_pos (hκ i) (ha i).1) (fun i => hbound i (a i) (ha i)) hd
      (fun i => (hRV i).trans (hV i).2.2)
      (fun i x hx => (hD i x hx).trans (hrawsign i x))
      (fun i x hx => (hE i x hx).trans (hsm i x)) houtside

end Schoenflies
