import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineMap_apply_add_smul_sub (A : E →ᵃ[ℝ] ℝ) (p x : E) (t : ℝ) :
    A (p + t • (x - p)) = A p + t * (A x - A p) := by
  simpa only [AffineMap.lineMap_apply_module', smul_eq_mul, add_comm] using A.apply_lineMap p x t

theorem isRadiallyInjective_of_affine_halfSpaces {ι : Type*} (A : ι → E →ᵃ[ℝ] ℝ)
    {S : Set E} (hnonneg : ∀ x ∈ S, ∀ i, 0 ≤ A i x)
    (hzero : ∀ x ∈ S, ∃ i, A i x = 0) {p : E}
    (hp : (∀ i, 0 < A i p) ∨ (∀ i, A i p < 0)) : IsRadiallyInjective p S := by
  have hnot {x y : E} (hx : x ∈ S) (hy : y ∈ S) {t : ℝ} (ht : 0 < t) (ht' : t < 1)
      (hyx : y = p + t • (x - p)) : False := by
    rcases hp with hp | hp
    · obtain ⟨i, hi⟩ := hzero y hy
      have h := affineMap_apply_add_smul_sub (A i) p x t
      rw [← hyx, hi] at h
      nlinarith [hp i, hnonneg x hx i, mul_nonneg ht.le (hnonneg x hx i)]
    · obtain ⟨i, hi⟩ := hzero x hx
      have h := affineMap_apply_add_smul_sub (A i) p x t
      rw [← hyx, hi] at h
      nlinarith [hp i, hnonneg y hy i]
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with ht' | rfl | ht'
  · exact (hnot hx hy ht ht' hyx).elim
  · simpa only [one_smul, add_sub_cancel] using hyx
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (hnot hy hx (inv_pos.mpr ht) (inv_lt_one_of_one_lt₀ ht') hxy).elim

theorem isConeBase_of_affine_halfSpaces {ι : Type*} (A : ι → E →ᵃ[ℝ] ℝ)
    (L : Geometry.SimplicialComplex ℝ E)
    (hnonneg : ∀ x ∈ L.space, ∀ i, 0 ≤ A i x)
    (hface : ∀ s ∈ L.faces, ∃ i, ∀ v ∈ s, A i v = 0) {p : E}
    (hp : (∀ i, 0 < A i p) ∨ (∀ i, A i p < 0)) : IsConeBase p L := by
  classical
  have hzero : ∀ x ∈ L.space, ∃ i, A i x = 0 := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := hface s hs
    refine ⟨i, ?_⟩
    calc A i x = A i (∑ v ∈ s, weights s x v • v) :=
          congrArg (A i) (sum_weights_smul hxs).symm
      _ = ∑ v ∈ s, weights s x v • A i v := affineMap_apply_sum_smul _ (sum_weights hxs)
      _ = 0 := Finset.sum_eq_zero fun v hv => by rw [hi v hv, smul_zero]
  have hpne : ∀ i, A i p ≠ 0 := fun i => hp.elim (fun h => (h i).ne') (fun h => (h i).ne)
  have hpL : p ∉ L.space := fun h => (hzero p h).elim fun i hi => hpne i hi
  refine ⟨hpL, ?_, isRadiallyInjective_of_affine_halfSpaces A hnonneg hzero hp⟩
  intro s hs
  have hps : p ∉ s := fun h => hpL (L.convexHull_subset_space hs (subset_convexHull ℝ _ h))
  rw [← Finset.coe_insert]
  refine (affineIndependent_insert_iff hps (L.indep hs)).mpr ?_
  rintro ⟨c, hc, hcp⟩
  obtain ⟨i, hi⟩ := hface s hs
  apply hpne i
  rw [← hcp, affineMap_apply_sum_smul _ hc]
  exact Finset.sum_eq_zero fun v hv => by rw [hi v hv, smul_zero]

theorem coneComplex_space_inter_eq_of_affine_halfSpaces [DecidableEq E]
    {ι : Type*} [Nonempty ι] (A : ι → E →ᵃ[ℝ] ℝ)
    {L : Geometry.SimplicialComplex ℝ E} {S : Set E} (hLS : L.space ⊆ S)
    (hnonneg : ∀ x ∈ S, ∀ i, 0 ≤ A i x)
    (hzero : ∀ x ∈ L.space, ∃ i, A i x = 0)
    {q : E} (hq : IsConeBase q L) (hqA : ∀ i, A i q < 0) :
    (coneComplex hq).space ∩ S = L.space := by
  apply Subset.antisymm
  · rintro x ⟨hxQ, hxS⟩
    have hxA : ∀ i, 0 ≤ A i x := hnonneg x hxS
    rcases (mem_coneComplex_space_iff hq).mp hxQ with rfl | ⟨z, hz, t, ht, ht', rfl⟩
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact (not_lt_of_ge (hxA i) (hqA i)).elim
    · obtain ⟨i, hi⟩ := hzero z hz
      have h := hxA i
      rw [affineMap_apply_add_smul_sub, hi] at h
      have ht1 : t = 1 := by nlinarith [hqA i]
      simpa only [ht1, one_smul, add_sub_cancel] using hz
  · exact fun x hx => ⟨space_subset_coneComplex_space hq hx, hLS hx⟩

theorem coneComplex_space_inter_of_affine_halfSpaces [DecidableEq E]
    {ι : Type*} [Nonempty ι] (A : ι → E →ᵃ[ℝ] ℝ)
    {L : Geometry.SimplicialComplex ℝ E}
    (hnonneg : ∀ x ∈ L.space, ∀ i, 0 ≤ A i x)
    (hzero : ∀ x ∈ L.space, ∃ i, A i x = 0)
    {p q : E} (hp : IsConeBase p L) (hq : IsConeBase q L)
    (hpA : ∀ i, 0 ≤ A i p) (hqA : ∀ i, A i q < 0) :
    (coneComplex hp).space ∩ (coneComplex hq).space = L.space := by
  rw [inter_comm]
  apply coneComplex_space_inter_eq_of_affine_halfSpaces A (space_subset_coneComplex_space hp)
    (hzero := hzero) (hq := hq) (hqA := hqA)
  intro x hx i
  rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, t, ht, ht', rfl⟩
  · exact hpA i
  · rw [affineMap_apply_add_smul_sub]
    nlinarith [hpA i, hnonneg z hz i, mul_nonneg (sub_nonneg.mpr ht') (hpA i),
      mul_nonneg ht.le (hnonneg z hz i)]

end DifferentialGeometry.Topology.PiecewiseLinear
