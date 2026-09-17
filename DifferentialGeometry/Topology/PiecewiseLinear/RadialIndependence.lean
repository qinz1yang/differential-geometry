import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem affineIndependent_insert_of_isRadiallyInjective {p : E} {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E))
    (hp : p ∉ convexHull ℝ (s : Set E))
    (hrad : IsRadiallyInjective p (convexHull ℝ (s : Set E))) :
    AffineIndependent ℝ ((↑) : {x // x ∈ (insert p s : Finset E)} → E) := by
  classical
  have hps : p ∉ s := fun h => hp (subset_convexHull ℝ _ h)
  refine (affineIndependent_insert_iff hps hs).mpr ?_
  rintro ⟨c, hc, hcp⟩
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hc
  let d : ℝ := (s.card : ℝ)⁻¹
  have hd : 0 < d := inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hsne))
  have hdsum : ∑ _v ∈ s, d = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, d]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hsne))
  let q : E := ∑ v ∈ s, d • v
  have hq : q ∈ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).sum_mem (fun _ _ => hd.le) hdsum
      (fun v hv => subset_convexHull ℝ _ hv)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ v ∈ s, 0 < d + t * (c v - d) := by
    rw [Filter.eventually_all_finset]
    intro v hv
    have hf : ContinuousAt (fun t : ℝ => d + t * (c v - d)) 0 := by fun_prop
    exact hf.eventually (Ioi_mem_nhds (by simpa using hd))
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have htlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hnear' : ∀ᶠ t : ℝ in 𝓝[>] 0, (0 < t ∧ t < 1) ∧ ∀ v ∈ s, 0 < d + t * (c v - d) :=
    Filter.Eventually.and (Filter.Eventually.and htpos htlt) (nhdsWithin_le_nhds hnear)
  obtain ⟨t, ⟨ht, ht1⟩, hcoeff⟩ := hnear'.exists
  have hsum : ∑ v ∈ s, (d + t * (c v - d)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hc, hdsum]
    ring
  have hy : (∑ v ∈ s, (d + t * (c v - d)) • v) ∈ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).sum_mem (fun v hv => (hcoeff v hv).le) hsum
      (fun v hv => subset_convexHull ℝ _ hv)
  have heq : (∑ v ∈ s, (d + t * (c v - d)) • v) = p + (1 - t) • (q - p) := by
    calc
      _ = (∑ v ∈ s, d • v) + t • (∑ v ∈ s, (c v • v - d • v)) := by
        simp only [add_smul, mul_smul, sub_smul, Finset.sum_add_distrib, Finset.smul_sum]
      _ = q + t • (p - q) := by rw [Finset.sum_sub_distrib, hcp]
      _ = p + (1 - t) • (q - p) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
  have hyq := hrad q hq _ hy (1 - t) (sub_pos.mpr ht1) heq
  have hzero : t • (p - q) = 0 := by
    have hyq' := heq.symm.trans hyq
    have hform : p + (1 - t) • (q - p) = q + t • (p - q) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [hform] at hyq'
    exact add_left_cancel (hyq'.trans (add_zero q).symm)
  have hpq : p = q := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
  exact hp (hpq ▸ hq)

theorem isConeBase_of_isRadiallyInjective {p : E} (K : Geometry.SimplicialComplex ℝ E)
    (hp : p ∉ K.space) (hrad : IsRadiallyInjective p K.space) : IsConeBase p K where
  notMem_space := hp
  radial := hrad
  indep s hs := by
    classical
    rw [← Finset.coe_insert]
    exact affineIndependent_insert_of_isRadiallyInjective (K.indep hs)
      (fun h => hp (K.convexHull_subset_space hs h))
      (fun x hx y hy => hrad x (K.convexHull_subset_space hs hx) y (K.convexHull_subset_space hs hy))

end DifferentialGeometry.Topology.PiecewiseLinear
