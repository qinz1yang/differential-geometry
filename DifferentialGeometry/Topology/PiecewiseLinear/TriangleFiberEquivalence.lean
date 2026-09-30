import DifferentialGeometry.Topology.PiecewiseLinear.TriangleFiberBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLHomeomorphOn_scale_Icc {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    IsPLHomeomorphOn (fun x => (u / t) * x) (Icc 0 t) (Icc 0 u) := by
  have ha : 0 < u / t := div_pos hu ht
  have hat : (u / t) * t = u := div_mul_cancel₀ _ ht.ne'
  have hpoly := (isHPolytope_Icc (a := (0 : ℝ)) (b := t)).isPolyhedron
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine ((u / t) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap
      isOpen_univ).mono_of_isPolyhedron hpoly (subset_univ _)) ?_
  refine ⟨?_, fun _ _ _ _ h => mul_left_cancel₀ ha.ne' h, ?_⟩
  · intro x hx
    exact ⟨mul_nonneg ha.le hx.1, (mul_le_mul_of_nonneg_left hx.2 ha.le).trans_eq hat⟩
  · intro y hy
    refine ⟨y / (u / t), ⟨div_nonneg hy.1 ha.le, ?_⟩, ?_⟩
    · apply (div_le_iff₀ ha).mpr
      simpa only [mul_comm t, hat] using hy.2
    · exact mul_div_cancel₀ y ha.ne'

theorem exists_isPLHomeomorphOn_triangle_fibers_preserving_edges
    {b c : ℝ × ℝ → ℝ} {r s : ℝ}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hc : IsPiecewiseAffineOn c {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hbh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hbl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hbr : StrictAntiOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (hch : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => c (x, y)) (Icc 0 (1 - y)))
    (hcl : StrictMonoOn (fun y => c (0, y)) (Icc (0 : ℝ) 1))
    (hcr : StrictAntiOn (fun y => c (1 - y, y)) (Icc (0 : ℝ) 1))
    (hb₀ : b (0, 0) < r) (hb₁ : r < b (1, 0))
    (hc₀ : c (0, 0) < s) (hc₁ : s < c (1, 0))
    (hleft : r ≤ b (0, 1) ↔ s ≤ c (0, 1))
    (hright : b (0, 1) ≤ r ↔ c (0, 1) ≤ s) :
    ∃ g : ℝ × ℝ → ℝ × ℝ, IsPLHomeomorphOn g
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ c z = s} ∧
      ∀ z, (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) → b z = r →
        ((g z).1 = 0 ↔ z.1 = 0) ∧ ((g z).2 = 0 ↔ z.2 = 0) ∧
        ((g z).1 + (g z).2 = 1 ↔ z.1 + z.2 = 1) := by
  obtain ⟨t, ht, hbPL, hbEdge⟩ :=
    exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges hb hbh hbl hbr hb₀ hb₁
  obtain ⟨u, hu, hcPL, hcEdge⟩ :=
    exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges hc hch hcl hcr hc₀ hc₁
  have hscale := isPLHomeomorphOn_scale_Icc ht.1 hu.1
  let g : ℝ × ℝ → ℝ × ℝ := Function.invFunOn Prod.snd
    {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ c z = s} ∘
      (fun x => (u / t) * x) ∘ Prod.snd
  have hg : IsPLHomeomorphOn g
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ c z = s} :=
    (hbPL.trans hscale).trans hcPL.symm
  refine ⟨g, hg, fun z hz hbz => ?_⟩
  have hgz := hg.bijOn.mapsTo ⟨hz, hbz⟩
  have hcoord : (g z).2 = (u / t) * z.2 :=
    hcPL.bijOn.invOn_invFunOn.2 (hscale.bijOn.mapsTo (hbPL.bijOn.mapsTo ⟨hz, hbz⟩))
  have ha : u / t ≠ 0 := (div_pos hu.1 ht.1).ne'
  have hzero : (g z).2 = 0 ↔ z.2 = 0 := by
    rw [hcoord, mul_eq_zero]
    exact or_iff_right ha
  have htop : (g z).2 = u ↔ z.2 = t := by
    constructor
    · intro h
      apply mul_left_cancel₀ ha
      exact (hcoord.symm.trans h).trans (div_mul_cancel₀ u ht.1.ne').symm
    · intro h
      rw [hcoord, h, div_mul_cancel₀ u ht.1.ne']
  have he₀ := hbEdge z hz hbz
  have he₁ := hcEdge (g z) hgz.1 hgz.2
  refine ⟨?_, hzero, ?_⟩
  · rw [he₁.1, he₀.1]
    exact and_congr htop hleft.symm
  · rw [he₁.2, he₀.2]
    exact and_congr htop hright.symm

end DifferentialGeometry.Topology.PiecewiseLinear
