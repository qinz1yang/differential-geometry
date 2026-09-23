import DifferentialGeometry.Topology.OpenPartialHomeomorph.OutwardGraphBand
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarAdvance
import DifferentialGeometry.Geometry.Neck.Spatial

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem SpatialNeck.exists_outward_annulus_of_core_frontier_graph
    (nk : SpatialNeck g eps p) {K : Set M}
    (hregular : closure (interior K) = K)
    (f : Sphere 2 → ℝ) (hf : ContMDiff I2 𝓘(ℝ) ∞ f)
    (hsmall : ∀ q, |f q| < 11 / 10)
    (hfront : frontier K = range (fun q : Sphere 2 => nk.map (q, f q))) :
    ∃ (b : ℝ) (A : PartialDiffeomorph IC I3 Cylinder M ∞),
      (b = -2 ∨ b = 2) ∧ univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
      (∀ z t, A (z, t) = nk.map (z, f z + (b - f z) * t)) ∧
      (∀ z, A (z, 0) = nk.map (z, f z)) ∧
      (∀ z, A (z, 1) = nk.map (z, b)) ∧
      IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ K = frontier K ∧
      closure (interior (K ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
        K ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      frontier (K ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun z : Sphere 2 => nk.map (z, b)) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hlen : (2 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  have hsource : univ ×ˢ Icc (-2 : ℝ) 2 ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨b, hb, hout⟩ := DifferentialGeometry.Topology.exists_outward_closed_graph_band
    nk.map.toOpenPartialHomeomorph f hf.continuous
    (by intro q; linarith [(abs_lt.mp (hsmall q)).1] : ∀ q, -2 < f q)
    (by intro q; linarith [(abs_lt.mp (hsmall q)).2] : ∀ q, f q < 2)
    hsource hregular hfront
  have hband : {z : Cylinder | z.2 ∈ uIcc (f z.1) b} ⊆ nk.map.source := by
    intro z hz
    apply hsource
    refine ⟨mem_univ _, ?_, ?_⟩
    · have hlow : -2 ≤ min (f z.1) b := le_min (by linarith [(abs_lt.mp (hsmall z.1)).1])
        (by rcases hb with rfl | rfl <;> norm_num)
      exact hlow.trans hz.1
    · have hhigh : max (f z.1) b ≤ 2 := max_le (by linarith [(abs_lt.mp (hsmall z.1)).2])
        (by rcases hb with rfl | rfl <;> norm_num)
      exact hz.2.trans hhigh
  obtain ⟨A, hA, hformula, _, hcompact, _⟩ :=
    DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk.map f (fun _ => b)
      hf contMDiff_const (fun q => (hout q).1) hband
  have hzero (q : Sphere 2) : A (q, 0) = nk.map (q, f q) := by
    simpa only [mul_zero, add_zero] using hformula (q, 0)
  have hone (q : Sphere 2) : A (q, 1) = nk.map (q, b) := by
    simpa only [mul_one, add_sub_cancel] using hformula (q, 1)
  have hface : A '' (univ ×ˢ ({0} : Set ℝ)) = frontier K := by
    rw [hfront]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hq⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨q, (hzero q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, (hzero q).trans hq⟩
  have hseed : (A '' (univ ×ˢ Ioo (0 : ℝ) 1) \ K).Nonempty := by
    refine ⟨A (nk.center, 1 / 2), ⟨(nk.center, 1 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩, ?_⟩
    rw [hformula]
    exact (hout nk.center).2 (1 / 2) (by norm_num)
  obtain ⟨hinter, hreg, hnew⟩ := A.toOpenPartialHomeomorph.closed_cylinder_advance
    zero_lt_one hA hregular isClosed_empty (by
      change frontier K = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ ∅
      rw [hface, union_empty]) (empty_disjoint _) hseed
  change closure (interior (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ K)) =
    A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ K at hreg
  change frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ K) =
    ∅ ∪ A '' (univ ×ˢ ({1} : Set ℝ)) at hnew
  have htop : A '' (univ ×ˢ ({1} : Set ℝ)) = range (fun q : Sphere 2 => nk.map (q, b)) := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hq⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨q, (hone q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨(q, 1), ⟨mem_univ _, rfl⟩, (hone q).trans hq⟩
  refine ⟨b, A, hb, hA, fun z t => hformula (z, t), hzero, hone, hcompact, ?_, ?_, ?_⟩
  · exact hinter.trans hface
  · simpa only [union_comm] using hreg
  · simpa only [empty_union, htop, union_comm] using hnew

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
