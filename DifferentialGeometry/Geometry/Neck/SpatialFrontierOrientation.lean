import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation
import DifferentialGeometry.Geometry.Neck.SpatialReflection

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem SpatialNeck.exists_outward_graph_orientation
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (f : Sphere 2 → ℝ) (hf : ContMDiff I2 𝓘(ℝ) ∞ f)
    (hsmall : ∀ q, |f q| < 1 / 10) (hzero : f nk.center = 0)
    {W S : Set M} (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = range (fun q => nk.map (q, f q)) ∪ S)
    (hdisjoint : Disjoint (range (fun q => nk.map (q, f q))) S) :
    ∃ (out : SpatialNeck g eps p) (h : Sphere 2 → ℝ),
      (out = nk ∨ out = nk.axialReflection) ∧
      ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, |h q| < 1 / 10) ∧ h out.center = 0 ∧
      (∀ q, out.map (q, h q) = nk.map (q, f q)) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → out.map (out.center, t) ∉ W := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hsource (q) : (q, f q) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;> linarith [(abs_lt.mp (hsmall q)).1,
      (abs_lt.mp (hsmall q)).2]⟩
  obtain ⟨r, hr, hor⟩ :=
    DifferentialGeometry.Topology.exists_graph_collar_orientation_of_frontier_eq_union
      nk.map.toOpenPartialHomeomorph hf.continuous hsource hregular hS hfront hdisjoint
  rcases hor with hor | hor
  · refine ⟨nk, f, Or.inl rfl, hf, hsmall, hzero, fun _ => rfl, r, hr, ?_⟩
    intro t ht htr
    have hh := (hor nk.center t ⟨ht, htr⟩).1
    change nk.map (nk.center, f nk.center + t) ∉ W at hh
    simpa only [hzero, zero_add] using hh
  · refine ⟨nk.axialReflection, fun q => -f q, Or.inr rfl, hf.neg, ?_, ?_, ?_, r, hr, ?_⟩
    · intro q
      simpa only [abs_neg] using hsmall q
    · change -f nk.center = 0
      rw [hzero, neg_zero]
    · intro q
      rw [SpatialNeck.axialReflection_apply, neg_neg]
    · intro t ht htr
      have hh := (hor nk.center t ⟨ht, htr⟩).1
      change nk.map (nk.center, f nk.center - t) ∉ W at hh
      change nk.map (nk.center, -t) ∉ W
      simpa only [hzero, zero_sub] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
