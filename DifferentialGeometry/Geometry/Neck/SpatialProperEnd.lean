import DifferentialGeometry.Geometry.Neck.ProperSlabEnd

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem SpatialNeck.exists_at_graph_band_point_of_tolerance
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 156000)
    (f : Sphere 2 → ℝ) (hfsmall : ∀ q, |f q| < 1 / 10)
    (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hformula : ∀ q t, A (q, t) = nk.map (q, f q + (3 - f q) * t))
    (q : Sphere 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ out : SpatialNeck g (13000 * eps) (A (q, t)),
      out.center = q ∧ out.map = partialDiffeomorphTransMixed
        (DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph (I := I2) (M := Sphere 2)
          (f q + (3 - f q) * t) 1 (by norm_num)).toPartialDiffeomorph nk.map := by
  have ha : |f q + (3 - f q) * t| ≤ 4 := by
    have hf := abs_lt.mp (hfsmall q)
    rw [abs_le]
    constructor <;> nlinarith [ht.1, ht.2, hf.1, hf.2]
  obtain ⟨_, out, hcenter, hmap⟩ := nk.exists_at_coordinate_mul heps q ha
  rw [hformula]
  refine ⟨out, hcenter, ?_⟩
  exact hmap


theorem SpatialNeck.exists_at_central_band_point_of_tolerance
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 156000)
    (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hcentral : A '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4))
    (q : Sphere 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ out : SpatialNeck g (13000 * eps) (A (q,t)), ∃ u, out.center = u := by
  obtain ⟨⟨u,a⟩, ha, hEq⟩ := hcentral ⟨(q,t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨_, out, hcenter, _⟩ := nk.exists_at_coordinate_mul heps u (abs_le.mpr ha.2)
  rw [← hEq]
  exact ⟨out, u, hcenter⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
