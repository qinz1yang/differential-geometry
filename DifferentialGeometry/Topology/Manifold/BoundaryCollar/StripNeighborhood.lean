import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowInverse

open Set Function Topology Filter Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem boundary_flow_image_mem_nhds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p)
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) {ε : ℝ} (hε : 0 < ε)
    {F : M × ℝ → M}
    (hzero : ∀ q ∈ U, F (q, 0) = q)
    (hcurve : ∀ q ∈ U, IsMIntegralCurveOn (fun t => F (q, t)) V (Icc (0 : ℝ) ε))
    (hi : ∀ q ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (q, t))) :
    {y | ∃ q ∈ U, (𝓡∂ (n + 1)).IsBoundaryPoint q ∧
      ∃ t ∈ Ico (0 : ℝ) ε, F (q, t) = y} ∈ 𝓝 p := by
  obtain ⟨O, hpO, R, _, hR⟩ := exists_smooth_boundary_flow_rightInverse hp hV hpos hU hpU hε
    hzero hcurve hi
  apply mem_of_superset (O.isOpen.mem_nhds hpO)
  intro y hy
  obtain ⟨hU, hb, ht, he⟩ := hR y hy
  exact ⟨(R y).1, hU, hb, (R y).2, ht, he⟩

end Poincare.Manifold.BoundaryCollar
