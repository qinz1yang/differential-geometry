import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveFootPoint

/-!
# Consumers of R1(i) / R1(ii) (S-SHAVE group 1)

* `exists_segment_mem_interior`: the design's R1(i) in the form "x ∈ int C, y ∈ C ⇒ some
  minimizing segment `[x, y)` lies in `int C`" (Hopf–Rinow segment + the open core).
* `expMap_smul_notMem_interior_of_foot`: the supporting half-line at a nearest boundary point —
  for a vector `ξ ⊥ v_p` (or pointing outward), `exp_p (s ξ) ∉ int C` for every `s ≥ 0`. This is the
  form consumed by the orthogonal boundary shift (`ShaveOrthogonalShift.lean`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **R1(i), design form.** From a point of `int C` to a point of `C` there is a unit-speed segment
whose half-open part `[x, y)` lies in `int C`. -/
theorem exists_segment_mem_interior
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {x y : M} (hx : x ∈ interior C) (hy : y ∈ C) :
    ∃ u : E, g.inner x u u = 1 ∧ g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y ∧
      ∀ s ∈ Ico 0 (dist x y), g.expMap (⟨x, s • u⟩ : TangentBundle I M) ∈ interior C := by
  obtain ⟨u, hu, -, hend⟩ := g.exists_unit_segment_expMap hr hnorm x y
  exact ⟨u, hu, hend, hC.expMap_smul_mem_interior_of_segment hr hnorm hx hy hend⟩

/-- **The supporting half-line at a nearest boundary point.** For `ξ` with `g(ξ, v_p) ≥ 0` at the
foot point `p = π φ_l(y, u)`, every `exp_p (s ξ)`, `s ≥ 0`, lies outside `int C`. -/
theorem expMap_smul_notMem_interior_of_foot
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {y : M} (hy : y ∈ C) {u : E}
    (hu : g.inner y u u = 1) (hl : 0 < infDist y (frontier C))
    (hfoot : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj ∈
      frontier C) (ξ : E)
    (hξ : 0 ≤ g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj ξ
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).snd)
    {s : ℝ} (hs : 0 ≤ s) :
    g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj,
      s • ξ⟩ : TangentBundle I M) ∉ interior C := by
  refine hC.expMap_notMem_interior_of_foot hr hnorm hy hu hl hfoot (s • ξ) ?_
  have h : g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj
      (s • ξ) = s • g.inner
        (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj ξ :=
    (g.inner _).map_smul s ξ
  rw [h]
  exact mul_nonneg hs hξ

end DifferentialGeometry.Geometry.FiniteSoul

end
