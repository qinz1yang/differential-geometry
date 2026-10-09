import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveConcavityConsumers

/-!
# S-SHAVE: the shaving step (maximal set of the boundary distance, finite metric)

Lane CMS-B. Review correction D2(2): the dimension drop is stated with `(frontier C).Nonempty`
(for `frontier C = ∅`, e.g. `C = M` compact, `d(·, ∂C) ≡ 0` and nothing is shaved).

* B5.1 `isTotallyConvexFinite_superlevel_infDist_frontier` (surface, `sec ≥ 0`): the superlevel
  sets `{x ∈ C | a ≤ d(x, ∂C)}` of a closed totally convex `C` are totally convex (concavity
  `concaveOn_infDist_frontier_geodesicFlow` + the minimum principle);
* B5.3 `interior_argmax_infDist_frontier_eq_empty` (no dimension, no curvature): the set where
  `d(·, ∂C)` attains its maximum over `C` has empty interior — along the segment to a nearest
  boundary point `d(·, ∂C)` drops with slope `1` (`dist_infDist_expMap_smul_of_foot`);
* B5.4 `isCompact_isTotallyConvexFinite_argmax_infDist_frontier` (surface, `sec ≥ 0`): for `C`
  compact, nonempty, totally convex with `(frontier C).Nonempty`, the maximal set is compact,
  nonempty, totally convex, contained in `C`, with empty interior (the output for S-SOUL2).

B5.5 (`[PreconnectedSpace M]`, `C` nonempty, `C ≠ univ` ⇒ `(frontier C).Nonempty`) EXISTS in
Mathlib: `nonempty_frontier_iff` (Topology/Connected/Clopen.lean); it is used in the consumers.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **B5.1: superlevel sets of the boundary distance are totally convex** (surface, `sec ≥ 0`). -/
theorem isTotallyConvexFinite_superlevel_infDist_frontier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCcl : IsClosed C)
    (hconv : IsTotallyConvexFinite g C) (a : ℝ) :
    IsTotallyConvexFinite g {x ∈ C | a ≤ infDist x (frontier C)} := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  intro p ℓ hℓ hp hpℓ t ht
  have hmaps : ∀ s ∈ Icc 0 ℓ, (g.geodesicFlow p s).proj ∈ C := hconv p ℓ hℓ hp.1 hpℓ.1
  refine ⟨hmaps t ht, ?_⟩
  have hmin := min_le_infDist_frontier_geodesicFlow g hr hnorm hsec hdim hCcl hconv p hℓ hmaps ht
  rw [g.geodesicFlow_zero hr1 p] at hmin
  exact le_trans (le_min hp.2 hpℓ.2) hmin

/-- **B5.3 (kernel): the maximal set of `d(·, ∂C)` on `C` has empty interior**, as soon as
`∂C ≠ ∅` (no dimension, no curvature, no convexity). -/
theorem interior_argmax_infDist_frontier_eq_empty [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hB : (frontier C).Nonempty) :
    interior {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  have hxA : x ∈ {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} :=
    interior_subset hx
  have hxC : x ∈ interior C := interior_mono (fun y hy => hy.1) hx
  have hl : 0 < infDist x (frontier C) :=
    (isClosed_frontier.notMem_iff_infDist_pos hB).1 (fun hf => hf.2 hxC)
  obtain ⟨u, hu, hfoot⟩ := exists_unit_foot_frontier g hr hnorm hB x
  obtain ⟨-, hτ⟩ := dist_infDist_expMap_smul_of_foot g hr hnorm hu hfoot
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have ht0 : 0 < min (ε / 2) (infDist x (frontier C)) := lt_min (by linarith) hl
  have htl : min (ε / 2) (infDist x (frontier C)) ≤ infDist x (frontier C) := min_le_right _ _
  have htε : min (ε / 2) (infDist x (frontier C)) < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨hd, hf⟩ := hτ _ ⟨ht0.le, htl⟩
  have hmem := interior_subset (hball (by rw [mem_ball, dist_comm, hd]; exact htε))
  have hle := hmem.2 x hxA.1
  rw [hf] at hle
  linarith

/-- **B5.4: the shaving step** (surface, `sec ≥ 0`). For `C` compact, nonempty, totally convex with
nonempty frontier, the maximal set of `d(·, ∂C)` on `C` is compact, nonempty, totally convex,
contained in `C`, and has empty interior. -/
theorem isCompact_isTotallyConvexFinite_argmax_infDist_frontier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvexFinite g C) (hB : (frontier C).Nonempty) :
    IsCompact {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} ∧
      {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)}.Nonempty ∧
      IsTotallyConvexFinite g
        {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} ∧
      {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} ⊆ C ∧
      interior {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} = ∅ := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hfc : Continuous fun x : M => infDist x (frontier C) := continuous_infDist_pt _
  obtain ⟨x₀, hx₀C, hx₀max⟩ := hCc.exists_isMaxOn hCne hfc.continuousOn
  have hmax : ∀ y ∈ C, infDist y (frontier C) ≤ infDist x₀ (frontier C) := fun y hy => hx₀max hy
  have hset : {x ∈ C | ∀ y ∈ C, infDist y (frontier C) ≤ infDist x (frontier C)} =
      {x ∈ C | infDist x₀ (frontier C) ≤ infDist x (frontier C)} := by
    ext x
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, hx x₀ hx₀C⟩
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, fun y hy => (hmax y hy).trans hx⟩
  refine ⟨?_, ⟨x₀, hx₀C, hmax⟩, ?_, fun x hx => hx.1,
    interior_argmax_infDist_frontier_eq_empty g (le_trans (by norm_num) hr) hnorm hB⟩
  · rw [hset]
    exact hCc.inter_right (isClosed_le continuous_const hfc)
  · rw [hset]
    exact isTotallyConvexFinite_superlevel_infDist_frontier g hr hnorm hsec hdim hCc.isClosed hconv _

end DifferentialGeometry.Geometry.FiniteSoul

end
