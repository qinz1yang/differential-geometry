import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveConcavityApplications

/-!
# DROP: one shaving step of the flag (CMS3-REL, G3)

Lane CMS3-REL, frozen interface DROP of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
(`maxSliceDimOfOrder_argmax_lt`; templates CMS-B B5.1/B5.3/B5.4, `ShaveMaximalSet.lean`). For a compact
totally convex `C` with nonempty relative boundary `B`, the argmax set `C₁` of `d(·, B)` on `C` is
nonempty, compact, totally convex (superlevel set of the concave `d(·, B)`, REL binding), contained in
the relative interior `Z` (its value is `> 0`), and of strictly smaller relative dimension: a slice of
`C₁` of the relative dimension of `C` would agree with `C` near one of its points
(`maxSlice_eq_near_finite`), while the segment to a nearest point of `B` decreases `d(·, B)` at rate one.
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

/-- **DROP** (`3 ≤ r`, `sec ≥ 0`): one shaving step of the flag. The frozen D-CMS3 statement,
verbatim. -/
theorem maxSliceDimOfOrder_argmax_lt [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCc : IsCompact C) (hconv : IsTotallyConvexFinite g C)
    (hB : (relBoundaryOfOrder I (r : ℕ∞ω) C).Nonempty) :
    let C₁ := {x ∈ C | ∀ y ∈ C, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C)}
    C₁.Nonempty ∧ IsCompact C₁ ∧ IsTotallyConvexFinite g C₁ ∧
      C₁ ⊆ maxSliceLocusOfOrder I (r : ℕ∞ω) C ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) C₁ < maxSliceDimOfOrder I (r : ℕ∞ω) C := by
  intro C₁
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  have hCcl : IsClosed C := hCc.isClosed
  have hBcl : IsClosed B := isClosed_relBoundaryOfOrder g hr2 hnorm hCcl hconv
  have hCne : C.Nonempty := hB.mono relBoundaryOfOrder_subset
  have hfc : Continuous fun x : M => infDist x B := continuous_infDist_pt _
  obtain ⟨x₀, hx₀C, hx₀max⟩ := hCc.exists_isMaxOn hCne hfc.continuousOn
  have hmax : ∀ y ∈ C, infDist y B ≤ infDist x₀ B := fun y hy => hx₀max hy
  have hset : C₁ = {x ∈ C | infDist x₀ B ≤ infDist x B} := by
    ext x
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, hx x₀ hx₀C⟩
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, fun y hy => (hmax y hy).trans hx⟩
  have hC₁ne : C₁.Nonempty := ⟨x₀, hx₀C, hmax⟩
  have hC₁C : C₁ ⊆ C := fun x hx => hx.1
  have hC₁Z : C₁ ⊆ Z := by
    intro x hx
    obtain ⟨z, hzZ⟩ := maxSliceLocusOfOrder_nonempty (I := I) (k := r) hCne
    have hz : 0 < infDist z B := (hBcl.notMem_iff_infDist_pos hB).1 fun hzB => hzB.2 hzZ
    have hxpos : 0 < infDist x B := lt_of_lt_of_le hz (hx.2 z (maxSliceLocusOfOrder_subset hzZ))
    by_contra hxZ
    have hxB : x ∈ B := ⟨hx.1, hxZ⟩
    rw [infDist_zero_of_mem hxB] at hxpos
    exact lt_irrefl 0 hxpos
  refine ⟨hC₁ne, ?_, ?_, hC₁Z, ?_⟩
  · rw [hset]
    exact hCc.inter_right (isClosed_le continuous_const hfc)
  · rw [hset]
    exact isTotallyConvexFinite_superlevel_infDist_relBoundaryOfOrder g hr hnorm hsec hCcl hconv _
  · by_contra hge
    push Not at hge
    obtain ⟨N, ⟨x, hxN⟩, hNC₁, hN⟩ := exists_maxSliceOfOrder (I := I) (k := r) hC₁ne
    have hdim : maxSliceDimOfOrder I (r : ℕ∞ω) C₁ = maxSliceDimOfOrder I (r : ℕ∞ω) C :=
      le_antisymm (maxSliceDimOfOrder_mono hC₁C) hge
    rw [hdim] at hN
    obtain ⟨U, hU, hxU, hUeq⟩ := maxSlice_eq_near_finite g hr2 hnorm hconv hN (hNC₁.trans hC₁C) hxN
    have hxC₁ : x ∈ C₁ := hNC₁ hxN
    have hxZ : x ∈ Z := hC₁Z hxC₁
    have hl : 0 < infDist x B := (hBcl.notMem_iff_infDist_pos hB).1 fun hxB => hxB.2 hxZ
    obtain ⟨u, hu, hfoot⟩ := exists_unit_foot_of_isClosed g hr2 hnorm hBcl hB x
    obtain ⟨-, hτ⟩ := dist_infDist_expMap_smul_of_foot g hr2 hnorm hu hfoot
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    set t : ℝ := min (ε / 2) (infDist x B) with htdef
    have ht0 : 0 < t := lt_min (by linarith) hl
    have htl : t ≤ infDist x B := min_le_right _ _
    have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨hd, hf⟩ := hτ t ⟨ht0.le, htl⟩
    have htC : g.expMap (⟨x, t • u⟩ : TangentBundle I M) ∈ C :=
      hconv.expMap_mem hr2 hnorm hl.le hxC₁.1 (relBoundaryOfOrder_subset hfoot) t ⟨ht0.le, htl⟩
    have htU : g.expMap (⟨x, t • u⟩ : TangentBundle I M) ∈ U :=
      hball (by rw [mem_ball, dist_comm, hd]; exact htε)
    have htN : g.expMap (⟨x, t • u⟩ : TangentBundle I M) ∈ U ∩ N := by
      rw [← hUeq]; exact ⟨htU, htC⟩
    have hle := (hNC₁ htN.2).2 x hxC₁.1
    rw [hf] at hle
    linarith

end DifferentialGeometry.Geometry.FiniteSoul

end
