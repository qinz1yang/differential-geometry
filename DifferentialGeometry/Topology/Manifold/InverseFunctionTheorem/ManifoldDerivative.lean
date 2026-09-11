import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {x : M}

theorem MDifferentiableAt.isInvertible_mfderiv_iff
    (hf : MDifferentiableAt I J f x) :
    (mfderiv I J f x).IsInvertible ↔
      (fderiv 𝕜 (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible := by
  classical
  change (if MDifferentiableAt I J f x then
    fderivWithin 𝕜 (writtenInExtChartAt I J x f) (Set.range I) (extChartAt I x x)
    else (0 : E →L[𝕜] F)).IsInvertible ↔ _
  rw [if_pos hf, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]

section Real

variable {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {f : M → N} {U : Set M}

theorem ContMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hinv : ∀ x ∈ U, (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphOn I J n f U := by
  have hinv' : ∀ x ∈ U,
      (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible := by
    intro x hx
    exact ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
      ((zero_lt_one.trans_le hn).ne')).isInvertible_mfderiv_iff.mp (hinv x hx)
  by_cases hn' : n = ∞
  · subst n
    exact DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty
      hU hf hinv'
  · exact DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn hn hn'
      hU hf hinv'

end Real
