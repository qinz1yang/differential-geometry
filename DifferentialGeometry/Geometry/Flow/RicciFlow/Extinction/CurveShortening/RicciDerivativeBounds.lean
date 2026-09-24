import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BackgroundBounds

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

omit [SigmaCompactSpace M] in
theorem RicciBackground.exists_iterCov_ricci_bound
    [I.Boundaryless] [CompactSpace M]
    (B : RicciBackground (I := I) (M := M) D a b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Icc a b, ∀ p : M,
        normSq0S (B.family.metric t) p (2 + m)
          (iterCov (B.family.metric t) 2 (B.family.ricci t) m p) ≤ C ^ 2 := by
  let F : SolutionOn (I := I) (M := M) D := ⟨B.family⟩
  obtain ⟨_, _, hbound⟩ := rfs_csf_background F B.equation B.lt B.regular
  obtain ⟨K, _, hRm⟩ := hbound m
  let N : ℝ := (Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2) * K ^ 2
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  let C : ℝ := N + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro t ht p
  have htower := ricTower_normSq_le F t m p
  change normSq0S (B.family.metric t) p (2 + m)
      (iterCov (B.family.metric t) 2 (B.family.ricci t) m p) ≤
    (Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2) *
      normSq0S (B.family.metric t) p (4 + m)
        (nablaKRm04Field F t m p) at htower
  have hboundN : normSq0S (B.family.metric t) p (2 + m)
      (iterCov (B.family.metric t) 2 (B.family.ricci t) m p) ≤ N :=
    htower.trans (mul_le_mul_of_nonneg_left (hRm t ht p)
      (by positivity : 0 ≤ (Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)))
  exact hboundN.trans (by
    dsimp only [C]
    nlinarith only [hN, sq_nonneg (N + 1)])

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
