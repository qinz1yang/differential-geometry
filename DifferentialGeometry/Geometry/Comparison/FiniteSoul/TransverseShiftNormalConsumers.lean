import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftNormalExists
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftBound

/-!
# S-SHIFT2 with its normal field (the form consumed by S-SHAVE)

`exists_transverse_shift_lipschitz_dim_two`: for a complete `C^(r+1)` metric, `r ≥ 3`, `sec ≥ 0`, on a
surface, a point `x` and `L`, there is `ρ > 0` such that for every unit `p` with `d(x, π p) < ρ` and every
unit `w ⊥ p` there is a unit normal field `ξ` along `γ t = π φ_t(p)` with `ξ 0 = w`, and every shifted
curve `t ↦ exp_{γ t}(h ξ t)`, `0 ≤ h < ρ`, is `1`-Lipschitz on `[0, L]`. This is the finite replacement
of the pair (`exists_isParallelPerpUnitField`, `HasParallelShiftBound`) used by the smooth
`hasOrthogonalBoundaryShift_relBoundary`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **S-SHIFT2 with the normal field.** -/
theorem exists_transverse_shift_lipschitz_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
                |t₁ - t₂| := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ (le_trans (by norm_num) hr) hnorm
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  obtain ⟨ρ, hρ, hb⟩ := dist_transverse_shift_le_dim_two_of_Ioo g hr hnorm hsec hdim x L
  refine ⟨ρ, hρ, fun p hxp hp w hw hwp => ?_⟩
  obtain ⟨ξ, hξc, hξ, hξ0⟩ := exists_unitNormal_dim_two g hr1 hdim p (fun t => hmem _) hp hw hwp
    (a := -1) (b := |L| + 1) (by norm_num) (by positivity)
  have hsub : Ioo (-1 : ℝ) (L + 1) ⊆ Icc (-1) (|L| + 1) := fun t ht =>
    ⟨ht.1.le, ht.2.le.trans (by linarith [le_abs_self L])⟩
  have hsub' : Icc (0 : ℝ) L ⊆ Icc (-1) (|L| + 1) := fun t ht =>
    ⟨by linarith [ht.1], ht.2.trans (by linarith [le_abs_self L])⟩
  exact ⟨ξ, hξ0, fun t ht => hξ t (hsub' ht),
    hb p hxp hp ξ (hξc.mono hsub) (fun t ht => (hξ t (hsub ht)).1)
      (fun t ht => (hξ t (hsub ht)).2)⟩

end DifferentialGeometry.Geometry.FiniteSoul
