import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftGeneral

/-!
# Consumers of the general-dimension transverse shift (lane CMS3-SHIFT, group G3)

* `transverseShift_hypothesis_of_sectional_nonneg`: the inline hypothesis `hshift` of the frozen A1
  (`exists_orthogonal_boundary_shift_of_transverseShift`) and of CMS-B's route, in every dimension: the
  output shape of CMS-J's `exists_transverse_shift_lipschitz_dim_two` without `hdim`.
* Example: CMS-J's two-dimensional statement re-derived from the general one.
* Example: the verbatim frozen statement of `exists_transverse_shift_lipschitz` (with the unused
  instance `[NeZero (finrank ℝ E)]`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The transverse-shift hypothesis of the top-dimensional shave (A1), in every dimension.** -/
theorem transverseShift_hypothesis_of_sectional_nonneg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
                |t₁ - t₂| := by
  intro x L
  obtain ⟨ρ, hρ, hb⟩ := exists_transverse_shift_lipschitz g hr hnorm hsec x L
  refine ⟨ρ, hρ, fun p hxp hp w hw hwp => ?_⟩
  obtain ⟨ξ, hξ0, -, -, hξu, hξL⟩ := hb p hxp hp w hw hwp
  exact ⟨ξ, hξ0, fun t _ => hξu t, hξL⟩

/-- CMS-J's two-dimensional S-SHIFT2 (`exists_transverse_shift_lipschitz_dim_two`) re-derived from the
general-dimension binding (`hdim` is not needed). -/
example (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (_hdim : Module.finrank ℝ E = 2) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
                |t₁ - t₂| :=
  transverseShift_hypothesis_of_sectional_nonneg g hr hnorm hsec x L

/-- The frozen statement of `exists_transverse_shift_lipschitz`, verbatim. -/
example [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ ∧
          Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) ∧
          (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂| :=
  exists_transverse_shift_lipschitz g hr hnorm hsec x L

end DifferentialGeometry.Geometry.FiniteSoul
