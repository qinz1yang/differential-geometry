import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftBound

/-!
# Consumers of S-SHIFT2

* `dist_transverse_shift_start_le`: the form used by the orthogonal boundary shift (S-SHAVE): the
  shifted point at time `t` is within `t` of the shifted starting point `exp_{γ 0}(h ξ 0)`.
* The verbatim frozen interface statement of `dist_transverse_shift_le_dim_two` (design §4.2, scratch
  `FiniteSoulInterfaces.lean`, with its full variable block and `hL : 0 < L`) as an `example`.
* A sanity instance of the scalar comparison kernel (`k = 0`, `j = 1`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- **Consumer (S-SHAVE form).** The shifted point at time `t ∈ [0, L]` is within `t` of the shifted
start `exp_{γ 0}(h ξ 0)`, for `0 ≤ h < ρ`, uniformly near `x`. -/
theorem dist_transverse_shift_start_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ ξ : ℝ → E,
        Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) →
        ∀ h ∈ Ico 0 ρ, ∀ t ∈ Icc 0 L,
          dist (g.expMap (⟨(g.geodesicFlow p 0).proj, h • ξ 0⟩ : TangentBundle I M))
            (g.expMap (⟨(g.geodesicFlow p t).proj, h • ξ t⟩ : TangentBundle I M)) ≤ t := by
  obtain ⟨ρ, hρ, hb⟩ := dist_transverse_shift_le_dim_two g hr hnorm hsec hdim x L
  refine ⟨ρ, hρ, fun p hxp hp ξ hcont hunit hperp h hh t ht => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, ht.1.trans ht.2⟩
  have := hb p hxp hp ξ hcont hunit hperp h hh 0 h0 t ht
  rwa [zero_sub, abs_neg, abs_of_nonneg ht.1] at this

/-- The frozen interface (design §4.2), verbatim, including `hL` and the full variable block. -/
example (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (x : M) : ∀ {L : ℝ}, 0 < L →
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ ξ : ℝ → E,
        Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) →
        (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) →
        ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
          dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
            (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
              |t₁ - t₂| :=
  fun {L} _ => dist_transverse_shift_le_dim_two g hr hnorm hsec hdim x L

/-- Sanity instance of the scalar kernel: the constant solution of `j'' = 0`. -/
example : ∀ s ∈ Ico (0 : ℝ) 1, 1 / 2 ≤ (fun _ : ℝ => (1 : ℝ)) s ∧ (fun _ : ℝ => (1 : ℝ)) s ≤ 1 :=
  DifferentialGeometry.Analysis.scalarJacobi_mem_Icc (k := fun _ => 0) (Λ := 0) le_rfl
    (by norm_num) continuousOn_const rfl (by simp)
    (fun s _ _ => ⟨by simpa using hasDerivAt_const s (1 : ℝ), by simpa using hasDerivAt_const s (0 : ℝ)⟩)
    (fun _ _ => ⟨le_rfl, le_rfl⟩)

end DifferentialGeometry.Geometry.FiniteSoul
