import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedNormalHessian
import DifferentialGeometry.Analysis.Complex.NormalizedGradient

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- The same actual Morrey branched-coordinate tuple also controls its normalized
normal-height slope. Every coefficient, coordinate and height from the Hessian
supplier is retained. The slope is Lipschitz through zero and differentiable away
from zero; no derivative at zero or original-disk rank conclusion is asserted. -/
theorem DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_normalized_gradient_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    ∃ (m : ℕ) (B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)),
      ContDiffAt ℝ 1 B a ∧ B a ≠ 0 ∧
      (∀ᶠ z in 𝓝 a,
        (fun k => chartComplexGradient (E := E)
          (diskExtension u a) (diskExtension u) k z) = (z - a) ^ m • B z) ∧
      (¬ Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a) → 1 ≤ m) ∧
      let p := diskExtension u a
      let proj := chartLeadingPlaneProjection g p p (B a)
      let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
      ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
        Metric.closedBall a r ⊆ Metric.ball (0 : ℂ) 1 ∧
        (∀ z ∈ Metric.closedBall a r, diskExtension u z ∈ (chartAt E p).source) ∧
        (∀ z ∈ Metric.closedBall a r, z ≠ a → (fderiv ℝ F z).IsInvertible) ∧
        (∀ z ∈ Metric.closedBall a r, F z = F a ↔ z = a) ∧
        (∀ z ∈ Metric.sphere a r, δ < ‖F z - F a‖) ∧
        let f : Metric.closedBall a r → ℂ := fun z => F z.val
        let S : Set ℂ := Metric.ball (F a) δ \ {F a}
        IsCoveringMap (S.restrictPreimage f) ∧
          (∀ y ∈ S, (f ⁻¹' {y}).encard = ((m + 1 : ℕ) : ℕ∞)) ∧
          let Ψ : ℂ → ℂ := fun z =>
            if z = a then 0 else
              (z - a) * Complex.exp
                (Complex.log
                  (((m + 1 : ℕ) : ℂ) * (F z - F a) / (z - a) ^ (m + 1)) /
                    ((m + 1 : ℕ) : ℂ))
          ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
            ∃ e : OpenPartialHomeomorph ℂ ℂ,
              e.source = Metric.ball a ρ ∧
              (e : ℂ → ℂ) = Ψ ∧ e a = 0 ∧
              HasFDerivAt Ψ (ContinuousLinearMap.id ℝ ℂ) a ∧
              ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source ∧
              ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target ∧
              ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}) ∧
              ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}) ∧
              (∀ z ∈ e.source,
                F z = F a + Ψ z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) ∧
              (1 ≤ m → ∀ N : E, proj N = 0 →
                let Q := chartGramBilin g p p
                let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
                let H : ℂ → ℝ := fun w => Q N (X (e.symm w) - X a)
                (∀ w ∈ e.target,
                  F (e.symm w) = F a + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) ∧
                  ContDiffAt ℝ 2 H 0 ∧ fderiv ℝ H 0 = 0 ∧
                  fderiv ℝ (fderiv ℝ H) 0 = 0 ∧
                  (∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
                    ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) ∧
                  let R := Analysis.complexPowerNormalizedGradient m H
                  R 0 = 0 ∧ ∃ ε > 0, ∃ K > 0,
                    (∀ w ∈ Metric.ball (0 : ℂ) ε, ‖R w‖ ≤ K * ‖w‖) ∧
                    (∀ w ∈ Metric.ball (0 : ℂ) ε, w ≠ 0 →
                      DifferentiableAt ℝ R w ∧ ‖fderiv ℝ R w‖ ≤ K) ∧
                    LipschitzOnWith (3 * K).toNNReal R (Metric.ball (0 : ℂ) ε)) := by
  obtain ⟨m, B, hB, hBne, hfactor, hpositive, hrest⟩ :=
    DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_normalized_height_hessian_bound
      hu hγ ha
  dsimp only at hrest
  obtain ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, hheight⟩ := hrest
  refine ⟨m, B, hB, hBne, hfactor, hpositive, ?_⟩
  dsimp only
  refine ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, ?_⟩
  intro hm N hN
  have hnormal := hheight hm N hN
  obtain ⟨hprojection, hC2, hD0, hDD0, hbound⟩ := hnormal
  exact ⟨hprojection, hC2, hD0, hDD0, hbound,
    Analysis.exists_normalized_gradient_bounds_of_hessian_order hm hC2 hD0 hbound⟩
