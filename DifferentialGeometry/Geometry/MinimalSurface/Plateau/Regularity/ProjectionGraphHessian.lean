/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProjectionGraphGradient
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientGraphHessian

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- The original Morrey disk's single root tuple supplies a common punctured
radius and Hessian bound for its fixed local projection graph germs. Every
previous tuple property and the same selected unit normal are retained. -/
theorem DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_projection_graph_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
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
                    LipschitzOnWith (3 * K).toNNReal R (Metric.ball (0 : ℂ) ε)) ∧
              let Q := chartGramBilin g p p
              let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
              let lift : ℂ → E := fun v => (chartModelBasis E).equivFunL.symm
                (fun i => (2 : ℝ) * (v * B a i).re)
              ∃ N : E,
                Q N N = 1 ∧ proj N = 0 ∧
                (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
                (∀ w ∈ e.target, w ≠ 0 →
                  ∃ eGraph : OpenPartialHomeomorph ℂ ℂ,
                    e.symm w ∈ eGraph.source ∧ eGraph.source ⊆ Metric.ball a r \ {a} ∧
                    (eGraph : ℂ → ℂ) = F ∧
                    ContDiffOn ℝ ∞ (eGraph.symm : ℂ → ℂ) eGraph.target ∧
                    let h : ℂ → ℝ := fun y => Q N (X (eGraph.symm y) - X a)
                    let Hroot : ℂ → ℝ := fun v => Q N (X (e.symm v) - X a)
                    ContDiffOn ℝ ∞ h eGraph.target ∧
                    (∀ y ∈ eGraph.target,
                      X (eGraph.symm y) = X a + lift (y - F a) + h y • N) ∧
                    fderiv ℝ h (F (e.symm w)) =
                      Analysis.complexPowerNormalizedGradient m Hroot w) ∧
                (1 ≤ m →
                  let H : ℂ → ℝ := fun v => Q N (X (e.symm v) - X a)
                  let R := Analysis.complexPowerNormalizedGradient m H
                  ∃ ε > 0, ∃ K > 0,
                    Metric.ball (0 : ℂ) ε ⊆ e.target ∧
                    (∀ w ∈ Metric.ball (0 : ℂ) ε, ‖R w‖ ≤ K * ‖w‖) ∧
                    (∀ w ∈ Metric.ball (0 : ℂ) ε, w ≠ 0 →
                      DifferentiableAt ℝ R w ∧ ‖fderiv ℝ R w‖ ≤ K) ∧
                    LipschitzOnWith (3 * K).toNNReal R (Metric.ball (0 : ℂ) ε) ∧
                    ∀ w ∈ Metric.ball (0 : ℂ) ε, w ≠ 0 →
                      ∃ eGraph : OpenPartialHomeomorph ℂ ℂ,
                        e.symm w ∈ eGraph.source ∧
                        eGraph.source ⊆ Metric.ball a r \ {a} ∧
                        (eGraph : ℂ → ℂ) = F ∧
                        ContDiffOn ℝ ∞ (eGraph.symm : ℂ → ℂ) eGraph.target ∧
                        let h : ℂ → ℝ := fun y => Q N (X (eGraph.symm y) - X a)
                        ContDiffOn ℝ ∞ h eGraph.target ∧
                        (∀ y ∈ eGraph.target,
                          X (eGraph.symm y) = X a + lift (y - F a) + h y • N) ∧
                        fderiv ℝ h (F (e.symm w)) = R w ∧
                        ((fun v : ℂ => fderiv ℝ h
                          (F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ))) =ᶠ[𝓝 w] R) ∧
                        fderiv ℝ (fderiv ℝ h) (F (e.symm w)) =
                          (fderiv ℝ R w).comp
                            (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)) ∧
                        ‖fderiv ℝ (fderiv ℝ h) (F (e.symm w))‖ ≤ K / ‖w‖ ^ m) := by
  obtain ⟨m, B, hB, hBne, hfactor, hpositive, hrest⟩ :=
    DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_projection_graph_gradient
      hu hγ hd3 ha
  dsimp only at hrest
  obtain ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, hheight, N, hNN, hN, hsplit, hgraphs⟩ := hrest
  refine ⟨m, B, hB, hBne, hfactor, hpositive, ?_⟩
  dsimp only
  refine ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, hheight, N, hNN, hN, hsplit, hgraphs, ?_⟩
  intro hm
  let p := diskExtension u a
  let Q := chartGramBilin g p p
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
  let H : ℂ → ℝ := fun v => Q N (X (e.symm v) - X a)
  let R := Analysis.complexPowerNormalizedGradient m H
  obtain ⟨hpower, _, _, _, _, _, ε0, hε0, K, hK, hsize, hder, hLip⟩ :=
    hheight hm N hN
  have hsize' : ∀ w ∈ Metric.ball (0 : ℂ) ε0, ‖R w‖ ≤ K * ‖w‖ := hsize
  have hder' : ∀ w ∈ Metric.ball (0 : ℂ) ε0, w ≠ 0 →
      DifferentiableAt ℝ R w ∧ ‖fderiv ℝ R w‖ ≤ K := hder
  have hLip' : LipschitzOnWith (3 * K).toNNReal R (Metric.ball (0 : ℂ) ε0) := hLip
  have hasource : a ∈ e.source := by
    rw [hesource]
    exact Metric.mem_ball_self hρ
  have h0target : (0 : ℂ) ∈ e.target := by
    rw [← hea]
    exact e.map_source hasource
  obtain ⟨s, hs, hstarget⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds h0target)
  let ε := min ε0 s
  have hε : 0 < ε := lt_min hε0 hs
  have hsubε : Metric.ball (0 : ℂ) ε ⊆ Metric.ball (0 : ℂ) ε0 :=
    Metric.ball_subset_ball (min_le_left ε0 s)
  have htarget : Metric.ball (0 : ℂ) ε ⊆ e.target :=
    (Metric.ball_subset_ball (min_le_right ε0 s)).trans hstarget
  refine ⟨ε, hε, K, hK, htarget, ?_, ?_, hLip'.mono hsubε, ?_⟩
  · intro w hw
    exact hsize' w (hsubε hw)
  · intro w hw hw0
    exact hder' w (hsubε hw) hw0
  · intro w hw hw0
    obtain ⟨eGraph, hwGraph, hGraphSource, heGraph, heiGraph, hh, hgraph, hgradient⟩ :=
      hgraphs w (htarget hw) hw0
    refine ⟨eGraph, hwGraph, hGraphSource, heGraph, heiGraph, hh, hgraph, hgradient, ?_⟩
    obtain ⟨hnear, _, hsecond, hnorm⟩ :=
      chartLeadingPlaneProjection_graph_second_fderiv_eq_normalized_gradient
        g p (diskExtension u) a (B a) N m e eGraph heGraph hpower hh
        w (htarget hw) hw0 hwGraph
    refine ⟨hnear, hsecond, hnorm.trans ?_⟩
    exact div_le_div_of_nonneg_right (hder' w (hsubε hw) hw0).2
      (pow_nonneg (norm_nonneg w) m)
