/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedNormalizedGradient
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalizedGraph

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- The single actual normalized-root tuple gives original-metric projection graph germs.
Their derivatives equal its literal normalized root gradient, for the one normal chosen
by the existing graph-germ producer. Every preceding tuple and slope bound is retained. -/
theorem DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_projection_graph_gradient
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
                ∀ w ∈ e.target, w ≠ 0 →
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
                      Analysis.complexPowerNormalizedGradient m Hroot w := by
  obtain ⟨m, B, hB, hBne, hfactor, hpositive, hrest⟩ :=
    DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_normalized_gradient_bounds
      hu hγ ha
  dsimp only at hrest
  obtain ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, hheight⟩ := hrest
  refine ⟨m, B, hB, hBne, hfactor, hpositive, ?_⟩
  dsimp only
  refine ⟨r, δ, hr, hδ, hsub, hchart, hreg, hcenter, hgap, hcover, hcard,
    ρ, hρ, hρr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower, hheight, ?_⟩
  let p := diskExtension u a
  let proj := chartLeadingPlaneProjection g p p (B a)
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
  let F : ℂ → ℂ := fun z => proj (X z)
  have hUgraph : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u)
      (Metric.ball a r) := hu.smoothInterior.mono (Metric.ball_subset_closedBall.trans hsub)
  have hnull := chartComplexGradient_leading_isotropic (E := E) (M := M) g
    (U := diskExtension u) (s := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
    (hu.smoothInterior.of_le (by norm_num)) hu.conformal
    (a := a) ha (p := p) (mem_chart_source E p) (m := m) (B := B)
    hB.continuousAt hfactor
  obtain ⟨N, hNN, hN, hsplit, hgerms⟩ :=
    chartLeadingPlaneProjection_exists_graph_germs (E := E) (M := M) g hd3
      (U := diskExtension u) (s := Metric.ball a r) Metric.isOpen_ball hUgraph
      (a := a) (Metric.mem_ball_self hr) (p := p)
      (fun z hz => hchart z (Metric.ball_subset_closedBall hz)) (b := B a) hBne hnull
      (fun z hz hza => hreg z (Metric.ball_subset_closedBall hz) hza)
  refine ⟨N, hNN, hN, hsplit, ?_⟩
  intro w hw hw0
  have hzρ : e.symm w ∈ Metric.ball a ρ := hesource ▸ e.map_target hw
  have hzr : e.symm w ∈ Metric.ball a r := Metric.ball_subset_ball hρr.le hzρ
  have hza : e.symm w ≠ a := by
    intro hza
    have hright := e.right_inv hw
    rw [hza, hea] at hright
    exact hw0 hright.symm
  obtain ⟨eGraph, hwGraph, hGraphSource, heGraph, heiGraph, hh, hgraph⟩ :=
    hgerms (e.symm w) hzr hza
  refine ⟨eGraph, hwGraph, hGraphSource, heGraph, heiGraph, hh, hgraph, ?_⟩
  have hpower (v : ℂ) (hv : v ∈ e.target) :
      F (e.symm v) = F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ) := by
    have hp := hepower (e.symm v) (e.map_target hv)
    rw [← congrFun he (e.symm v), e.right_inv hv] at hp
    exact hp
  exact chartLeadingPlaneProjection_graph_fderiv_eq_normalized_gradient
    g p (diskExtension u) a (B a) N m e eGraph heGraph hpower hh w hw hw0 hwGraph
