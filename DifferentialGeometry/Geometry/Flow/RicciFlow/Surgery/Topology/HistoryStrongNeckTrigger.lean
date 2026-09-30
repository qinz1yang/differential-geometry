import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornCanonicalNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessNeckExclusion

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_tolerance_historyStrongNeck_of_spatialNeck (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) {ε ε₁ eps : ℝ}
      {y : (H.stage k).Carrier} {t : ℝ},
      ε ≤ 1 / 1000 → H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t → eps ≤ eta →
      Nonempty (SpatialNeck (G.flow.base.metric t) eps y) →
      H.toHistory.HistoryStrongNeck k G ε₁ y t := by
  obtain ⟨eta, heta, hneck⟩ := exists_tolerance_alternative_eq_neck_of_spatialNeck.{u} C1 C2
  refine ⟨eta, heta, ?_⟩
  intro H k s G ε ε₁ eps y t hε hcan heps hnk
  obtain ⟨W, hW, himp⟩ := hcan
  obtain ⟨n, hn⟩ := hneck _ _ ε ε eps y W hW hε heps hnk
  exact himp ⟨n, hn⟩

theorem eventually_historyStrongNeck_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) (L : G.TerminalLimitMetric)
      (hsing : G.SingularEndpoint) (parameters : CutoffParameters) {εP Λ : ℝ}
      (P : TerminalCorePresentation
        { stage := H.stage k
          startTime := H.time k
          endTime := s
          startTime_nonneg := H.toHistory.time_nonneg k
          startTime_lt_endTime := G.lt
          slab := G
          terminal := L
          singular := hsing
          parameters := parameters } εP Λ), εP ≤ eta →
    ∀ (c : ConnectedComponents G.terminalRegularOpen) (e : P.hornIndex c)
      (x : G.terminalRegularOpen), x ∈ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ}, 0 < ε → ε ≤ eta →
      4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt L.metric x →
      qcan < metricScalarAt L.metric x →
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s →
      ∀ᶠ t in 𝓝[<] s, H.toHistory.HistoryStrongNeck k G ε₁ x.val t := by
  obtain ⟨eta, heta, hneck⟩ :=
    TerminalCorePresentation.eventually_neck_alternative_of_mem_hornHalfRange.{u}
  refine ⟨eta, heta, ?_⟩
  intro H k s G L hsing parameters εP Λ P hεP c e x hx ε ε₁ C1 C2 qcan hε hεη hscalar hq hcan
  have hev := hneck P hεP c e x hx (epsCan := ε) (C1 := C1) hε hεη hscalar
  have hhigh : ∀ᶠ t in 𝓝[<] s, qcan < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually_const_lt hq
  filter_upwards [hev, hhigh, Ioo_mem_nhdsLT G.lt] with t ht hqt hts
  obtain ⟨W, hW, himp⟩ := hcan x.val t hts hqt
  exact himp (ht W hW)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
