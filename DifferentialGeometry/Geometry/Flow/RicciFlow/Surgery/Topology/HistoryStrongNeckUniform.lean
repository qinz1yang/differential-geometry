import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornCanonicalNeckUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalFineNeckOfSpatialNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckOpenSubset

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

def TruncatedNeck.toSpatialNeck {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps depth : ℝ} {x : M} {t : ℝ} (nk : TruncatedNeck S eps depth x t) :
    SpatialNeck (S.base.metric t) eps x := by
  let C := nk.comparison.singleton
    (show (0 : ℝ) ∈ Set.Icc (-depth) 0 from ⟨by linarith [nk.depth_pos], le_rfl⟩)
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := nk.Q_pos
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    comparison := {
      pullback := fun _ => C.pullback 0
      pullback_eq := ?_
      jet := fun b _ => C.jet b 0
      jet_zero := ?_
      jet_succ := ?_
      equivalence := ?_
      close := ?_ } }
  · intro s y hy v
    have hscale : S.scalar t x = metricScalarAt (S.base.metric t) x := rfl
    simpa only [rescaledMetric, parabolicTime_zero, hscale] using C.pullback_eq 0 y hy v
  · intro s y v
    exact C.jet_zero 0 y v
  · intro b s hs y hy v
    have h := C.jet_succ b 0 (by simp) y hy v
    have hz : derivWithin (fun a => C.jet b a y v) ({0} : Set ℝ) 0 = 0 := by
      apply derivWithin_zero_of_not_accPt
      rw [accPt_iff_clusterPt, Filter.inf_principal]
      simp [ClusterPt]
    rw [hz] at h
    simpa only [derivWithin_fun_const, Pi.zero_apply] using h
  · intro s hs y hy v
    exact C.equivalence 0 (by simp) y hy v
  · intro a b hab s hs y hy
    exact C.close a b hab 0 (by simp) y hy

theorem TruncatedNeck.toSpatialNeck_map {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps depth : ℝ} {x : M} {t : ℝ}
    (nk : TruncatedNeck S eps depth x t) : nk.toSpatialNeck.map = nk.map :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace ObservedHistory

theorem nonempty_spatialNeck_of_historyStrongNeck (H : ObservedHistory.{u})
    (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) {eps : ℝ}
    {y : (H.stage k).Carrier} {t : ℝ} (h : H.HistoryStrongNeck k G eps y t)
    (ht : H.time k ≤ t) : Nonempty (SpatialNeck (G.flow.base.metric t) eps y) := by
  obtain ⟨first, hle, hts, gflow, -, -, hG, -, z, hz, ⟨nk⟩⟩ := h
  have hts' : t < s := (nk.time_domain
    ⟨sub_le_self _ (mul_nonneg nk.depth_pos.le (inv_nonneg.mpr nk.Q_pos.le)), le_rfl⟩).2
  have hmetric : gflow t =
      (G.flow.base.metric t).restrictOpen (H.backwardSurvivorDomain first k hle) :=
    hG t ⟨ht, hts'⟩
  let sn : SpatialNeck (gflow t) eps z := nk.toSpatialNeck
  subst hz
  exact ⟨(hmetric ▸ sn).ofRestrictOpen⟩

theorem exists_normalizedNeck_of_frequently_historyStrongNeck (H : ObservedHistory.{u})
    (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hx : 0 < metricScalarAt L.metric x) {εc eps : ℝ} (hεc : 0 < εc) (hεc1 : εc < 1)
    (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∃ᶠ t in 𝓝[<] s, H.HistoryStrongNeck k G eps x.val t) :
    ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x := by
  apply L.exists_normalizedNeck_of_frequently_spatialNeck x hx hεc hεc1 hfit
  apply (h.and_eventually (Ioo_mem_nhdsLT G.lt)).mono
  intro t ht
  exact H.nonempty_spatialNeck_of_historyStrongNeck k G ht.1 ht.2.1.le

end ObservedHistory

namespace RetainedCoreHistory

theorem eventually_forall_historyStrongNeck_of_subset_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (k : Fin (H.eventCount + 1))
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
      {B : Set G.terminalRegularOpen}, IsCompact B → B ⊆ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ}, 0 < ε → ε ≤ eta →
      (∀ x ∈ B, 4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt L.metric x) →
      (∀ x ∈ B, qcan < metricScalarAt L.metric x) →
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s →
      ∀ᶠ t in 𝓝[<] s, ∀ x ∈ B, H.toHistory.HistoryStrongNeck k G ε₁ x.val t := by
  obtain ⟨eta, heta, hneck⟩ :=
    TerminalCorePresentation.eventually_forall_neck_alternative_of_subset_hornHalfRange.{u}
  refine ⟨eta, heta, ?_⟩
  intro P₀ H k s G L hsing parameters εP Λ P hεP c e B hB hBsub ε ε₁ C1 C2 qcan hε hεη hscalar
    hq hcan
  have hev := hneck P hεP c e hB hBsub (epsCan := ε) (C1 := C1) hε hεη hscalar
  have hhigh : ∀ᶠ t in 𝓝[<] s, ∀ x ∈ B, qcan < G.flow.scalar t x.val := by
    rcases B.eq_empty_or_nonempty with hemp | hne
    · exact Eventually.of_forall fun t x hx => by simp [hemp] at hx
    have hcont : Continuous (metricScalarAt L.metric) :=
      (metricScalar_smooth L.metric).continuous
    obtain ⟨m, hm, hmin⟩ := hB.exists_isMinOn hne hcont.continuousOn
    have hgap : 0 < metricScalarAt L.metric m - qcan := sub_pos.mpr (hq m hm)
    filter_upwards [L.eventually_scalar_close_on_compact hB hgap] with t ht
    intro x hx
    have hc := abs_lt.mp (ht x hx)
    have hmx : metricScalarAt L.metric m ≤ metricScalarAt L.metric x := hmin hx
    change qcan < metricScalarAt (G.flow.base.metric t) x.val
    linarith [hc.1]
  filter_upwards [hev, hhigh, Ioo_mem_nhdsLT G.lt] with t ht hqt hts
  intro x hx
  obtain ⟨W, hW, himp⟩ := hcan x.val t hts (hqt x hx)
  exact himp (ht x hx W hW)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
