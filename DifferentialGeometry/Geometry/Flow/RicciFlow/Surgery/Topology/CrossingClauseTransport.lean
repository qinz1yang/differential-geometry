import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalWitnessTimeRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem canonical_clauses_of_base_eq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D D' : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (F : SolutionOn (I := I3) (M := M) D') (hbase : S.base = F.base)
    (hD : D.carrier ⊆ D'.carrier) {ε C1 C2 τ a t : ℝ} {Ctime Cgrad : ℝ≥0} {x : M}
    (hwit : τ ≤ S.scalar t x * (t - a) →
      ∃ W : CanonicalWitness S ε C1 C2 x t, W.capTubeHasNeckChart ε)
    (hder : |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ Ctime * S.scalar t x ^ 2)
    (hgrad : ∀ v : TangentSpace I3 x,
      |Perelman.CanonicalNeighborhood.scalarDifferential S t x v| ≤
        Cgrad * S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) :
    (τ ≤ F.scalar t x * (t - a) →
        ∃ W : CanonicalWitness F ε C1 C2 x t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => F.scalar v x) (Iic t) t| ≤ Ctime * F.scalar t x ^ 2 ∧
      ∀ v : TangentSpace I3 x,
        |Perelman.CanonicalNeighborhood.scalarDifferential F t x v| ≤
          Cgrad * F.scalar t x * Real.sqrt (F.scalar t x) *
            Real.sqrt ((F.base.metric t).inner x v v) := by
  obtain ⟨b⟩ := F
  subst hbase
  refine ⟨fun hage => ?_, hder, hgrad⟩
  obtain ⟨W, hW⟩ := hwit hage
  exact ⟨W.timeRestrict hD, hW.timeRestrict hD⟩

private theorem canonical_clauses_upgrade {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    {ε C C1 C2 τ₀ τmin a t : ℝ} {Ctime Cgrad : ℝ≥0} {x : M} (h1 : C ≤ C1) (h2 : C ≤ C2)
    (h3 : C ≤ Ctime) (h4 : C ≤ Cgrad) (hτ : τ₀ ≤ τmin)
    (hwit : τ₀ ≤ S.scalar t x * (t - a) →
      ∃ W : CanonicalWitness S ε C C x t, W.capTubeHasNeckChart ε)
    (hder : |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ C * S.scalar t x ^ 2)
    (hgrad : ∀ v : TangentSpace I3 x,
      |Perelman.CanonicalNeighborhood.scalarDifferential S t x v| ≤
        C * S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) :
    (τmin ≤ S.scalar t x * (t - a) →
        ∃ W : CanonicalWitness S ε C1 C2 x t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ Ctime * S.scalar t x ^ 2 ∧
      ∀ v : TangentSpace I3 x,
        |Perelman.CanonicalNeighborhood.scalarDifferential S t x v| ≤
          Cgrad * S.scalar t x * Real.sqrt (S.scalar t x) *
            Real.sqrt ((S.base.metric t).inner x v v) := by
  refine ⟨fun hage => ?_, hder.trans (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)),
    fun v => (hgrad v).trans ?_⟩
  · obtain ⟨W, hW⟩ := hwit (hτ.trans hage)
    exact ⟨W.enlargeConstants h1 h2, hW.enlarge_constants h1 h2⟩
  · have hnn : 0 ≤ S.scalar t x * Real.sqrt (S.scalar t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := by
      refine mul_nonneg ?_ (Real.sqrt_nonneg _)
      rcases le_total 0 (S.scalar t x) with hR | hR
      · exact mul_nonneg hR (Real.sqrt_nonneg _)
      · rw [Real.sqrt_eq_zero'.mpr hR, mul_zero]
    calc C * S.scalar t x * Real.sqrt (S.scalar t x) * Real.sqrt ((S.base.metric t).inner x v v)
        = C * (S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) := by ring
      _ ≤ Cgrad * (S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) := mul_le_mul_of_nonneg_right h4 hnn
      _ = _ := by ring

private theorem canonical_clauses_of_closedPrefixAt {K : ObservedHistory.{u}}
    {τ : Icc (0 : ℝ) K.horizon} (hlt : K.time (K.activeStage τ) < τ)
    (k : Fin (K.eventCount + 1)) (hk : K.activeStage τ = k) {D : RealTimeInterval}
    (F : SolutionOn (I := I3) (M := (K.stage k).Carrier) D)
    (hF : ∀ v, F.base.metric v = K.stageMetric k v) (hD : Icc (K.time k) (τ : ℝ) ⊆ D.carrier)
    (ŷ : (K.stage (K.activeStage τ)).Carrier) (y : (K.stage k).Carrier) (hy : HEq ŷ y)
    {ε C1 C2 τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hwit : τmin ≤ (K.closedPrefixAt τ hlt).flow.scalar τ ŷ *
        ((τ : ℝ) - K.time (K.activeStage τ)) →
      ∃ W : CanonicalWitness (K.closedPrefixAt τ hlt).flow ε C1 C2 ŷ τ,
        W.capTubeHasNeckChart ε)
    (hder : |derivWithin (fun v => (K.closedPrefixAt τ hlt).flow.scalar v ŷ) (Iic (τ : ℝ)) τ| ≤
      Ctime * (K.closedPrefixAt τ hlt).flow.scalar τ ŷ ^ 2)
    (hgrad : ∀ v : TangentSpace I3 ŷ,
      |Perelman.CanonicalNeighborhood.scalarDifferential (K.closedPrefixAt τ hlt).flow τ ŷ v| ≤
        Cgrad * (K.closedPrefixAt τ hlt).flow.scalar τ ŷ *
          Real.sqrt ((K.closedPrefixAt τ hlt).flow.scalar τ ŷ) *
          Real.sqrt (((K.closedPrefixAt τ hlt).flow.base.metric τ).inner ŷ v v)) :
    (τmin ≤ F.scalar τ y * ((τ : ℝ) - K.time k) →
        ∃ W : CanonicalWitness F ε C1 C2 y τ, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => F.scalar v y) (Iic (τ : ℝ)) τ| ≤ Ctime * F.scalar τ y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential F τ y v| ≤
          Cgrad * F.scalar τ y * Real.sqrt (F.scalar τ y) *
            Real.sqrt ((F.base.metric τ).inner y v v) := by
  subst hk
  cases hy
  have hbase : (K.closedPrefixAt τ hlt).flow.base = F.base := by
    change SolutionFamily.mk _ = SolutionFamily.mk _
    congr 1
    funext v
    rw [K.closedPrefixAt_metric τ hlt v, hF v]
  exact canonical_clauses_of_base_eq _ F hbase hD hwit hder hgrad

theorem RetainedCoreHistory.canonical_clauses_of_extendAt
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hy : HEq ŷ y)
    (hlt : (H.extendAt hend G hG hat hts).toHistory.time
      ((H.extendAt hend G hG hat hts).toHistory.activeStage (H.extendAtTime hend G hG hat hts)) <
        (H.extendAtTime hend G hG hat hts : ℝ))
    {ε C C1 C2 τ₀ τmin : ℝ} {Ctime Cgrad : ℝ≥0} (h1 : C ≤ C1) (h2 : C ≤ C2)
    (h3 : C ≤ Ctime) (h4 : C ≤ Cgrad) (hτ : τ₀ ≤ τmin) :
    (τ₀ ≤ ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
          (H.extendAtTime hend G hG hat hts) hlt).flow.scalar t ŷ *
        (t - (H.extendAt hend G hG hat hts).toHistory.time
          ((H.extendAt hend G hG hat hts).toHistory.activeStage
            (H.extendAtTime hend G hG hat hts))) →
      ∃ W : CanonicalWitness ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
          (H.extendAtTime hend G hG hat hts) hlt).flow ε C C ŷ t,
        W.capTubeHasNeckChart ε) →
    |derivWithin (fun v => ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
        (H.extendAtTime hend G hG hat hts) hlt).flow.scalar v ŷ) (Iic t) t| ≤
      C * ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
        (H.extendAtTime hend G hG hat hts) hlt).flow.scalar t ŷ ^ 2 →
    (∀ v : TangentSpace I3 ŷ,
      |Perelman.CanonicalNeighborhood.scalarDifferential
          ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
            (H.extendAtTime hend G hG hat hts) hlt).flow t ŷ v| ≤
        C * ((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
            (H.extendAtTime hend G hG hat hts) hlt).flow.scalar t ŷ *
          Real.sqrt (((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
            (H.extendAtTime hend G hG hat hts) hlt).flow.scalar t ŷ) *
          Real.sqrt ((((H.extendAt hend G hG hat hts).toHistory.closedPrefixAt
            (H.extendAtTime hend G hG hat hts) hlt).flow.base.metric t).inner ŷ v v)) →
    (τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
        ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
          Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
            Real.sqrt ((G.flow.base.metric t).inner y v v) := by
  intro hwit hder hgrad
  obtain ⟨hwit', hder', hgrad'⟩ :=
    canonical_clauses_upgrade _ h1 h2 h3 h4 hτ hwit hder hgrad
  have hk := H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
    (H.extendAtTime hend G hG hat hts) hat.le
  exact canonical_clauses_of_closedPrefixAt hlt (Fin.last H.eventCount) hk G.flow
    (fun v => (H.stageMetric_extendHorizon_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      hat v).symm)
    (fun v hv => ⟨hv.1, hv.2.trans_lt hts⟩) ŷ y hy hwit' hder' hgrad'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
