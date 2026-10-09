import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TruncatedNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

def HistoryStrongNeck (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ) :
    Prop :=
  ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ k) (hts : H.time first < s)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle)),
    H.time first ≤ t - 1 / 5 * (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ) ∧
    (∀ τ ∈ Ico (H.time k) s,
      gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle)) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)) ∧
    ∃ z : H.backwardSurvivorDomain first k hle, z.val = y ∧
      Nonempty (TruncatedNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
          (RealTimeInterval.closedOpen (H.time first) s hts)) eps (1 / 5) z t)

theorem mem_backwardSurvivorDomain_self (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1))
    (y : (H.stage k).Carrier) : y ∈ H.backwardSurvivorDomain k k le_rfl :=
  ⟨BackwardPointTrace.singleton H k y⟩

theorem historyStrongNeck_of_strongNeck (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1))
    {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) {eps : ℝ} {y : (H.stage k).Carrier}
    {t : ℝ} (nk : StrongNeck G.flow eps y t) : H.HistoryStrongNeck k G eps y t := by
  let U := H.backwardSurvivorDomain k k le_rfl
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hR : 0 ≤ (G.flow.scalar t y)⁻¹ := inv_nonneg.mpr nk.Q_pos.le
  have hstart := nk.time_domain ⟨le_rfl, sub_le_self _ hR⟩
  have hend := nk.time_domain ⟨sub_le_self _ hR, le_rfl⟩
  have hreg : Ioo (t - (G.flow.scalar t y)⁻¹) t ⊆
      (RealTimeInterval.closedOpen (H.time k) s G.lt).regular :=
    fun r hr => ⟨hstart.1.trans_lt hr.1, hr.2.trans hend.2⟩
  let tk : TruncatedNeck G.flow eps (1 / 5) y t := TruncatedNeck.ofStrongNeck nk (by norm_num)
    (by norm_num) fun b r hr z hz v =>
      nk.comparison_jet_differentiableWithinAt_of_lt_one G.equation (by norm_num) hreg b hr z hz v
  refine ⟨k, le_rfl, G.lt, fun τ => (G.flow.base.metric τ).restrictOpen U,
    (tk.time_domain ⟨le_rfl, sub_le_self _ (mul_nonneg (by norm_num) hR)⟩).1, ?_, fun _ _ => rfl,
    DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen G.flow G.equation U,
    ⟨y, H.mem_backwardSurvivorDomain_self k y⟩, rfl,
    ⟨tk.restrictOpen (x := ⟨y, H.mem_backwardSurvivorDomain_self k y⟩) (fun _ => rfl)
      (fun p _ => H.mem_backwardSurvivorDomain_self k p)⟩⟩
  intro j hf hl
  exact absurd (hl.trans hf) (not_le.mpr j.castSucc_lt_succ)

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

def StronglyCanonicalAt (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 : ℝ) (y : (H.stage k).Carrier)
    (t : ℝ) : Prop :=
  ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε ∧
    ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeck k G ε₁ y t)

def StronglyCanonicalBefore (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan t₀ : ℝ) : Prop :=
  ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) t₀ → qcan < G.flow.scalar t y →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def StronglyCanonicalOn (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan t₀ η : ℝ) : Prop :=
  ∀ y t, H.time k < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def StronglyCanonicalWhere (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan : ℝ)
    (S : (H.stage k).Carrier → ℝ → Prop) : Prop :=
  ∀ y t, t ∈ Ioo (H.time k) s → qcan < G.flow.scalar t y → S y t →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def EventSlabsStronglyCanonical (ε ε₁ C1 C2 qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    H.StronglyCanonicalBefore j.castSucc (H.toHistory.event j).incoming ε ε₁ C1 C2 qcan
      (H.time j.succ)

variable {H} {k : Fin (H.eventCount + 1)} {s : ℝ} {G : (H.stage k).IncomingSlab (H.time k) s}
  {ε ε₁ C1 C2 qcan t₀ : ℝ}

theorem StronglyCanonicalBefore.spatiallyCanonicalBefore
    (h : H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀) :
    G.SpatiallyCanonicalBefore ε C1 C2 qcan t₀ :=
  fun y t ht hR => (h y t ht hR).imp fun _ hW => hW.1

theorem StronglyCanonicalBefore.of_threshold_le {q q' : ℝ} (hq : q ≤ q')
    (h : H.StronglyCanonicalBefore k G ε ε₁ C1 C2 q t₀) :
    H.StronglyCanonicalBefore k G ε ε₁ C1 C2 q' t₀ :=
  fun y t ht hR => h y t ht (hq.trans_lt hR)

theorem stronglyCanonicalBefore_of_where_cover {S₁ S₂ S₃ : (H.stage k).Carrier → ℝ → Prop}
    (h₁ : H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan S₁)
    (h₂ : H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan S₂)
    (h₃ : H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan S₃)
    (hcover : ∀ y t, S₁ y t ∨ S₂ y t ∨ S₃ y t) :
    H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s :=
  fun y t ht hR => (hcover y t).elim (h₁ y t ht hR) fun h => h.elim (h₂ y t ht hR) (h₃ y t ht hR)

theorem stronglyCanonicalWhere_of_canonicalBefore (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) {τmin : ℝ} (hε : ε ≤ ε₁) (hε₁ : ε₁ < 1 / 11)
    (hG : G.CanonicalBefore ε C1 C2 qcan τmin s) :
    H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan
      fun y t => τmin ≤ G.flow.scalar t y * (t - H.time k) := by
  intro y t ht hR hτ
  obtain ⟨W, hW⟩ := hG y t ht hR hτ
  refine ⟨W.toSpatial, W.capTubeHasNeckChart_toSpatial hW, fun ⟨n, hn⟩ => ?_⟩
  change W.alternative.toSpatial = SpatialCanonicalAlternative.neck n at hn
  cases halt : W.alternative with
  | neck data =>
    exact H.toHistory.historyStrongNeck_of_strongNeck k G (data.strong.mono hε hε₁)
  | cap data deep =>
    rw [halt] at hn
    cases hn
  | positive whole data sec =>
    rw [halt] at hn
    cases hn
  | round whole data =>
    rw [halt] at hn
    cases hn

theorem StronglyCanonicalWhere.mono_constants {S : (H.stage k).Carrier → ℝ → Prop}
    {C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (h : H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan S) :
    H.StronglyCanonicalWhere k G ε ε₁ C1' C2' qcan S := by
  intro y t ht hR hS
  obtain ⟨W, hW, hn⟩ := h y t ht hR hS
  refine ⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2, fun ⟨n, hn'⟩ => hn ?_⟩
  change W.alternative.monoConstant (zero_lt_one.trans_le W.one_le_comparison_constant) hC2
    W.Q_pos.le = SpatialCanonicalAlternative.neck n at hn'
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep =>
    rw [halt] at hn'
    cases hn'
  | positive whole data sec =>
    rw [halt] at hn'
    cases hn'
  | round whole data =>
    rw [halt] at hn'
    cases hn'

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
