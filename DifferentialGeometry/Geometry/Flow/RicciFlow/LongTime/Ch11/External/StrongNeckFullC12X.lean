import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck

/-!
# Untruncated history strong necks (C12X, S16 G2a)

`HistoryStrongNeck` (`Surgery/Topology/HistoryStrongNeck`) records a `TruncatedNeck … (1 / 5)` on
the backward survivor flow.  Its two neck producers start from a depth-one `StrongNeck` and
truncate.  `HistoryStrongNeckFull_C12X` keeps the depth-one `StrongNeck` (time window
`[t - R⁻¹, t]`) and additionally records `H.time k ≤ t` and `H.time first ≤ t - R⁻¹`.
Every full neck projects to the tree predicate (`toHistoryStrongNeck_C12X`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- Depth-one analogue of `HistoryStrongNeck`: a full `StrongNeck` on the survivor flow. -/
def HistoryStrongNeckFull_C12X (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ) :
    Prop :=
  ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ k) (hts : H.time first < s)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle)),
    H.time k ≤ t ∧ H.time first ≤ t - (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ) ∧
    (∀ τ ∈ Ico (H.time k) s,
      gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle)) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)) ∧
    ∃ z : H.backwardSurvivorDomain first k hle, z.val = y ∧
      Nonempty (StrongNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
          (RealTimeInterval.closedOpen (H.time first) s hts)) eps z t)

variable {H : ObservedHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s} {eps : ℝ} {y : (H.stage k).Carrier} {t : ℝ}

/-- Accuracy monotonicity. -/
theorem HistoryStrongNeckFull_C12X.mono_eps (h : H.HistoryStrongNeckFull_C12X k G eps y t)
    {eps' : ℝ} (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    H.HistoryStrongNeckFull_C12X k G eps' y t := by
  obtain ⟨first, hle, hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, ⟨nk⟩⟩ := h
  exact ⟨first, hle, hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz,
    ⟨nk.mono heps hsmall⟩⟩

/-- Depth monotonicity: a full neck yields the survivor-flow truncated neck of every depth
`d ∈ (0, 1)`, with the matching start-time bound. -/
theorem HistoryStrongNeckFull_C12X.truncate (h : H.HistoryStrongNeckFull_C12X k G eps y t)
    {d : ℝ} (hd : 0 < d) (hd1 : d < 1) :
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ k) (hts : H.time first < s)
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle)),
      H.time first ≤ t - d * (G.flow.scalar t y)⁻¹ ∧
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
            (RealTimeInterval.closedOpen (H.time first) s hts)) eps d z t) := by
  obtain ⟨first, hle, hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, ⟨nk⟩⟩ := h
  have : SigmaCompactSpace (H.backwardSurvivorDomain first k hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first k hle).isOpen)
  have hR : 0 ≤ (({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)).scalar t z)⁻¹ :=
    inv_nonneg.mpr nk.Q_pos.le
  have hstart := nk.time_domain ⟨le_rfl, sub_le_self _ hR⟩
  have hend := nk.time_domain ⟨sub_le_self _ hR, le_rfl⟩
  have hreg : Ioo (t - (({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)).scalar t z)⁻¹) t ⊆
      (RealTimeInterval.closedOpen (H.time first) s hts).regular :=
    fun r hr => ⟨hstart.1.trans_lt hr.1, hr.2.trans hend.2⟩
  have hscal : (({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)).scalar t z) =
      G.flow.scalar t y := by
    change metricScalarAt (gflow t) z = metricScalarAt (G.flow.base.metric t) y
    rw [hcur t ⟨htk, hend.2⟩, metricScalarAt_restrictOpen, hz]
  have hRG : 0 ≤ (G.flow.scalar t y)⁻¹ := hscal ▸ hR
  refine ⟨first, hle, hts, gflow, hfirst.trans (sub_le_sub_left
      (mul_le_of_le_one_left hRG hd1.le) t), hslab, hcur, hsol, z, hz,
    ⟨TruncatedNeck.ofStrongNeck nk hd hd1.le fun b r hr w hw v =>
      nk.comparison_jet_differentiableWithinAt_of_lt_one hsol hd1 hreg b hr w hw v⟩⟩

/-- Projection to the tree predicate (depth `1 / 5`). -/
theorem HistoryStrongNeckFull_C12X.toHistoryStrongNeck_C12X
    (h : H.HistoryStrongNeckFull_C12X k G eps y t) : H.HistoryStrongNeck k G eps y t :=
  h.truncate (by norm_num) (by norm_num)

/-- Slab producer: a depth-one strong neck of the incoming slab flow is a full history neck
(`first := k`); untruncated analogue of `historyStrongNeck_of_strongNeck`. -/
theorem historyStrongNeckFull_of_strongNeck_C12X (H : ObservedHistory.{u})
    (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    {eps : ℝ} {y : (H.stage k).Carrier} {t : ℝ} (nk : StrongNeck G.flow eps y t) :
    H.HistoryStrongNeckFull_C12X k G eps y t := by
  let U := H.backwardSurvivorDomain k k le_rfl
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hR : 0 ≤ (G.flow.scalar t y)⁻¹ := inv_nonneg.mpr nk.Q_pos.le
  have hstart := nk.time_domain ⟨le_rfl, sub_le_self _ hR⟩
  have hend := nk.time_domain ⟨sub_le_self _ hR, le_rfl⟩
  refine ⟨k, le_rfl, G.lt, fun τ => (G.flow.base.metric τ).restrictOpen U, hend.1, hstart.1,
    ?_, fun _ _ => rfl,
    DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen G.flow G.equation U,
    ⟨y, H.mem_backwardSurvivorDomain_self k y⟩, rfl,
    ⟨nk.restrictOpen (x := ⟨y, H.mem_backwardSurvivorDomain_self k y⟩) (fun _ => rfl)
      (fun p _ => H.mem_backwardSurvivorDomain_self k p)⟩⟩
  intro j hf hl
  exact absurd (hl.trans hf) (not_le.mpr j.castSucc_lt_succ)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
