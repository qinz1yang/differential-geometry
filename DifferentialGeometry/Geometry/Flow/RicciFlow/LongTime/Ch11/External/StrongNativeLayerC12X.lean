import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullClassC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullTransportC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixInvariants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinalSlabNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData

/-!
# Native layer of the full strong-neck supply (C12X, S16 G6, part a)

`native_strongFull_of_classFull_C12X` applies the S16B class theorem
`strong_necks_full_of_cutoff_class_C12X` to a *native* history `K` (astra `NativeEstimates` form,
no `time last = horizon` requirement): every event slab and the final slab of `K` is strongly
canonical with full history necks, accuracy `ε` on the diagonal.

* Each slab is treated as the continuation slab of a prefix: event slab `j` on
  `K.prefixAt j.castSucc`, the final slab on `K.prefixAt (Fin.last _)`; the result is moved back to
  `K` by `historyStrongNeckFull_of_prefixAt_C12X` (S16B).
* Pinching is not a hypothesis: `phi` is the Hamilton–Ivey function of the initial data
  (`Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs`, depends on `P₀ g₀`).
* Threshold alignment (R-S16 D-4): `NativeEstimates` carries the derivative / gradient / canonical
  bounds above `qcan` and the spatial bound above `qs`; the class theorem is fed the common
  threshold `qs` (`qcan ≤ qs` raises the first three), and its output threshold has `qs ≤ qh`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {H : RetainedCoreHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s}

/-- `StronglyCanonicalBeforeFull_C12X` is monotone in the constants `C1 C2` and the threshold. -/
theorem stronglyCanonicalBeforeFull_mono_C12X {ε ε₁ C1 C2 C1' C2' q q' t₀ : ℝ}
    (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hq : q ≤ q')
    (h : H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1 C2 q t₀) :
    H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1' C2' q' t₀ := by
  intro y t ht hR
  obtain ⟨W, hW, hn⟩ := h y t ht (hq.trans_lt hR)
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

/-- A slab statement on the prefix `H.prefixAt k` (its last stage) is one on `H` at stage `k`. -/
theorem stronglyCanonicalBeforeFull_of_prefixAt_C12X {ε ε₁ C1 C2 q t₀ : ℝ}
    (h : (H.prefixAt k).StronglyCanonicalBeforeFull_C12X (Fin.last (H.prefixAt k).eventCount) G
      ε ε₁ C1 C2 q t₀) :
    H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1 C2 q t₀ :=
  fun y t ht hR => (h y t ht hR).imp fun _ hW =>
    ⟨hW.1, fun hn => H.historyStrongNeckFull_of_prefixAt_C12X k G (hW.2 hn)⟩

end RetainedCoreHistory

/-- **S16 G6 (native layer)**: the class Full theorem on a native history.  For the class inputs
`(P₀, g₀, B, ε, C1, C2, C1s, C2s, qcan ≤ qs, τmin, Ctime, Cgrad, κ)` there are constants
`C1h C2h qh` (with `qs ≤ qh`) and smallness thresholds such that every native history `K` of the
class (initial identification, canonical cutoff records, `K.horizon ≤ B`, noncollapsing, astra
`NativeEstimates`) has full strong necks on every event slab and on its final slab. -/
theorem native_strongFull_of_classFull_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (hεs : ε ≤ εStrong_C12X.{u})
    (C1 C2 C1s C2s qcan qs τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ)
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hC1s : 1 ≤ C1s) (hC2s : 1 ≤ C2s) (hqcan : 0 < qcan)
    (hqs : qcan ≤ qs) (hτ : 0 < τmin) (hκ : 0 < κ) :
    ∃ (C1h C2h qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      1 ≤ C1h ∧ 1 ≤ C2h ∧ qs ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ K.toHistory →
      ∀ (pK : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        GC.GeneralFlow.NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad →
        K.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last K.eventCount) ∧
        ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
          K.StronglyCanonicalBeforeFull_C12X (Fin.last K.eventCount)
            ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
            K.horizon := by
  obtain ⟨phi, hphi, hpin⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  obtain ⟨C1h, C2h, qh, δmax, ρmax, εcap, Dcap, mcap, hC1h, hC2h, hqh, hδ, hρ, hεc, hD, hX⟩ :=
    strong_necks_full_of_cutoff_class_C12X P₀ g₀ B ε hB hε hεs C1 C2 C1s C2s qs τmin Ctime Cgrad
      κ phi hC1 hC2 hC1s hC2s (hqcan.trans_le hqs) hτ hκ hphi
  refine ⟨C1h, C2h, qh, δmax, ρmax, εcap, Dcap, mcap, hC1h, hC2h, hqh, hδ, hρ, hεc, hD, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb hΛ K IK pK records hKB hfam hnc hest
  have hcanK : ∀ k, K.EventSlabsCanonical ε C1 C2 qs τmin k := fun _ j _ =>
    (K.toHistory.event j).incoming.canonicalBefore_of_threshold_le hqs (hest.1 j).2.2.1
  have hderK : ∀ k, K.EventSlabsDerivative Ctime qs k := fun _ j _ =>
    (K.toHistory.event j).incoming.derivativeBoundBefore_of_threshold_le hqs (hest.1 j).1
  have hgradK : ∀ k, K.EventSlabsGradient Cgrad qs k := fun _ j _ =>
    (K.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le hqs (hest.1 j).2.1
  have hspatK : ∀ k, K.EventSlabsSpatiallyCanonical ε C1s C2s qs k := fun _ j _ =>
    (hest.1 j).2.2.2
  have hpinK : K.EventSlabsPinched phi := fun j =>
    hpin K.toHistory IK pK records j.castSucc (K.time j.succ) (K.toHistory.event j).incoming
      (K.event_initial j)
  -- every slab of `K` is the continuation slab of the prefix ending at its initial stage
  have key : ∀ (k : Fin (K.eventCount + 1)) (s : ℝ) (G : (K.stage k).IncomingSlab (K.time k) s)
      (hG0 : G.flow.base.metric (K.time k) = K.initialMetric k), K.time k < s → s ≤ K.horizon →
      G.CanonicalBefore ε C1 C2 qs τmin s → G.DerivativeBoundBefore Ctime qs s →
      G.GradientBoundBefore Cgrad qs s → G.SpatiallyCanonicalBefore ε C1s C2s qs s →
      (∀ t₀ ∈ Ioo (K.time k) s, (K.prefixAt k).TerminalNoncollapsedBefore rfl G hG0 κ ε t₀) →
      K.StronglyCanonicalBeforeFull_C12X k G ε ε C1h C2h qh s := by
    intro k s G hG0 hks hsK hcanG hderG hgradG hspatG hterm
    have hH : (K.prefixAt k).InCutoffClass g₀ B p₀ δbound ρbound := by
      have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))
          (0 : Fin (k.val + 1)) = 0 := Fin.ext (by simp)
      refine ⟨⟨InitialIdentification.ofStageZero IK (congrArg K.stage hc)
        (congr_arg_heq K.initialMetric hc)⟩, rfl, (hks.trans_le hsK).trans_le hKB, ?_, hΛ⟩
      exact ((K.prefixAt k).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
        p₀ δbound ρbound).mpr
          ⟨pK, K.prefixRecords k records, K.isCanonicalCutoffRecordFamily_prefixAt k hfam⟩
    have hres := (hX p₀ δbound ρbound hacc hrad hord hδb hρb (K.prefixAt k) hH
      (K.eventSlabsPinched_prefixAt k hpinK) (K.eventSlabsCanonical_prefixAt k (hcanK k))
      (K.eventSlabsDerivative_prefixAt k (hderK k)) (K.eventSlabsGradient_prefixAt k (hgradK k))
      (K.eventSlabsSpatiallyCanonical_prefixAt k (hspatK k))
      (K.noncollapsedBefore_prefixAt k hnc (hks.le.trans hsK))).2 s G ⟨hsK.trans hKB, hG0⟩
      (hpin K.toHistory IK pK records k s G hG0) hcanG hderG hgradG hspatG hterm
    exact RetainedCoreHistory.stronglyCanonicalBeforeFull_of_prefixAt_C12X hres
  refine ⟨fun j _ => ?_, fun hfinal => ?_⟩
  · have hsK : K.time j.succ ≤ K.horizon :=
      (K.time_strictMono.monotone (Fin.le_last _)).trans K.time_le_horizon
    exact key j.castSucc (K.time j.succ) (K.toHistory.event j).incoming (K.event_initial j)
      (K.time_strictMono Fin.castSucc_lt_succ) hsK (hcanK _ j (Fin.castSucc_lt_last j))
      (hderK _ j (Fin.castSucc_lt_last j)) (hgradK _ j (Fin.castSucc_lt_last j))
      (hest.1 j).2.2.2 fun t₀ ht₀ => K.terminalNoncollapsedBefore_prefixAt j
        (K.noncollapsedBefore_mono (ht₀.2.le.trans hsK) hnc)
  · obtain ⟨hderF, hgradF, hcanF, hspatF⟩ := hest.2 hfinal
    have hfin := K.terminalNoncollapsedBefore_finalSlab hfinal hnc
    exact key (Fin.last _) K.horizon _ (K.final_initial hfinal) hfinal le_rfl
      (OrientedThreeStage.IncomingSlab.canonicalBefore_of_threshold_le _ hqs hcanF)
      (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _ hqs hderF)
      (OrientedThreeStage.IncomingSlab.gradientBoundBefore_of_threshold_le _ hqs hgradF) hspatF
      fun t₀ ht₀ T hT hTs hTt => hfin T hT hTs (hTt.trans ht₀.2.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
