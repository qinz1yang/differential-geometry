import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNativeLayerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformClassDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepTransportHistoryC12X

/-!
# Native layer of the uniform full strong-neck supply, record-hypothesis form (C12X, S16 round 3)

O-C12X-S16K G3b.  Same as `native_strongFull_of_classFull_C12X` (S16E, `StrongNativeLayerC12X`)
with the S16B per-class theorem replaced by the uniform producer v2
`strong_necks_full_uniform_of_youngWindowDeep_C12X` for the route β′ record hypothesis
`RecordHypFar_C12X θ` (spec v3 D4):

* the constants are the uniform pair `max C1 (max Ccore Cu)`, `max C2 (max (max Ccore Cu) Cgrad)`,
  `Ccore` chosen before `P₀ g₀ B` and `Cu` the window constant;
* the native history carries `RecordHypFar_C12X θ K records`; each prefix `K.prefixAt k` gets it
  for `K.prefixRecords k records` (`RecordHypFar_C12X.prefixRecords_C12X`);
* the capacity is used as in S16E: every prefix horizon `time k < s ≤ K.horizon ≤ B` is strictly
  below `B` (spec v2 §2.2 "plan A" is automatic here).

This is the engine the class preparer (NC/PreparedClosedBirthClass, S16PROD p3) switches to in the
spec v3 round; conditional on the window input, not counted as S16 supplied.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **Uniform native layer (v3 engine).** -/
theorem native_strongFull_uniform_of_classFull_C12X (θ : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hεs : ε ≤ εStrong_C12X.{u}) (D₀ θ₀ : ℝ) (hD₀ : 0 < D₀) (hθ₀ : θ₀ < 1) :
    ∃ Ccore : ℝ, 1 ≤ Ccore ∧ ∀ Cu : ℝ,
    HwinYoungDeep_C12X (fun H _ records => RecordHypFar_C12X.{u} θ H records) ε D₀ θ₀ Cu →
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ), 0 < B →
    ∀ (C1 C2 C1s C2s qcan qs τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ),
      1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → qcan ≤ qs → 0 < τmin → 0 < κ →
    ∃ (qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      qs ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ K.toHistory →
      ∀ (pK : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        RecordHypFar_C12X θ K records →
        K.NoncollapsedBefore κ ε K.horizon →
        GC.GeneralFlow.NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad →
        K.EventSlabsStronglyCanonicalFull_C12X ε ε (max C1 (max Ccore Cu))
          (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh (Fin.last K.eventCount) ∧
        ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
          K.StronglyCanonicalBeforeFull_C12X (Fin.last K.eventCount)
            ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε (max C1 (max Ccore Cu))
          (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh
            K.horizon := by
  obtain ⟨Ccore, hCcore, hU⟩ := strong_necks_full_uniform_of_youngWindowDeep_C12X
    (fun H _ records => RecordHypFar_C12X.{u} θ H records) ε hε hεs D₀ θ₀ hD₀ hθ₀
  refine ⟨Ccore, hCcore, fun Cu hwin => ?_⟩
  intro P₀ g₀ B hB C1 C2 C1s C2s qcan qs τmin Ctime Cgrad κ hC1 hC2 hC1s hC2s hqcan hqs hτ hκ
  obtain ⟨phi, hphi, hpin⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  obtain ⟨qh, δmax, ρmax, εcap, Dcap, mcap, hqh, hδ, hρ, hεc, hD, hX⟩ :=
    hU Cu hwin P₀ g₀ B hB C1 C2 C1s C2s qs τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s
      (hqcan.trans_le hqs) hτ hκ hphi
  refine ⟨qh, δmax, ρmax, εcap, Dcap, mcap, hqh, hδ, hρ, hεc, hD, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb hΛ K IK pK records hKB hfam hrecHyp hnc hest
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
      K.StronglyCanonicalBeforeFull_C12X k G ε ε (max C1 (max Ccore Cu))
          (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh s := by
    intro k s G hG0 hks hsK hcanG hderG hgradG hspatG hterm
    have hH : (K.prefixAt k).InCutoffClass g₀ B p₀ δbound ρbound := by
      have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))
          (0 : Fin (k.val + 1)) = 0 := Fin.ext (by simp)
      refine ⟨⟨InitialIdentification.ofStageZero IK (congrArg K.stage hc)
        (congr_arg_heq K.initialMetric hc)⟩, rfl, (hks.trans_le hsK).trans_le hKB, ?_, hΛ⟩
      exact ((K.prefixAt k).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
        p₀ δbound ρbound).mpr
          ⟨pK, K.prefixRecords k records, K.isCanonicalCutoffRecordFamily_prefixAt k hfam⟩
    have hres := (hX p₀ δbound ρbound hacc hrad hord hδb hρb (K.prefixAt k) hH pK
      (K.prefixRecords k records) (K.isCanonicalCutoffRecordFamily_prefixAt k hfam)
      (hrecHyp.prefixRecords_C12X k) (K.eventSlabsPinched_prefixAt k hpinK)
      (K.eventSlabsCanonical_prefixAt k (hcanK k))
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
