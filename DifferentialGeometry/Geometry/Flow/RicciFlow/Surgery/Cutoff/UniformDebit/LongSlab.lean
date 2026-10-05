import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Cutoff.Horn.UniformFactory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecksLongSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.UniformEstimates

open private exists_horn_cutoff_record_of_fineCutNecks_of_le fineCutNecks_of_le
  hasCanonicalCutoffRecords_of_le exists_compact_volume_debit_of_incoming_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Cutoff.Horn.UniformFactory

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem uniformDebitSurgeryStepStrong_of_long_slabs
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hlong : ∀ B θ : ℝ, 0 < B → 0 < θ → ∃ Qθ : ℝ,
      ∀ H : RetainedCoreHistory.{u}, InitialIdentification P₀ g₀ H.toHistory → H.horizon < B →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B → G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
        ∀ Qc : ℝ, Qθ ≤ Qc → 2 * θ ≤ Qc * (s - H.time (Fin.last H.eventCount))) :
    UniformDebitSurgeryStepStrong P₀ g₀ := by
  obtain ⟨eta, εcone, heta, hεcone, hB12⟩ :=
    TerminalCorePresentation.exists_fineCutNecks_of_long_terminal_slab.{u}
  obtain ⟨fixed, c, hc, εP, εF, hεP, hεPη, hεF, hεF11, hF⟩ :=
    exists_horn_cutoff_record_of_fineCutNecks_of_le P₀ g₀ eta heta
  obtain ⟨Φ, hΦ, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  intro B εbar hB hεbar
  refine ⟨c, by linarith, ?_⟩
  intro Ctime
  have hε : 0 < min εbar (min εF εcone) := lt_min hεbar (lt_min hεF hεcone)
  have hεεF : min εbar (min εF εcone) ≤ εF := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min εbar (min εF εcone), hε, hεεF.trans_lt hεF11, min_le_left _ _, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ _ _ _ hC2s hqcan _
    hδmax hρmax hεcap hDcap hκ _
  obtain ⟨r, hr⟩ : ∃ r : ℝ, StandardCap.transitionEnd + (1 / 1000 : ℝ)⁻¹ + 1 < r :=
    ⟨_, lt_add_one _⟩
  obtain ⟨Dtrace, hDtrace⟩ : ∃ Dtrace : ℝ, 64 * (r + (1 / 1000 : ℝ)⁻¹) < Dtrace :=
    ⟨_, lt_add_one _⟩
  obtain ⟨εold, δold, hεold, hδold, hF⟩ := hF Dtrace (max Dcap (Dtrace + 1)) r (1 / 1000)
    Ctime (le_max_right _ _) (by norm_num) le_rfl hr hDtrace
  obtain ⟨δ, εcut, -, -, hδη, hεcut, -, hF⟩ :=
    hF (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) (min εold εcap) (lt_min hεold hεcap)
      (min δold δmax) (lt_min hδold hδmax)
  have hεc : 0 < min εcut (1 / 4) := lt_min hεcut (by norm_num)
  obtain ⟨K, θ, hK, hθ, hfineK⟩ := hB12 hκ hε C1s C2s Ctime Cgrad hΦ (min εbar (min εF εcone))
    ((min_le_right _ _).trans (min_le_right _ _)) hεc
    ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨Qθ, hQθ⟩ := hlong B θ hB hθ
  obtain ⟨C, Λ, -, -, hF⟩ := hF C1s C2s hC2s
  have hρb : 0 < min ρmax 1 := lt_min hρmax one_pos
  have hKfine : 0 ≤ max K Qθ := le_max_of_le_left (zero_le_one.trans hK)
  obtain ⟨Q, v, -, hv, -, hF⟩ := hF qcan (1 / 2 * min ρmax 1) 1 (max K Qθ) hqcan
    (by positivity) one_pos hKfine
  obtain ⟨p₀, hpf, hpD, hpm, hpa, hpc, hpδ, hpρ, hpp⟩ : ∃ p₀ : CutoffParameters,
      p₀.fixed = fixed ∧ p₀.modelRadius = max Dcap (Dtrace + 1) ∧
      p₀.modelOrder = max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2) ∧
      p₀.modelAccuracy = min εold εcap ∧ p₀.recenterConstant = c ∧
      p₀.delta = (fun _ => 1 / 2) ∧ p₀.neckRadius = (fun _ => min ρmax 1) ∧
      p₀.protectedRadius = (fun _ => 1) :=
    ⟨{ delta := fun _ => 1 / 2
       neckRadius := fun _ => min ρmax 1
       protectedRadius := fun _ => 1
       delta_pos := fun _ _ => by norm_num
       delta_lt_one := fun _ _ => by norm_num
       neckRadius_pos := fun _ _ => hρb
       protectedRadius_pos := fun _ _ => one_pos
       fixed := fixed
       modelRadius := max Dcap (Dtrace + 1)
       modelRadius_pos := lt_max_of_lt_left hDcap
       modelOrder := max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)
       modelAccuracy := min εold εcap
       modelAccuracy_pos := lt_min hεold hεcap
       recenterConstant := c
       recenterConstant_ge_four := hc }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨p₀, min δold δmax, min ρmax 1, v, hpa ▸ min_le_right _ _, hpD ▸ le_max_left _ _,
    hpm ▸ le_max_left _ _, lt_min hδold hδmax, min_le_right _ _, hρb, min_le_left _ _,
    hpc.le, hv, ?_⟩
  intro H initial hend hhor hclass hderH _ _ _ _ _ s G hs hG hsing hderG hgradG _ hspatG hncG
  obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
  have hclassF : H.hasCanonicalCutoffRecords p₀ δold (min ρmax 1) :=
    hasCanonicalCutoffRecords_of_le (min_le_left _ _) le_rfl hclass
  have hspatF : G.SpatiallyCanonicalBefore εF C1s C2s qcan s :=
    G.spatiallyCanonicalBefore_mono_eps hεεF hεF11 hspatG
  have hpin : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time (Fin.last H.eventCount)) s) Φ ∧ H.EventSlabsPinched Φ := by
    obtain ⟨p', -, -, -, -, -, records, -⟩ := hclass
    exact ⟨hpinch H.toHistory initial p' records (Fin.last H.eventCount) s G hG,
      fun j => hpinch H.toHistory initial p' records j.castSucc (H.time j.succ) _
        (H.event_initial j)⟩
  have hderEv : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) :=
    fun j _ y t ht hy => hderH j y t ht hy
  have hs0 : 0 ≤ s := (H.toHistory.time_nonneg _).trans G.lt.le
  classical
  choose ρ hρ hρle hρantitone hρantitoneOn hρrecenter hρprotected P hcoreRadius hcoreLower
    hcoreUpper hprotectedCore hhornBoundary Qout E hOld K' initialK i parameters n δO kO NO hδO
    rot hmark side hord hδ1 Nrec eO hQpos hEG hEL hbfr hprefix hhorizon heventCount hlastTime
    hlastStage hlastMetric hi hsourceStage hsourceTime htargetStage htargetTime hcoreEvent
    happend hpδ' hprotectedRadius hpρ' hpf' hpc' hpm' hpD' hpa' hprotectedInterior
    hretainedMeets hneckScale hneckPrecision hneckRecipe htube hrecord hvol hcapScalarLower using
    hF p₀ hpD (by rw [hpm]; exact le_max_right _ _) (by rw [hpa]; exact min_le_left _ _) H
      initial hend (min ρmax 1) hclassF s G L hsing p₀ hG hderH hderG
      (by change _ ≤ p₀.delta s * p₀.neckRadius s; rw [hpδ, hpρ])
      (by change _ ≤ p₀.protectedRadius s; rw [hpp]) hspatF
      (fun ρ' hρ' P' hKQ => by
        have hM : 1 ≤ max (Λ * (P'.coreRadius ^ 2)⁻¹) (max qcan 1) :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hKQ' : K * max (Λ * (P'.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q :=
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hM)).trans hKQ
        have hQθQ : Qθ ≤ Q :=
          (le_max_right K Qθ).trans ((le_mul_of_one_le_right hKfine hM).trans hKQ)
        exact fineCutNecks_of_le hεc (min_le_left _ _)
          (hfineK H hend G L hsing (p₀.withNeckRadius ρ' hρ') hG qcan hderEv
            (fun y t ht hy => hderG y t ht hy) hgradG hpin.2 hpin.1 hspatG hncG P' hεPη Q hKQ'
            (hQθ H initial hhor s G hs hG hsing Q hQθQ)))
  clear hρantitone hρantitoneOn hρrecenter hρprotected hcoreRadius hcoreLower hcoreUpper
    hprotectedCore hhornBoundary hQpos hprefix hhorizon heventCount hlastTime hlastStage
    hlastMetric hsourceStage hsourceTime htargetStage htargetTime hcoreEvent hprotectedRadius
    hprotectedInterior hretainedMeets hneckScale hneckPrecision hneckRecipe htube
    hcapScalarLower
  obtain ⟨Record, -, -, -, -, hwin, hstdE, -, -⟩ := hrecord
  obtain ⟨Eappend, hOldAppend, hInitial, hHEq, hK⟩ := happend
  have hEE := eq_of_heq hHEq
  subst hEE
  subst hK
  have hi' : i = Fin.last H.eventCount := Fin.ext hi
  subst hi'
  refine ⟨Qout, Eappend.toRetainedCoreEvent hOldAppend, hInitial, parameters, hEG, ?_,
    hpf'.trans hpf.symm, hpD'.trans hpD.symm, hpm'.trans hpm.symm, hpa'.trans hpa.symm,
    hpc'.trans hpc.symm, ⟨Record⟩, hbfr, hstdE, ?_⟩
  · exact H.hasCanonicalCutoffRecords_appendEvent _ (Eappend.toRetainedCoreEvent hOldAppend)
      hInitial hclass Record (hpf'.trans hpf.symm) (hpD'.trans hpD.symm) (hpm'.trans hpm.symm)
      (hpa'.trans hpa.symm) (hpc'.trans hpc.symm) hwin ((congrFun hpδ' s).le.trans hδη)
      ((congrFun hpρ' s).le.trans ((hρle s hs0).trans (congrFun hpρ s).le))
  · exact exists_compact_volume_debit_of_incoming_eq Eappend G L hEG hEL _ hvol

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
