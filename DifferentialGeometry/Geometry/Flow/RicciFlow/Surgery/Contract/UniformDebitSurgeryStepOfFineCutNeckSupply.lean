import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory

open private exists_horn_cutoff_record_of_fineCutNecks_of_le fineCutNecks_of_le
  hasCanonicalCutoffRecords_of_le exists_compact_volume_debit_of_incoming_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory

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

def FineCutNeckSupply (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
  ∀ (κ C1s C2s qcan a₀ : ℝ) (Ctime Cgrad : ℝ≥0) (ε : ℝ),
    0 < κ → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < a₀ → 0 < ε → ε ≤ εcone →
  ∃ (Rrad ζ₀ δ₀ ρ₀ : ℝ) (m₀ : ℕ), 0 < ζ₀ ∧ 0 < δ₀ ∧ 0 < ρ₀ ∧
  ∀ εc : ℝ, 0 < εc → εc < 1 / 2 →
  ∃ Kfine : ℝ, 1 ≤ Kfine ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
    Rrad ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    δbound ≤ δ₀ → ρbound ≤ ρ₀ →
  ∀ H : RetainedCoreHistory.{u}, InitialIdentification P₀ g₀ H.toHistory →
  ∀ hend : H.time (Fin.last H.eventCount) = H.horizon,
    H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan (H.time j.succ)) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
  ∀ {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)),
    G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
    G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
    (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
      H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
  ∀ {εP Λ : ℝ} (P : TerminalCorePresentation
      { stage := H.stage (Fin.last H.eventCount)
        startTime := H.time (Fin.last H.eventCount)
        endTime := s
        startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
        startTime_lt_endTime := G.lt
        slab := G
        terminal := L
        singular := hsing
        parameters := parameters } εP Λ), εP ≤ eta →
  ∀ Qc : ℝ, Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Qc →
    P.FineCutNecks εc Qc

theorem uniformDebitSurgeryStepStrong_of_fineCutNeckSupply
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hfine : FineCutNeckSupply P₀ g₀) :
    UniformDebitSurgeryStepStrong P₀ g₀ := by
  obtain ⟨eta, εcone, heta, hεcone, hsupply⟩ := hfine
  obtain ⟨fixed, c, hc, εP, εF, hεP, hεPη, hεF, hεF11, hF⟩ :=
    exists_horn_cutoff_record_of_fineCutNecks_of_le P₀ g₀ eta heta
  intro B εbar hB hεbar
  refine ⟨c, by linarith, ?_⟩
  intro Ctime
  have hε : 0 < min εbar (min εF εcone) := lt_min hεbar (lt_min hεF hεcone)
  have hεεF : min εbar (min εF εcone) ≤ εF := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min εbar (min εF εcone), hε, hεεF.trans_lt hεF11, min_le_left _ _, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ _ _ hC1s hC2s hqcan _
    hδmax hρmax hεcap hDcap hκ ha₀
  obtain ⟨Rrad, ζ₀, δ₀, ρ₀, m₀, hζ₀, hδ₀, hρ₀, hsupply⟩ :=
    hsupply κ C1s C2s qcan a₀ Ctime Cgrad (min εbar (min εF εcone)) hκ hC1s hC2s hqcan ha₀ hε
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, StandardCap.transitionEnd + (1 / 1000 : ℝ)⁻¹ + 1 < r :=
    ⟨_, lt_add_one _⟩
  obtain ⟨Dtrace, hDtrace⟩ : ∃ Dtrace : ℝ, 64 * (r + (1 / 1000 : ℝ)⁻¹) < Dtrace :=
    ⟨_, lt_add_one _⟩
  obtain ⟨εold, δold, hεold, hδold, hF⟩ := hF Dtrace (max (max Dcap (Dtrace + 1)) Rrad) r
    (1 / 1000) Ctime ((le_max_right _ _).trans (le_max_left _ _)) (by norm_num) le_rfl hr hDtrace
  have hacc : 0 < min (min εold εcap) ζ₀ := lt_min (lt_min hεold hεcap) hζ₀
  have hδb : 0 < min (min δold δmax) δ₀ := lt_min (lt_min hδold hδmax) hδ₀
  obtain ⟨δ, εcut, -, -, hδη, hεcut, -, hF⟩ :=
    hF (max (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) m₀) (min (min εold εcap) ζ₀) hacc
      (min (min δold δmax) δ₀) hδb
  have hεc : 0 < min εcut (1 / 4) := lt_min hεcut (by norm_num)
  obtain ⟨Kfine, hK, hsupply⟩ :=
    hsupply (min εcut (1 / 4)) hεc ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨C, Λ, -, -, hF⟩ := hF C1s C2s hC2s
  have hρb : 0 < min (min ρmax 1) ρ₀ := lt_min (lt_min hρmax one_pos) hρ₀
  obtain ⟨Q, v, -, hv, -, hF⟩ := hF qcan (1 / 2 * min (min ρmax 1) ρ₀) 1 Kfine hqcan
    (by positivity) one_pos (zero_le_one.trans hK)
  obtain ⟨p₀, hpf, hpD, hpm, hpa, hpc, hpδ, hpρ, hpp⟩ : ∃ p₀ : CutoffParameters,
      p₀.fixed = fixed ∧ p₀.modelRadius = max (max Dcap (Dtrace + 1)) Rrad ∧
      p₀.modelOrder = max (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) m₀ ∧
      p₀.modelAccuracy = min (min εold εcap) ζ₀ ∧ p₀.recenterConstant = c ∧
      p₀.delta = (fun _ => 1 / 2) ∧ p₀.neckRadius = (fun _ => min (min ρmax 1) ρ₀) ∧
      p₀.protectedRadius = (fun _ => 1) :=
    ⟨{ delta := fun _ => 1 / 2
       neckRadius := fun _ => min (min ρmax 1) ρ₀
       protectedRadius := fun _ => 1
       delta_pos := fun _ _ => by norm_num
       delta_lt_one := fun _ _ => by norm_num
       neckRadius_pos := fun _ _ => hρb
       protectedRadius_pos := fun _ _ => one_pos
       fixed := fixed
       modelRadius := max (max Dcap (Dtrace + 1)) Rrad
       modelRadius_pos := lt_max_of_lt_left (lt_max_of_lt_left hDcap)
       modelOrder := max (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) m₀
       modelAccuracy := min (min εold εcap) ζ₀
       modelAccuracy_pos := hacc
       recenterConstant := c
       recenterConstant_ge_four := hc }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨p₀, min (min δold δmax) δ₀, min (min ρmax 1) ρ₀, v,
    hpa ▸ (min_le_left _ _).trans (min_le_right _ _),
    hpD ▸ (le_max_left _ _).trans (le_max_left _ _),
    hpm ▸ (le_max_left _ _).trans (le_max_left _ _), hδb,
    (min_le_left _ _).trans (min_le_right _ _), hρb,
    (min_le_left _ _).trans (min_le_left _ _), hpc.le, hv, ?_⟩
  intro H initial hend hhor hclass hderH hgradH _ hspatH hHI hncH s G hs hG hsing hderG hgradG _
    hspatG hncG
  obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
  have hclassF : H.hasCanonicalCutoffRecords p₀ δold (min (min ρmax 1) ρ₀) :=
    hasCanonicalCutoffRecords_of_le ((min_le_left _ _).trans (min_le_left _ _)) le_rfl hclass
  have hspatF : G.SpatiallyCanonicalBefore εF C1s C2s qcan s :=
    G.spatiallyCanonicalBefore_mono_eps hεεF hεF11 hspatG
  have hderEv : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) :=
    fun j _ y t ht hy => hderH j y t ht hy
  have hs0 : 0 ≤ s := (H.toHistory.time_nonneg _).trans G.lt.le
  obtain ⟨ρ, hρ, hρle, -, -, -, -, P, -, -, -, -, -, Qout, E, hOld, K', initialK, i, parameters,
      n, δO, kO, NO, hδO, rot, hmark, side, hord, hδ1, Nrec, eO, -, hEG, hEL, hbfr, -, -, -, -,
      -, -, hi, -, -, -, -, -, happend, hpδ', -, hpρ', hpf', hpc', hpm', hpD', hpa', -, -, -,
      -, -, -, hrecord, hvol, -⟩ :=
    hF p₀ hpD (by rw [hpm]; exact (le_max_right _ _).trans (le_max_left _ _))
      (by rw [hpa]; exact (min_le_left _ _).trans (min_le_left _ _)) H
      initial hend (min (min ρmax 1) ρ₀) hclassF s G L hsing p₀ hG hderH hderG
      (by change _ ≤ p₀.delta s * p₀.neckRadius s; rw [hpδ, hpρ])
      (by change _ ≤ p₀.protectedRadius s; rw [hpp]) hspatF
      (fun ρ' hρ' P' hKQ => fineCutNecks_of_le hεc (min_le_left _ _)
        (hsupply p₀ (min (min δold δmax) δ₀) (min (min ρmax 1) ρ₀)
          (by rw [hpD]; exact le_max_right _ _) (by rw [hpm]; exact le_max_right _ _)
          (by rw [hpa]; exact min_le_right _ _) (min_le_right _ _) (min_le_right _ _) H initial
          hend hclass hHI hderEv hgradH hspatH hncH G L hsing (p₀.withNeckRadius ρ' hρ') hG
          (fun y t ht hy => hderG y t ht hy) hgradG hspatG hncG P' hεPη Q hKQ))
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
