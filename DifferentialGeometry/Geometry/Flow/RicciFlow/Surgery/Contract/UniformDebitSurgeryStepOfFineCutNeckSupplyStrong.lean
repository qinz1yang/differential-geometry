import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNecksOfCutoffClass

open private exists_horn_cutoff_record_of_fineCutNecks_of_le fineCutNecks_of_le
  hasCanonicalCutoffRecords_of_le exists_compact_volume_debit_of_incoming_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hpinch : PinchingThroughSurgery P₀ g₀)
    (hstrong : StrongNecksOfCutoffClass P₀ g₀) (hfine : FineCutNeckSupplyStrong P₀ g₀) :
    UniformDebitSurgeryStepStrong P₀ g₀ := by
  obtain ⟨ε₁, hε₁, hε₁', eta, εcone, heta, hεcone, hsupply⟩ := hfine
  obtain ⟨εs, hεs, -, hstrong⟩ := hstrong ε₁ hε₁ hε₁'
  obtain ⟨fixed, c, hc, εP, εF, hεP, hεPη, hεF, hεF11, hF⟩ :=
    exists_horn_cutoff_record_of_fineCutNecks_of_le P₀ g₀ eta heta
  intro B εbar hB hεbar
  obtain ⟨phi, δA, ρA, εA, hphi, hδA, hρA, hεA, hpinch⟩ := hpinch B hB
  refine ⟨c, by linarith, ?_⟩
  intro Ctime
  obtain ⟨ε, hε, hεbarε, hεεF, hεcone', hεs'⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ εbar ∧ ε ≤ εF ∧ ε ≤ εcone ∧ ε ≤ εs :=
    ⟨min εbar (min εF (min εcone εs)), lt_min hεbar (lt_min hεF (lt_min hεcone hεs)),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨ε, hε, hεεF.trans_lt hεF11, hεbarε, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ hC1 hC2 hC1s hC2s hqcan hτ
    hδmax hρmax hεcap hDcap hκ ha₀
  obtain ⟨C1h, C2h, qh, δh, ρh, εh, Dh, mh, hC1h, hC2h, hqh, hδh, hρh, hεh, -, hstrong⟩ :=
    hstrong B ε hB hε hεs' C1 C2 C1s C2s qcan τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s hqcan hτ
      hκ hphi
  have hqh0 : 0 < qh := hqcan.trans_le hqh
  have hsupply := hsupply κ C1h C2h qh a₀ Ctime Cgrad ε hκ hC1h hC2h hqh0 ha₀ hε hεcone'
  obtain ⟨r, hr⟩ : ∃ r : ℝ, StandardCap.transitionEnd + (1 / 1000 : ℝ)⁻¹ + 1 < r :=
    ⟨_, lt_add_one _⟩
  obtain ⟨Dtrace, hDtrace⟩ : ∃ Dtrace : ℝ, 64 * (r + (1 / 1000 : ℝ)⁻¹) < Dtrace :=
    ⟨_, lt_add_one _⟩
  obtain ⟨Dbig, hDbigT, hDbigcap, hDbigh⟩ :
      ∃ Dbig : ℝ, Dtrace + 1 ≤ Dbig ∧ Dcap ≤ Dbig ∧ Dh ≤ Dbig :=
    ⟨max (max Dcap (Dtrace + 1)) Dh, (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨εold, δold, hεold, hδold, hF⟩ :=
    hF Dtrace Dbig r (1 / 1000) Ctime hDbigT (by norm_num) le_rfl hr hDtrace
  obtain ⟨acc, hacc, haccold, hacccap, hacch, haccA⟩ :
      ∃ acc : ℝ, 0 < acc ∧ acc ≤ εold ∧ acc ≤ εcap ∧ acc ≤ εh ∧ acc ≤ εA :=
    ⟨min (min εold εcap) (min εh εA), lt_min (lt_min hεold hεcap) (lt_min hεh hεA),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hc0 : 0 < c := by linarith
  obtain ⟨δb, hδb, hδbold, hδbmax, hδbh, hδbA, hδbc⟩ :
      ∃ δb : ℝ, 0 < δb ∧ δb ≤ δold ∧ δb ≤ δmax ∧ δb ≤ δh ∧ δb ≤ δA ∧ δb ≤ (2 * c)⁻¹ :=
    ⟨min (min δold δmax) (min δh (min δA (2 * c)⁻¹)),
      lt_min (lt_min hδold hδmax) (lt_min hδh (lt_min hδA (by positivity))),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨mord, hmcap, hmtol, hmh⟩ :
      ∃ m : ℕ, mcap ≤ m ∧ ⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2 ≤ m ∧ mh ≤ m :=
    ⟨max (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) mh, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨δ, εcut, -, -, hδη, hεcut, -, hF⟩ := hF mord acc hacc δb hδb
  have hεc : 0 < min εcut (1 / 4) := lt_min hεcut (by norm_num)
  obtain ⟨Kfine, hK, hsupply⟩ :=
    hsupply (min εcut (1 / 4)) hεc ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨C, Λ, -, -, hF⟩ := hF C1s C2s hC2s
  obtain ⟨ρb, hρb, hρbmax, hρbh, hρbA⟩ :
      ∃ ρb : ℝ, 0 < ρb ∧ ρb ≤ ρmax ∧ ρb ≤ ρh ∧ ρb ≤ ρA :=
    ⟨min ρmax (min ρh ρA), lt_min hρmax (lt_min hρh hρA), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨Q, v, -, hv, -, hF⟩ := hF qh (1 / 2 * ρb) 1 Kfine hqh0 (by positivity) one_pos
    (zero_le_one.trans hK)
  obtain ⟨p₀, hpf, hpD, hpm, hpa, hpc, hpδ, hpρ, hpp⟩ : ∃ p₀ : CutoffParameters,
      p₀.fixed = fixed ∧ p₀.modelRadius = Dbig ∧ p₀.modelOrder = mord ∧
      p₀.modelAccuracy = acc ∧ p₀.recenterConstant = c ∧
      p₀.delta = (fun _ => 1 / 2) ∧ p₀.neckRadius = (fun _ => ρb) ∧
      p₀.protectedRadius = (fun _ => 1) :=
    ⟨{ delta := fun _ => 1 / 2
       neckRadius := fun _ => ρb
       protectedRadius := fun _ => 1
       delta_pos := fun _ _ => by norm_num
       delta_lt_one := fun _ _ => by norm_num
       neckRadius_pos := fun _ _ => hρb
       protectedRadius_pos := fun _ _ => one_pos
       fixed := fixed
       modelRadius := Dbig
       modelRadius_pos := hDcap.trans_le hDbigcap
       modelOrder := mord
       modelAccuracy := acc
       modelAccuracy_pos := hacc
       recenterConstant := c
       recenterConstant_ge_four := hc }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨p₀, δb, ρb, v, hpa ▸ hacccap, hpD ▸ hDbigcap, hpm ▸ hmcap, hδb, hδbmax, hρb, hρbmax,
    hpc.le, hv, ?_⟩
  intro H initial hend hhor hclass hderH hgradH hcanH hspatH hHI hncH s G hs hG hsing hderG
    hgradG hcanG hspatG hncG
  obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
  have hH : H.InCutoffClass g₀ B p₀ δb ρb := ⟨⟨initial⟩, hend, hhor, hclass,
    CutoffParameters.recenterConstant_mul_le_half hc0 hpc.le hδbc⟩
  have hpinchH := hpinch p₀ δb ρb (hpa ▸ haccA) hδbA hρbA H hH
  obtain ⟨hstrongEv, hstrongT⟩ :=
    hstrong p₀ δb ρb (hpa ▸ hacch) (hpD ▸ hDbigh) (hpm ▸ hmh) hδbh hρbh H hH
      (fun j => hpinchH j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
        (H.isContinuationSlab_event hhor j))
      (fun j _ => hcanH j) (fun j _ => hderH j) (fun j _ => hgradH j) (fun j _ => hspatH j) hncH
  have hstrongG := hstrongT s G ⟨hs, hG⟩ (hpinchH (Fin.last H.eventCount) s G ⟨hs, hG⟩) hcanG
    hderG hgradG hspatG hncG
  have hclassF : H.hasCanonicalCutoffRecords p₀ δold ρb :=
    hasCanonicalCutoffRecords_of_le hδbold le_rfl hclass
  have hspatF : G.SpatiallyCanonicalBefore εF C1s C2s qh s := fun y t ht hR =>
    G.spatiallyCanonicalBefore_mono_eps hεεF hεF11 hspatG y t ht (hqh.trans_lt hR)
  have hs0 : 0 ≤ s := (H.toHistory.time_nonneg _).trans G.lt.le
  obtain ⟨ρ, hρ, hρle, -, -, -, -, P, -, -, -, -, -, Qout, E, hOld, K', initialK, i, parameters,
      n, δO, kO, NO, hδO, rot, hmark, side, hord, hδ1, Nrec, eO, -, hEG, hEL, hbfr, -, -, -, -,
      -, -, hi, -, -, -, -, -, happend, hpδ', -, hpρ', hpf', hpc', hpm', hpD', hpa', -, -, -,
      -, -, -, hrecord, hvol, -⟩ :=
    hF p₀ hpD (hpm ▸ hmtol) (hpa ▸ haccold) H initial hend ρb hclassF s G L hsing p₀ hG
      (fun j y t ht hy => hderH j y t ht (hqh.trans_lt hy))
      (fun y t ht hy => hderG y t ht (hqh.trans_lt hy))
      (by change _ ≤ p₀.delta s * p₀.neckRadius s; rw [hpδ, hpρ])
      (by change _ ≤ p₀.protectedRadius s; rw [hpp]) hspatF
      (fun ρ' hρ' P' hKQ => fineCutNecks_of_le hεc (min_le_left _ _)
        (hsupply p₀ δb ρb H initial hend hclass hHI
          (fun j _ y t ht hy => hderH j y t ht (hqh.trans_lt hy))
          (fun j y t ht hy => hgradH j y t ht (hqh.trans_lt hy)) hstrongEv hncH G L hsing
          (p₀.withNeckRadius ρ' hρ') hG (fun y t ht hy => hderG y t ht (hqh.trans_lt hy))
          (fun y t ht hy => hgradG y t ht (hqh.trans_lt hy)) hstrongG hncG P' hεPη Q hKQ))
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
