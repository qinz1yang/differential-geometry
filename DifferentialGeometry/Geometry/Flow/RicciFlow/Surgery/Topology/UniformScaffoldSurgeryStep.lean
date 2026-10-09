import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformFineCutoffScaffold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Cutoff.UniformDebit

open private distanceScalar_toRetainedCoreEvent from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private fineCutNecks_of_le hasCanonicalCutoffRecords_of_le
  exists_compact_volume_debit_of_incoming_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- One scaffold and recenter constant precede all initial metrics. Actual
pinching, strong-neck and fine-cut suppliers then construct the finite-horizon
step with parameters carrying that same pair and the same-event volume debit. -/
theorem exists_uniform_scaffold_surgery_step_with_radial_coordinates_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
  ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
  (4 ≤ recenterConstant ∧ ∃ (A : ℝ) (hA : 0 < A),
    fixed = StaticCapScaffold.ofCollarLength A hA ∧
    DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ (B εbar : ℝ), 0 < B → 0 < εbar →
  ∀ Ctime : ℝ≥0,
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ ε ≤ εbar ∧
  ∀ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Cgrad : ℝ≥0) (κ a₀ : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax →
    0 < εcap → 0 < Dcap → 0 < κ → 0 < a₀ →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ p₀.recenterConstant ≤ recenterConstant ∧
    0 < v ∧
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        G.GradientBoundBefore Cgrad qcan s →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
          (q : CutoffParameters),
          E.incoming = G ∧
          (H.appendEvent E.incoming.lt E hinit).hasCanonicalCutoffRecords p₀ δbound ρbound ∧
          q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
          q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
          q.recenterConstant = p₀.recenterConstant ∧
          (∃ Record : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q,
            (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
            (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
            Record.DeepNecks_C12X (5 / 4) ∧
            q.delta s ≤ δbound ∧ q.neckRadius s ≤ ρbound) ∧
          (q.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ q.modelRadius →
            E.toMetricCutCapEvent.HasUniformDistanceScalar Cdist) ∧
          E.transition.boundaryFrameReversing ∧
          E.toMetricCutCapEvent.poincareStandardDiscarded ∧
          ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
  obtain ⟨Cdist, hCdist, fixed, c, hc, hF⟩ :=
    exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, c, hc, ?_⟩
  intro P₀ g₀
  have hpinch := pinchingThroughSurgery P₀ g₀
  have hstrong := strong_necks_of_cutoff_class P₀ g₀
  have hfine := fineCutNeckSupplyStrong_holds P₀ g₀
  obtain ⟨ε₁, hε₁, hε₁', eta, εcone, heta, hεcone, hsupply⟩ := hfine
  obtain ⟨εs, hεs, -, hstrong⟩ := hstrong ε₁ hε₁ hε₁'
  obtain ⟨εP, εF, hεP, hεPη, hεF, hεF11, hF⟩ := hF P₀ g₀ eta heta
  intro B εbar hB hεbar
  obtain ⟨phi, δA, ρA, εA, hphi, hδA, hρA, hεA, hpinch⟩ := hpinch B hB
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
       recenterConstant_ge_four := hc.1 }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨p₀, δb, ρb, v, hpf, hpc, hpa ▸ hacccap, hpD ▸ hDbigcap, hpm ▸ hmcap, hδb, hδbmax, hρb, hρbmax,
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
      -, -, -, hrecord, hvol, -, hDistance⟩ :=
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
  obtain ⟨Record, -, -, -, -, hwin, hcoordinates, hdeep, hstdE, -, -⟩ := hrecord
  obtain ⟨Eappend, hOldAppend, hInitial, hHEq, hK⟩ := happend
  have hEE := eq_of_heq hHEq
  subst hEE
  subst hK
  have hi' : i = Fin.last H.eventCount := Fin.ext hi
  subst hi'
  refine ⟨Qout, Eappend.toRetainedCoreEvent hOldAppend, hInitial, parameters, hEG, ?_,
    hpf'.trans hpf.symm, hpD'.trans hpD.symm, hpm'.trans hpm.symm, hpa'.trans hpa.symm,
    hpc'.trans hpc.symm,
    ⟨Record, hwin, hcoordinates, hdeep, (congrFun hpδ' s).le.trans hδη,
      (congrFun hpρ' s).le.trans ((hρle s hs0).trans (congrFun hpρ s).le)⟩,
    ?_, hbfr, hstdE, ?_⟩
  · exact H.hasCanonicalCutoffRecords_appendEvent _ (Eappend.toRetainedCoreEvent hOldAppend)
      hInitial hclass Record (hpf'.trans hpf.symm) (hpD'.trans hpD.symm) (hpm'.trans hpm.symm)
      (hpa'.trans hpa.symm) (hpc'.trans hpc.symm) (fun b => (hwin b).hasCanonicalWindow)
      ((congrFun hpδ' s).le.trans hδη)
      ((congrFun hpρ' s).le.trans ((hρle s hs0).trans (congrFun hpρ s).le))
  · intro hacc hD
    exact distanceScalar_toRetainedCoreEvent Eappend hOldAppend (hDistance hacc hD).1
  · exact exists_compact_volume_debit_of_incoming_eq Eappend G L hEG hEL _ hvol

/-- Forget the distance certificate from the same producer result. -/
theorem exists_uniform_scaffold_surgery_step_with_radial_coordinates :
  ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ (B εbar : ℝ), 0 < B → 0 < εbar →
  ∀ Ctime : ℝ≥0,
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ ε ≤ εbar ∧
  ∀ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Cgrad : ℝ≥0) (κ a₀ : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax →
    0 < εcap → 0 < Dcap → 0 < κ → 0 < a₀ →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ p₀.recenterConstant ≤ recenterConstant ∧
    0 < v ∧
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        G.GradientBoundBefore Cgrad qcan s →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
          (q : CutoffParameters),
          E.incoming = G ∧
          (H.appendEvent E.incoming.lt E hinit).hasCanonicalCutoffRecords p₀ δbound ρbound ∧
          q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
          q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
          q.recenterConstant = p₀.recenterConstant ∧
          (∃ Record : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q,
            (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
            (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
            Record.DeepNecks_C12X (5 / 4) ∧
            q.delta s ≤ δbound ∧ q.neckRadius s ≤ ρbound) ∧
          E.transition.boundaryFrameReversing ∧
          E.toMetricCutCapEvent.poincareStandardDiscarded ∧
          ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
  obtain ⟨_, _, distanceProjectionSource⟩ :=
    exists_uniform_scaffold_surgery_step_with_radial_coordinates_with_distance_scalars.{u}
  obtain ⟨fixed, recenterConstant, distanceProjectionh1⟩ := distanceProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2.1, ?_⟩
  intro P₀ g₀ B εbar distanceProjectionx4 distanceProjectionx5 Ctime
  have distanceProjectionh6 := @distanceProjectionh3 P₀ g₀ B εbar distanceProjectionx4
    distanceProjectionx5 Ctime
  obtain ⟨ε, distanceProjectionh7⟩ := distanceProjectionh6
  refine ⟨ε, ?_⟩
  obtain ⟨distanceProjectionfield8, distanceProjectionfield9, distanceProjectionfield10,
    distanceProjectionh11⟩ := distanceProjectionh7
  refine ⟨distanceProjectionfield8, distanceProjectionfield9, distanceProjectionfield10, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ distanceProjectionx12
    distanceProjectionx13 distanceProjectionx14 distanceProjectionx15 distanceProjectionx16
    distanceProjectionx17 distanceProjectionx18 distanceProjectionx19 distanceProjectionx20
    distanceProjectionx21 distanceProjectionx22 distanceProjectionx23
  have distanceProjectionh24 := @distanceProjectionh11 C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap
    mcap Cgrad κ a₀ distanceProjectionx12 distanceProjectionx13 distanceProjectionx14
    distanceProjectionx15 distanceProjectionx16 distanceProjectionx17 distanceProjectionx18
    distanceProjectionx19 distanceProjectionx20 distanceProjectionx21 distanceProjectionx22
    distanceProjectionx23
  obtain ⟨p₀, δbound, ρbound, v, distanceProjectionh25⟩ := distanceProjectionh24
  refine ⟨p₀, δbound, ρbound, v, ?_⟩
  obtain ⟨distanceProjectionfield26, distanceProjectionfield27, distanceProjectionfield28,
    distanceProjectionfield29, distanceProjectionfield30, distanceProjectionfield31,
    distanceProjectionfield32, distanceProjectionfield33, distanceProjectionfield34,
    distanceProjectionfield35, distanceProjectionfield36, distanceProjectionh37⟩ :=
    distanceProjectionh25
  refine ⟨distanceProjectionfield26, distanceProjectionfield27, distanceProjectionfield28,
    distanceProjectionfield29, distanceProjectionfield30, distanceProjectionfield31,
    distanceProjectionfield32, distanceProjectionfield33, distanceProjectionfield34,
    distanceProjectionfield35, distanceProjectionfield36, ?_⟩
  intro H distanceProjectionx38 hend distanceProjectionx39 distanceProjectionx40
    distanceProjectionx41 distanceProjectionx42 distanceProjectionx43 distanceProjectionx44
    distanceProjectionx45 distanceProjectionx46 s G distanceProjectionx47 hG distanceProjectionx48
    distanceProjectionx49 distanceProjectionx50 distanceProjectionx51 distanceProjectionx52
    distanceProjectionx53
  have distanceProjectionh54 := @distanceProjectionh37 H distanceProjectionx38 hend
    distanceProjectionx39 distanceProjectionx40 distanceProjectionx41 distanceProjectionx42
    distanceProjectionx43 distanceProjectionx44 distanceProjectionx45 distanceProjectionx46 s G
    distanceProjectionx47 hG distanceProjectionx48 distanceProjectionx49 distanceProjectionx50
    distanceProjectionx51 distanceProjectionx52 distanceProjectionx53
  obtain ⟨Q, E, hinit, q, distanceProjectionh55⟩ := distanceProjectionh54
  refine ⟨Q, E, hinit, q, ?_⟩
  obtain ⟨distanceProjectionfield56, distanceProjectionfield57, distanceProjectionfield58,
    distanceProjectionfield59, distanceProjectionfield60, distanceProjectionfield61,
    distanceProjectionfield62, distanceProjectionfield63, distanceProjectionh64⟩ :=
    distanceProjectionh55
  refine ⟨distanceProjectionfield56, distanceProjectionfield57, distanceProjectionfield58,
    distanceProjectionfield59, distanceProjectionfield60, distanceProjectionfield61,
    distanceProjectionfield62, distanceProjectionfield63, ?_⟩
  exact distanceProjectionh64.2

/-- Forget the radial certificate from the same stronger producer result. -/
theorem exists_uniform_scaffold_surgery_step :
  ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ (B εbar : ℝ), 0 < B → 0 < εbar →
  ∀ Ctime : ℝ≥0,
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ ε ≤ εbar ∧
  ∀ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Cgrad : ℝ≥0) (κ a₀ : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax →
    0 < εcap → 0 < Dcap → 0 < κ → 0 < a₀ →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ p₀.recenterConstant ≤ recenterConstant ∧
    0 < v ∧
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        G.GradientBoundBefore Cgrad qcan s →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
          (q : CutoffParameters),
          E.incoming = G ∧
          (H.appendEvent E.incoming.lt E hinit).hasCanonicalCutoffRecords p₀ δbound ρbound ∧
          q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
          q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
          q.recenterConstant = p₀.recenterConstant ∧
          Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
            (Fin.last H.eventCount) q) ∧
          E.transition.boundaryFrameReversing ∧
          E.toMetricCutCapEvent.poincareStandardDiscarded ∧
          ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
  have radialProjectionSource := exists_uniform_scaffold_surgery_step_with_radial_coordinates.{u}
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  intro P₀ g₀ B εbar radialProjectionx4 radialProjectionx5 Ctime
  have radialProjectionh6 := @radialProjectionh3 P₀ g₀ B εbar radialProjectionx4 radialProjectionx5
    Ctime
  obtain ⟨ε, radialProjectionh7⟩ := radialProjectionh6
  refine ⟨ε, ?_⟩
  obtain ⟨radialProjectionfield8, radialProjectionfield9, radialProjectionfield10,
    radialProjectionh11⟩ := radialProjectionh7
  refine ⟨radialProjectionfield8, radialProjectionfield9, radialProjectionfield10, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ radialProjectionx12
    radialProjectionx13 radialProjectionx14 radialProjectionx15 radialProjectionx16
    radialProjectionx17 radialProjectionx18 radialProjectionx19 radialProjectionx20
    radialProjectionx21 radialProjectionx22 radialProjectionx23
  have radialProjectionh24 := @radialProjectionh11 C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap
    Cgrad κ a₀ radialProjectionx12 radialProjectionx13 radialProjectionx14 radialProjectionx15
    radialProjectionx16 radialProjectionx17 radialProjectionx18 radialProjectionx19
    radialProjectionx20 radialProjectionx21 radialProjectionx22 radialProjectionx23
  obtain ⟨p₀, δbound, ρbound, v, radialProjectionh25⟩ := radialProjectionh24
  refine ⟨p₀, δbound, ρbound, v, ?_⟩
  obtain ⟨radialProjectionfield26, radialProjectionfield27, radialProjectionfield28,
    radialProjectionfield29, radialProjectionfield30, radialProjectionfield31,
    radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, radialProjectionh37⟩ := radialProjectionh25
  refine ⟨radialProjectionfield26, radialProjectionfield27, radialProjectionfield28,
    radialProjectionfield29, radialProjectionfield30, radialProjectionfield31,
    radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, ?_⟩
  intro H radialProjectionx38 hend radialProjectionx39 radialProjectionx40 radialProjectionx41
    radialProjectionx42 radialProjectionx43 radialProjectionx44 radialProjectionx45
    radialProjectionx46 s G radialProjectionx47 hG radialProjectionx48 radialProjectionx49
    radialProjectionx50 radialProjectionx51 radialProjectionx52 radialProjectionx53
  have radialProjectionh54 := @radialProjectionh37 H radialProjectionx38 hend radialProjectionx39
    radialProjectionx40 radialProjectionx41 radialProjectionx42 radialProjectionx43
    radialProjectionx44 radialProjectionx45 radialProjectionx46 s G radialProjectionx47 hG
    radialProjectionx48 radialProjectionx49 radialProjectionx50 radialProjectionx51
    radialProjectionx52 radialProjectionx53
  obtain ⟨Q, E, hinit, q, radialProjectionh55⟩ := radialProjectionh54
  refine ⟨Q, E, hinit, q, ?_⟩
  obtain ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionh63⟩ := radialProjectionh55
  refine ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, ?_⟩
  refine ⟨?_, radialProjectionh63.2⟩
  have radialProjectionh64 := radialProjectionh63.1
  obtain ⟨radialProjectionx65, _⟩ := radialProjectionh64
  exact ⟨radialProjectionx65⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
