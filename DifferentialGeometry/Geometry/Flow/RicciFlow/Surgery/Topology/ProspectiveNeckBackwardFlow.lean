import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTimeJetConvergence

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance {Q : OrientedThreeStage.{u}} {a s : ℝ} (G : Q.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_subsequence_selected_neck_append_backward_flow
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (s : ℕ → ℝ) (Qstage : ℕ → OrientedThreeStage.{u})
      (E : ∀ i, MetricCutCapEvent ((H i).stage (Fin.last (H i).eventCount)) (Qstage i)
        ((H i).time (Fin.last (H i).eventCount)) (s i)),
    ∀ hinit : ∀ i, (E i).incoming.flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount),
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (E i).terminal.metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ Fin.last (H i).eventCount → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (s i), q₀ < (E i).incoming.flow.scalar t y →
      |derivWithin (fun v => (E i).incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * (E i).incoming.flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (E i).incoming.flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
      let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
      ∀ᶠ i in atTop,
        ∃ (first : Fin ((H (ind i)).eventCount + 1)) (hle : first ≤ Fin.last (H (ind i)).eventCount),
      (H (ind i)).time first ≤ (s (ind i)) - 2 / (N i).scale ∧
      ∃ (K : Set (E (ind i)).incoming.terminalRegularOpen)
        (Phi : neckBuffer δ → (H (ind i)).backwardSurvivorIncomingFootprint first
          (Fin.last (H (ind i)).eventCount) hle (E (ind i)).incoming K)
        (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (ind i)).backwardSurvivorIncomingFootprint first (Fin.last (H (ind i)).eventCount) hle (E (ind i)).incoming K))
        (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
          (RealTimeInterval.closed (-2) 0 (by norm_num))),
        ((H (ind i)).backwardSurvivorIncomingFootprintMap first
          (Fin.last (H (ind i)).eventCount) hle (E (ind i)).incoming K ∘ Phi = (N i).chart) ∧
        IsSolutionOn S ∧ S.base.metric 0 = (N i).normalizedMetric ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric (N i).scale (N i).scale_pos (gflow ((s (ind i)) + t / (N i).scale))) Phi hPhi) ∧
        (∀ (j : Fin (H (ind i)).eventCount) (hf : first ≤ j.castSucc)
          (hl : j.succ ≤ Fin.last (H (ind i)).eventCount),
          ∀ t ∈ Icc ((H (ind i)).time j.castSucc) ((H (ind i)).time j.succ),
            gflow t = (((H (ind i)).backwardSurvivorSlabMetric first (Fin.last (H (ind i)).eventCount) hle
              j hf hl t).restrictOpen
              ((H (ind i)).backwardSurvivorIncomingDomain first (Fin.last (H (ind i)).eventCount) hle
                (E (ind i)).incoming)).restrictOpen
                ((H (ind i)).backwardSurvivorIncomingFootprint first (Fin.last (H (ind i)).eventCount) hle (E (ind i)).incoming K)) ∧
        (∀ t ∈ Icc ((H (ind i)).time (Fin.last (H (ind i)).eventCount)) (s (ind i)),
          gflow t = ((H (ind i)).backwardSurvivorIncomingMetric first (Fin.last (H (ind i)).eventCount) hle
            (E (ind i)).incoming (E (ind i)).terminal t).restrictOpen
            ((H (ind i)).backwardSurvivorIncomingFootprint first (Fin.last (H (ind i)).eventCount) hle (E (ind i)).incoming K)) ∧
        (∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn (neckClosedTest δ) k (S.base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ) ∧
        (∃ Zextra : (b : ℕ) → Icc (-(5 / 4 : ℝ)) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Zextra b v x = iteratedDerivWithin b (fun t =>
            metricTensorField (S.base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-(5 / 4 : ℝ)) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Zextra q v) r x)) ≤ η) ∧
        ∃ N' : NormalizedNeck (((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i)) (hinit (ind i))).event
          (Fin.last (H (ind i)).eventCount)).terminal.metric δ k,
          HEq N' (N i) ∧ ∃ B : IncomingBackwardNeck ((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i)) (hinit (ind i)))
            (Fin.last (H (ind i)).eventCount) N' (Real.sqrt (N i).scale⁻¹), B.metric = S.base.metric := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hrec⟩ :=
    exists_prospective_neck_convergence_of_improving_necks D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H s Qstage E hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨ind, hind, first, hle, hprec, hord, hstart, K, Phi, hPhi, gflow, S, rho, hrho,
    hmap, hS, hterminal, hmetric, hslabs, hlast, hconv, hjets⟩ :=
    hrec H (fun i => Fin.last (H i).eventCount) s (fun i => (E i).incoming)
      (fun i => (E i).terminal) hinit eta m O heta hm hscale ha hsa
      parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
      hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark hδ hδ1 k
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  refine ⟨ind ∘ rho, hind.comp hrho, (fun i => hprec (rho i)), (fun i => hord (rho i)), ?_⟩
  obtain ⟨j, hj⟩ := hconv (neckClosedTest δ) (isCompact_neckClosedTest δ) k δ hδ
  have hextra := eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence
    (a := (-2 : ℝ)) (c := -(5 / 4 : ℝ)) hδ (by norm_num) (by norm_num) k
    (fun i => S (rho i)) (fun i => hS (rho i)) Subset.rfl Subset.rfl
    (fun A hA p η hη => by
      obtain ⟨j, hj⟩ := hconv A hA p η hη
      exact ⟨j, fun i hi t ht => hj i hi t ⟨by linarith [ht.1], ht.2⟩⟩)
  filter_upwards [hjets, eventually_ge_atTop j, hextra] with i hi hij hiExtra
  obtain ⟨Z, hZ, eta', heta', hclose⟩ := hi
  have hclock : (H (ind (rho i))).time (first (rho i)) ≤ s (ind (rho i)) - (N (rho i)).scale⁻¹ := by
    apply (hstart (rho i)).trans
    have hscale : (N (rho i)).scale = (O (ind (rho i))).scale := rfl
    rw [hscale, inv_eq_one_div]
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (O (ind (rho i))).scale_pos.le
  obtain ⟨N', hN', B, hBmetric, _⟩ := NormalizedNeck.exists_incomingBackwardNeck_appendEvent
    (H (ind (rho i))) (first (rho i)) (hle (rho i)) (E (ind (rho i))) (hinit (ind (rho i)))
    (N (rho i)) (K (rho i)) (Phi (rho i)) (hPhi (rho i)) (hmap (rho i)) (gflow (rho i))
    (by norm_num : (1 : ℝ) < 2) (S (rho i)) (hS (rho i)) (hterminal (rho i))
    (fun t _ => hmetric (rho i) t) (hslabs (rho i)) (hlast (rho i)) hclock Z hZ ⟨eta', heta', hclose⟩
  exact ⟨first (rho i), hle (rho i), hstart (rho i), K (rho i), Phi (rho i), hPhi (rho i),
    gflow (rho i), S (rho i), hmap (rho i), hS (rho i), hterminal (rho i), hmetric (rho i),
    hslabs (rho i), hlast (rho i), hj i hij, hiExtra, N', hN', B, hBmetric⟩



private theorem exists_selected_neck_append_backward_flow_threshold
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ ηstar : ℝ, ∃ mstar : ℕ, ∃ Qmin : ℝ,
      0 < ηstar ∧ ηstar ≤ δ ∧ k ≤ mstar ∧ 0 < Qmin ∧
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    η ≤ ηstar → mstar ≤ m → Qmin ≤ O.scale →
    ∀ (hprec : η ≤ δ) (hord : k ≤ m),
    let N := (O.monoDelta hprec hδ1).lowerOrder hord
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ Fin.last H.eventCount),
      H.time first ≤ s - 2 / N.scale ∧
      ∃ (K : Set E.incoming.terminalRegularOpen)
        (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first
          (Fin.last H.eventCount) hle E.incoming K)
        (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
        (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
          (RealTimeInterval.closed (-2) 0 (by norm_num))),
        (H.backwardSurvivorIncomingFootprintMap first
          (Fin.last H.eventCount) hle E.incoming K ∘ Phi = N.chart) ∧
        IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric N.scale N.scale_pos (gflow (s + t / N.scale))) Phi hPhi) ∧
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
          (hl : j.succ ≤ Fin.last H.eventCount),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle
              j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle
                E.incoming)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (H.time (Fin.last H.eventCount)) s,
          gflow t = (H.backwardSurvivorIncomingMetric first (Fin.last H.eventCount) hle
            E.incoming E.terminal t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn (neckClosedTest δ) k (S.base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ) ∧
        (∃ Zextra : (b : ℕ) → Icc (-(5 / 4 : ℝ)) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Zextra b v x = iteratedDerivWithin b (fun t =>
            metricTensorField (S.base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-(5 / 4 : ℝ)) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Zextra q v) r x)) ≤ η) ∧
        ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
          (Fin.last H.eventCount)).terminal.metric δ k,
          HEq N' N ∧ ∃ B : IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
            (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹), B.metric = S.base.metric := by
  classical
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hseq⟩ :=
    exists_subsequence_selected_neck_append_backward_flow D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q0 ha hq0 phi hphi
  by_contra hnot
  push Not at hnot
  have hfail (n : ℕ) := hnot (min (δ / 2) (1 / ((n : ℝ) + 1))) (k + n) ((n : ℝ) + 1)
    (lt_min (half_pos hδ) (by positivity))
    ((min_le_left _ _).trans (half_le_self hδ.le)) (Nat.le_add_right k n) (by positivity)
  choose H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale hprec hord hbad using hfail
  have hηlim : Tendsto η atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (O n).delta_pos.le)
      (fun n => (hη n).trans (min_le_right _ _))
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat k)
    intro n
    have hn := hm n
    omega
  have hscaleLim : Tendsto (fun n => (O n).scale) atTop atTop :=
    tendsto_atTop_mono hscale
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨ind, hind, hprecision, horder', hsuccess⟩ :=
    hseq H s Qstage E hinit η m O hηlim hmlim hscaleLim ha hsa parameters records
      hfixed hlower (Eventually.of_forall fun i j _ => hdelta i j)
      (Eventually.of_forall haccuracy) hmargin horder q0 hq0
      (fun i j _ => hderiv i j) hfinal hphi (fun i j _ => hpinch i j) hpinchFinal
      (fun i j _ => hcap i j)
      (fun i j _ => center i j) (fun i j _ => precision i j) (fun i j _ => order i j)
      (fun i j _ => d i j) (fun i j _ => w i j) (fun i j _ => Jbig i j)
      (fun i j _ => hJbig i j) (fun i j _ => hzero i j) (fun i j _ => hmark i j)
      hδ hδ1 k
  obtain ⟨n, hn⟩ := hsuccess.exists
  exact hbad (ind n) hn


theorem exists_uniform_selected_neck_append_backward_flow
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ Fin.last H.eventCount),
      H.time first ≤ s - 2 / N.scale ∧
      ∃ (K : Set E.incoming.terminalRegularOpen)
        (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first
          (Fin.last H.eventCount) hle E.incoming K)
        (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
        (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
          (RealTimeInterval.closed (-2) 0 (by norm_num))),
        (H.backwardSurvivorIncomingFootprintMap first
          (Fin.last H.eventCount) hle E.incoming K ∘ Phi = N.chart) ∧
        IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric N.scale N.scale_pos (gflow (s + t / N.scale))) Phi hPhi) ∧
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
          (hl : j.succ ≤ Fin.last H.eventCount),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle
              j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle
                E.incoming)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (H.time (Fin.last H.eventCount)) s,
          gflow t = (H.backwardSurvivorIncomingMetric first (Fin.last H.eventCount) hle
            E.incoming E.terminal t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn (neckClosedTest δ) k (S.base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ) ∧
        (∃ Zextra : (b : ℕ) → Icc (-(5 / 4 : ℝ)) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Zextra b v x = iteratedDerivWithin b (fun t =>
            metricTensorField (S.base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-(5 / 4 : ℝ)) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Zextra q v) r x)) ≤ η) ∧
        ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
          (Fin.last H.eventCount)).terminal.metric δ k,
          HEq N' N ∧ ∃ B : IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
            (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹), B.metric = S.base.metric := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    exists_selected_neck_append_backward_flow_threshold D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q0 ha hq0 phi hphi
  obtain ⟨ηstar, mstar, Qmin, hηstar, hηδ, hkm, hQmin, hmain⟩ :=
    hthreshold hδ hδ1 k a q0 ha hq0 phi hphi
  refine ⟨ηstar, mstar, Qmin, hηδ, hkm, hηstar, hQmin, ?_⟩
  intro H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale
  exact hmain H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale (hη.trans hηδ) (hkm.trans hm)


private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_selected_neck_append_backward_flow_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (D Dbig r tol : ℝ) (Ctime : ℝ≥0)
    (hmargin : D + 1 ≤ Dbig) (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ q₀ : ℝ, 0 < q₀ →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
    ∀ (H : RetainedCoreHistory P), InitialIdentification P g H.toHistory →
    ∀ ρ : ℝ, H.hasCanonicalCutoffRecords p₀ δ₀ ρ →
    ∀ (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    E.incoming.SingularEndpoint →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ Fin.last H.eventCount),
      H.time first ≤ s - 2 / N.scale ∧
      ∃ (K : Set E.incoming.terminalRegularOpen)
        (Phi : neckBuffer δ → H.toHistory.backwardSurvivorIncomingFootprint first
          (Fin.last H.eventCount) hle E.incoming K)
        (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
        (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
          (RealTimeInterval.closed (-2) 0 (by norm_num))),
        (H.toHistory.backwardSurvivorIncomingFootprintMap first
          (Fin.last H.eventCount) hle E.incoming K ∘ Phi = N.chart) ∧
        IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric N.scale N.scale_pos (gflow (s + t / N.scale))) Phi hPhi) ∧
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
          (hl : j.succ ≤ Fin.last H.eventCount),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle
              j hf hl t).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle
                E.incoming)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (H.time (Fin.last H.eventCount)) s,
          gflow t = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount) hle
            E.incoming E.terminal t).restrictOpen
            (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K)) ∧
        (∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn (neckClosedTest δ) k (S.base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ) ∧
        (∃ Zextra : (b : ℕ) → Icc (-(5 / 4 : ℝ)) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Zextra b v x = iteratedDerivWithin b (fun t =>
            metricTensorField (S.base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-(5 / 4 : ℝ)) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Zextra q v) r x)) ≤ η) ∧
        ∃ N' : NormalizedNeck ((H.toHistory.appendEvent E.incoming.lt E hinit).event
          (Fin.last H.eventCount)).terminal.metric δ k,
          HEq N' N ∧ ∃ B : IncomingBackwardNeck (H.toHistory.appendEvent E.incoming.lt E hinit)
            (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹), B.metric = S.base.metric := by
  classical
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  obtain ⟨Phi, hPhi, hpinch⟩ := Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P g
  obtain ⟨a, ha, htime⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P g
  obtain ⟨εback, δ₀, hεback, hδ₀, hback⟩ := exists_uniform_selected_neck_append_backward_flow
    D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  have hDbig : StandardCap.transitionEnd < Dbig := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr htol
    linarith
  obtain ⟨εscalar, hεscalar, hscalar⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window Dbig hDbig
  refine ⟨min εback εscalar, δ₀, lt_min hεback hεscalar, hδ₀, ?_⟩
  intro δ hδ hδ1 k q₀ hq₀
  obtain ⟨ηstar,mstar,Qmin,hηδ,hkm,hηstar,hQmin,hmain⟩ := hback hδ hδ1 k a q₀ ha hq₀ Phi hPhi
  refine ⟨ηstar,mstar,Qmin,hηδ,hkm,hηstar,hQmin,?_⟩
  intro p₀ hpD hpm hpε H A ρ hInv s Qstage E hinit hsing hderiv hfinal η m O hη hm hscale
  obtain ⟨p,_,hmodel,horder,haccuracy,_,records,hcanonical,hδold,_⟩ := hInv
  have hstart := hinitial H.toHistory A
  have hs := htime H.toHistory A (fun j => (records j).singular) (Fin.last H.eventCount) s E.incoming hinit hsing
  have hcap : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤
        metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z) := by
    intro j b z
    have hh := hscalar (H.toHistory.event j) (fixed := p.fixed) (m := p.modelOrder) (ε := p.modelAccuracy)
    rw [← hpD, ← hmodel] at hh
    exact hh (haccuracy.trans_le (hpε.trans (min_le_right _ _))) (by omega) ((records j).static b)
      (hcanonical j b) z
  choose center precision order datum w hdatum hmetric hmark using hcanonical
  have hzero (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (y : standardCapWindow p.modelRadius) (v z : TangentSpace ThreeModel y) :
      (w j b).windowMetric.inner y v z = ((records j).static b).neck.scale *
        (H.initialMetric j.succ).inner (((records j).static b).window y)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y z) := by
    have he : (H.toHistory.event j).outputMetric = H.initialMetric j.succ := H.event_output j
    have hh := hmetric j b y v z
    rw [he] at hh
    exact hh
  exact hmain H.toHistory s Qstage E hinit hs p records hstart.1 hstart.2
    (fun j b => ((records j).delta_le b).trans (hδold j))
    (haccuracy.trans_le (hpε.trans (min_le_left _ _)))
    (by rw [hmodel,hpD]; exact hmargin) (by omega) hderiv hfinal
    (fun j => hpinch H.toHistory A p records j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j))
    (hpinch H.toHistory A p records (Fin.last H.eventCount) s E.incoming hinit)
    hcap center precision order datum w (fun j b => ((records j).static b).window)
    (fun j b => ((records j).static b).window_smooth) hzero hmark η m O hη hm hscale

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
