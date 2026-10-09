import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvivalVariableThreshold
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepProducerAppendC12X

/-!
# Deep uniform backward-neck producer (C12X, S16 round 3, O-C12X-S16K G1b)

The record backward necks of the main chain come from
`exists_threshold_uniform_selected_neck_append_backward`
(ST/ProspectiveNeckSurvivalVariableThreshold), used by CT/PreparedHistoryCutoff.  Its private
convergence step already exposes depth-two historical rows (`S` on `[-2, 0]`, metric identification
for every time, `time first ≤ s - 2 / scale`) converging to the shrinking cylinder on `[-3/2, 0]`.
Hence for every depth factor `1 < θ < 3/2` the same argument yields jets and parabolic closeness
on `[-θ, 0]` (`eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence`), and
`NormalizedNeck.exists_incomingBackwardNeckDeep_appendEvent_C12X` assembles the deep backward neck.

* `exists_threshold_uniform_selected_neck_append_backwardDeep_C12X`: the deep uniform producer
  (main instance `θ = 5/4`, the record contract `DeepBackwardNecks_C12X (5/4)` of S16G G5).

No tracked file is changed; the private convergence theorem is reused via `open private`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private prospective_neck_convergence_improving_of_threshold_ratio from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvivalVariableThreshold

/-- Deep analogue of the private subsequence step of
`exists_threshold_uniform_selected_neck_append_backward` (depth factor `1 < θ < 3/2`). -/
private theorem exists_subsequence_selected_neck_append_backwardDeep_C12X
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ < 3 / 2) :
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
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ Fin.last (H i).eventCount → ∀ b,
        (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (s i), q₀ i <
        (E i).incoming.flow.scalar t y →
      |derivWithin (fun v => (E i).incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          (E i).incoming.flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (E i).incoming.flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
      let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
      ∀ᶠ i in atTop,
        ∃ N' : NormalizedNeck (((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i))
          (hinit (ind i))).event (Fin.last (H (ind i)).eventCount)).terminal.metric δ k,
          HEq N' (N i) ∧ Nonempty (IncomingBackwardNeckDeep_C12X
            ((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i)) (hinit (ind i)))
            (Fin.last (H (ind i)).eventCount) N' (Real.sqrt (N i).scale⁻¹) θ) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hrec⟩ :=
    prospective_neck_convergence_improving_of_threshold_ratio D r eps a₀ Ctime ha₀ heps
        hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H s Qstage E hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨ind, hind, first, hle, hprec, hord, hstart, K, Phi, hPhi, gflow, S, rho, hrho,
    hmap, hS, hterminal, hmetric, hslabs, hlast, hconv, hjets⟩ :=
    hrec H (fun i => Fin.last (H i).eventCount) s (fun i => (E i).incoming)
      (fun i => (E i).terminal) hinit eta m O heta hm hscale ha hsa
      parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
      hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark hδ hδ1 k
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  have hjetsD := eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence
    hδ (show -(3 / 2 : ℝ) < -θ by linarith) (show -θ < (0 : ℝ) by linarith) k
    (fun i => S (rho i)) (fun i => hS (rho i))
    (show Icc (-(3 / 2 : ℝ)) 0 ⊆ (RealTimeInterval.closed (-2) 0 (by norm_num)).carrier from
      Icc_subset_Icc (by norm_num) le_rfl)
    (show Ioo (-(3 / 2 : ℝ)) 0 ⊆ (RealTimeInterval.closed (-2) 0 (by norm_num)).regular from
      Ioo_subset_Ioo (by norm_num) le_rfl)
    (fun A hA p η hη => by
      obtain ⟨j, hj⟩ := hconv A hA p η hη
      exact ⟨j, fun i hi t ht => hj i hi t ⟨by linarith [ht.1], ht.2⟩⟩)
  refine ⟨ind ∘ rho, hind.comp hrho, (fun i => hprec (rho i)), (fun i => hord (rho i)), ?_⟩
  filter_upwards [hjets, hjetsD] with i hi hiD
  obtain ⟨Z, hZ, eta', heta', hclose⟩ := hi
  obtain ⟨Zd, hZd, etaD, hetaD, hcloseD⟩ := hiD
  have hclock : (H (ind (rho i))).time (first (rho i)) ≤
      s (ind (rho i)) - θ * (N (rho i)).scale⁻¹ := by
    apply (hstart (rho i)).trans
    have hscale : (N (rho i)).scale = (O (ind (rho i))).scale := rfl
    rw [hscale, div_eq_mul_inv]
    apply sub_le_sub_left
    exact mul_le_mul_of_nonneg_right (by linarith)
      (inv_nonneg.mpr (O (ind (rho i))).scale_pos.le)
  obtain ⟨N', hN', D, _⟩ := NormalizedNeck.exists_incomingBackwardNeckDeep_appendEvent_C12X
    (H (ind (rho i))) (first (rho i)) (hle (rho i)) (E (ind (rho i))) (hinit (ind (rho i)))
    (N (rho i)) (K (rho i)) (Phi (rho i)) (hPhi (rho i)) (hmap (rho i)) (gflow (rho i))
    hθ (show θ < 2 by linarith) (S (rho i)) (hS (rho i)) (hterminal (rho i))
    (fun t _ => hmetric (rho i) t) (hslabs (rho i)) (hlast (rho i)) hclock Z hZ
    ⟨eta', heta', hclose⟩ Zd hZd ⟨etaD, hetaD, hcloseD⟩
  exact ⟨N', hN', ⟨D⟩⟩

/-- Deep analogue of the private uniform (contradiction) step. -/
private theorem selected_neck_append_backwardDeep_uniform_C12X
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D)
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ < 3 / 2) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ ηstar : ℝ, ∃ mstar : ℕ, ∃ Λ : ℝ,
      0 < ηstar ∧ ηstar ≤ δ ∧ k ≤ mstar ∧ 0 < Λ ∧
    ∀ q₀ : ℝ, 0 < q₀ →
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
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          E.incoming.flow.scalar t y ^ 2) →
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
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    η ≤ ηstar → mstar ≤ m → Λ * max q₀ 1 ≤ O.scale →
    ∀ (hprec : η ≤ δ) (hord : k ≤ m),
    let N := (O.monoDelta hprec hδ1).lowerOrder hord
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeckDeep_C12X (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹) θ) := by
  classical
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hseq⟩ :=
    exists_subsequence_selected_neck_append_backwardDeep_C12X D r tol a₀ Ctime ha₀ htol
        htolsmall hr hfit hθ hθ'
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a ha phi hphi
  by_contra hnot
  push Not at hnot
  have hfail (n : ℕ) := hnot (min (δ / 2) (1 / ((n : ℝ) + 1))) (k + n) ((n : ℝ) + 1)
    (lt_min (half_pos hδ) (by positivity))
    ((min_le_left _ _).trans (half_le_self hδ.le)) (Nat.le_add_right k n) (by positivity)
  choose q0 hq0 H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
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
  have hscaleLower (n : ℕ) : (n : ℝ) + 1 ≤ (O n).scale :=
    (le_mul_of_one_le_right (by positivity) (le_max_right _ _)).trans (hscale n)
  have hscaleLim : Tendsto (fun n => (O n).scale) atTop atTop :=
    tendsto_atTop_mono hscaleLower
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hratio (n : ℕ) : q0 n / (O n).scale ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (O n).scale_pos (by positivity)]
    calc q0 n * ((n : ℝ) + 1) ≤ max (q0 n) 1 * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ((n : ℝ) + 1) * max (q0 n) 1 := mul_comm _ _
      _ ≤ (O n).scale := hscale n
      _ = 1 * (O n).scale := (one_mul _).symm
  have hqlim : Tendsto (fun n => q0 n / (O n).scale) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (div_pos (hq0 n) (O n).scale_pos).le) hratio
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨ind, hind, hprecision, horder', hsuccess⟩ :=
    hseq H s Qstage E hinit η m O hηlim hmlim hscaleLim ha hsa parameters records
      hfixed hlower (Eventually.of_forall fun i j _ => hdelta i j)
      (Eventually.of_forall haccuracy) hmargin horder q0 hq0 hqlim
      (fun i j _ => hderiv i j) hfinal hphi (fun i j _ => hpinch i j) hpinchFinal
      (fun i j _ => hcap i j)
      (fun i j _ => center i j) (fun i j _ => precision i j) (fun i j _ => order i j)
      (fun i j _ => d i j) (fun i j _ => w i j) (fun i j _ => Jbig i j)
      (fun i j _ => hJbig i j) (fun i j _ => hzero i j) (fun i j _ => hmark i j)
      hδ hδ1 k
  obtain ⟨n, hn⟩ := hsuccess.exists
  obtain ⟨N', hN', hB⟩ := hn
  exact hbad (ind n) ⟨N', hN', hB⟩

/-- **Deep uniform backward-neck producer** (route β, S16 round 3).  Same hypotheses and
quantifier order as `exists_threshold_uniform_selected_neck_append_backward`; for a depth factor
`1 < θ < 3/2` (main instance `θ = 5/4`) the selected neck carries a deep backward neck
`IncomingBackwardNeckDeep_C12X … θ` (whose depth-one part is the old backward neck). -/
theorem exists_threshold_uniform_selected_neck_append_backwardDeep_C12X
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D)
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ < 3 / 2) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Λ : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Λ ∧
    ∀ q₀ : ℝ, 0 < q₀ →
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
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          E.incoming.flow.scalar t y ^ 2) →
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
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Λ * max q₀ 1 ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeckDeep_C12X (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹) θ) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    selected_neck_append_backwardDeep_uniform_C12X D r tol a₀ Ctime ha₀ htol
        htolsmall hr hfit hθ hθ'
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a ha phi hphi
  obtain ⟨ηstar, mstar, Λ, hηstar, hηδ, hkm, hΛ, hmain⟩ :=
    hthreshold hδ hδ1 k a ha phi hphi
  refine ⟨ηstar, mstar, Λ, hηδ, hkm, hηstar, hΛ, ?_⟩
  intro q₀ hq₀ H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale
  exact hmain q₀ hq₀ H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale (hη.trans hηδ) (hkm.trans hm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
