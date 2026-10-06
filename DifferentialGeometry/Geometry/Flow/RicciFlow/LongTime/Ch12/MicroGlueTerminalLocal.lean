import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueTracedLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceTerminal
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall

/-!
# CH12-O3, group 4b: the surgery-tolerant KL70.2 kernel with a local terminal volume test

`exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_local_O3` is
`RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal`
(`ST/BoundedCurvatureAtDistanceSliceTerminal.lean:249`) with `TerminalNoncollapsedBefore κ ρ t`
replaced by the terminal-time local volume test about `y` at scale `ρ`.  This kernel has no
`H.time last ≤ t - Λ/R` window premise: recent surgeries are handled by backward chain traces and
the alternative `CapWindowPoint` (to be covered by the cap-window jets, W5).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem rebase_lam_bound_O3 {A K Q R r₀ L : ℝ} (hA : 0 < A) (hK : 1 ≤ K) (hR : 0 < R)
    (hRQ : R ≤ Q) (hQK : Q ≤ K * R) (hL : 0 < L) (hr₀ : r₀ = L / (2 * Real.sqrt (2 * Q)))
    {N : ℕ} (hN : (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀) :
    (N : ℝ) * r₀ ≤ (2 * A * Real.sqrt K + L) / Real.sqrt Q := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h1 : A / Real.sqrt R ≤ A * Real.sqrt K / Real.sqrt Q := by
    rw [div_le_div_iff₀ hsR hsQ]
    have : Real.sqrt Q ≤ Real.sqrt K * Real.sqrt R := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hQK
    nlinarith
  have h2 : 2 * r₀ ≤ L / Real.sqrt Q := by
    rw [hr₀]
    have h2Q : Real.sqrt Q ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt (by linarith)
    rw [show 2 * (L / (2 * Real.sqrt (2 * Q))) = L / Real.sqrt (2 * Q) by field_simp]
    exact div_le_div_of_nonneg_left hL.le hsQ h2Q
  calc (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀ := hN
    _ ≤ 2 * (A * Real.sqrt K / Real.sqrt Q) + L / Real.sqrt Q := by linarith
    _ = (2 * A * Real.sqrt K + L) / Real.sqrt Q := by ring

private theorem false_of_terminal_counterexamples_local_O3 {ε : ℝ}
    (heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) {A Cq θ : ℝ} (hA : 0 < A) (hθ : 0 < θ)
    {K : ℝ} (hK : K = max Cq 1) (Dn : ℕ → ℝ) (hDn : Tendsto Dn atTop atTop)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters}
    (records : ∀ n (i : Fin (H n).eventCount), GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hscale : ∀ n i b z, ((records n i).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i).static b).witness.metric
        (((records n i).static b).witness.cap z))
    (hacc : ∀ n, (p n).modelAccuracy ≤ 1 / 2) (hradius : ∀ n, Dn n ≤ (p n).modelRadius)
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hΛ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n))
    (hΛt : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n) * t n)
    (hW : ∀ n x, q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, (G n).DerivativeBoundBefore Ctime (q n) (t n))
    (hgrad : ∀ n, (G n).GradientBoundBefore Cgrad (q n) (t n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ n, (∀ (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier),
        riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) w < ENNReal.ofReal (ρ n) →
        ∀ b : ℝ, 0 < b → b ≤ ρ n →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H n).stage (Fin.last (H n).eventCount)).Carrier
              ((G n).flow.base.metric (t n)) (riemannianBallOf ((G n).flow.base.metric (t n)) w b)))
    (hρ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (Dn n) θ)
    (z : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hz : ∀ n, z n ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))
    (hbad : ∀ n : ℕ, ((n : ℝ) + K + 1) * (G n).flow.scalar (t n) (y n) <
      (G n).flow.scalar (t n) (z n)) : False := by
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hRpos (n : ℕ) : 0 < (G n).flow.scalar (t n) (y n) := by linarith [hΛ n, hn0 n]
  have hqK (n : ℕ) : q n ≤ K * (G n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (hK ▸ le_max_left _ _) (hRpos n).le)
  let Asl : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (t n) := fun n =>
    (G n).closedPrefix (t n) (ht n) (hts n)
  have hzmax (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      (G n).flow.scalar (t n) (z n) := by
    refine max_le ?_ ?_
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  choose xc Nc pc hxc hxy hpc0 hpcN hchainc hMc hNc using fun n =>
    (Asl n).exists_rebase_chain Cgrad (hq n) (fun y' t' ht' hq' v => hgrad n y' t' ht' hq' v)
      (y n) (z n) (hz n) (hzmax n)
  have hQy (n : ℕ) : (G n).flow.scalar (t n) (y n) ≤ max (q n) ((G n).flow.scalar (t n) (y n)) :=
    le_max_right _ _
  have hQK (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      K * (G n).flow.scalar (t n) (y n) :=
    max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK1)
  have hU (n : ℕ) (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
      w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen := by
    change w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
    rw [(Asl n).terminalRegularRegion_eq_univ _]
    trivial
  let x : ∀ n, ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    fun n => ⟨xc n, hU n (xc n)⟩
  have hxQ (n : ℕ) : (Asl n).flow.scalar (t n) (x n).val =
      max (q n) ((G n).flow.scalar (t n) (y n)) := hxc n
  have hQ1 (n : ℕ) : 1 ≤ (Asl n).flow.scalar (t n) (x n).val := by
    rw [hxQ n]
    linarith [hQy n, hΛ n, hn0 n]
  have hlp := localPropagationRadius_pos Cgrad.coe_nonneg
  have hr₀ (n : ℕ) : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n)))) := by
    have : 0 < max (q n) ((G n).flow.scalar (t n) (y n)) := (hq n).trans_le (le_max_left _ _)
    positivity
  have hlamc (n : ℕ) : ∑ k ∈ Finset.range (Nc n), (fun _ : ℕ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) k ≤
      (2 * A * Real.sqrt K + localPropagationRadius Cgrad) /
        Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hxQ n]
    exact rebase_lam_bound_O3 hA hK1 (hRpos n) (hQy n) (hQK n) hlp rfl (hNc n)
  have htr (n : ℕ) := RetainedCoreHistory.chain_traces_of_not_capWindowPoint_of_incomingSlab
    (H n) (hend n) (G n) (hG n) (ht n) (hts n) (records n) (hcan n) (hscale n) (hacc n) hphi
    (hpinch n) (hpinchG n) (hslabs n) (hder n) le_rfl (hradius n) (y n) (hnot n) (pc n)
    (fun _ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) (hpc0 n)
    (fun _ _ => hr₀ n) (hchainc n) (hMc n) (hlamc n)
  have hlam : 0 ≤ 2 * A * Real.sqrt K + localPropagationRadius Cgrad := by positivity
  have hDn' : Tendsto Dn atTop atTop := hDn
  have hQlim : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    rw [hxQ n]
    linarith [hQy n, hΛ n, hK1]
  have htime : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val * t n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have ht0 : 0 ≤ t n := ((H n).toHistory.time_nonneg _).trans (ht n).le
    rw [hxQ n]
    have := mul_le_mul_of_nonneg_right (hQy n) ht0
    linarith [hΛt n, hK1]
  let σ : ℕ → ℝ := fun n => ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))
  have hσlim : Tendsto (fun n => σ n * Real.sqrt ((Asl n).flow.scalar (t n) (x n).val))
      atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + (K + 1 - A)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have hid : σ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) =
        ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) - A := by
      change (ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))) *
        Real.sqrt ((G n).flow.scalar (t n) (y n)) = _
      field_simp
    have hAn : A ≤ (n : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hn)
    have hρn := hρ n
    have hlow : (n : ℝ) + (K + 1 - A) ≤ σ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
      rw [hid]; linarith
    have hσ0 : 0 ≤ σ n := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hsy
      linarith
    rw [hxQ n]
    exact hlow.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQy n)) hσ0)
  have hloc : ∀ n (zz : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((Asl n).endpointTerminalLimitMetric
        ((H n).stage (Fin.last (H n).eventCount))).metric (x n) zz < ENNReal.ofReal (σ n) →
      ∀ b : ℝ, 0 < b → b ≤ σ n →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
            ((Asl n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            (riemannianBallOf ((Asl n).endpointTerminalLimitMetric
              ((H n).stage (Fin.last (H n).eventCount))).metric zz b) := by
    intro n zz hzz b hb hbσ
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have ha'0 : 0 ≤ A / Real.sqrt ((G n).flow.scalar (t n) (y n)) := div_nonneg hA.le hsy.le
    have hσpos : 0 < σ n := hb.trans_le hbσ
    have hσρ : σ n ≤ ρ n := by
      change ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n)) ≤ ρ n; linarith
    rw [(Asl n).riemannianEDistOf_endpointTerminalLimitMetric] at hzz
    have hyz : riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) zz.val <
        ENNReal.ofReal (ρ n) := by
      calc riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) zz.val
          ≤ riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) (xc n) +
              riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) zz.val :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) +
            ENNReal.ofReal (σ n) := ENNReal.add_lt_add (hxy n) hzz
        _ = ENNReal.ofReal (ρ n) := by
            rw [← ENNReal.ofReal_add ha'0 hσpos.le]
            congr 1
            change A / Real.sqrt ((G n).flow.scalar (t n) (y n)) +
              (ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))) = ρ n
            ring
    have hv := hnc n zz.val hyz b hb (hbσ.trans hσρ)
    have hUc : IsClosed ((((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :
        TopologicalSpace.Opens ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
          Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) := by
      change IsClosed ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
      rw [(Asl n).terminalRegularRegion_eq_univ _]
      exact isClosed_univ
    have heq := riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
      ((Asl n).flow.base.metric (t n))
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen hUc zz b
    dsimp only at heq
    change _ ≤ riemannianVolumeMeasure ThreeModel
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
      (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen)
      (riemannianBallOf (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen) zz b)
    rw [heq]
    exact hv
  obtain ⟨B, hB⟩ := exists_normalized_scalar_bound_of_chain_traces_local_O3
    H t Asl (fun n => hG n) (fun n => (hend n) ▸ ht n) Ctime Cgrad q hq
    (fun n j y' t' ht' hq' => hslabs n j (Fin.castSucc_lt_last j) y' t' ht' hq')
    (fun n y' t' ht' hq' => hder n y' t' ht' hq')
    (fun n y' t' ht' hq' v => hgrad n y' t' ht' hq' v) x hQ1
    (fun n => by rw [hxQ n]; exact le_max_left _ _) hQlim hphi (fun n => hpinch n)
    (fun n τ hτ w => hpinchG n τ ⟨hτ.1, hτ.2.trans (hts n)⟩ w) σ hκ hσlim hloc
    heps (fun n => hW n) htime (Kc := 6) hlam hθ Dn hDn'
    (fun n N pp δ M τ h0 hδ hch hb hKc h1 hτ0 hτt hC h4 hDD =>
      htr n N pp δ M τ (h0.trans (hpcN n).symm) hδ hch hb
        (by rw [hxQ n] at hKc; exact hKc) (by
          rw [hxQ n] at hKc
          have := le_max_left (q n) ((G n).flow.scalar (t n) (y n))
          linarith) h1 hτ0 hτt hC h4 hDD)
    (2 * A * Real.sqrt K + 1) (by positivity)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, hU n (z n)⟩
  have hsx : 0 < Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ1 n))
  have hsy : 0 < Real.sqrt ((G n).flow.scalar (t n) (y n)) := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (by linarith), hxQ n]
    exact Real.sqrt_le_sqrt (hQK n)
  have hxz : riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n) <
      ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
    calc riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n)
        ≤ riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (y n) +
          riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) (z n) :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) +
          ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) := by
          rw [riemannianEDistOf_comm]
          exact ENNReal.add_lt_add (hxy n) (hz n)
      _ = ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
          rw [← ENNReal.ofReal_add (div_nonneg hA.le (Real.sqrt_nonneg _))
            (div_nonneg hA.le (Real.sqrt_nonneg _))]
          ring_nf
  have hdist : riemannianEDistOf (scaleMetric ((Asl n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ1 n))
      ((Asl n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (2 * A * Real.sqrt K + 1) := by
    rw [(Asl n).scaled_endpoint_edist_eq]
    calc ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((Asl n).flow.base.metric (t n)) (x n).val z'.val <
        ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top hxz
      _ = ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
          (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (2 * A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
            (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) =
            2 * A * (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) /
              Real.sqrt ((G n).flow.scalar (t n) (y n))) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hsy]
          exact hratio
      _ < ENNReal.ofReal (2 * A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((Asl n).endpointTerminalLimitMetric _).metric z' =
      (G n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ1 n)), hxQ n] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hQKn := hQK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤
        B * (K * (G n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hQKn hB0
    have h2 : B * K * (G n).flow.scalar (t n) (y n) ≤ n * (G n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    nlinarith
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (by linarith [hQy n])
    nlinarith

theorem exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_local_O3
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
      Λ ≤ G.flow.scalar t y * t →
      (∀ x, q < G.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime q t → G.GradientBoundBefore Cgrad q t →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      (∀ (w : ((H).stage (Fin.last (H).eventCount)).Carrier),
        riemannianEDistOf ((G).flow.base.metric (t)) (y) w < ENNReal.ofReal (ρ) →
        ∀ b : ℝ, 0 < b → b ≤ ρ →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H).stage (Fin.last (H).eventCount)).Carrier
              ((G).flow.base.metric (t)) (riemannianBallOf ((G).flow.base.metric (t)) w b)) →
      Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
      ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θ →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
        G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    unfold coneAccuracy at hεle
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  have hTE := StandardCap.transitionEnd_pos
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hDn (n : ℕ) : StandardCap.transitionEnd < StandardCap.transitionEnd + 1 + n := by
    linarith [hn0 n]
  have hK1 : (1 : ℝ) ≤ max Cq 1 := le_max_right _ _
  choose ε₀ hε₀ hsc using fun n : ℕ =>
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
      (StandardCap.transitionEnd + 1 + n) (hDn n)
  by_contra hcon
  push Not at hcon
  choose H hend s G hG p₀ δb ρb p records hrec hRrad hord hζ t ht hts y q ρ hq hqy hΛ hΛt hW
    hslabs hder hgrad hpinch hpinchG hnc hρ hnot z hz hbad using fun n : ℕ =>
    hcon ((n : ℝ) + max Cq 1 + 1) ((n : ℝ) + max Cq 1 + 1) (StandardCap.transitionEnd + 1 + n)
      (StandardCap.transitionEnd + 1 + n) (min (1 / 2) (ε₀ n)) (by linarith [hn0 n])
      (by linarith [hn0 n]) (hDn n) le_rfl (lt_min (by norm_num) (hε₀ n))
  have hcan (n : ℕ) := (hrec n).2.2.2.2.2.1
  have hradius (n : ℕ) : StandardCap.transitionEnd + 1 + n ≤ (p n).modelRadius := by
    rw [(hrec n).2.1]
    exact hRrad n
  have hacc (n : ℕ) : (p n).modelAccuracy ≤ 1 / 2 := by
    rw [(hrec n).2.2.2.1]
    exact (hζ n).trans (min_le_left _ _)
  have hscale (n : ℕ) (i : Fin (H n).eventCount)
      (b : ((H n).toHistory.event i).RetainedBoundaryIndex) (w : ThreeBall) :
      ((records n i).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i).static b).witness.metric
        (((records n i).static b).witness.cap w) :=
    hsc n ((H n).toHistory.event i) (hradius n)
      (by rw [(hrec n).2.2.2.1]; exact (hζ n).trans (min_le_right _ _))
      (by rw [(hrec n).2.2.1]; exact hord n) ((records n i).static b) (hcan n i b) w
  refine false_of_terminal_counterexamples_local_O3 heps hκ hphi hA hθ rfl
    (fun n => StandardCap.transitionEnd + 1 + n) ?_ H hend s G hG records hcan hscale hacc
    hradius t ht hts y q ρ hq hqy hΛ hΛt hW hslabs hder hgrad hpinch hpinchG hnc hρ hnot z hz hbad
  exact tendsto_atTop_add_const_left atTop _ tendsto_natCast_atTop_atTop


end GC.LongTime.Ch12
