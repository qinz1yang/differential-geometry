import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedSecondLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_of_chain_backward_traces
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ : ℝ} (hθ : 0 < θ)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ (G n).flow.scalar (t n) (y n))
    (hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop)
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (hW : ∀ n x, q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, (G n).DerivativeBoundBefore Ctime (q n) (t n))
    (hgrad : ∀ n, (G n).GradientBoundBefore Cgrad (q n) (t n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ n, (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ (ρ n) (t n))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (hsupply : ∀ n (N : ℕ) (p : ℕ → ((H n).stage (Fin.last (H n).eventCount)).Carrier)
      (δ : ℕ → ℝ) (M : ℝ), p 0 = y n → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (p k) (δ k),
        (G n).flow.scalar (t n) z ≤ M) →
      (G n).flow.scalar (t n) (y n) ≤ M →
      M ≤ D n ^ 2 * (G n).flow.scalar (t n) (y n) →
      ∑ k ∈ Finset.range (N + 1), δ k ≤ D n / Real.sqrt ((G n).flow.scalar (t n) (y n)) →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (p k) (δ k),
        ∃ first : Fin ((H n).eventCount + 1), (H n).time first ≤ t n - θ / M ∧
          Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  intro A hA
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    unfold coneAccuracy at hεle
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  by_contra hcon
  push Not at hcon
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
      (∃ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ((k : ℝ) + 1) * (G n).flow.scalar (t n) (y n) < (G n).flow.scalar (t n) z) ∧
      (1 ≤ (G n).flow.scalar (t n) (y n) ∧
        1 ≤ ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) := fun k =>
    (hcon ((k : ℝ) + 1) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])).and_eventually
      ((hR.eventually_ge_atTop 1).and (hρ.eventually_ge_atTop 1))
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_frequently hfreq
  choose z hz hzbad using fun k => (hbad k).1
  have hR1 (k : ℕ) : 1 ≤ (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) := (hbad k).2.1
  have hσQ (k : ℕ) : 1 ≤ ρ (φ k) * Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) :=
    (hbad k).2.2
  have hφt := hφ.tendsto_atTop
  let Asl : ∀ k, ((H (φ k)).stage (Fin.last (H (φ k)).eventCount)).ClosedSlab
      ((H (φ k)).time (Fin.last (H (φ k)).eventCount)) (t (φ k)) := fun k =>
    (G (φ k)).closedPrefix (t (φ k)) (ht (φ k)) (hts (φ k))
  have hU (k : ℕ) (w : ((H (φ k)).stage (Fin.last (H (φ k)).eventCount)).Carrier) :
      w ∈ ((Asl k).restrictIncoming le_rfl (Asl k).lt le_rfl).terminalRegularOpen := by
    change w ∈ ((Asl k).restrictIncoming le_rfl (Asl k).lt le_rfl).terminalRegularRegion
    rw [(Asl k).terminalRegularRegion_eq_univ _]
    trivial
  let x : ∀ k, ((Asl k).restrictIncoming le_rfl (Asl k).lt le_rfl).terminalRegularOpen :=
    fun k => ⟨y (φ k), hU k (y (φ k))⟩
  have hTE := StandardCap.transitionEnd_pos
  obtain ⟨B, hB⟩ := RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces
    (fun k => H (φ k)) (fun k => t (φ k)) Asl (fun k => hG (φ k))
    (fun k => (hend (φ k)) ▸ ht (φ k)) Ctime Cgrad (fun k => q (φ k)) (fun k => hq (φ k))
    (fun k j y' t' ht' hq' => hslabs (φ k) j (Fin.castSucc_lt_last j) y' t' ht' hq')
    (fun k y' t' ht' hq' => hder (φ k) y' t' ht' hq')
    (fun k y' t' ht' hq' v => hgrad (φ k) y' t' ht' hq' v) x hR1 (fun k => hqy (φ k))
    (hR.comp hφt) hphi (fun k => hpinch (φ k))
    (fun k τ hτ w => hpinchG (φ k) τ ⟨hτ.1, hτ.2.trans (hts (φ k))⟩ w) (fun k => ρ (φ k)) hκ
    one_pos hσQ
    (fun k T hT hTt => by
      intro _ tm yy b _ hbρ hball
      exact RetainedCoreHistory.noncollapsedBefore_closedPrefix_of_terminalNoncollapsedBefore
        (H (φ k)) (hend (φ k)) (G (φ k)) (hG (φ k)) (hnc (φ k)) (ht (φ k)) (hts (φ k)) le_rfl T
        hT hTt tm yy b le_rfl hbρ hball)
    heps (fun k => hW (φ k)) (hRt.comp hφt) (Kc := 1) (lam := 1) zero_le_one
    (θ := 4 * θ) (by positivity) (fun k => Real.sqrt 8 * D (φ k))
    ((hD.comp hφt).const_mul_atTop (by positivity))
    (fun k N pp δ M τ h0 hδ hch hb hKc h1 hτ0 _ _ h4 hDD => by
      have hRy : 1 ≤ (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) := hR1 k
      have hRypos : 0 < (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) := by linarith
      have hsRy : 0 < Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) :=
        Real.sqrt_pos.mpr hRypos
      have hRM : (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) ≤ M := by
        have h := hKc
        rw [one_mul] at h
        exact h
      have hMpos : 0 < M := by linarith
      have hsM : Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) ≤ Real.sqrt M :=
        Real.sqrt_le_sqrt hRM
      have hsMpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
      have hS0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), δ j := Finset.sum_nonneg fun j hj =>
        (hδ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).le
      have hE : 1 ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) := by
        have h1p := hphi.pos 1
        have h0p := hphi.pos 0
        exact Real.one_le_exp (by positivity)
      have hmain : Real.sqrt M * (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
          ∑ j ∈ Finset.range (N + 1), δ j) < D (φ k) := by
        have hpos : 0 ≤ Real.sqrt (8 * M) *
            (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
              ∑ j ∈ Finset.range (N + 1), δ j) := by positivity
        have hle : Real.sqrt (8 * M) *
            (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
              ∑ j ∈ Finset.range (N + 1), δ j) < Real.sqrt 8 * D (φ k) := by
          have hDD' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
              Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
              (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
                ∑ j ∈ Finset.range (N + 1), δ j) < Real.sqrt 8 * D (φ k) := hDD
          have hX := le_mul_of_one_le_right hpos hE
          have hre : Real.sqrt (8 * M) *
              Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
              (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
                ∑ j ∈ Finset.range (N + 1), δ j) =
              Real.sqrt (8 * M) *
              (1 / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) +
                ∑ j ∈ Finset.range (N + 1), δ j) *
              Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) := by ring
          linarith
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), mul_assoc] at hle
        exact lt_of_mul_lt_mul_left hle (Real.sqrt_nonneg 8)
      have hfirst : Real.sqrt M / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) <
          D (φ k) := by
        have h := mul_nonneg hsMpos.le hS0
        rw [mul_add, mul_one_div] at hmain
        linarith
      have hD0 : 0 < D (φ k) := lt_of_le_of_lt (by positivity) hfirst
      have hMle : M ≤ D (φ k) ^ 2 * (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) := by
        rw [div_lt_iff₀ hsRy] at hfirst
        have hsq := mul_self_lt_mul_self hsMpos.le hfirst
        rw [Real.mul_self_sqrt hMpos.le] at hsq
        have hR2 := Real.mul_self_sqrt hRypos.le
        nlinarith
      have hsum : ∑ j ∈ Finset.range (N + 1), δ j ≤
          D (φ k) / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) := by
        have h := mul_nonneg hsMpos.le (one_div_nonneg.mpr hsRy.le)
        rw [mul_add] at hmain
        have h2 : Real.sqrt M * ∑ j ∈ Finset.range (N + 1), δ j < D (φ k) := by linarith
        have h3 : ∑ j ∈ Finset.range (N + 1), δ j < D (φ k) / Real.sqrt M := by
          rw [lt_div_iff₀ hsMpos]
          linarith
        exact h3.le.trans (div_le_div_of_nonneg_left hD0.le hsRy hsM)
      intro k' hk' w hw
      obtain ⟨first, hfirst', htr⟩ :=
        hsupply (φ k) N pp δ M h0 hδ hch hb hRM hMle hsum k' hk' w hw
      refine ⟨first, hfirst'.trans ?_, htr⟩
      have hτθ : τ ≤ θ / M := by
        rw [le_div_iff₀ hMpos]
        linarith
      linarith)
    (A + 1) (by positivity)
  obtain ⟨k, hk, hkB⟩ := (hB.and (eventually_gt_atTop ⌈B⌉₊)).exists
  let z' : ((Asl k).restrictIncoming le_rfl (Asl k).lt le_rfl).terminalRegularOpen :=
    ⟨z k, hU k (z k)⟩
  have hRpos : 0 < (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) := zero_lt_one.trans_le (hR1 k)
  have hsy : 0 < Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k))) :=
    Real.sqrt_pos.mpr hRpos
  have hdist : riemannianEDistOf (scaleMetric ((Asl k).flow.scalar (t (φ k)) (x k).val)
      (zero_lt_one.trans_le (hR1 k))
      ((Asl k).endpointTerminalLimitMetric _).metric) (x k) z' <
        ENNReal.ofReal (A + 1) := by
    rw [(Asl k).scaled_endpoint_edist_eq]
    calc ENNReal.ofReal (Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k)))) *
          riemannianEDistOf ((G (φ k)).flow.base.metric (t (φ k))) (y (φ k)) (z k) <
        ENNReal.ofReal (Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k)))) *
          ENNReal.ofReal (A / Real.sqrt ((G (φ k)).flow.scalar (t (φ k)) (y (φ k)))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsy).ne' ENNReal.ofReal_ne_top (hz k)
      _ = ENNReal.ofReal A := by
          rw [← ENNReal.ofReal_mul hsy.le, mul_div_cancel₀ _ hsy.ne']
      _ < ENNReal.ofReal (A + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hk z' hdist
  have hscal : metricScalarAt ((Asl k).endpointTerminalLimitMetric _).metric z' =
      (G (φ k)).flow.scalar (t (φ k)) (z k) := metricScalarAt_restrictOpen _ _ _
  rw [hscal] at hle
  change (G (φ k)).flow.scalar (t (φ k)) (z k) /
    (G (φ k)).flow.scalar (t (φ k)) (y (φ k)) ≤ B at hle
  rw [div_le_iff₀ hRpos] at hle
  have hceil : B ≤ (k : ℝ) := (Nat.le_ceil B).trans (by exact_mod_cast hkB.le)
  have hbadk := hzbad k
  nlinarith

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem RetainedCoreHistory.eventually_terminal_scalar_bound_at_distance_of_chain_backward_traces
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ : ℝ} (hθ : 0 < θ)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (L : ∀ n, (G n).TerminalLimitMetric) (x : ∀ n, (G n).terminalRegularOpen)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hρ0 : ∀ n, 0 < ρ n)
    (hqx : ∀ᶠ n in atTop, q n < metricScalarAt (L n).metric (x n))
    (hR : Tendsto (fun n => metricScalarAt (L n).metric (x n)) atTop atTop)
    (hRs : Tendsto (fun n => metricScalarAt (L n).metric (x n) * s n) atTop atTop)
    (hW : ∀ n, (G n).SpatiallyCanonicalBefore ε C1 C2 (q n) (s n))
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, (G n).DerivativeBoundBefore Ctime (q n) (s n))
    (hgrad : ∀ n, (G n).GradientBoundBefore Cgrad (q n) (s n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ n, ∀ t₀ ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
      (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ (ρ n) t₀)
    (hρ : Tendsto (fun n => ρ n * Real.sqrt (metricScalarAt (L n).metric (x n))) atTop atTop)
    (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (hsupply : ∀ᶠ n in atTop, ∀ᶠ τ in 𝓝[<] s n,
      ∀ (N : ℕ) (p : ℕ → ((H n).stage (Fin.last (H n).eventCount)).Carrier)
        (δ : ℕ → ℝ) (M : ℝ), p 0 = (x n).val → (∀ k ≤ N, 0 < δ k) →
        (∀ k < N, p (k + 1) ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k)) →
        (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
          (G n).flow.scalar τ z ≤ M) →
        (G n).flow.scalar τ (x n).val ≤ M →
        M ≤ D n ^ 2 * (G n).flow.scalar τ (x n).val →
        ∑ k ∈ Finset.range (N + 1), δ k ≤ D n / Real.sqrt ((G n).flow.scalar τ (x n).val) →
        ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
          ∃ first : Fin ((H n).eventCount + 1), (H n).time first ≤ τ - θ / M ∧
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) z)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      (∀ w : (G n).terminalRegularOpen,
        riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n))) →
        metricScalarAt (L n).metric w ≤ Q * metricScalarAt (L n).metric (x n)) ∧
      IsCompact (riemannianClosedBallOf (L n).metric (x n)
        (A / Real.sqrt (metricScalarAt (L n).metric (x n)))) := by
  have hbound : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ w : (G n).terminalRegularOpen,
        riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n))) →
        metricScalarAt (L n).metric w ≤ Q * metricScalarAt (L n).metric (x n) := by
    intro A hA
    by_contra hcon
    push Not at hcon
    have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
        (∃ w : (G n).terminalRegularOpen,
          riemannianEDistOf (L n).metric (x n) w <
            ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n))) ∧
          4 * ((k : ℝ) + 1) * metricScalarAt (L n).metric (x n) <
            metricScalarAt (L n).metric w) ∧
        1 ≤ metricScalarAt (L n).metric (x n) ∧ q n < metricScalarAt (L n).metric (x n) ∧
        ∀ᶠ τ in 𝓝[<] s n,
          ∀ (N : ℕ) (p : ℕ → ((H n).stage (Fin.last (H n).eventCount)).Carrier)
            (δ : ℕ → ℝ) (M : ℝ), p 0 = (x n).val → (∀ k ≤ N, 0 < δ k) →
            (∀ k < N, p (k + 1) ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k)) →
            (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
              (G n).flow.scalar τ z ≤ M) →
            (G n).flow.scalar τ (x n).val ≤ M →
            M ≤ D n ^ 2 * (G n).flow.scalar τ (x n).val →
            ∑ k ∈ Finset.range (N + 1), δ k ≤ D n / Real.sqrt ((G n).flow.scalar τ (x n).val) →
            ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
              ∃ first : Fin ((H n).eventCount + 1), (H n).time first ≤ τ - θ / M ∧
                Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
                  (Fin.le_last first) z) := fun k =>
      (hcon (4 * ((k : ℝ) + 1)) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])).and_eventually
        ((hR.eventually_ge_atTop 1).and (hqx.and hsupply))
    obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_frequently hfreq
    choose w hwd hwbad using fun k => (hbad k).1
    have hR1 (k : ℕ) : 1 ≤ metricScalarAt (L (φ k)).metric (x (φ k)) := (hbad k).2.1
    have hφt := hφ.tendsto_atTop
    have hev : ∀ k : ℕ, ∀ᶠ τ in 𝓝[<] s (φ k),
        τ ∈ Ioo (max ((H (φ k)).time (Fin.last (H (φ k)).eventCount)) (s (φ k) / 2)) (s (φ k)) ∧
        (G (φ k)).flow.scalar τ (x (φ k)).val ∈
          Ioo (metricScalarAt (L (φ k)).metric (x (φ k)) / 2)
            (2 * metricScalarAt (L (φ k)).metric (x (φ k))) ∧
        q (φ k) < (G (φ k)).flow.scalar τ (x (φ k)).val ∧
        riemannianEDistOf ((G (φ k)).flow.base.metric τ) (x (φ k)).val (w k).val <
          ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L (φ k)).metric (x (φ k)))) ∧
        2 * ((k : ℝ) + 1) * metricScalarAt (L (φ k)).metric (x (φ k)) <
          (G (φ k)).flow.scalar τ (w k).val ∧
        ∀ (N : ℕ) (p : ℕ → ((H (φ k)).stage (Fin.last (H (φ k)).eventCount)).Carrier)
          (δ : ℕ → ℝ) (M : ℝ), p 0 = (x (φ k)).val → (∀ j ≤ N, 0 < δ j) →
          (∀ j < N, p (j + 1) ∈ riemannianBallOf ((G (φ k)).flow.base.metric τ) (p j) (δ j)) →
          (∀ j ≤ N, ∀ z ∈ riemannianBallOf ((G (φ k)).flow.base.metric τ) (p j) (δ j),
            (G (φ k)).flow.scalar τ z ≤ M) →
          (G (φ k)).flow.scalar τ (x (φ k)).val ≤ M →
          M ≤ D (φ k) ^ 2 * (G (φ k)).flow.scalar τ (x (φ k)).val →
          ∑ j ∈ Finset.range (N + 1), δ j ≤
            D (φ k) / Real.sqrt ((G (φ k)).flow.scalar τ (x (φ k)).val) →
          ∀ j ≤ N, ∀ z ∈ riemannianBallOf ((G (φ k)).flow.base.metric τ) (p j) (δ j),
            ∃ first : Fin ((H (φ k)).eventCount + 1),
              (H (φ k)).time first ≤ τ - θ / M ∧
              Nonempty (BackwardPointTrace (H (φ k)).toHistory first
                (Fin.last (H (φ k)).eventCount) (Fin.le_last first) z) := by
      intro k
      have hRl : 0 < metricScalarAt (L (φ k)).metric (x (φ k)) := zero_lt_one.trans_le (hR1 k)
      have hs0 : 0 < s (φ k) :=
        ((H (φ k)).toHistory.time_nonneg _).trans_lt (G (φ k)).lt
      have hlow : max ((H (φ k)).time (Fin.last (H (φ k)).eventCount)) (s (φ k) / 2) <
          s (φ k) := max_lt (G (φ k)).lt (by linarith)
      have hw2 : 2 * ((k : ℝ) + 1) * metricScalarAt (L (φ k)).metric (x (φ k)) <
          metricScalarAt (L (φ k)).metric (w k) := by
        have := hwbad k
        nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
      filter_upwards [Ioo_mem_nhdsLT hlow,
        ((L (φ k)).tendsto_metricScalarAt (x (φ k))).eventually
          (Ioo_mem_nhds (by linarith : metricScalarAt (L (φ k)).metric (x (φ k)) / 2 <
            metricScalarAt (L (φ k)).metric (x (φ k)))
            (by linarith : metricScalarAt (L (φ k)).metric (x (φ k)) <
              2 * metricScalarAt (L (φ k)).metric (x (φ k)))),
        ((L (φ k)).tendsto_metricScalarAt (x (φ k))).eventually (lt_mem_nhds (hbad k).2.2.1),
        (L (φ k)).eventually_riemannianEDistOf_lt (x (φ k)) (w k) (hwd k),
        ((L (φ k)).tendsto_metricScalarAt (w k)).eventually (lt_mem_nhds hw2),
        (hbad k).2.2.2] with τ h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    choose τ hτ using fun k => (hev k).exists
    have hτa (k : ℕ) : (H (φ k)).time (Fin.last (H (φ k)).eventCount) < τ k :=
      (le_max_left _ _).trans_lt (hτ k).1.1
    have hτs (k : ℕ) : τ k < s (φ k) := (hτ k).1.2
    have hτ2 (k : ℕ) : s (φ k) / 2 ≤ τ k := ((le_max_right _ _).trans_lt (hτ k).1.1).le
    obtain ⟨Q₀, -, hQ₀⟩ :=
      RetainedCoreHistory.eventually_scalar_bound_at_distance_of_chain_backward_traces hεle hκ
        hphi hθ (fun k => H (φ k)) (fun k => hend (φ k)) (fun k => s (φ k))
        (fun k => G (φ k)) (fun k => hG (φ k)) τ hτa hτs (fun k => (x (φ k)).val)
        (fun k => q (φ k)) (fun k => ρ (φ k)) (fun k => hq (φ k)) (fun k => (hτ k).2.2.1.le)
        (tendsto_atTop_mono (fun k => (hτ k).2.1.1.le) ((hR.comp hφt).atTop_div_const two_pos))
        (tendsto_atTop_mono (fun k => by
            have h1 := (hτ k).2.1.1
            have h2 := hτ2 k
            have hs0 : 0 < s (φ k) :=
              ((H (φ k)).toHistory.time_nonneg _).trans_lt (G (φ k)).lt
            have hRl := zero_lt_one.trans_le (hR1 k)
            change metricScalarAt (L (φ k)).metric (x (φ k)) * s (φ k) / 4 ≤
              (G (φ k)).flow.scalar (τ k) (x (φ k)).val * τ k
            nlinarith)
          ((hRs.comp hφt).atTop_div_const (by norm_num : (0 : ℝ) < 4)))
        (fun k y' hy' => hW (φ k) y' (τ k) ⟨hτa k, hτs k⟩ hy')
        (fun k => hslabs (φ k))
        (fun k y' t' ht' => hder (φ k) y' t' ⟨ht'.1, ht'.2.trans (hτs k)⟩)
        (fun k y' t' ht' => hgrad (φ k) y' t' ⟨ht'.1, ht'.2.trans (hτs k)⟩)
        (fun k => hpinch (φ k)) (fun k => hpinchG (φ k))
        (fun k => hnc (φ k) (τ k) ⟨hτa k, hτs k⟩)
        (tendsto_atTop_mono (fun k => by
            have h1 := (hτ k).2.1.1
            have hRl := zero_lt_one.trans_le (hR1 k)
            change ρ (φ k) * Real.sqrt (metricScalarAt (L (φ k)).metric (x (φ k))) /
                Real.sqrt 2 ≤
              ρ (φ k) * Real.sqrt ((G (φ k)).flow.scalar (τ k) (x (φ k)).val)
            rw [mul_div_assoc, ← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1.le) (hρ0 (φ k)).le)
          ((hρ.comp hφt).atTop_div_const (Real.sqrt_pos.mpr two_pos)))
        (fun k => D (φ k)) (hD.comp hφt) (fun k => (hτ k).2.2.2.2.2) (2 * A) (by positivity)
    obtain ⟨k, hk, hkQ⟩ := (hQ₀.and (eventually_gt_atTop ⌈Q₀⌉₊)).exists
    have hRl : 0 < metricScalarAt (L (φ k)).metric (x (φ k)) := zero_lt_one.trans_le (hR1 k)
    have hRτ := (hτ k).2.1
    have hRτpos : 0 < (G (φ k)).flow.scalar (τ k) (x (φ k)).val := by linarith [hRτ.1]
    have hball : (w k).val ∈ riemannianBallOf ((G (φ k)).flow.base.metric (τ k)) (x (φ k)).val
        (2 * A / Real.sqrt ((G (φ k)).flow.scalar (τ k) (x (φ k)).val)) := by
      change riemannianEDistOf ((G (φ k)).flow.base.metric (τ k)) (x (φ k)).val (w k).val < _
      refine (hτ k).2.2.2.1.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hRl) (Real.sqrt_pos.mpr hRτpos)]
      have hsq : Real.sqrt ((G (φ k)).flow.scalar (τ k) (x (φ k)).val) ≤
          2 * Real.sqrt (metricScalarAt (L (φ k)).metric (x (φ k))) := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
          ← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by linarith [hRτ.2])
      nlinarith
    have hle : (G (φ k)).flow.scalar (τ k) (w k).val ≤
        Q₀ * (G (φ k)).flow.scalar (τ k) (x (φ k)).val := hk (w k).val hball
    have hceil : Q₀ ≤ (k : ℝ) := (Nat.le_ceil Q₀).trans (by exact_mod_cast hkQ.le)
    have hwk : 2 * ((k : ℝ) + 1) * metricScalarAt (L (φ k)).metric (x (φ k)) <
        (G (φ k)).flow.scalar (τ k) (w k).val := (hτ k).2.2.2.2.1
    have hQ0 : 0 ≤ Q₀ := by
      by_contra hneg
      have := mul_neg_of_neg_of_pos (not_le.mp hneg) hRτpos
      have hw0 : 0 < (G (φ k)).flow.scalar (τ k) (w k).val := by
        nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
      linarith
    have h1 := mul_le_mul_of_nonneg_left hRτ.2.le hQ0
    have h2 := mul_le_mul_of_nonneg_right hceil (by linarith : (0 : ℝ) ≤
      2 * metricScalarAt (L (φ k)).metric (x (φ k)))
    nlinarith
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := hbound (2 * A) (by positivity)
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hev, hR.eventually_gt_atTop 0] with n hn hRn
  have hsq : 0 < Real.sqrt (metricScalarAt (L n).metric (x n)) := Real.sqrt_pos.mpr hRn
  have hlt : A / Real.sqrt (metricScalarAt (L n).metric (x n)) <
      2 * A / Real.sqrt (metricScalarAt (L n).metric (x n)) :=
    div_lt_div_of_pos_right (by linarith) hsq
  refine ⟨fun w hw => hn w (hw.trans ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt)),
    ?_⟩
  refine ((L n).isCompact_scalar_sublevel
    (Q * metricScalarAt (L n).metric (x n))).of_isClosed_subset
    (isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist (L n).metric
      (x n)) continuous_const) fun w hw => hn w ?_
  exact lt_of_le_of_lt hw ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
