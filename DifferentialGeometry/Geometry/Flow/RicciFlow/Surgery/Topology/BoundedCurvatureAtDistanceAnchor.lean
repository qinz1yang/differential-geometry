import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCloseComparison
import DifferentialGeometry.Geometry.Metric.Distance.SublevelMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSliceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingPersistenceInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialWindowScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

private theorem scalar_le_of_rebase_capWindow_dichotomy {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (CWP : M → Prop)
    {Rn A D QB AB D₁ D₂ r η₃ Cup Lc : ℝ} (hRn : 0 < Rn) (hA : 1 ≤ A) (hD : 0 < D)
    (hQB : 0 ≤ QB) (hCup : 0 < Cup) (hLc : 0 < Lc) (hAB : 2 * D * Real.sqrt A ≤ AB)
    (hr : 2 * D * Lc * Real.sqrt (2 * A) < r) (hD₂ : D₁ + 1 + r ≤ D₂)
    (hB3e : ∀ w, ¬ CWP w → Rn ≤ metricScalarAt g w → ∀ x,
      riemannianEDistOf g w x < ENNReal.ofReal (AB / Real.sqrt (metricScalarAt g w)) →
        metricScalarAt g x ≤ QB * metricScalarAt g w)
    (hP1 : ∀ w, CWP w →
      ∃ (Ξ : standardCapWindow D₂ → M) (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (z₀ : standardCapWindow D₂), Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < D₁ + 1 ∧
        ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
          τw ∈ Icc (0 : ℝ) (1 / 2) ∧
          ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
            metricDerivNorm m (localPullMetric (scaleMetric lam hlam g) Ξ hΞ)
              ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
              (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)
    (hP3 : ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : SmoothRiemannianMetric (𝓡 3) U), ∀ τ ∈ Icc (0 : ℝ) (1 / 2), ∀ x : U,
        (∀ j : ℕ, j ≤ 2 → metricDerivNorm j g ((Q.val.metric τ).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ η₃) →
        1 / 2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ Cup ∧
        ∀ v : TangentSpace (𝓡 3) x,
          (StandardCap.metric.restrictOpen U).inner x v v ≤ Lc ^ 2 * g.inner x v v)
    (z x : M) (hz : metricScalarAt g z ≤ A * Rn)
    (hzx : riemannianEDistOf g z x < ENNReal.ofReal (D / Real.sqrt Rn)) :
    metricScalarAt g x ≤ A * (QB + 2 * Cup + 1) * Rn := by
  set R := metricScalarAt g with hRdef
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hbound : A * Rn ≤ A * (QB + 2 * Cup + 1) * Rn := by
    have : A * 1 * Rn ≤ A * (QB + 2 * Cup + 1) * Rn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA0.le) hRn.le
    simpa using this
  by_cases hx : R x ≤ A * Rn
  · exact hx.trans hbound
  push Not at hx
  have hsRn : 0 < Real.sqrt Rn := Real.sqrt_pos.mpr hRn
  obtain ⟨w, hRw, hzw⟩ : ∃ w, R w = max Rn (R z) ∧
      riemannianEDistOf g z w ≤ riemannianEDistOf g z x := by
    by_cases hzR : Rn ≤ R z
    · refine ⟨z, by rw [max_eq_right hzR], ?_⟩
      rw [riemannianEDistOf_self]
      exact bot_le
    · push Not at hzR
      have hcont : Continuous R := (metricScalar_smooth g).continuous
      have hK : IsCompact {w | R w ≤ Rn} := (isClosed_le hcont continuous_const).isCompact
      have hRxn : Rn ≤ R x := by nlinarith
      obtain ⟨w, -, hw, -, hwz, -⟩ :=
        Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel g R hcont hK z x hzR
          hRxn (ne_top_of_lt hzx)
      exact ⟨w, by rw [hw, max_eq_left hzR.le], hwz⟩
  set L := R w with hLdef
  have hLn : Rn ≤ L := by rw [hRw]; exact le_max_left _ _
  have hLA : L ≤ A * Rn := by
    rw [hRw]
    exact max_le (by nlinarith) hz
  have hL : 0 < L := hRn.trans_le hLn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwx : riemannianEDistOf g w x < ENNReal.ofReal (2 * D / Real.sqrt Rn) := by
    have h1 := riemannianEDistOf_triangle g w z x
    rw [riemannianEDistOf_comm g w z] at h1
    have h2 : riemannianEDistOf g z w + riemannianEDistOf g z x <
        ENNReal.ofReal (D / Real.sqrt Rn) + ENNReal.ofReal (D / Real.sqrt Rn) :=
      ENNReal.add_lt_add (hzw.trans_lt hzx) hzx
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h2
    refine h1.trans_lt (h2.trans_le (le_of_eq ?_))
    congr 1
    ring
  have hsqL : Real.sqrt L ≤ Real.sqrt A * Real.sqrt Rn := by
    rw [← Real.sqrt_mul hA0.le]
    exact Real.sqrt_le_sqrt hLA
  by_cases hcw : CWP w
  · obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hnorm, lam, hlam, Q, τw, hτw, hclose⟩ := hP1 w hcw
    set gt := localPullMetric (scaleMetric lam hlam g) Ξ hΞ with hgt
    have hP3u := fun u : standardCapWindow D₂ =>
      hP3 Q (standardCapWindow D₂) gt τw hτw u fun m hm => (hclose u m hm).le
    have hRz₀ : metricScalarAt gt z₀ = lam⁻¹ * L := by
      rw [hgt, metricScalarAt_localPullMetric_scaleMetric, hz₀]
    have hlamL : lam ≤ 2 * L := by
      have h := (hP3u z₀).1
      rw [hRz₀] at h
      have h' : lam * (1 / 2) ≤ lam * (lam⁻¹ * L) := mul_le_mul_of_nonneg_left h hlam.le
      rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
      linarith
    have hroom : ‖z₀.val‖ + r < D₂ + 1 := by linarith
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
    have hcap := ball_subset_image_capWindow_of_scaled_lower g Ξ hΞ hinj z₀ hr0 hlam hLc hroom
      fun u v => (hP3u u).2.2 v
    have hslam : Real.sqrt lam ≤ Real.sqrt (2 * A) * Real.sqrt Rn := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hxball : x ∈ riemannianBallOf g (Ξ z₀) (r / (Lc * Real.sqrt lam)) := by
      change riemannianEDistOf g (Ξ z₀) x < ENNReal.ofReal (r / (Lc * Real.sqrt lam))
      rw [hz₀]
      refine hwx.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRn (mul_pos hLc hsl)]
      have h1 : 2 * D * (Lc * Real.sqrt lam) ≤ 2 * D * Lc * Real.sqrt (2 * A) * Real.sqrt Rn := by
        have := mul_le_mul_of_nonneg_left hslam (by positivity : (0 : ℝ) ≤ 2 * D * Lc)
        linarith
      have h2 := mul_le_mul_of_nonneg_right hr.le hsRn.le
      linarith
    obtain ⟨u, -, rfl⟩ := hcap hxball
    have hRu : metricScalarAt gt u = lam⁻¹ * R (Ξ u) := by
      rw [hgt, metricScalarAt_localPullMetric_scaleMetric]
    have hup := (hP3u u).2.1
    rw [hRu] at hup
    have hRx : R (Ξ u) ≤ lam * Cup := by
      have h' := mul_le_mul_of_nonneg_left hup hlam.le
      rwa [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
    have : lam * Cup ≤ 2 * A * Cup * Rn := by nlinarith
    nlinarith
  · have hxw : riemannianEDistOf g w x < ENNReal.ofReal (AB / Real.sqrt L) := by
      refine hwx.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRn hsL]
      have h1 := mul_le_mul_of_nonneg_left hsqL (by positivity : (0 : ℝ) ≤ 2 * D)
      have h2 := mul_le_mul_of_nonneg_right hAB hsRn.le
      nlinarith
    have h := hB3e w hcw hLn x hxw
    have : QB * L ≤ QB * (A * Rn) := mul_le_mul_of_nonneg_left hLA hQB
    nlinarith

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {B ε C1 C2 τmin θ κ C1s C2s Cs : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap qcan qs η t₀ t s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
    ((H n).time (Fin.last (H n).eventCount)) (s n)}
  {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}

private theorem eventually_slab_scalar_le_at_normalized_distance
    (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ)
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ B (p₀ n) (δb n) (ρb n))
    (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslabs : ∀ n,
      (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
      (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
    (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
      (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
      (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
      (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
      (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
      (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
    (hbad : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (A Dd : ℝ) (hA : 1 ≤ A) (hD : 0 < Dd) :
    ∃ C Λ : ℝ, 0 < Λ ∧ ∀ᶠ n in atTop,
      (∀ τ : ℝ, (H n).time (Fin.last (H n).eventCount) < τ → τ < t₀ n →
        Λ ≤ (G n).flow.scalar (t n) (y n) * τ →
        ∀ z x : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
          (G n).flow.scalar τ z ≤ A * (G n).flow.scalar (t n) (y n) →
          riemannianEDistOf ((G n).flow.base.metric τ) z x <
            ENNReal.ofReal (Dd / Real.sqrt ((G n).flow.scalar (t n) (y n))) →
          (G n).flow.scalar τ x ≤ C * (G n).flow.scalar (t n) (y n)) ∧
      (∀ (j : Fin (H n).eventCount) (τ : ℝ), (H n).time j.castSucc < τ →
        τ < (H n).time j.succ → Λ ≤ (G n).flow.scalar (t n) (y n) * τ →
        ∀ z x : ((H n).stage j.castSucc).Carrier,
          ((H n).toHistory.event j).incoming.flow.scalar τ z ≤
            A * (G n).flow.scalar (t n) (y n) →
          riemannianEDistOf (((H n).toHistory.event j).incoming.flow.base.metric τ) z x <
            ENNReal.ofReal (Dd / Real.sqrt ((G n).flow.scalar (t n) (y n))) →
          ((H n).toHistory.event j).incoming.flow.scalar τ x ≤
            C * (G n).flow.scalar (t n) (y n)) := by
  set AB : ℝ := 2 * Dd * Real.sqrt A + 1 with hABdef
  have hAB : 0 < AB := by positivity
  obtain ⟨QB, Λ, Dcap, Rrad, ζB, hQB, hΛ, hDcap, -, hζB, hB3e⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal.{u}
      hεcone κ C1s C2s hκ Ctime Cgrad hphi AB hAB Cs (1 / 2) (by norm_num)
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  set r : ℝ := 2 * Dd * Lc * Real.sqrt (2 * A) + 1 with hrdef
  have hr0 : 0 < r := by positivity
  set D₂ : ℝ := Dcap + 1 + r with hD₂def
  have hDcap0 : 0 < Dcap := StandardCap.transitionEnd_pos.trans hDcap
  obtain ⟨Cbirth, hCbirth, hP1⟩ :=
    RetainedCoreHistory.exists_capWindow_embedding_standard_close.{u} Ctime
  obtain ⟨RP, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hP1'⟩ :=
    hP1 Dcap D₂ η₃ hDcap0 (by linarith) hη₃
  obtain ⟨a₀, -, hinit, hev⟩ := exists_capWindow_persistence_inputs_eventually
    (fun n => (hH n).1) hrec (fun n => (hG n).2) (fun n => (hslabs n).2.1)
    (fun n => ⟨(hbefore n).1, (hbefore n).2.2.1⟩) (fun n => (hq n).1) hpar hscale
  refine ⟨A * (QB + 2 * Cup + 1), Λ, zero_lt_one.trans_le hΛ, ?_⟩
  have hRbig : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c ≤ (G n).flow.scalar (t n) (y n) := by
    intro c
    obtain ⟨N, hN⟩ := exists_nat_gt c
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(hq n).1, hbad n]
  filter_upwards [hev (max RP Rrad) (min ζ₁ ζB) δ₀ Cbirth m₀ (lt_min hζ₁ hζB) hδ₀ hCbirth,
    hRbig Λ, hRbig ((Λ / ε) ^ 2)] with n hP1s hΛR hΛε
  obtain ⟨hδn, hRn', hmn, hζn, hbirth, -⟩ := hP1s
  set Rn := (G n).flow.scalar (t n) (y n) with hRndef
  have hqcan0 : 0 < qcan n := lt_of_lt_of_le (by positivity) (hq n).1
  have hRn : qcan n < Rn := hbad n
  have hRn0 : 0 < Rn := hqcan0.trans hRn
  have hqs0 : 0 < qs n := hqcan0.trans_le (hq n).2.1
  have hCs0 : 0 ≤ Cs := by
    by_contra hneg
    push Not at hneg
    have := (hq n).2.2
    nlinarith
  have hΛε' : Λ ≤ ε * Real.sqrt Rn := by
    have h1 : Real.sqrt ((Λ / ε) ^ 2) ≤ Real.sqrt Rn := Real.sqrt_le_sqrt hΛε
    rw [Real.sqrt_sq (div_pos (zero_lt_one.trans_le hΛ) hε).le, div_le_iff₀ hε] at h1
    linarith
  have hgates : ∀ Rw τ : ℝ, Rn ≤ Rw → Λ ≤ Rn * τ →
      qs n ≤ Cs * Rw ∧ Λ ≤ Rw ∧ Λ ≤ Rw * τ ∧ Λ ≤ ε * Real.sqrt Rw := by
    intro Rw τ hRw hΛτ
    have hτ0 : 0 ≤ τ := by
      by_contra hneg
      push Not at hneg
      have : Rn * τ < 0 := mul_neg_of_pos_of_neg hRn0 hneg
      linarith [zero_lt_one.trans_le hΛ]
    refine ⟨(hq n).2.2.trans (mul_le_mul_of_nonneg_left (hRn.le.trans hRw) hCs0),
      hΛR.trans hRw, hΛτ.trans (mul_le_mul_of_nonneg_right hRw hτ0),
      hΛε'.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hε.le)⟩
  have hrad : Rrad ≤ (p₀ n).modelRadius := (le_max_right _ _).trans hRn'
  have hord : 2 ≤ (p₀ n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  have hacc : (p₀ n).modelAccuracy ≤ ζB := hζn.trans (min_le_right _ _)
  have hP1n := hP1' (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n) hδn
    ((le_max_left _ _).trans hRn') hmn (hζn.trans (min_le_left _ _)) (qcan n) a₀ hqcan0
    (fun x => (hinit n x).1) (fun x => (hinit n x).2) hbirth
  have hderq : ∀ {P : OrientedThreeStage.{u}} {a b : ℝ} (S : P.IncomingSlab a b) (τ τ' : ℝ),
      τ ≤ τ' → S.DerivativeBoundBefore Ctime (qcan n) τ' →
      S.DerivativeBoundBefore Ctime (qs n) τ := fun S τ τ' hle h y' v hv hR =>
    h y' v ⟨hv.1, hv.2.trans_le hle⟩ (lt_of_le_of_lt (hq n).2.1 hR)
  have hgradq : ∀ {P : OrientedThreeStage.{u}} {a b : ℝ} (S : P.IncomingSlab a b) (τ τ' : ℝ),
      τ ≤ τ' → S.GradientBoundBefore Cgrad (qcan n) τ' →
      S.GradientBoundBefore Cgrad (qs n) τ := fun S τ τ' hle h y' v hv hR =>
    h y' v ⟨hv.1, hv.2.trans_le hle⟩ (lt_of_le_of_lt (hq n).2.1 hR)
  have hslabq : ∀ k : Fin ((H n).eventCount + 1),
      (H n).EventSlabsDerivative Ctime (qs n) k := fun k j _ =>
    hderq _ _ _ le_rfl ((hslabs n).2.1 j (Fin.castSucc_lt_last j))
  have hslabc : ∀ k : Fin ((H n).eventCount + 1),
      (H n).EventSlabsDerivative Ctime (qcan n) k := fun k j _ =>
    (hslabs n).2.1 j (Fin.castSucc_lt_last j)
  refine ⟨fun τ hτ hτ₀ hΛτ z x hz hzx => ?_, fun j τ hτ hτj hΛτ z x hz hzx => ?_⟩
  · have hτs : τ < s n := hτ₀.trans_le (hbefore n).1.2.le
    refine scalar_le_of_rebase_capWindow_dichotomy ((G n).flow.base.metric τ)
      (fun w => (H n).CapWindowPoint (records n) (Fin.last _) w τ Dcap (1 / 2))
      (Rn := Rn) (A := A) (D := Dd) (QB := QB) (AB := AB) (D₁ := Dcap) (D₂ := D₂) (r := r)
      (η₃ := η₃) (Cup := Cup) (Lc := Lc) hRn0 hA hD (by linarith) hCup hLc (by linarith)
      (by linarith) le_rfl ?_ ?_ hP3 z x hz hzx
    · intro w hnot hRw x' hx'
      obtain ⟨g1, g2, g3, g4⟩ := hgates _ τ hRw hΛτ
      exact hB3e (H n) (hH n).2.1 (G n) (hG n).2 (p₀ n) (δb n) (ρb n) (records n) (hrec n)
        hrad hord hacc hτ hτs w (qs n) ε hqs0 g1 g2 g3
        (fun x'' hx'' => (hbefore n).2.2.2.2.1 x'' τ ⟨hτ, hτ₀⟩ hx'') (hslabq _)
        (hderq _ _ _ hτ₀.le (hbefore n).2.2.1) (hgradq _ _ _ hτ₀.le (hbefore n).2.2.2.1)
        (hpinch n).1 (hpinch n).2
        (fun T hT hTs hTτ => (hbefore n).2.2.2.2.2 T hT hTs (hTτ.trans hτ₀.le)) g4 hnot x' hx'
    · intro w hcw
      obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, b, Q, τw, hτw, hcl⟩ := hP1n (Fin.last _) (s n) (G n)
        (hG n).2 (hslabc _) τ hτ hτs
        (fun y' v hv hR => (hbefore n).2.2.1 y' v ⟨hv.1, hv.2.trans hτ₀⟩ hR) w hcw
      exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩
  · have hjl : (H n).time j.succ ≤ (H n).time (Fin.last _) :=
      (H n).time_strictMono.monotone (Fin.le_last _)
    refine scalar_le_of_rebase_capWindow_dichotomy
      (((H n).toHistory.event j).incoming.flow.base.metric τ)
      (fun w => (H n).CapWindowPoint (records n) j.castSucc w τ Dcap (1 / 2))
      (Rn := Rn) (A := A) (D := Dd) (QB := QB) (AB := AB) (D₁ := Dcap) (D₂ := D₂) (r := r)
      (η₃ := η₃) (Cup := Cup) (Lc := Lc) hRn0 hA hD (by linarith) hCup hLc (by linarith)
      (by linarith) le_rfl ?_ ?_ hP3 z x hz hzx
    · intro w hnot hRw x' hx'
      obtain ⟨g1, g2, g3, g4⟩ := hgates _ τ hRw hΛτ
      exact hB3e ((H n).prefixAt j.castSucc) rfl ((H n).toHistory.event j).incoming
        ((H n).event_initial j) (p₀ n) (δb n) (ρb n) ((H n).prefixRecords j.castSucc (records n))
        ((H n).isCanonicalCutoffRecordFamily_prefixAt _ (hrec n)) hrad hord hacc hτ hτj w
        (qs n) ε hqs0 g1 g2 g3
        (fun x'' hx'' => (hslabs n).2.2.2.1 j (Fin.castSucc_lt_last j) x'' τ ⟨hτ, hτj⟩ hx'')
        ((H n).eventSlabsDerivative_prefixAt _ (hslabq _))
        (hderq _ _ _ hτj.le ((hslabs n).2.1 j (Fin.castSucc_lt_last j)))
        (hgradq _ _ _ hτj.le ((hslabs n).2.2.1 j (Fin.castSucc_lt_last j)))
        ((H n).eventSlabsPinched_prefixAt _ (hpinch n).1) ((hpinch n).1 j)
        ((H n).terminalNoncollapsedBefore_prefixAt j
          ((H n).noncollapsedBefore_mono (hτj.le.trans hjl) (hslabs n).2.2.2.2)) g4
        (fun h => hnot ((H n).capWindowPoint_of_prefixAt j (records n) h)) x' hx'
    · intro w hcw
      obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, b, Q, τw, hτw, hcl⟩ := hP1n j.castSucc
        ((H n).time j.succ) ((H n).toHistory.event j).incoming ((H n).event_initial j)
        (hslabc _) τ hτ hτj
        (fun y' v hv hR => (hslabs n).2.1 j (Fin.castSucc_lt_last j) y' v
          ⟨hv.1, hv.2.trans hτj⟩ hR) w hcw
      exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩

private theorem scalar_le_of_right_shift {P : OrientedThreeStage.{u}} {a b : ℝ}
    (S : P.IncomingSlab a b) {v Rn A A' Dd D' C₁ e : ℝ} (hv : v ∈ Ico a b) (hRn : 1 ≤ Rn)
    (hA : A + 1 ≤ A') (hD : 0 < Dd) (hD' : Dd + 1 ≤ D') (he : 0 < e)
    (hbound : ∀ τ, v < τ → τ < v + e → τ < b → ∀ z x : P.Carrier,
      S.flow.scalar τ z ≤ A' * Rn →
      riemannianEDistOf (S.flow.base.metric τ) z x < ENNReal.ofReal (D' / Real.sqrt Rn) →
      S.flow.scalar τ x ≤ C₁ * Rn)
    (z x : P.Carrier) (hz : S.flow.scalar v z ≤ A * Rn)
    (hzx : riemannianEDistOf (S.flow.base.metric v) z x < ENNReal.ofReal (Dd / Real.sqrt Rn)) :
    S.flow.scalar v x ≤ (C₁ + 1) * Rn := by
  set ζ : ℝ := min 1 (1 / Dd) with hζdef
  have hζ : 0 < ζ := lt_min one_pos (by positivity)
  have hζ1 : ζ ≤ 1 := min_le_left _ _
  obtain ⟨δ, hδ, hδb, hclose⟩ := S.exists_forall_Icc_scalar_riemannNorm_metric_close hv hζ
  have hm : 0 < min δ e := lt_min hδ he
  set τ : ℝ := v + min δ e / 2 with hτdef
  have hvτ : v < τ := by linarith
  have hτe : τ < v + e := by linarith [min_le_right δ e]
  have hτδ : τ ≤ v + δ := by linarith [min_le_left δ e]
  have hτb : τ < b := by linarith
  have hvmem : v ∈ Icc (max a (v - δ)) (v + δ) := ⟨max_le hv.1 (by linarith), by linarith⟩
  have hτmem : τ ∈ Icc (max a (v - δ)) (v + δ) :=
    ⟨(max_le hv.1 (by linarith)).trans hvτ.le, hτδ⟩
  have hz' : S.flow.scalar τ z ≤ A' * Rn := by
    have h := (hclose τ hτmem v hvmem z).1
    rw [abs_le] at h
    nlinarith
  have hball := DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul
    (S.flow.base.metric v) (S.flow.base.metric τ) z (r := Dd / Real.sqrt Rn)
    (by linarith : (0 : ℝ) < 1 + ζ) (fun q _ w => (hclose τ hτmem v hvmem q).2.2 w)
  have hx : x ∈ riemannianBallOf (S.flow.base.metric τ) z
      (Real.sqrt (1 + ζ) * (Dd / Real.sqrt Rn)) := hball hzx
  have hrad : Real.sqrt (1 + ζ) * (Dd / Real.sqrt Rn) ≤ D' / Real.sqrt Rn := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h1 : Real.sqrt (1 + ζ) * Dd = Real.sqrt ((1 + ζ) * Dd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD.le]
    have hζD : ζ * Dd ≤ 1 := by
      calc ζ * Dd ≤ 1 / Dd * Dd := mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
        _ = 1 := by field_simp
    have h2 : (1 + ζ) * Dd ^ 2 ≤ (Dd + 1) ^ 2 := by nlinarith
    rw [h1]
    calc Real.sqrt ((1 + ζ) * Dd ^ 2) ≤ Real.sqrt ((Dd + 1) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Dd + 1 := Real.sqrt_sq (by linarith)
      _ ≤ D' := hD'
  have hxτ := hbound τ hvτ hτe hτb z x hz' (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad))
  have h := (hclose v hvmem τ hτmem x).1
  rw [abs_le] at h
  nlinarith

theorem eventually_scalar_le_at_normalized_distance_of_anchor
    (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ)
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ B (p₀ n) (δb n) (ρb n))
    (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslabs : ∀ n,
      (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
      (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
      (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
    (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
      (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
      (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
      (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
      (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
      (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
    (hsliver : ∀ n, 0 < η n ∧ t₀ n + η n < s n ∧
      (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ n + η n) ∧
      (∀ t' ∈ Icc (t₀ n) (t₀ n + η n), ∀ x, (G n).flow.scalar t' x * η n ≤ 1 / ((n : ℝ) + 1) ∧
        |(G n).flow.scalar t' x - (G n).flow.scalar (t₀ n) x| ≤ qcan n / 4 ∧
        ∀ v : TangentSpace ThreeModel x,
          ((G n).flow.base.metric t').inner x v v ≤
            Real.exp 1 * ((G n).flow.base.metric (t₀ n)).inner x v v ∧
          ((G n).flow.base.metric (t₀ n)).inner x v v ≤
            Real.exp 1 * ((G n).flow.base.metric t').inner x v v) ∧
      ∀ i b, ((records n i).static b).neck.scale * η n ≤ 1 / ((n : ℝ) + 2))
    (hbad : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n ∧ t₀ n ≤ t n ∧
      t n < t₀ n + η n ∧ qcan n < (G n).flow.scalar (t n) (y n) ∧
      (G n).flow.scalar (t n) (y n) * (t n - (H n).time (Fin.last (H n).eventCount)) < θ ∧
      ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n) (D n) (θcap n)) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n => (H n).extendAt (hH n).2.1 (G n) (hG n).2
      (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, σ < 0 → ∀ᶠ n in atTop,
      ∀ v : Icc (0 : ℝ) (K n).toHistory.horizon,
        (v : ℝ) = t n + σ / (G n).flow.scalar (t n) (y n) →
      ∀ z x : ((K n).toHistory.stageAt v).Carrier,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z ≤
          A * (G n).flow.scalar (t n) (y n) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z x <
          ENNReal.ofReal (Dd / Real.sqrt ((G n).flow.scalar (t n) (y n))) →
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
          C * (G n).flow.scalar (t n) (y n) := by
  intro K A Dd hA hD
  obtain ⟨C₁, Λ, hΛ, hslab⟩ := eventually_slab_scalar_le_at_normalized_distance hε hεcone hκ hphi
    hH hG hrec hq hpar hscale hpinch hslabs hbefore (fun n => (hbad n).2.2.2.1) (max A 1 + 1)
    (Dd + 1) (by linarith [le_max_right A 1]) (by linarith)
  refine ⟨max 1 (C₁ + 1), le_max_left _ _, fun σ hσ => ?_⟩
  have hRbig : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c ≤ (G n).flow.scalar (t n) (y n) := by
    intro c
    obtain ⟨N, hN⟩ := exists_nat_gt c
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(hq n).1, (hbad n).2.2.2.1]
  have hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop :=
    tendsto_atTop.mpr hRbig
  have hF3 := RetainedCoreHistory.tendsto_scalar_mul_time_atTop_of_inCutoffClass hH G
    (fun n => (hG n).2) y (fun n => ⟨(hbad n).1.le, (hbad n).2.2.1.trans (hsliver n).2.1⟩) hR
  have hgap : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < -σ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / -σ)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ (by linarith : (0 : ℝ) < -σ)).mp hN
    nlinarith
  filter_upwards [hslab, hF3.eventually_ge_atTop (Λ - σ), hgap, hRbig 1] with n hsl hRt hgn hR1
  intro v hv
  set Rn := (G n).flow.scalar (t n) (y n) with hRndef
  have hRn0 : 0 < Rn := by linarith
  have hRv : Rn * v = Rn * t n + σ := by
    rw [hv, mul_add, mul_div_cancel₀ _ hRn0.ne']
  have hΛv : Λ ≤ Rn * v := by linarith
  have hvt₀ : (v : ℝ) < t₀ n := by
    have h1 := ((hsliver n).2.2.2.1 (t n) ⟨(hbad n).2.1, (hbad n).2.2.1.le⟩ (y n)).1
    have h2 : Rn * (t n - t₀ n) ≤ Rn * η n :=
      mul_le_mul_of_nonneg_left (by linarith [(hbad n).2.2.1]) hRn0.le
    have h3 : Rn * v < Rn * t₀ n := by nlinarith
    exact lt_of_mul_lt_mul_left h3 hRn0.le
  have hvs : (v : ℝ) < s n := hvt₀.trans (hbefore n).1.2
  have hA1 : A ≤ max A 1 := le_max_left _ _
  have hC : C₁ + 1 ≤ max 1 (C₁ + 1) := le_max_right _ _
  have key : ∀ k : Fin ((K n).toHistory.eventCount + 1),
      (v : ℝ) ∈ (K n).toHistory.stageDomain k → ∀ z x : ((K n).toHistory.stage k).Carrier,
      metricScalarAt ((K n).toHistory.stageMetric k v) z ≤ A * Rn →
      riemannianEDistOf ((K n).toHistory.stageMetric k v) z x <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      metricScalarAt ((K n).toHistory.stageMetric k v) x ≤ max 1 (C₁ + 1) * Rn := by
    intro k
    cases k using Fin.lastCases with
    | last =>
      intro hmem z x hz hzx
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hmem
      have hmet : (K n).toHistory.stageMetric (Fin.last _) v = (G n).flow.base.metric v :=
        (H n).stageMetric_extendHorizon_last _ _ _ (hbad n).1 v
      rw [hmet] at hz hzx ⊢
      have h := scalar_le_of_right_shift (G n) (v := v) (Rn := Rn) (A := max A 1)
        (A' := max A 1 + 1) (Dd := Dd) (D' := Dd + 1) (C₁ := C₁) (e := t₀ n - v)
        ⟨hmem.1, hvs⟩ hR1 le_rfl hD le_rfl (by linarith)
        (fun τ hvτ hτe _ z' x' hz' hzx' => hsl.1 τ (lt_of_le_of_lt hmem.1 hvτ) (by linarith)
          (hΛv.trans (mul_le_mul_of_nonneg_left hvτ.le hRn0.le)) z' x' hz' hzx')
        z x (hz.trans (mul_le_mul_of_nonneg_right hA1 hRn0.le)) hzx
      exact h.trans (mul_le_mul_of_nonneg_right hC hRn0.le)
    | cast i =>
      intro hmem z x hz hzx
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
      rw [ObservedHistory.stageMetric_castSucc_apply] at hz hzx ⊢
      have h := scalar_le_of_right_shift ((H n).toHistory.event i).incoming (v := v) (Rn := Rn)
        (A := max A 1) (A' := max A 1 + 1) (Dd := Dd) (D' := Dd + 1) (C₁ := C₁) (e := 1)
        ⟨hmem.1, hmem.2⟩ hR1 le_rfl hD le_rfl one_pos
        (fun τ hvτ _ hτb z' x' hz' hzx' => hsl.2 i τ (lt_of_le_of_lt hmem.1 hvτ) hτb
          (hΛv.trans (mul_le_mul_of_nonneg_left hvτ.le hRn0.le)) z' x' hz' hzx')
        z x (hz.trans (mul_le_mul_of_nonneg_right hA1 hRn0.le)) hzx
      exact h.trans (mul_le_mul_of_nonneg_right hC hRn0.le)
  exact key _ ((K n).toHistory.activeStage_mem v)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
