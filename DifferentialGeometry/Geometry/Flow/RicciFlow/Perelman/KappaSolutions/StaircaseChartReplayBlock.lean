import DifferentialGeometry.Analysis.Calculus.Compactness.EventuallyBounded
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.MetricLimits

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter Topology
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace InjectivityRadiusDecay

omit [CompleteSpace E] in
theorem riemannianEDistOf_basepoint_le_of_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (hreal : hd.RealizesDistance) {A : Real} {j : Nat} {x : (X.obj j).M}
    (h : hd.dist j x (X.obj j).basepoint <= A) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
       ENNReal.ofReal A) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : EMetricSpace (X.obj j).M := (X.obj j).emetricSpace
  have hbridge : (letI : EMetricSpace (X.obj j).M := (X.obj j).emetricSpace
      edist (X.obj j).basepoint x) =
        riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x := rfl
  rw [← hbridge, edist_comm, hreal.edist_eq j x (X.obj j).basepoint]
  exact ENNReal.ofReal_le_ofReal h

end InjectivityRadiusDecay

omit [CompleteSpace E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem iteratedFDerivBoundsOnCompactsWithin_of_eventually_bdd
    {U : Set E} (hU : IsOpen U) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace Real F] {Phi : Nat → E → F}
    (hPhi : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (Phi k) U)
    (hbdd : ∀ r : Nat, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : Real, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv Real r (Phi k) x‖ ≤ M) :
    iteratedFDerivBoundsOnCompactsWithin U Phi := by
  classical
  intro r K hK hKU
  obtain ⟨M, hM⟩ := hbdd r K hK hKU
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hM
  have hfin : ∀ k : Nat, ∃ Mk : Real,
      ∀ x ∈ K, ‖iteratedFDeriv Real r (Phi k) x‖ ≤ Mk := fun k => by
    obtain ⟨Mk, hMk⟩ := hK.exists_bound_of_continuousOn
      (((hPhi k).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast (le_top (a := (r : ℕ∞)))) hU.uniqueDiffOn).mono hKU)
    exact ⟨Mk, fun x hx => by
      rw [← iteratedFDerivWithin_of_isOpen r hU (hKU hx)]
      exact hMk x hx⟩
  choose Mk hMk using hfin
  let S : Finset Real := (Finset.range (k0 + 1)).image Mk
  have hSne : S.Nonempty :=
    ⟨Mk 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k0), rfl⟩⟩
  refine ⟨max M (S.max' hSne), fun k x hx => ?_⟩
  rcases lt_or_ge k (k0 + 1) with hk | hk
  · have hm : Mk k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact (hMk k x hx).trans
      ((Finset.le_max' S (Mk k) hm).trans (le_max_right M (S.max' hSne)))
  · exact (hk0 k (Nat.le_of_succ_le hk) x hx).trans (le_max_left M (S.max' hSne))

namespace SeqBallNormalChartData

def chartMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  (d.chart k x).metric (X.obj k).metric

omit [CompleteSpace E] in
theorem metric_deriv_ball_of_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {A : Real} {p j : Nat} (hj : Nat.ceil A + p <= j) {x : (X.obj j).M}
    (hx : hd.dist j x (X.obj j).basepoint <= A) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.chart j x).MetricDerivBound (X.obj j).metric
       (Metric.ball (0 : E) (d.chart j x).radius) p (d.metricC (Nat.ceil A) p)) := by
  refine d.metric_deriv (Nat.ceil A) p j hj x ?_
  exact (InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le
      (I := I) hreal hx).trans (ENNReal.ofReal_le_ofReal (Nat.le_ceil A))

omit [CompleteSpace E] in
theorem exists_chart_metric_limit_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (c : ∀ k : Nat, (X.obj k).M) {R : Real}
    (hcR : ∀ k : Nat, hd.dist k (c k) (X.obj k).basepoint <= R)
    {U : Set E} (hU : IsOpen U)
    (hsub : ∀ k,
      U ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (c k) (X.obj k).basepoint))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) gInf U ∧
      MapCInfConvergenceOnCompacts U
        (fun k => d.chartMetric (phi k) (c (phi k))) gInf ∧
      ∀ z ∈ U, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v ∧
          gInf z v v ≤ 2 * ‖v‖ ^ 2 := by
  apply exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd hU
    (fun k => d.chartMetric k (c k))
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    simpa only [SeqBallNormalChartData.chartMetric] using
      (d.chart k (c k)).metric_cont_diff_on (X.obj k).metric hU
        ((d.chart k (c k)).smooth_to.mono hrad)
  · intro p K _hK hKU
    refine ⟨d.metricC (Nat.ceil R) p, ?_⟩
    refine eventually_atTop.mpr ⟨Nat.ceil R + p, fun k hk z hz => ?_⟩
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    have hshell : Nat.ceil R + p <= k := hk
    simpa only [SeqBallNormalChartData.chartMetric] using
      d.metric_deriv_ball_of_dist_le (I := I) hreal hshell (hcR k)
        z (hrad (hKU hz))
  · intro k z hz v
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    simpa only [SeqBallNormalChartData.chartMetric] using
      d.metric_equiv k (c k) z (hrad hz) v

omit [CompleteSpace E] in
theorem exists_finite_chart_metric_limit_subsequence
    {i : Type uE} [Fintype i]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (c : i → ∀ k : Nat, (X.obj k).M) {R : Real}
    (hcR : ∀ k : Nat, ∀ a : i,
      hd.dist k (c a k) (X.obj k).basepoint <= R)
    {U : Set E} (hU : IsOpen U)
    (hsub : ∀ k a,
      U ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (c a k) (X.obj k).basepoint))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (i → (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) gInf U ∧
      MapCInfConvergenceOnCompacts U
        (fun k z a ↦ d.chartMetric (phi k) (c a (phi k)) z) gInf ∧
      ∀ z ∈ U, ∀ a v,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z a v v ∧
          gInf z a v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let gLocal : Nat → E → (i → (E →L[Real] E →L[Real] Real)) :=
    fun k z a ↦ d.chartMetric k (c a k) z
  have hsmoothComp : ∀ k a,
      ContDiffOn Real (⊤ : ℕ∞) (fun z ↦ gLocal k z a) U := by
    intro k a
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c a k)).radius := by
      simpa only [d.radius_eq k (c a k)] using hsub k a
    simpa only [gLocal, SeqBallNormalChartData.chartMetric] using
      (d.chart k (c a k)).metric_cont_diff_on (X.obj k).metric hU
        ((d.chart k (c a k)).smooth_to.mono hrad)
  have hsmooth : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (gLocal k) U :=
    fun k ↦ contDiffOn_pi.mpr (hsmoothComp k)
  have hbddComp : ∀ a, ∀ r : Nat, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : Real, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv Real r (fun z ↦ gLocal k z a) x‖ ≤ M := by
    intro a r K _hK hKU
    refine ⟨d.metricC (Nat.ceil R) r, ?_⟩
    refine eventually_atTop.mpr ⟨Nat.ceil R + r, fun k hk x hx => ?_⟩
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c a k)).radius := by
      simpa only [d.radius_eq k (c a k)] using hsub k a
    have hshell : Nat.ceil R + r <= k := hk
    simpa only [gLocal, SeqBallNormalChartData.chartMetric] using
      d.metric_deriv_ball_of_dist_le (I := I) hreal hshell (hcR k a)
        x (hrad (hKU hx))
  have hbddEv : ∀ r : Nat, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : Real, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv Real r (gLocal k) x‖ ≤ M := by
    intro r K hK hKU
    have hone : ∀ a : i, ∃ M : Real, 0 ≤ M ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv Real r (fun z ↦ gLocal k z a) x‖ ≤ M := by
      intro a
      obtain ⟨M, hM⟩ := hbddComp a r K hK hKU
      exact ⟨max M 0, le_max_right M 0,
        hM.mono fun k hk x hx => (hk x hx).trans (le_max_left M 0)⟩
    choose M hM0 hM using hone
    have hall : ∀ᶠ k in atTop, ∀ a ∈ (Finset.univ : Finset i), ∀ x ∈ K,
        ‖iteratedFDeriv Real r (fun z ↦ gLocal k z a) x‖ ≤ M a := by
      rw [eventually_all_finset]
      exact fun a _ => hM a
    refine ⟨∑ a, M a, hall.mono fun k hk x hx => ?_⟩
    have hcd : ∀ a, ContDiffAt Real ((r : ℕ∞) : WithTop ℕ∞)
        (fun y => gLocal k y a) x := fun a =>
      ((hsmoothComp k a).contDiffAt (hU.mem_nhds (hKU hx))).of_le
        (by exact_mod_cast le_top)
    rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => hM0 a)]
    intro a
    exact (hk a (Finset.mem_univ a) x hx).trans
      (Finset.single_le_sum (fun b _ => hM0 b) (Finset.mem_univ a))
  have hbdd : iteratedFDerivBoundsOnCompactsWithin U gLocal :=
    iteratedFDerivBoundsOnCompactsWithin_of_eventually_bdd hU hsmooth hbddEv
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on hU gLocal hsmooth hbdd
  refine ⟨phi, gInf, hphi, hginf, hconv, ?_⟩
  intro z hz a v
  have htendAll : Tendsto (fun k ↦ gLocal (phi k) z) atTop
      (nhds (gInf z)) :=
    tendsto_of_cInf hconv hz
  have htend : Tendsto (fun k ↦ gLocal (phi k) z a) atTop
      (nhds (gInf z a)) :=
    (tendsto_pi_nhds.mp htendAll) a
  have heval : Continuous
      (fun A : E →L[Real] E →L[Real] Real ↦ A v v) := by
    fun_prop
  have htendv : Tendsto (fun k ↦ gLocal (phi k) z a v v) atTop
      (nhds (gInf z a v v)) :=
    (heval.tendsto _).comp htend
  have hequiv : ∀ n,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gLocal (phi n) z a v v ∧
        gLocal (phi n) z a v v ≤ 2 * ‖v‖ ^ 2 := by
    intro n
    let : TopologicalSpace (X.obj (phi n)).M :=
      (X.obj (phi n)).topology
    let : ChartedSpace H (X.obj (phi n)).M :=
      (X.obj (phi n)).charted
    let : IsManifold I ∞ (X.obj (phi n)).M :=
      (X.obj (phi n)).smooth
    let : T2Space (TangentBundle I (X.obj (phi n)).M) :=
      (X.obj (phi n)).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E)
          (d.chart (phi n) (c a (phi n))).radius := by
      simpa only [d.radius_eq (phi n) (c a (phi n))] using hsub (phi n) a
    simpa only [gLocal, SeqBallNormalChartData.chartMetric] using
      d.metric_equiv (phi n) (c a (phi n)) z (hrad hz) v
  exact ⟨
    ge_of_tendsto htendv
      (Filter.Eventually.of_forall fun n ↦ (hequiv n).1),
    le_of_tendsto htendv
      (Filter.Eventually.of_forall fun n ↦ (hequiv n).2)⟩

omit [CompleteSpace E] in
theorem exists_metricDerivBound_quarter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (j : Nat) (x : (X.obj j).M)
    (q : Nat) :
    ∃ C : Real, 0 <= C ∧
      (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
       letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
       letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
       letI : T2Space (TangentBundle I (X.obj j).M) :=
         (X.obj j).t2TangentBundle
       (d.chart j x).MetricDerivBound (X.obj j).metric
         (Metric.ball (0 : E) ((d.chart j x).radius / 4)) q C) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hr : 0 < (d.chart j x).radius := (d.chart j x).radius_pos
  let U : Set E := Metric.ball (0 : E) ((d.chart j x).radius / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hUrad : U ⊆ Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball (by linarith)
  have hcont :=
    (d.chart j x).metric_cont_diff_on (X.obj j).metric hU
      ((d.chart j x).smooth_to.mono hUrad)
  have hK : IsCompact (Metric.closedBall (0 : E) ((d.chart j x).radius / 4)) :=
    isCompact_closedBall _ _
  have hKU : Metric.closedBall (0 : E) ((d.chart j x).radius / 4) ⊆ U :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hcont.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top (a := (q : ℕ∞)))) hU.uniqueDiffOn).mono hKU)
  refine ⟨max M 0, le_max_right M 0, fun z hz => ?_⟩
  have hzK : z ∈ Metric.closedBall (0 : E) ((d.chart j x).radius / 4) :=
    Metric.ball_subset_closedBall hz
  rw [← iteratedFDerivWithin_of_isOpen q hU (hKU hzK)]
  exact (hM z hzK).trans (le_max_left M 0)

omit [CompleteSpace E] in
def metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint <= n) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    (d.chart j x).MetricBounds (X.obj j).metric := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hr : 0 < (d.chart j x).radius := (d.chart j x).radius_pos
  have hsub : Metric.ball (0 : E) ((d.chart j x).radius / 4) ⊆
      Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball (by linarith)
  have hx : riemannianEDistOf (I := I) (X.obj j).metric
      (X.obj j).basepoint x <= ENNReal.ofReal (n : Real) :=
    (InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le
      (I := I) hreal (by exact_mod_cast hn))
  refine
    { C := fun q => if n + q <= j then d.metricC n q
        else Classical.choose (exists_metricDerivBound_quarter (I := I) d j x q)
      C_nonneg := fun q => ?_
      radius := (d.chart j x).radius / 4
      radius_pos := by linarith
      equiv := fun z hz v => d.metric_equiv j x z (hsub hz) v
      deriv := fun q z hz => ?_ }
  · by_cases h : n + q <= j
    · simpa only [h, if_true] using d.metricC_nonneg n q
    · simpa only [h, if_false] using
        (Classical.choose_spec
          (exists_metricDerivBound_quarter (I := I) d j x q)).1
  · by_cases h : n + q <= j
    · simpa only [h, if_true] using
        d.metric_deriv n q j h x hx z (hsub hz)
    · simpa only [h, if_false] using
        (Classical.choose_spec
          (exists_metricDerivBound_quarter (I := I) d j x q)).2 z hz

omit [CompleteSpace E] in
theorem metricBounds_C_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint <= n) {q : Nat} (hq : n + q <= j) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) :=
       (X.obj j).t2TangentBundle
     (d.metricBounds hreal x hn).C q) = d.metricC n q := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  simp only [metricBounds, hq, if_true]

omit [CompleteSpace E] in
theorem metricBounds_radius_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint <= n) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) :=
       (X.obj j).t2TangentBundle
     (d.metricBounds hreal x hn).radius = (d.chart j x).radius / 4) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  simp only [metricBounds]

def phaseRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) : Real :=
  d.ratio * hd.mu R / 4

omit [CompleteSpace E] in
theorem phaseRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) :
    0 < d.phaseRadius R := by
  exact div_pos (mul_pos d.ratio_pos (hd.mu_pos R)) (by norm_num)

omit [CompleteSpace E] in
theorem phaseRadius_chart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {j : Nat} {x : (X.obj j).M}
    {R : Real} (hx : hd.dist j x (X.obj j).basepoint <= R) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     Metric.ball (0 : E) (d.phaseRadius R) ⊆
       Metric.ball (0 : E) ((d.chart j x).radius / 4)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  apply Metric.ball_subset_ball
  rw [d.radius_eq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le)
    (by norm_num)

omit [CompleteSpace E] in
theorem phaseRadius_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} {x : (X.obj j).M}
    (hn : hd.dist j x (X.obj j).basepoint <= n) {R : Real}
    (hx : hd.dist j x (X.obj j).basepoint <= R) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) :=
       (X.obj j).t2TangentBundle
     Metric.ball (0 : E) (d.phaseRadius R) ⊆
       Metric.ball (0 : E) (d.metricBounds hreal x hn).radius) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hquarter := d.phaseRadius_chart (I := I) hx
  change Metric.ball (0 : E) (d.phaseRadius R) ⊆
    Metric.ball (0 : E) ((d.chart j x).radius / 4)
  exact hquarter

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
