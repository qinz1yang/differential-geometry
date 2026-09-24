import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseChartReplayBlock

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter Topology
open scoped Manifold ContDiff ENNReal NNReal Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem exists_innerBall_bound_not_ball_bound :
    ∃ F : Real → Real →L[Real] Real →L[Real] Real,
      (∃ C : Real, 0 ≤ C ∧
        ∀ z ∈ Metric.ball (0 : Real) (1 / 4), ‖F z‖ ≤ C) ∧
      ¬ (∃ C : Real, ∀ z ∈ Metric.ball (0 : Real) 1, ‖F z‖ ≤ C) := by
  let L : Real →L[Real] Real →L[Real] Real := ContinuousLinearMap.mul Real Real
  have hval : L 1 1 = 1 := by simp [L]
  have hLpos : 0 < ‖L‖ := by
    refine norm_pos_iff.mpr fun hzero => ?_
    rw [hzero] at hval
    simp at hval
  have hLone : 1 ≤ ‖L‖ := by
    have h1 : ‖L 1 1‖ ≤ ‖L 1‖ * ‖(1 : Real)‖ :=
      ContinuousLinearMap.le_opNorm (L 1) 1
    have h2 : ‖L 1‖ ≤ ‖L‖ * ‖(1 : Real)‖ := ContinuousLinearMap.le_opNorm L 1
    rw [hval, norm_one, mul_one] at h1
    rw [norm_one, mul_one] at h2
    linarith
  refine ⟨fun z => (|z - 1 / 2|)⁻¹ • L, ⟨4 * ‖L‖, by positivity, ?_⟩, ?_⟩
  · intro z hz
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
    have hzlt : z < 1 / 4 := (abs_lt.mp hz).2
    have hsub : z - 1 / 2 < 0 := by linarith
    have habs : |z - 1 / 2| = 1 / 2 - z := by rw [abs_of_neg hsub]; ring
    have hge : 1 / 4 ≤ |z - 1 / 2| := by rw [habs]; linarith
    have hpos : 0 < |z - 1 / 2| := lt_of_lt_of_le (by norm_num) hge
    have hinv : (|z - 1 / 2|)⁻¹ ≤ 4 := by
      have := one_div_le_one_div_of_le (a := (1 / 4 : Real)) (by norm_num) hge
      simpa using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    nlinarith [norm_nonneg L]
  · rintro ⟨C, hC⟩
    let n : Nat := Nat.ceil (max C 0) + 2
    let z : Real := 1 / 2 - (n : Real)⁻¹
    have hceil : max C 0 ≤ (Nat.ceil (max C 0) : Real) := Nat.le_ceil _
    have hn2 : (2 : Real) ≤ (n : Real) := by
      have h0 : (0 : Real) ≤ (Nat.ceil (max C 0) : Real) := Nat.cast_nonneg _
      simp only [n]
      push_cast
      linarith
    have hnpos : 0 < (n : Real) := by linarith
    have hznn : 0 ≤ z := by
      have hinv : (n : Real)⁻¹ ≤ 1 / 2 := by
        have := one_div_le_one_div_of_le (a := (2 : Real)) (by norm_num) hn2
        simpa using this
      simp only [z]
      linarith
    have hzle : z ≤ 1 / 2 := by
      have : 0 < (n : Real)⁻¹ := inv_pos.mpr hnpos
      simp only [z]
      linarith
    have hmem : z ∈ Metric.ball (0 : Real) 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hznn]
      linarith
    have hbound := hC z hmem
    have hdist : |z - 1 / 2| = (n : Real)⁻¹ := by
      have hneg : z - 1 / 2 = -((n : Real)⁻¹) := by simp only [z]; ring
      rw [hneg, abs_neg, abs_of_pos (inv_pos.mpr hnpos)]
    have hval2 : ‖(|z - 1 / 2|)⁻¹ • L‖ = (n : Real) * ‖L‖ := by
      have hpos : 0 < |z - 1 / 2| := by rw [hdist]; exact inv_pos.mpr hnpos
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), hdist,
        inv_inv]
    simp only [] at hbound
    rw [hval2] at hbound
    have hbig : C < (n : Real) * ‖L‖ := by
      have hle : (n : Real) ≤ (n : Real) * ‖L‖ := by nlinarith
      have hlt : C < (n : Real) := by
        have h0 : (0 : Real) ≤ (Nat.ceil (max C 0) : Real) := Nat.cast_nonneg _
        simp only [n]
        push_cast
        linarith [le_max_left C 0, hceil]
      linarith
    linarith

namespace SeqBallNormalChartData

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem offShell_orders_unbounded {n j m : Nat} :
    ∃ q : Nat, m ≤ q ∧ ¬ n + q ≤ j :=
  ⟨max m (j + 1), le_max_left m (j + 1), by omega⟩

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem eventually_onShell_index {n q : Nat} :
    ∀ᶠ j : Nat in Filter.atTop, n + q ≤ j :=
  Filter.eventually_atTop.mpr ⟨n + q, fun _ hj => hj⟩

omit [CompleteSpace E] in
def offShellDerivCeil
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M)
    (q : Nat) : Real :=
  if n + q ≤ j then 0
  else max 0 (Classical.choose (exists_metricDerivBound_quarter (I := I) d j x q))

omit [CompleteSpace E] in
theorem offShellDerivCeil_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M)
    (q : Nat) :
    0 ≤ d.offShellDerivCeil (n := n) (j := j) x q := by
  by_cases h : n + q ≤ j
  · simp only [offShellDerivCeil, h, if_true]
    exact le_rfl
  · simp only [offShellDerivCeil, h, if_false]
    exact le_max_left 0 _

omit [CompleteSpace E] in
def twoPieceC
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M)
    (q : Nat) : Real :=
  max (d.metricC n q) (d.offShellDerivCeil (n := n) (j := j) x q)

omit [CompleteSpace E] in
theorem twoPieceC_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M)
    (q : Nat) :
    0 ≤ d.twoPieceC (n := n) (j := j) x q :=
  le_trans (d.metricC_nonneg n q) (le_max_left _ _)

omit [CompleteSpace E] in
theorem twoPieceC_eq_of_shell
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M)
    {q : Nat} (hq : n + q ≤ j) :
    d.twoPieceC (n := n) (j := j) x q = d.metricC n q := by
  have h0 : d.offShellDerivCeil (n := n) (j := j) x q = 0 := by
    simp only [offShellDerivCeil, hq, if_true]
  rw [twoPieceC, h0, max_eq_left (d.metricC_nonneg n q)]

omit [CompleteSpace E] in
def metricBoundsTwoPiece
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint ≤ n) :
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
      (X.obj j).basepoint x ≤ ENNReal.ofReal (n : Real) :=
    InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le
      (I := I) hreal (by exact_mod_cast hn)
  refine
    { C := d.twoPieceC (n := n) (j := j) x
      C_nonneg := fun q => d.twoPieceC_nonneg (n := n) (j := j) x q
      radius := (d.chart j x).radius / 4
      radius_pos := by linarith
      equiv := fun z hz v => d.metric_equiv j x z (hsub hz) v
      deriv := fun q z hz => ?_ }
  by_cases hq : n + q ≤ j
  · rw [d.twoPieceC_eq_of_shell (n := n) (j := j) x hq]
    exact d.metric_deriv n q j hq x hx z (hsub hz)
  · refine ((Classical.choose_spec
      (exists_metricDerivBound_quarter (I := I) d j x q)).2 z hz).trans ?_
    simp only [twoPieceC, offShellDerivCeil, hq, if_false]
    exact le_max_of_le_right (le_max_right (0 : Real) _)

omit [CompleteSpace E] in
theorem metricBoundsTwoPiece_C
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ n)
    (q : Nat) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.metricBoundsTwoPiece hreal x hn).C q) =
      d.twoPieceC (n := n) (j := j) x q :=
  rfl

omit [CompleteSpace E] in
theorem metricBoundsTwoPiece_C_eq_of_shell
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ n)
    {q : Nat} (hq : n + q ≤ j) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.metricBoundsTwoPiece hreal x hn).C q) = d.metricC n q :=
  (d.metricBoundsTwoPiece_C (n := n) (j := j) hreal x hn q).trans
    (d.twoPieceC_eq_of_shell (n := n) (j := j) x hq)

omit [CompleteSpace E] in
theorem metricBoundsTwoPiece_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ n) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.metricBoundsTwoPiece hreal x hn).radius = (d.chart j x).radius / 4) :=
  rfl

omit [CompleteSpace E] in
theorem exists_metricBoundsTwoPiece_C_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (n : Nat) (c : ∀ j : Nat, (X.obj j).M)
    (hc : ∀ j : Nat, hd.dist j (c j) (X.obj j).basepoint ≤ n) :
    ∃ K CB : Nat → Real, (∀ q, 0 ≤ CB q) ∧
      (∀ q, CB q = max (d.metricC n q) (K q)) ∧
      ∀ q j : Nat,
        (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
         letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
         letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
         letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
         (d.metricBoundsTwoPiece hreal (c j) (hc j)).C q) ≤ CB q := by
  let K : Nat → Real := fun q =>
    (insert 0 (Finset.range (n + q))).sup' (Finset.insert_nonempty 0 _)
      (fun j => d.offShellDerivCeil (n := n) (j := j) (c j) q)
  have hK0 : ∀ q, 0 ≤ K q := by
    intro q
    have hmem : (0 : Nat) ∈ insert 0 (Finset.range (n + q)) :=
      Finset.mem_insert_self 0 _
    have hsup := Finset.le_sup' (s := insert 0 (Finset.range (n + q)))
      (f := fun j => d.offShellDerivCeil (n := n) (j := j) (c j) q) hmem
    exact (d.offShellDerivCeil_nonneg (n := n) (j := 0) (c 0) q).trans hsup
  have hoff : ∀ q j : Nat,
      d.offShellDerivCeil (n := n) (j := j) (c j) q ≤ K q := by
    intro q j
    by_cases hle : n + q ≤ j
    · rw [offShellDerivCeil, if_pos hle]
      exact hK0 q
    · have hmem : j ∈ insert 0 (Finset.range (n + q)) :=
        Finset.mem_insert_of_mem (Finset.mem_range.mpr (by omega))
      exact Finset.le_sup' (s := insert 0 (Finset.range (n + q)))
        (f := fun j => d.offShellDerivCeil (n := n) (j := j) (c j) q) hmem
  refine ⟨K, fun q => max (d.metricC n q) (K q),
    fun q => le_trans (d.metricC_nonneg n q) (le_max_left _ _), fun _ => rfl, ?_⟩
  intro q j
  rw [d.metricBoundsTwoPiece_C (n := n) (j := j) hreal (c j) (hc j) q]
  exact max_le_max le_rfl (hoff q j)

omit [CompleteSpace E] in
theorem exists_metricBounds_full_radius_of_twoPiece
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ n)
    (CF : Nat → Real) (hCF : ∀ q, 0 ≤ CF q)
    (hshell : ∀ q, n + q ≤ j → d.metricC n q ≤ CF q)
    (hfull : ∀ q, ¬ n + q ≤ j →
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
      (d.chart j x).MetricDerivBound (X.obj j).metric
        (Metric.ball (0 : E) (d.chart j x).radius) q (CF q)) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
       b.radius = (d.chart j x).radius ∧
       (∀ q, n + q ≤ j → b.C q = d.metricC n q) ∧
       ∀ q, b.C q ≤ CF q) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hx : riemannianEDistOf (I := I) (X.obj j).metric
      (X.obj j).basepoint x ≤ ENNReal.ofReal (n : Real) :=
    InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le
      (I := I) hreal (by exact_mod_cast hn)
  refine ⟨
    { C := fun q => if n + q ≤ j then d.metricC n q else CF q
      C_nonneg := fun q => ?_
      radius := (d.chart j x).radius
      radius_pos := (d.chart j x).radius_pos
      equiv := d.metric_equiv j x
      deriv := fun q z hz => ?_ }, rfl, ?_, ?_⟩
  · by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using d.metricC_nonneg n q
    · simpa only [hq, if_false] using hCF q
  · by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using d.metric_deriv n q j hq x hx z hz
    · simpa only [hq, if_false] using hfull q hq z hz
  · intro q hq
    simp only [hq, if_true]
  · intro q
    by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using hshell q hq
    · simp only [hq, if_false]
      exact le_rfl

omit [CompleteSpace E] in
theorem exists_metricBounds_full_radius_of_boundedGeometry
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d₀ : BoundedGeometryNormalChartData (I := I) X hd) (j : Nat)
    (x : (X.obj j).M) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     ∃ b : (((SeqBallNormalChartData.of_boundedGeometryNormalChartData
       (I := I) d₀).chart j x).MetricBounds (X.obj j).metric),
       b.radius = ((SeqBallNormalChartData.of_boundedGeometryNormalChartData
         (I := I) d₀).chart j x).radius ∧ ∀ q, b.C q ≤ d₀.metricC q) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  refine ⟨d₀.metricBounds j x, rfl, fun _ => le_rfl⟩

omit [CompleteSpace E] in
theorem metric_deriv_le_on_phaseBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (c : ∀ k : Nat, (X.obj k).M) {n : Nat} {R : Real}
    (hc : ∀ k : Nat, hd.dist k (c k) (X.obj k).basepoint ≤ (n : Real))
    (hnR : (n : Real) ≤ R)
    {U : Set E} (hU : U ⊆ Metric.ball (0 : E) (d.phaseRadius R))
    {i k : Nat} (hk : n + i ≤ k) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     ∀ x ∈ U, ‖iteratedFDeriv Real i (d.chartMetric k (c k)) x‖ ≤ d.metricC n i) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have hdist : hd.dist k (c k) (X.obj k).basepoint ≤ R := le_trans (hc k) hnR
  have hsub : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) ((d.chart k (c k)).radius / 4) :=
    d.phaseRadius_chart (I := I) hdist
  have hquarter : Metric.ball (0 : E) ((d.chart k (c k)).radius / 4) ⊆
      Metric.ball (0 : E) (d.chart k (c k)).radius :=
    Metric.ball_subset_ball (by linarith [(d.chart k (c k)).radius_pos])
  have hx : riemannianEDistOf (I := I) (X.obj k).metric
      (X.obj k).basepoint (c k) ≤ ENNReal.ofReal (n : Real) :=
    InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le
      (I := I) hreal (hc k)
  intro x hxU
  exact d.metric_deriv n i k hk (c k) hx x (hquarter (hsub (hU hxU)))

omit [CompleteSpace E] in
theorem phaseRadius_metricBoundsTwoPiece
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ n)
    {R : Real} (hR : (n : Real) ≤ R) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     Metric.ball (0 : E) (d.phaseRadius R) ⊆
       Metric.ball (0 : E) (d.metricBoundsTwoPiece hreal x hn).radius) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  rw [d.metricBoundsTwoPiece_radius]
  exact d.phaseRadius_chart (I := I) (le_trans hn hR)

end SeqBallNormalChartData

section ConsumerBounds

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [T2Space (TangentBundle I M)]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] in
theorem MetricBounds.fderiv_apply_le_of_C_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) {C1 : Real}
    (h1 : b.C 1 ≤ C1) {z : E} (hz : z ∈ Metric.ball (0 : E) b.radius) (u v w : E) :
    ‖fderiv Real (c.metric g) z u v w‖ ≤ C1 * ‖u‖ * ‖v‖ * ‖w‖ := by
  have hb1 : 0 ≤ b.C 1 := b.C_nonneg 1
  have hunit : 0 ≤ ‖u‖ * ‖v‖ * ‖w‖ := by positivity
  calc ‖fderiv Real (c.metric g) z u v w‖
      ≤ b.C 1 * ‖u‖ * ‖v‖ * ‖w‖ := b.fderiv_apply_le (I := I) g hz u v w
    _ ≤ C1 * ‖u‖ * ‖v‖ * ‖w‖ := by nlinarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] in
theorem MetricBounds.koszul_vec_norm_le_of_C_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) {C1 : Real}
    (h1 : b.C 1 ≤ C1) {z : E} (hz : z ∈ Metric.ball (0 : E) b.radius) (v w : E) :
    ‖MetricKoszul.koszulVec (b.equiv.coercive g hz)
        (fderiv Real (c.metric g) z) v w‖ ≤ 3 * C1 * ‖v‖ * ‖w‖ := by
  have hb1 : 0 ≤ b.C 1 := b.C_nonneg 1
  have hunit : 0 ≤ ‖v‖ * ‖w‖ := by positivity
  calc ‖MetricKoszul.koszulVec (b.equiv.coercive g hz)
        (fderiv Real (c.metric g) z) v w‖
      ≤ 3 * b.C 1 * ‖v‖ * ‖w‖ := b.koszul_vec_norm_le (I := I) g hz v w
    _ ≤ 3 * C1 * ‖v‖ * ‖w‖ := by nlinarith

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] in
theorem chartPhaseK_le_of_C_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (b : c.MetricBounds g) (CF : Nat → Real)
    (h1 : b.C 1 ≤ CF 1) (h2 : b.C 2 ≤ CF 2) (R : NNReal) :
    (chartPhaseK g b R : Real) ≤
      (6 * (CF 1) ^ 2 + 3 * CF 2) * (R : Real) ^ 2 + 6 * CF 1 * (R : Real) := by
  have hb1 : 0 ≤ b.C 1 := b.C_nonneg 1
  have hb2 : 0 ≤ b.C 2 := b.C_nonneg 2
  have hsq : (b.C 1) ^ 2 ≤ (CF 1) ^ 2 := pow_le_pow_left₀ hb1 h1 2
  have hR : (0 : Real) ≤ (R : Real) := R.coe_nonneg
  change (6 * (b.C 1) ^ 2 + 3 * b.C 2) * (R : Real) ^ 2 + 6 * b.C 1 * (R : Real) ≤
    (6 * (CF 1) ^ 2 + 3 * CF 2) * (R : Real) ^ 2 + 6 * CF 1 * (R : Real)
  nlinarith [hsq, hR, sq_nonneg (R : Real)]

end ConsumerBounds

end CheegerGromovCompactness
end DifferentialGeometry
