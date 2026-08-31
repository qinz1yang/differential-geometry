import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology NNReal

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem lRampAct_fwd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ omega : Real} (ht₀omega : t₀ ≤ omega)
    (hreg : Icc t₀ t₁ ⊆ D.regular) (p : M)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target) :
    ∃ Cg Cs : Real, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {T a L : Real} {y z : E} (_hT : T ≤ omega) (hL : 0 < L),
        (∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ Icc t₀ t₁) →
        MapsTo (lChartRamp y z hL.le).toFun (Icc (0 : Real) L) K →
        lChartAction S T a p (lChartRamp y z hL.le) ≤
          (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
  obtain ⟨Cg, hCg⟩ := chartGramOp_bound (I := I) hS.smoothMetric hreg
    isCompact_Icc p hKchart hKc
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar : ContinuousOn (fun q : Real × M ↦ S.scalar q.1 q.2)
      (Icc t₀ t₁ ×ˢ (univ : Set M)) := by
    apply hSc.scalar_continuousOn.mono
    intro q hq
    exact ⟨D.regular_subset (hreg hq.1), hq.2⟩
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn
      hscalar
  let C : Real := max C₀ 0
  let Cs : Real := 2 * (omega - t₀) * C
  have hC : 0 ≤ C := le_max_right _ _
  have homega : 0 ≤ omega - t₀ := sub_nonneg.mpr ht₀omega
  refine ⟨Cg, Cs, NNReal.coe_nonneg Cg, mul_nonneg
    (mul_nonneg (by norm_num) homega) hC, ?_⟩
  intro T a L y z _hT hL htime hrange
  apply lRampAct_bound (I := I) S hS T a p hL
  · intro r hr
    exact hreg (htime r hr)
  · intro r hr
    exact hKchart (hrange hr)
  · intro r hr
    exact hCg (T - (a + r) ^ 2,
      (lChartRamp y z hL.le).toFun r) ⟨htime r hr, hrange hr⟩
  · intro r hr
    have hforward := htime r hr
    have hsquare : (a + r) ^ 2 ≤ omega - t₀ := by
      linarith [hforward.1, _hT]
    have hscalar₀ := hC₀
      (T - (a + r) ^ 2,
        (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))
      ⟨hforward, mem_univ _⟩
    rw [Real.norm_eq_abs] at hscalar₀
    have hscalarC :
        |S.scalar (T - (a + r) ^ 2)
          ((extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))| ≤ C :=
      hscalar₀.trans (le_max_left C₀ 0)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
      abs_of_nonneg (sq_nonneg (a + r))]
    dsimp only [Cs]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hscalarC
      (abs_nonneg _) (mul_nonneg (by positivity) homega)

omit [NeZero (Module.finrank ℝ E)] in
theorem redLen_ramp_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ omega : Real} (ht₀omega : t₀ ≤ omega)
    (hregFwd : Icc t₀ t₁ ⊆ D.regular) (p : M)
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I p).target) :
    ∃ Cg Cs : Real, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {T b c l₀ : Real} {x : M} {W : TangentSpace I x},
        T ≤ omega → 0 < c → c < b →
        Icc (T - b ^ 2) T ⊆ D.regular →
        (∀ r ∈ Icc (0 : Real) (b - c),
          T - (c + r) ^ 2 ∈ Icc t₀ t₁) →
        b ∈ lRegDomain S T x W → (W, c ^ 2) ∈ lMinDomain S T x →
        lRegCurve S T x W c ∈ (chartAt H p).source →
        (extChartAt I p) (lRegCurve S T x W c) ∈ K →
        redLength S T x (lRegCurve S T x W c) (c ^ 2) ≤ l₀ →
        ∀ z ∈ K,
          redLength S T x ((extChartAt I p).symm z) (b ^ 2) ≤
            (2 * c * l₀ +
                (Cg / 2) *
                  (‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ^ 2 /
                    (b - c)) + Cs * (b - c)) /
              (2 * b) := by
  obtain ⟨Cg, Cs, hCg, hCs, hramp⟩ :=
    lRampAct_fwd (I := I) S hS ht₀omega hregFwd p hKc hKchart
  refine ⟨Cg, Cs, hCg, hCs, ?_⟩
  intro T b c l₀ x W hT hc hcb hslab hforward hbdom hmin hrayc hyK hred z hzK
  have hb : 0 < b := hc.trans hcb
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    intro s hs
    have hsquare : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hreg : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hslab (hback s hs)
  have htime : Icc (T - b ^ 2) T ⊆ D.carrier := fun _ ht ↦
    D.regular_subset (hslab ht)
  let y : E := (extChartAt I p) (lRegCurve S T x W c)
  have hmap : MapsTo
      (lChartRamp y z (sub_nonneg.mpr hcb.le)).toFun
      (Icc (0 : Real) (b - c)) K :=
    lRamp_mapsTo hKconv (sub_nonneg.mpr hcb.le) hyK hzK
  have hmapTarget : MapsTo
      (lChartRamp y z (sub_nonneg.mpr hcb.le)).toFun
      (Icc (0 : Real) (b - c)) (extChartAt I p).target := by
    intro r hr
    exact interior_subset (hKchart (hmap hr))
  have hcost := lCost_ramp_le (I := I) S hS T x p hc hcb
    htime hback hreg W hbdom hrayc z hmapTarget
  have hrampLe := hramp hT (sub_pos.mpr hcb) hforward hmap
  have hminEq := ((mem_lMinDomain S T x W (c ^ 2)).1 hmin).2
  have hhead : lRegAction S T (lRegCurve S T x W) 0 c =
      lCost S T x (lRegCurve S T x W c) (c ^ 2) := by
    calc
      lRegAction S T (lRegCurve S T x W) 0 c =
          lLength S T (squareRootReparametrization (lRegCurve S T x W)) 0 (c ^ 2) := by
        simpa only [Real.sqrt_sq hc.le] using
          (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x W)
            (c ^ 2) (sq_nonneg c)).symm
      _ = lCost S T x (lExp S T x W (c ^ 2)) (c ^ 2) := by
        change lLength S T (fun r : Real ↦
          lRegCurve S T x W (Real.sqrt r)) 0 (c ^ 2) = _
        simpa only [lExp] using hminEq
      _ = lCost S T x (lRegCurve S T x W c) (c ^ 2) := by
        simp only [lExp, Real.sqrt_sq hc.le]
  have hheadLe : lCost S T x (lRegCurve S T x W c) (c ^ 2) ≤
      2 * c * l₀ := by
    unfold redLength at hred
    rw [Real.sqrt_sq hc.le] at hred
    simpa only [mul_comm l₀] using
      (div_le_iff₀ (by positivity : 0 < 2 * c)).1 hred
  have hcostLe : lCost S T x ((extChartAt I p).symm z) (b ^ 2) ≤
      2 * c * l₀ +
        (Cg / 2) * (‖z - y‖ ^ 2 / (b - c)) + Cs * (b - c) := by
    rw [hhead] at hcost
    linarith
  unfold redLength
  rw [Real.sqrt_sq hb.le]
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * b)).2
    (by simpa only [y] using hcostLe)

omit [NeZero (Module.finrank ℝ E)] in
theorem redLen_ball_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ omega : Real} (ht₀omega : t₀ ≤ omega)
    (hregFwd : Icc t₀ t₁ ⊆ D.regular) (p : M)
    (q : E) {R : Real} (hR : 0 < R)
    (hball : Metric.closedBall q R ⊆
      interior (extChartAt I p).target) :
    ∃ Cg Cs : Real, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {T b c l₀ : Real} {x : M} {W : TangentSpace I x},
        T ≤ omega → 0 < c → c < b →
        Icc (T - b ^ 2) T ⊆ D.regular →
        (∀ r ∈ Icc (0 : Real) (b - c),
          T - (c + r) ^ 2 ∈ Icc t₀ t₁) →
        b ∈ lRegDomain S T x W → (W, c ^ 2) ∈ lMinDomain S T x →
        lRegCurve S T x W c ∈ (chartAt H p).source →
        (extChartAt I p) (lRegCurve S T x W c) ∈
          Metric.closedBall q R →
        redLength S T x (lRegCurve S T x W c) (c ^ 2) ≤ l₀ →
        let A := (extChartAt I p).symm '' Metric.ball q R
        MeasurableSet A ∧
          0 < riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - b ^ 2)) A ∧
          ∀ y ∈ A,
            redLength S T x y (b ^ 2) ≤
              (2 * c * l₀ +
                  (Cg / 2) * ((2 * R) ^ 2 / (b - c)) +
                    Cs * (b - c)) /
                (2 * b) := by
  obtain ⟨Cg, Cs, hCg, hCs, hbound⟩ :=
    redLen_ramp_bound (I := I) S hS ht₀omega hregFwd p
      (isCompact_closedBall q R) (convex_closedBall q R) hball
  refine ⟨Cg, Cs, hCg, hCs, ?_⟩
  intro T b c l₀ x W hT hc hcb hslab hforward hbdom hmin hrayc hyBall hred
  let A : Set M := (extChartAt I p).symm '' Metric.ball q R
  have hballTarget : Metric.ball q R ⊆ (extChartAt I p).target := by
    intro z hz
    exact interior_subset (hball (Metric.ball_subset_closedBall hz))
  have hAopen : IsOpen A := by
    change IsOpen ((extChartAt I p).symm '' Metric.ball q R)
    rw [(extChartAt I p).symm_image_eq_source_inter_preimage hballTarget]
    exact isOpen_extChartAt_preimage' (I := I) p Metric.isOpen_ball
  have hAne : A.Nonempty := by
    exact ⟨(extChartAt I p).symm q, q, Metric.mem_ball_self hR, rfl⟩
  let mu := riemannianVolumeMeasure (I := I) (M := M)
    (S.base.metric (T - b ^ 2))
  let : mu.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M)
      (S.base.metric (T - b ^ 2))
  refine ⟨hAopen.measurableSet, hAopen.measure_pos mu hAne, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzClosed : z ∈ Metric.closedBall q R :=
    Metric.ball_subset_closedBall hz
  have hraw := hbound hT hc hcb hslab hforward hbdom hmin hrayc
    hyBall hred z hzClosed
  have hnorm :
      ‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ≤ 2 * R := by
    calc
      ‖z - (extChartAt I p) (lRegCurve S T x W c)‖ =
          dist z ((extChartAt I p) (lRegCurve S T x W c)) := by
        rw [dist_eq_norm]
      _ ≤ dist z q + dist q ((extChartAt I p) (lRegCurve S T x W c)) :=
        dist_triangle _ _ _
      _ ≤ R + R := by
        rw [dist_comm q]
        exact add_le_add hz.le hyBall
      _ = 2 * R := by ring
  have hsq :
      ‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ^ 2 ≤
        (2 * R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR.le)).2 hnorm
  have hfrac :
      ‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ^ 2 /
          (b - c) ≤
        (2 * R) ^ 2 / (b - c) :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hcb)).2 hsq
  have hterm :
      (Cg / 2) *
          (‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ^ 2 /
            (b - c)) ≤
        (Cg / 2) * ((2 * R) ^ 2 / (b - c)) :=
    mul_le_mul_of_nonneg_left hfrac (div_nonneg hCg (by norm_num))
  have hb : 0 < b := hc.trans hcb
  calc
    redLength S T x ((extChartAt I p).symm z) (b ^ 2) ≤
        (2 * c * l₀ +
            (Cg / 2) *
              (‖z - (extChartAt I p) (lRegCurve S T x W c)‖ ^ 2 /
                (b - c)) + Cs * (b - c)) /
          (2 * b) := hraw
    _ ≤ (2 * c * l₀ +
            (Cg / 2) * ((2 * R) ^ 2 / (b - c)) + Cs * (b - c)) /
          (2 * b) := by
      apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hb)).2
      linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
