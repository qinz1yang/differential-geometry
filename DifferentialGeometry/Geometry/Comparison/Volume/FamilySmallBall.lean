import DifferentialGeometry.Geometry.Comparison.Volume.FamilyParamControl
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Comparison.Volume.SmallBall

set_option autoImplicit false

/-!
# Uniform small-ball lower bounds for metric families

This file isolates the metric-family version of the compact-uniform small-ball
volume theorem needed by Perelman's initial-time noncollapsing argument.  The
pointwise fixed-centre theorem lives in `SmallBall`; the missing content here is
the compact-uniform all-centre/all-radius strengthening for a continuous
time-dependent metric family.
-/

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open Bundle MeasureTheory Metric Set

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [ConnectedSpace M] [BoundarylessManifold I M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Compact-uniform raw small-ball volume lower bound for a smooth metric
family near the initial endpoint of `[0, omega)`.

This is the geometric producer behind the initial-time part of Perelman's
no-local-collapsing theorem. -/
theorem family_vol_low
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (G : RealizedMetricFamilyOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega))
    (_hG : MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega) G)
    {rho : Real} (_hrho : 0 < rho) :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ (p : M) {r : Real}, 0 < r → r ≤ rho → r ^ 2 ≤ (t : Real) →
          ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank Real E ≤
            riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
              {x : M | riemannianEDistOf (I := I) (G.metric (t : Real)) p x <
                ENNReal.ofReal r} := by
  classical
  by_cases hM : IsEmpty M
  · refine ⟨omega / 2, 1, by linarith, by linarith, one_pos, ?_⟩
    intro _t _ht p
    exact (hM.false p).elim
  rw [not_isEmpty_iff] at hM
  let Ψ : M → PartialDiffeomorph 𝓘(Real, E) I E M 1 :=
    fun a => NormalCoordinates.expMapDiffeo (I := I) (G.metric 0) a
  have hlocal : ∀ a : M, ∃ tau R c L : Real,
      0 < tau ∧ tau < omega ∧ 0 < R ∧ 0 < c ∧ 1 ≤ L ∧
      Metric.closedBall (0 : E) (2 * R) ⊆ (Ψ a).source ∧
      ∀ (t : RealTimeInterval.FlowTime
          (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ w ∈ Metric.closedBall (0 : E) (2 * R),
          c ≤ paramDensity (I := I) (G.metric (t : Real)) (Ψ a) w ∧
          ∀ v : E,
            Real.sqrt
              ((G.metric (t : Real)).inner ((Ψ a) w)
                (mfderiv 𝓘(Real, E) I (Ψ a) w v)
                (mfderiv 𝓘(Real, E) I (Ψ a) w v)) ≤ L * ‖v‖ := by
    intro a
    simpa only [Ψ] using exists_param_ctrl (I := I) h0omega G _hG a
  choose tauLoc RLoc cLoc LLoc htau_pos htau_lt hR_pos hc_pos hL_one hsource hctrl
    using hlocal
  let U : M → Set M := fun a => (Ψ a) '' Metric.ball (0 : E) (RLoc a)
  have hball_source : ∀ a : M,
      Metric.ball (0 : E) (RLoc a) ⊆ (Ψ a).source := by
    intro a w hw
    apply hsource a
    have hwR : ‖w‖ < RLoc a := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [hR_pos a]
  have hU_open : ∀ a : M, IsOpen (U a) := by
    intro a
    exact (Ψ a).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball (hball_source a)
  have haU : ∀ a : M, a ∈ U a := by
    intro a
    refine ⟨0, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_self] using hR_pos a
    · simpa only [Ψ] using
        NormalCoordinates.expMapDiffeo_zero (I := I) (G.metric 0) a
  have hcover : (Set.univ : Set M) ⊆ ⋃ a : M, U a := by
    intro a _ha
    exact Set.mem_iUnion.mpr ⟨a, haU a⟩
  obtain ⟨s, hs_cover⟩ :=
    (isCompact_univ (X := M)).elim_finite_subcover U hU_open hcover
  have hs_ne : s.Nonempty := by
    obtain ⟨a⟩ := hM
    have ha : a ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ a)
    rw [Set.mem_iUnion₂] at ha
    obtain ⟨i, hi, _⟩ := ha
    exact ⟨i, hi⟩
  let unitVol : Real :=
    ((modelHaar (E := E)) (Metric.ball (0 : E) 1)).toReal
  have hunit_pos : 0 < unitVol := by
    dsimp only [unitVol]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos (modelHaar (E := E)) (0 : E) one_pos).ne'
      measure_ball_lt_top.ne
  let kLoc : M → Real :=
    fun a => cLoc a * (LLoc a)⁻¹ ^ Module.finrank Real E * unitVol
  have hkLoc_pos : ∀ a : M, 0 < kLoc a := by
    intro a
    dsimp only [kLoc]
    exact mul_pos
      (mul_pos (hc_pos a) (pow_pos (inv_pos.mpr (zero_lt_one.trans_le (hL_one a))) _))
      hunit_pos
  let tau : Real :=
    s.inf' hs_ne (fun a => min (tauLoc a) ((RLoc a) ^ 2))
  let kappa : Real := s.inf' hs_ne kLoc
  have htau_pos' : 0 < tau := by
    rw [show tau = s.inf' hs_ne
      (fun a => min (tauLoc a) ((RLoc a) ^ 2)) from rfl,
      Finset.lt_inf'_iff]
    intro a _ha
    exact lt_min (htau_pos a) (sq_pos_of_pos (hR_pos a))
  have htau_le : ∀ a ∈ s, tau ≤ min (tauLoc a) ((RLoc a) ^ 2) := by
    intro a ha
    exact Finset.inf'_le _ ha
  have htau_lt' : tau < omega := by
    obtain ⟨a, ha⟩ := hs_ne
    exact (htau_le a ha).trans_lt <|
      (min_le_left (tauLoc a) ((RLoc a) ^ 2)).trans_lt (htau_lt a)
  have hkappa_pos : 0 < kappa := by
    rw [show kappa = s.inf' hs_ne kLoc from rfl, Finset.lt_inf'_iff]
    intro a _ha
    exact hkLoc_pos a
  have hkappa_le : ∀ a ∈ s, kappa ≤ kLoc a := by
    intro a ha
    exact Finset.inf'_le _ ha
  refine ⟨tau, kappa, htau_pos', htau_lt', hkappa_pos, ?_⟩
  intro t ht p r hr _hrho hr2
  have hp : p ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ p)
  rw [Set.mem_iUnion₂] at hp
  obtain ⟨a, ha, w, hw, hwp⟩ := hp
  have htau_a : tau ≤ tauLoc a :=
    (htau_le a ha).trans (min_le_left _ _)
  have hR_sq : tau ≤ (RLoc a) ^ 2 :=
    (htau_le a ha).trans (min_le_right _ _)
  have hrR : r ≤ RLoc a := by
    nlinarith [hR_pos a]
  let B : Set E := Metric.ball w (r / LLoc a)
  have hL_pos : 0 < LLoc a := zero_lt_one.trans_le (hL_one a)
  have hrad_pos : 0 < r / LLoc a := div_pos hr hL_pos
  have hw_norm : ‖w‖ < RLoc a := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hB_closed : B ⊆ Metric.closedBall (0 : E) (2 * RLoc a) := by
    intro z hz
    have hzw : dist z w < r / LLoc a := by
      simpa only [B, Metric.mem_ball] using hz
    have hdiv_le : r / LLoc a ≤ r := by
      exact (div_le_iff₀ hL_pos).2 <| by nlinarith [hL_one a, hr]
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ ‖w‖ + ‖z - w‖ := norm_le_norm_add_norm_sub' z w
      _ = ‖w‖ + dist z w := by rw [dist_eq_norm]
      _ ≤ 2 * RLoc a := by linarith
  have hB_source : B ⊆ (Ψ a).source :=
    hB_closed.trans (hsource a)
  have hseg : ∀ z ∈ B,
      segment Real w z ⊆ Metric.closedBall (0 : E) (2 * RLoc a) := by
    intro z hz
    apply (convex_closedBall (0 : E) (2 * RLoc a)).segment_subset
    · simp only [Metric.mem_closedBall, dist_zero_right]
      linarith [hw_norm, hR_pos a]
    · exact hB_closed hz
  have hctrl_t := hctrl a t (ht.trans htau_a)
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨(G.metric (t : Real)).toRiemannianMetric⟩
  have hspd : ∀ q ∈ Metric.closedBall (0 : E) (2 * RLoc a), ∀ ξ : E,
      ‖mfderiv 𝓘(Real, E) I (Ψ a) q ξ‖ₑ ≤
        ENNReal.ofReal (LLoc a * ‖ξ‖) := by
    intro q hq ξ
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    change ENNReal.ofReal
      (Real.sqrt
        ((G.metric (t : Real)).inner ((Ψ a) q)
          (mfderiv 𝓘(Real, E) I (Ψ a) q ξ)
          (mfderiv 𝓘(Real, E) I (Ψ a) q ξ))) ≤
        ENNReal.ofReal (LLoc a * ‖ξ‖)
    exact ENNReal.ofReal_le_ofReal ((hctrl_t q hq).2 ξ)
  have himage : (Ψ a) '' B ⊆
      {x : M | riemannianEDistOf (I := I) (G.metric (t : Real)) p x <
        ENNReal.ofReal r} := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hdist := param_edist_le (I := I) (Ψ a)
      (hsource a) hspd (hseg z hz)
    rw [← hwp]
    refine lt_of_le_of_lt hdist ?_
    have hzw : dist w z < r / LLoc a := by
      simpa only [B, Metric.mem_ball, dist_comm] using hz
    have hmul : LLoc a * dist w z < r := by
      calc
        LLoc a * dist w z < LLoc a * (r / LLoc a) :=
          mul_lt_mul_of_pos_left hzw hL_pos
        _ = r := by field_simp
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hmul
  have hparam :
      ENNReal.ofReal (cLoc a) * (modelHaar (E := E)) B ≤
        riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
          ((Ψ a) '' B) := by
    apply param_vol_ge (I := I) (G.metric (t : Real)) (Ψ a)
      measurableSet_ball hB_source
    intro z hz
    exact (hctrl_t z (hB_closed hz)).1
  have hmono :
      riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
          ((Ψ a) '' B) ≤
        riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
          {x : M | riemannianEDistOf (I := I) (G.metric (t : Real)) p x <
            ENNReal.ofReal r} :=
    measure_mono himage
  have hball :
      (modelHaar (E := E)) B =
        ENNReal.ofReal ((r / LLoc a) ^ Module.finrank Real E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1) := by
    simpa only [B] using
      (MeasureTheory.Measure.addHaar_ball_of_pos
        (μ := modelHaar (E := E)) (x := w) hrad_pos)
  have hkappa_ofReal :
      ENNReal.ofReal kappa ≤ ENNReal.ofReal (kLoc a) :=
    ENNReal.ofReal_le_ofReal (hkappa_le a ha)
  calc
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank Real E
        ≤ ENNReal.ofReal (kLoc a) *
            ENNReal.ofReal r ^ Module.finrank Real E := by gcongr
    _ = ENNReal.ofReal (cLoc a) * (modelHaar (E := E)) B := by
      rw [hball]
      dsimp only [kLoc, unitVol]
      rw [ENNReal.ofReal_mul (mul_nonneg (hc_pos a).le
          (pow_nonneg (inv_nonneg.mpr hL_pos.le) _)),
        ENNReal.ofReal_mul (hc_pos a).le,
        ENNReal.ofReal_pow (inv_nonneg.mpr hL_pos.le),
        ENNReal.ofReal_inv_of_pos hL_pos,
        ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      conv_rhs =>
        rw [ENNReal.ofReal_pow (div_nonneg hr.le hL_pos.le),
          ENNReal.ofReal_div_of_pos hL_pos]
      simp only [div_eq_mul_inv, mul_pow]
      ac_rfl
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
          ((Ψ a) '' B) := hparam
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real))
          {x : M | riemannianEDistOf (I := I) (G.metric (t : Real)) p x <
            ENNReal.ofReal r} := hmono

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
