import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallEuclideanUpper
import DifferentialGeometry.Analysis.Integration.Measure.Properties

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] [ConnectedSpace M] [NoncompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_univ_eq_top_of_complete_noncompact_ricci_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    riemannianVolumeMeasure (I := I) (M := M) g Set.univ = ⊤ := by
  classical
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (⊤ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  let _ : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  let _ : ProperSpace M :=
    HopfRinow.properSpace_riemMetric (I := I) (M := M)
      hcomplete.complete g hEnorm
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : mu.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  let n : Nat := Module.finrank Real E
  let p : M := Classical.choice (inferInstance : Nonempty M)
  have hunbounded : ¬ Bornology.IsBounded (Set.univ : Set M) := by
    intro hbounded
    have hcompact : IsCompact (Set.univ : Set M) :=
      (Metric.isCompact_iff_isClosed_bounded).2 ⟨isClosed_univ, hbounded⟩
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M)) ⟨hcompact⟩
  have hfar (R : Real) : ∃ y : M, R < dist y p := by
    by_contra hnot
    have hbound : ∀ y : M, dist y p ≤ R := by
      intro y
      exact le_of_not_gt (fun hy => hnot ⟨y, hy⟩)
    apply hunbounded
    rw [Metric.isBounded_iff_subset_closedBall p]
    refine ⟨R, ?_⟩
    intro y _hy
    rw [Metric.mem_closedBall]
    simpa [dist_comm] using hbound y
  let d : Nat → Real := fun j => (4 : Real) ^ (j + 1)
  have hd_pos (j : Nat) : 0 < d j := by
    dsimp only [d]
    positivity
  have hexact (j : Nat) : ∃ q : M, dist q p = d j := by
    obtain ⟨y, hy⟩ := hfar (d j)
    exact HopfRinow.intermediateDist_riemMetric (I := I) (M := M)
      hcomplete.complete g hEnorm p y (d j) (hd_pos j).le hy.le
  choose q hq using hexact
  let r : Nat → Real := fun j => d j / 4
  have hr_pos (j : Nat) : 0 < r j := div_pos (hd_pos j) (by norm_num)
  have hdisj_of_lt {j k : Nat} (hjk : j < k) :
      Disjoint (Metric.ball (q j) (r j)) (Metric.ball (q k) (r k)) := by
    have hscale : 4 * d j ≤ d k := by
      dsimp only [d]
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hdist : d k - d j ≤ dist (q j) (q k) := by
      have htriangle := dist_triangle (q k) (q j) p
      rw [hq k, hq j, dist_comm (q k) (q j)] at htriangle
      linarith
    apply Metric.ball_disjoint_ball
    have hrsum : r j + r k ≤ d k - d j := by
      dsimp only [r]
      nlinarith [hd_pos j]
    exact hrsum.trans hdist
  have hdisj : Pairwise (fun j k : Nat =>
      Disjoint (Metric.ball (q j) (r j)) (Metric.ball (q k) (r k))) := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with hjk' | hkj'
    · exact hdisj_of_lt hjk'
    · exact (hdisj_of_lt hkj').symm
  have hball_eq (x : M) {R : Real} :
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} = Metric.ball x R := by
    ext y
    rw [Metric.mem_ball]
    change riemannianEDist I x y < ENNReal.ofReal R ↔ dist y x < R
    rw [ENNReal.lt_ofReal_iff_toReal_lt
      (Exponential.riemannianEDist_ne_top (I := I) x y)]
    rw [← HopfRinow.riemMetric_dist_eq (I := I) (M := M) x y]
    exact iff_of_eq (congrArg (fun z : Real => z < R) (dist_comm x y))
  have hbase_pos : 0 < mu (Metric.ball p 1) :=
    Metric.measure_ball_pos mu p (by norm_num)
  let C : ENNReal := ENNReal.ofReal ((8 : Real) ^ n)
  have hC_pos : 0 < C := ENNReal.ofReal_pos.mpr (by positivity)
  have hC_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let eps : ENNReal := mu (Metric.ball p 1) / C
  have heps_pos : 0 < eps := ENNReal.div_pos hbase_pos.ne' hC_top
  have hlower (j : Nat) : eps ≤ mu (Metric.ball (q j) (r j)) := by
    let R : Real := d j + 1
    have hd_one : 1 ≤ d j := by
      dsimp only [d]
      exact one_le_pow₀ (by norm_num)
    have hR_pos : 0 < R := by dsimp only [R]; linarith [hd_pos j]
    have hrR : r j ≤ R := by
      dsimp only [r, R]
      linarith [hd_pos j]
    have hBG := segBall_vol_pow (I := I) g hEnorm (q j)
      (s := r j) (R := R) (hr_pos j) hrR hRic
    rw [hball_eq (q j), hball_eq (q j)] at hBG
    have hbase_subset : Metric.ball p 1 ⊆ Metric.ball (q j) R := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      have htriangle := dist_triangle y p (q j)
      have hpq : dist p (q j) = d j := by
        rw [dist_comm]
        exact hq j
      rw [hpq] at htriangle
      dsimp only [R]
      linarith
    have hbase_le : mu (Metric.ball p 1) ≤ mu (Metric.ball (q j) R) :=
      measure_mono hbase_subset
    have hscaled :
        mu (Metric.ball p 1) * ENNReal.ofReal ((r j) ^ n) ≤
          ENNReal.ofReal (R ^ n) * mu (Metric.ball (q j) (r j)) :=
      (by
        have hbase_scaled :=
          mul_le_mul_right hbase_le (ENNReal.ofReal ((r j) ^ n))
        have hbase_scaled' :
            mu (Metric.ball p 1) * ENNReal.ofReal ((r j) ^ n) ≤
              mu (Metric.ball (q j) R) * ENNReal.ofReal ((r j) ^ n) := by
          simpa only [mul_comm] using hbase_scaled
        exact hbase_scaled'.trans hBG)
    have hRs : R ≤ 8 * r j := by
      dsimp only [R, r]
      linarith
    have hRpow : ENNReal.ofReal (R ^ n) ≤
        C * ENNReal.ofReal ((r j) ^ n) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num) n)]
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_pow]
      exact pow_le_pow_left₀ hR_pos.le hRs n
    have hscaled' :
        mu (Metric.ball p 1) * ENNReal.ofReal ((r j) ^ n) ≤
          C * ENNReal.ofReal ((r j) ^ n) * mu (Metric.ball (q j) (r j)) :=
      (by
        have hR_scaled :=
          mul_le_mul_right hRpow (mu (Metric.ball (q j) (r j)))
        have hR_scaled' :
            ENNReal.ofReal (R ^ n) * mu (Metric.ball (q j) (r j)) ≤
              C * ENNReal.ofReal ((r j) ^ n) *
                mu (Metric.ball (q j) (r j)) := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hR_scaled
        exact hscaled.trans hR_scaled')
    have hrpow_pos : 0 < ENNReal.ofReal ((r j) ^ n) :=
      ENNReal.ofReal_pos.mpr (pow_pos (hr_pos j) n)
    have hbase_C : mu (Metric.ball p 1) ≤
        C * mu (Metric.ball (q j) (r j)) := by
      apply (ENNReal.mul_le_mul_iff_right hrpow_pos.ne' ENNReal.ofReal_ne_top).mp
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled'
    exact (ENNReal.div_le_iff' hC_pos.ne' hC_top).2 hbase_C
  apply top_unique
  calc
    ⊤ = ∑' _j : Nat, eps :=
      (ENNReal.tsum_const_eq_top_of_ne_zero heps_pos.ne').symm
    _ ≤ ∑' j : Nat, mu (Metric.ball (q j) (r j)) :=
      ENNReal.tsum_le_tsum hlower
    _ ≤ mu Set.univ :=
      tsum_measure_le_measure_univ
        (fun j => (Metric.isOpen_ball.measurableSet).nullMeasurableSet)
        (fun j k hjk => (hdisj hjk).aedisjoint)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
