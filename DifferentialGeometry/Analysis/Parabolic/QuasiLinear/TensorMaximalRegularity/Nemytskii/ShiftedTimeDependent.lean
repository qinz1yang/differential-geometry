import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedTame
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeInterval

noncomputable section
open MeasureTheory Set Filter
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {A X Y Z : Type*}
  [SeminormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem shiftedRemainder_timeNemyMeas
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z) (D : Z →L[ℝ] Y)
    (d : Y →L[ℝ] Y) (q : A)
    (alpha : ℝ → Z → A) (reaction : ℝ → Z → Y) (f : X)
    {R τ : ℝ} {S : Set X} (hzero : (0 : X) ∈ S)
    (hS : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (ha : Continuous (fun p : Set.Icc (0 : ℝ) τ × Metric.closedBall (0 : Z) R =>
      alpha p.1 p.2))
    (hB : Continuous (fun p : Set.Icc (0 : ℝ) τ × Metric.closedBall (0 : Z) R =>
      reaction p.1 p.2)) :
    Continuous (fun p : Set.Icc (0 : ℝ) τ × S =>
      shiftedRemainder m Q J D d q alpha reaction f p.1 (p.2 : X)) ∧
      TimeNemyMeas hzero
        (fun t (u : S) => shiftedRemainder m Q J D d q alpha reaction f t (u : X)) τ := by
  let hj : S → Metric.closedBall (0 : Z) R := fun u =>
    ⟨J (u : X), by simpa only [Metric.mem_closedBall, dist_zero_right] using hS u⟩
  have hjc : Continuous hj :=
    (J.continuous.comp continuous_subtype_val).subtype_mk _
  have hJ : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => J (p.2 : X)) :=
    J.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hQ : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => Q (p.2 : X)) :=
    Q.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have ha' : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => alpha p.1 (J (p.2 : X))) :=
    ha.comp (continuous_fst.prodMk (hjc.comp continuous_snd))
  have hB' : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => reaction p.1 (J (p.2 : X))) :=
    hB.comp (continuous_fst.prodMk (hjc.comp continuous_snd))
  have hN : Continuous (fun p : Set.Icc (0 : ℝ) τ × S =>
      m (alpha p.1 (J (p.2 : X)) - q) (Q (p.2 : X)) +
      m (alpha p.1 (J (p.2 : X))) (Q f) +
      reaction p.1 (J (p.2 : X)) - d (D (J (p.2 : X)))) :=
    ((((m.continuous.comp (ha'.sub continuous_const)).clm_apply hQ).add
      ((m.continuous.comp ha').clm_apply continuous_const)).add hB').sub
        (d.continuous.comp (D.continuous.comp hJ))
  refine ⟨?_, ?_⟩
  · simpa only [shiftedRemainder] using hN
  · apply QuasiLinear.timeNemy_of_contOn_Icc hzero
    simpa only [shiftedRemainder] using hN

end DifferentialGeometry.Analysis.Parabolic
