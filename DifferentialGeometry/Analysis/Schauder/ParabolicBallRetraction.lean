import DifferentialGeometry.Analysis.Calculus.BallRetraction
import DifferentialGeometry.Analysis.Schauder.Composition

noncomputable section

open Real Set
open DifferentialGeometry.Analysis.Calculus
open scoped InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V]
  [NormedAddCommGroup F]

def parabolicTimeCenteredBallRetraction (tau R : Real) :
    ParabolicPoint V → ParabolicPoint V :=
  fun p ↦ parabolicPoint (p.time - tau) (ballRetraction R p.space)

def parabolicBallRetraction (R : Real) :
    ParabolicPoint V → ParabolicPoint V :=
  parabolicTimeCenteredBallRetraction 0 R

def parabolicTimeCenteredBallRetractionExtension
    (tau R : Real) (f : ParabolicPoint V → F) :
    ParabolicPoint V → F :=
  f ∘ parabolicTimeCenteredBallRetraction tau R

def parabolicBallRetractionExtension
    (R : Real) (f : ParabolicPoint V → F) :
    ParabolicPoint V → F :=
  parabolicTimeCenteredBallRetractionExtension 0 R f

@[simp]
theorem parabolicTimeCenteredBallRetraction_apply
    (tau R : Real) (p : ParabolicPoint V) :
    parabolicTimeCenteredBallRetraction tau R p =
      parabolicPoint (p.time - tau) (ballRetraction R p.space) :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem parabolicTimeCenteredBallRetraction_time
    (tau R : Real) (p : ParabolicPoint V) :
    (parabolicTimeCenteredBallRetraction tau R p).time = p.time - tau :=
  rfl

@[simp]
theorem parabolicTimeCenteredBallRetraction_space
    (tau R : Real) (p : ParabolicPoint V) :
    (parabolicTimeCenteredBallRetraction tau R p).space =
      ballRetraction R p.space :=
  rfl

omit [NormedAddCommGroup F] in
set_option linter.unusedSectionVars false in
@[simp]
theorem parabolicTimeCenteredBallRetractionExtension_apply
    (tau R : Real) (f : ParabolicPoint V → F) (p : ParabolicPoint V) :
    parabolicTimeCenteredBallRetractionExtension tau R f p =
      f (parabolicTimeCenteredBallRetraction tau R p) :=
  rfl

@[simp]
theorem parabolicBallRetraction_apply
    (R : Real) (p : ParabolicPoint V) :
    parabolicBallRetraction R p =
      parabolicPoint p.time (ballRetraction R p.space) := by
  simp only [parabolicBallRetraction,
    parabolicTimeCenteredBallRetraction_apply, sub_zero]

set_option linter.unusedSectionVars false in
theorem parabolicBallRetraction_time
    (R : Real) (p : ParabolicPoint V) :
    (parabolicBallRetraction R p).time = p.time :=
  by simp only [parabolicBallRetraction,
    parabolicTimeCenteredBallRetraction_time, sub_zero]

@[simp]
theorem parabolicBallRetraction_space
    (R : Real) (p : ParabolicPoint V) :
    (parabolicBallRetraction R p).space = ballRetraction R p.space :=
  rfl

omit [NormedAddCommGroup F] in
set_option linter.unusedSectionVars false in
@[simp]
theorem parabolicBallRetractionExtension_apply
    (R : Real) (f : ParabolicPoint V → F) (p : ParabolicPoint V) :
    parabolicBallRetractionExtension R f p =
      f (parabolicBallRetraction R p) :=
  rfl

theorem lipschitzWith_one_parabolicTimeCenteredBallRetraction
    (tau : Real) {R : Real} (hR : 0 ≤ R) :
    LipschitzWith 1
      (parabolicTimeCenteredBallRetraction (V := V) tau R) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, ← parabolicPoint_time_space p,
    ← parabolicPoint_time_space q,
    parabolicTimeCenteredBallRetraction_apply,
    parabolicTimeCenteredBallRetraction_apply,
    dist_parabolicPoint, dist_parabolicPoint]
  change max (|(p.time - tau) - (q.time - tau)| ^ (1 / 2 : Real))
      (dist (ballRetraction R p.space) (ballRetraction R q.space)) ≤
    max (|p.time - q.time| ^ (1 / 2 : Real)) (dist p.space q.space)
  have hspace :=
    (lipschitzWith_one_ballRetraction (X := V) hR).dist_le_mul
      p.space q.space
  rw [NNReal.coe_one, one_mul] at hspace
  apply max_le
  · rw [show (p.time - tau) - (q.time - tau) = p.time - q.time by ring]
    exact le_max_left _ _
  · exact hspace.trans (le_max_right _ _)

theorem lipschitzWith_one_parabolicBallRetraction
    {R : Real} (hR : 0 ≤ R) :
    LipschitzWith 1 (parabolicBallRetraction (V := V) R) := by
  simpa only [parabolicBallRetraction] using
    lipschitzWith_one_parabolicTimeCenteredBallRetraction (V := V) 0 hR

theorem parabolicBallRetraction_eq_self_of_mem_closedBall
    {R : Real} {p : ParabolicPoint V}
    (hp : p.space ∈ Metric.closedBall (0 : V) R) :
    parabolicBallRetraction R p = p := by
  have hnorm : ‖p.space‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  rw [parabolicBallRetraction_apply,
    ballRetraction_eq_self_of_mem hnorm, parabolicPoint_time_space]

theorem parabolicBallRetraction_mapsTo_parabolicCylinder_closedBall
    {J : Set Real} {R : Real} (hR : 0 ≤ R) :
    MapsTo (parabolicBallRetraction (V := V) R)
      (parabolicCylinder J Set.univ)
      (parabolicCylinder J (Metric.closedBall 0 R)) := by
  intro p hp
  refine ⟨?_, ?_⟩
  · simpa only [parabolicBallRetraction_time] using hp.1
  · simpa only [parabolicBallRetraction_space, Metric.mem_closedBall,
      dist_zero_right] using ballRetraction_mem_closedBall hR p.space

theorem parabolicTimeCenteredBallRetraction_mem_ball
    (tau : Real) {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    {p : ParabolicPoint V}
    (htime : |p.time - tau| ^ (1 / 2 : Real) < S) :
    parabolicTimeCenteredBallRetraction tau R p ∈
      Metric.ball (parabolicPoint 0 0) S := by
  rw [Metric.mem_ball, ← parabolicPoint_time_space p,
    parabolicTimeCenteredBallRetraction_apply, dist_parabolicPoint]
  apply max_lt
  · simpa only [sub_zero] using htime
  · rw [dist_zero_right]
    exact (ballRetraction_mem_closedBall hR p.space).trans_lt hRS

theorem parabolicBallRetraction_mem_ball
    {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    {p : ParabolicPoint V}
    (htime : |p.time| ^ (1 / 2 : Real) < S) :
    parabolicBallRetraction R p ∈
      Metric.ball (parabolicPoint 0 0) S := by
  exact parabolicTimeCenteredBallRetraction_mem_ball 0 hR hRS
    (by simpa only [sub_zero] using htime)

theorem parabolicTimeCenteredBallRetraction_mapsTo_ball
    (tau : Real) {J : Set Real} {R S : Real}
    (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t - tau| ^ (1 / 2 : Real) < S) :
    MapsTo (parabolicTimeCenteredBallRetraction (V := V) tau R)
      (parabolicCylinder J Set.univ)
      (Metric.ball (parabolicPoint 0 0) S) := by
  intro p hp
  exact parabolicTimeCenteredBallRetraction_mem_ball tau hR hRS
    (htime p.time hp.1)

theorem parabolicBallRetraction_mapsTo_ball
    {J : Set Real} {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t| ^ (1 / 2 : Real) < S) :
    MapsTo (parabolicBallRetraction (V := V) R)
      (parabolicCylinder J Set.univ)
      (Metric.ball (parabolicPoint 0 0) S) := by
  have htime' : ∀ t ∈ J, |t - 0| ^ (1 / 2 : Real) < S := by
    intro t ht
    simpa only [sub_zero] using htime t ht
  simpa only [parabolicBallRetraction, sub_zero] using
    parabolicTimeCenteredBallRetraction_mapsTo_ball
      (V := V) 0 hR hRS htime'

omit [NormedAddCommGroup F] in
theorem parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall
    (tau : Real) {R : Real} (f : ParabolicPoint V → F)
    {p : ParabolicPoint V}
    (hp : p.space ∈ Metric.closedBall (0 : V) R) :
    parabolicTimeCenteredBallRetractionExtension tau R f p =
      f (parabolicPoint (p.time - tau) p.space) := by
  rw [parabolicTimeCenteredBallRetractionExtension_apply,
    parabolicTimeCenteredBallRetraction_apply,
    ballRetraction_eq_self_of_mem]
  simpa only [Metric.mem_closedBall, dist_zero_right] using hp

omit [NormedAddCommGroup F] in
theorem parabolicBallRetractionExtension_eq_of_mem_closedBall
    {R : Real} (f : ParabolicPoint V → F) {p : ParabolicPoint V}
    (hp : p.space ∈ Metric.closedBall (0 : V) R) :
    parabolicBallRetractionExtension R f p = f p := by
  simpa only [parabolicBallRetractionExtension,
    parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall,
    sub_zero, parabolicPoint_time_space] using
    parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall
      0 f hp

theorem parabolicTimeCenteredBallRetractionExtension_holderWith
    (tau : Real) {J : Set Real} {R S : Real}
    (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t - tau| ^ (1 / 2 : Real) < S)
    {alpha K : NNReal} (f : ParabolicPoint V → F)
    (hf : HolderWith K alpha
      ((Metric.ball (parabolicPoint 0 0) S).restrict f)) :
    HolderWith K alpha
      ((parabolicCylinder J Set.univ).restrict
        (parabolicTimeCenteredBallRetractionExtension tau R f)) := by
  have hresult := holderWith_restrict_comp_of_lipschitzWith
    (parabolicTimeCenteredBallRetraction tau R) f
    (lipschitzWith_one_parabolicTimeCenteredBallRetraction tau hR)
    (parabolicTimeCenteredBallRetraction_mapsTo_ball tau hR hRS htime) hf
  simpa only [parabolicTimeCenteredBallRetractionExtension, mul_one,
    NNReal.one_rpow] using hresult

theorem parabolicBallRetractionExtension_holderWith
    {J : Set Real} {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t| ^ (1 / 2 : Real) < S)
    {alpha K : NNReal} (f : ParabolicPoint V → F)
    (hf : HolderWith K alpha
      ((Metric.ball (parabolicPoint 0 0) S).restrict f)) :
    HolderWith K alpha
      ((parabolicCylinder J Set.univ).restrict
        (parabolicBallRetractionExtension R f)) := by
  have htime' : ∀ t ∈ J, |t - 0| ^ (1 / 2 : Real) < S := by
    intro t ht
    simpa only [sub_zero] using htime t ht
  simpa only [parabolicBallRetractionExtension, sub_zero] using
    parabolicTimeCenteredBallRetractionExtension_holderWith
      0 hR hRS htime' f hf

theorem norm_parabolicTimeCenteredBallRetractionExtension_le
    (tau : Real) {J : Set Real} {R S : Real}
    (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t - tau| ^ (1 / 2 : Real) < S)
    {B : NNReal} (f : ParabolicPoint V → F)
    (hf : ∀ p, p ∈ Metric.ball (parabolicPoint 0 0) S → ‖f p‖ ≤ B) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖parabolicTimeCenteredBallRetractionExtension tau R f p‖ ≤ B := by
  intro p hp
  rw [parabolicTimeCenteredBallRetractionExtension_apply]
  exact hf _
    (parabolicTimeCenteredBallRetraction_mapsTo_ball tau hR hRS htime hp)

theorem norm_parabolicBallRetractionExtension_le
    {J : Set Real} {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t| ^ (1 / 2 : Real) < S)
    {B : NNReal} (f : ParabolicPoint V → F)
    (hf : ∀ p, p ∈ Metric.ball (parabolicPoint 0 0) S → ‖f p‖ ≤ B) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖parabolicBallRetractionExtension R f p‖ ≤ B := by
  have htime' : ∀ t ∈ J, |t - 0| ^ (1 / 2 : Real) < S := by
    intro t ht
    simpa only [sub_zero] using htime t ht
  simpa only [parabolicBallRetractionExtension, sub_zero] using
    norm_parabolicTimeCenteredBallRetractionExtension_le
      0 hR hRS htime' f hf

theorem norm_sub_parabolicTimeCenteredBallRetractionExtension_le
    (tau : Real) {J : Set Real} {R S : Real}
    (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t - tau| ^ (1 / 2 : Real) < S)
    {omega : NNReal} (f0 : F) (f : ParabolicPoint V → F)
    (hf : ∀ p, p ∈ Metric.ball (parabolicPoint 0 0) S →
      ‖f0 - f p‖ ≤ omega) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖f0 - parabolicTimeCenteredBallRetractionExtension tau R f p‖ ≤
        omega := by
  intro p hp
  rw [parabolicTimeCenteredBallRetractionExtension_apply]
  exact hf _
    (parabolicTimeCenteredBallRetraction_mapsTo_ball tau hR hRS htime hp)

theorem norm_sub_parabolicBallRetractionExtension_le
    {J : Set Real} {R S : Real} (hR : 0 ≤ R) (hRS : R < S)
    (htime : ∀ t ∈ J, |t| ^ (1 / 2 : Real) < S)
    {omega : NNReal} (f0 : F) (f : ParabolicPoint V → F)
    (hf : ∀ p, p ∈ Metric.ball (parabolicPoint 0 0) S →
      ‖f0 - f p‖ ≤ omega) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖f0 - parabolicBallRetractionExtension R f p‖ ≤ omega := by
  have htime' : ∀ t ∈ J, |t - 0| ^ (1 / 2 : Real) < S := by
    intro t ht
    simpa only [sub_zero] using htime t ht
  simpa only [parabolicBallRetractionExtension, sub_zero] using
    norm_sub_parabolicTimeCenteredBallRetractionExtension_le
      0 hR hRS htime' f0 f hf

end DifferentialGeometry.Analysis.Schauder

end
