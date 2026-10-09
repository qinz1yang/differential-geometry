import DifferentialGeometry.Geometry.Metric.Approximation.TargetBasepointRepair

set_option autoImplicit false


namespace GC.MetricGeometry

noncomputable def recenterTolerance (δ C : ℝ) : ℝ :=
  min (δ / 100) (1 / (100 * (C + δ⁻¹ + 2)))

theorem recenterTolerance_pos {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    0 < recenterTolerance δ C := by
  unfold recenterTolerance
  positivity

end GC.MetricGeometry

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {ε δ C : ℝ}

noncomputable def recenterWithTarget (f : KleinerLottApprox p q ε) (a : X) (b : Y)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C) (hε : ε ≤ recenterTolerance δ C)
    (ha : dist p a ≤ C) (hb : dist (f.toFun a) b ≤ ε) :
    KleinerLottApprox a b δ := by
  classical
  let s := δ⁻¹ + 1
  let R₀ := C + δ⁻¹ + 2
  have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hRpos : 0 < R₀ := by dsimp [R₀]; linarith
  have heδ : ε ≤ δ / 100 := hε.trans (min_le_left _ _)
  have heR : ε ≤ (100 * R₀)⁻¹ := by
    simpa only [one_div] using hε.trans (min_le_right _ _)
  have hRinv : R₀ < ε⁻¹ := by
    have hh := (inv_le_inv₀ (by positivity : 0 < (100 * R₀)⁻¹) f.error_pos).mpr heR
    rw [inv_inv] at hh
    linarith
  have h22 : 22 * ε < δ := by linarith
  have h3 : 3 * ε < R₀ := by dsimp [R₀]; linarith
  have h9 : 9 * ε < s := by dsimp [s]; linarith
  have h11 : 11 * ε < s := by dsimp [s]; linarith
  let F₀ := f.toClosedBall h3 hRinv
  let G : PointedBallApprox a (f.toFun a) s (9 * ε) :=
    (F₀.recenter a (by linarith) (by dsimp [R₀, s]; rw [dist_comm a p]; linarith)).enlargeError
      (by linarith) h9
  let K : PointedBallApprox a b s (11 * ε) :=
    (G.repairTarget b f.error_pos.le hb (by linarith)).enlargeError (by linarith) h11
  let F : X → Y := fun x => if x = a then b else f.toFun x
  have hK (x : BallCarrier a s) : K.toFun x = F x.val := rfl
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · simp only [F, ite_true]
  · intro x hx y hy
    have hxS : dist x a ≤ s := by dsimp [s]; linarith [Metric.mem_ball.mp hx]
    have hyS : dist y a ≤ s := by dsimp [s]; linarith [Metric.mem_ball.mp hy]
    have hd := K.distortion ⟨x, hxS⟩ ⟨y, hyS⟩
    rw [hK, hK] at hd
    dsimp only at hd
    linarith [f.error_pos]
  · intro y hy
    obtain ⟨x, hx⟩ := K.coverage y (by dsimp [s]; linarith [f.error_pos])
    have hrad := K.radial_lower x
    have ht := dist_triangle (K.toFun x) y b
    rw [dist_comm (K.toFun x) y] at ht
    have hxa : dist x.val a < δ⁻¹ := by linarith
    have hm : K.toFun x ∈ F '' Metric.ball a δ⁻¹ := ⟨x.val, hxa, (hK x).symm⟩
    exact (Metric.infDist_le_dist_of_mem hm).trans (by linarith [f.error_pos])

theorem recenterWithTarget_apply_of_ne (f : KleinerLottApprox p q ε) (a : X) (b : Y)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C) (hε : ε ≤ recenterTolerance δ C)
    (ha : dist p a ≤ C) (hb : dist (f.toFun a) b ≤ ε) (x : X) (hx : x ≠ a) :
    (f.recenterWithTarget a b hδ hδone hC hε ha hb).toFun x = f.toFun x := by
  classical
  simp only [recenterWithTarget, ite_eq_right hx]

theorem recenterWithTarget_dist_le (f : KleinerLottApprox p q ε) (a : X) (b : Y)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C) (hε : ε ≤ recenterTolerance δ C)
    (ha : dist p a ≤ C) (hb : dist (f.toFun a) b ≤ ε) (x : X) :
    dist ((f.recenterWithTarget a b hδ hδone hC hε ha hb).toFun x) (f.toFun x) ≤
      dist (f.toFun a) b := by
  by_cases hx : x = a
  · rw [hx, (f.recenterWithTarget a b hδ hδone hC hε ha hb).basepoint, dist_comm]
  · rw [f.recenterWithTarget_apply_of_ne a b hδ hδone hC hε ha hb x hx, dist_self]
    exact dist_nonneg

theorem recenterWithTarget_self_apply (f : KleinerLottApprox p q ε) (a : X)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C) (hε : ε ≤ recenterTolerance δ C)
    (ha : dist p a ≤ C) (x : X) :
    (f.recenterWithTarget a (f.toFun a) hδ hδone hC hε ha
      (by simpa only [dist_self] using f.error_pos.le)).toFun x = f.toFun x := by
  by_cases hx : x = a
  · rw [hx]
    exact (f.recenterWithTarget a (f.toFun a) hδ hδone hC hε ha
      (by simpa only [dist_self] using f.error_pos.le)).basepoint
  · exact f.recenterWithTarget_apply_of_ne a (f.toFun a) hδ hδone hC hε ha _ x hx

end GC.MetricGeometry.KleinerLottApprox
