import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstaclePullbackModel
import DifferentialGeometry.Topology.Engulfing.Local.Charts.ChartCorrection

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {η : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}
  {M : Type*} [TopologicalSpace M]

namespace RelativeGeneralPositionApproximation

variable (a : RelativeGeneralPositionApproximation K L T f d p η)
theorem correctedChart_eq_rawMap_of_exact
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (G : K.space → M) {x : K.space} (hx : e (G x) = a.approximation x) :
    correctedAffineChart e a.correction (G x) = a.rawMap x := by
  exact congrArg a.correction.symm hx
theorem correctedChart_eq_rawMap_on
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (G : K.space → M) {B : Set K.space}
    (hB : ∀ x ∈ B, e (G x) = a.approximation x) :
    EqOn (fun x => correctedAffineChart e a.correction (G x)) a.rawMap B :=
  fun _ hx => a.correctedChart_eq_rawMap_of_exact e G (hB _ hx)
theorem correctedChart_eq_rawMap_of_relative
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g G : K.space → M) {x : K.space} (hxL : x.val ∈ L.space)
    (hfix : G x = g x) (hlocal : f x = e (g x)) :
    correctedAffineChart e a.correction (G x) = a.rawMap x := by
  apply a.correctedChart_eq_rawMap_of_exact e G
  rw [hfix, a.relative x hxL, hlocal]
theorem original_dist_rawMap_lt (x : K.space) : dist (f x) (a.rawMap x) < 2 * η := by
  have hnear : dist (f x) (a.approximation x) < η := by
    simpa only [dist_eq_norm, norm_sub_rev] using a.near x
  have hcorrection : dist (a.approximation x) (a.rawMap x) < η := by
    have h := a.correction_near (a.rawMap x)
    change ‖a.correction (a.correction.symm (a.approximation x)) - a.rawMap x‖ < η at h
    simpa only [a.correction.apply_symm_apply, dist_eq_norm] using h
  have htri := dist_triangle (f x) (a.approximation x) (a.rawMap x)
  linarith
theorem originalChart_mem_ball_of_rawMap_mem_closedBall
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} {x : K.space}
    (hlocal : f x = e (g x)) (hx : a.rawMap x ∈ closedBall c r) :
    e (g x) ∈ ball c (r + 2 * η) := by
  have hnear := a.original_dist_rawMap_lt x
  rw [hlocal] at hnear
  have hsmall := mem_closedBall.mp hx
  have htri := dist_triangle (e (g x)) (a.rawMap x) c
  apply mem_ball.mpr
  linarith
theorem originalChart_mem_ball_of_rawMap_mem_ball
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} {x : K.space}
    (hlocal : f x = e (g x)) (hx : a.rawMap x ∈ ball c r) :
    e (g x) ∈ ball c (r + 2 * η) :=
  a.originalChart_mem_ball_of_rawMap_mem_closedBall e g c hlocal (ball_subset_closedBall hx)
theorem original_mem_chart_closedBall_of_rawMap_mem_ball
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ} {x : K.space}
    (hsource : g x ∈ e.source) (hlocal : f x = e (g x))
    (hx : a.rawMap x ∈ ball c r) (hrR : r + 2 * η ≤ R) :
    g x ∈ e.symm '' closedBall c R := by
  refine ⟨e (g x), ?_, e.left_inv hsource⟩
  exact closedBall_subset_closedBall hrR
    (ball_subset_closedBall (a.originalChart_mem_ball_of_rawMap_mem_ball e g c hlocal hx))
theorem face_subset_core_of_raw_image
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hrR : r + 2 * η ≤ R) {s : Finset E} {B : Set K.space}
    (hsource : ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → g x ∈ e.source)
    (hlocal : ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → f x = e (g x))
    (hsmall : a.rawMap '' {x : K.space | x.val ∈ convexHull ℝ (s : Set E)} ⊆ ball c r)
    (hcore : ∀ x : K.space, g x ∈ e.symm '' closedBall c R → x ∈ B) :
    {x : K.space | x.val ∈ convexHull ℝ (s : Set E)} ⊆ B := by
  intro x hx
  exact hcore x (a.original_mem_chart_closedBall_of_rawMap_mem_ball e g c
    (hsource x hx) (hlocal x hx) (hsmall (mem_image_of_mem _ hx)) hrR)
theorem originalChart_mem_ball_of_fixed_corrected
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g G : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} {x : K.space}
    (hfix : G x = g x)
    (hx : correctedAffineChart e a.correction (G x) ∈ ball c r) :
    e (g x) ∈ ball c (r + η) := by
  have hnear := a.correction_near (a.correction.symm (e (g x)))
  rw [a.correction.apply_symm_apply, ← dist_eq_norm] at hnear
  have hsmall : dist (a.correction.symm (e (g x))) c < r := by
    simpa only [correctedAffineChart_apply, hfix] using mem_ball.mp hx
  have htri := dist_triangle (e (g x)) (a.correction.symm (e (g x))) c
  apply mem_ball.mpr
  linarith
theorem fixed_mem_chart_closedBall_of_corrected
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g G : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ} {x : K.space}
    (hfix : G x = g x) (hsource : G x ∈ e.source)
    (hx : correctedAffineChart e a.correction (G x) ∈ ball c r) (hrR : r + η ≤ R) :
    g x ∈ e.symm '' closedBall c R := by
  refine ⟨e (g x), ?_, e.left_inv (hfix ▸ hsource)⟩
  exact closedBall_subset_closedBall hrR
    (ball_subset_closedBall (a.originalChart_mem_ball_of_fixed_corrected e g G c hfix hx))
theorem fixed_core_mem_interior
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g G : K.space → M) (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hrR : r + η ≤ R) {D S : Set E}
    (hfix : ∀ x : K.space, x.val ∈ S → G x = g x)
    (hentry : ∀ x : K.space, g x ∈ e.symm '' closedBall c R →
      x ∈ interior (Subtype.val ⁻¹' D)) :
    ∀ x : K.space, x.val ∈ S →
      G x ∈ (correctedAffineChart e a.correction).source ∩
        correctedAffineChart e a.correction ⁻¹' ball c r →
      x ∈ interior (Subtype.val ⁻¹' D) := by
  intro x hxL hx
  exact hentry x (a.fixed_mem_chart_closedBall_of_corrected e g G c
    (hfix x hxL) hx.1 hx.2 hrR)

end RelativeGeneralPositionApproximation

end

end DifferentialGeometry.Topology.Engulfing
