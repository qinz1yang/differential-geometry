import DifferentialGeometry.Geometry.Metric.Approximation.PerturbApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product

open Set Metric

namespace GC.MetricGeometry.PointedBallApprox

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]
variable {p : X} {a : E} {b : Y} {R ε ρ δ : ℝ}

noncomputable def replaceFirstCoordinate
    (f : PointedBallApprox p (WithLp.toLp 2 (a, b)) R ε)
    (h : X → E) (hp : h p = a)
    (hclose : ∀ x : BallCarrier p R, dist (h x.val) (f.toFun x).fst ≤ ρ)
    (hE : ε + 2 * ρ < R) :
    PointedBallApprox p (WithLp.toLp 2 (a, b)) R (ε + 2 * ρ) :=
  f.perturb (fun x => WithLp.toLp 2 (h x.val, (f.toFun x).snd))
    (by change WithLp.toLp 2 (h p, (f.toFun ⟨p, _⟩).snd) = _; rw [hp, f.basepoint]; rfl)
    (by
      intro x
      change dist (WithLp.toLp 2 (h x.val, (f.toFun x).snd))
        (WithLp.toLp 2 ((f.toFun x).fst, (f.toFun x).snd)) ≤ ρ
      rw [(WithLp.isometry_prodMk_right (f.toFun x).snd).dist_eq (h x.val) (f.toFun x).fst]
      exact hclose x) hE

theorem replaceFirstCoordinate_fst
    (f : PointedBallApprox p (WithLp.toLp 2 (a, b)) R ε)
    (h : X → E) (hp : h p = a)
    (hclose : ∀ x : BallCarrier p R, dist (h x.val) (f.toFun x).fst ≤ ρ)
    (hE : ε + 2 * ρ < R) (x : BallCarrier p R) :
    ((f.replaceFirstCoordinate h hp hclose hE).toFun x).fst = h x.val := rfl

noncomputable def toKleinerLottWithFirstCoordinate
    (f : PointedBallApprox p (WithLp.toLp 2 (a, b)) R ε)
    (h : X → E)
    (hδ : 0 < δ) (hδone : δ < 1) (hε : ε < δ / 2) (hR : δ⁻¹ ≤ R) :
    KleinerLottApprox p (WithLp.toLp 2 (a, b)) δ := by
  classical
  let F (x : X) : WithLp 2 (E × Y) :=
    if hx : dist x p ≤ R then f.toFun ⟨x, hx⟩ else WithLp.toLp 2 (h x, b)
  have hF (x : BallCarrier p R) : F x.val = f.toFun x := by
    simp only [F, dite_eq_left x.property]
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · have hpR : dist p p ≤ R := by simpa using (inv_pos.mpr hδ).le.trans hR
    rw [hF ⟨p, hpR⟩]
    exact f.basepoint
  · intro x hx y hy
    have hxR : dist x p ≤ R := hx.le.trans hR
    have hyR : dist y p ≤ R := hy.le.trans hR
    rw [hF ⟨x, hxR⟩, hF ⟨y, hyR⟩]
    exact (f.distortion _ _).le.trans (by linarith)
  · intro y hy
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    have ht := dist_triangle (f.toFun x) y (WithLp.toLp 2 (a, b))
    rw [dist_comm (f.toFun x) y] at ht
    have hxin : dist x.val p < δ⁻¹ := by linarith [f.radial_lower x]
    have hmem : F x.val ∈ F '' ball p δ⁻¹ := ⟨x.val, hxin, rfl⟩
    have hdist : dist y (F x.val) < ε := by rwa [hF x]
    exact (infDist_le_dist_of_mem hmem).trans (hdist.le.trans (by linarith))

theorem toKleinerLottWithFirstCoordinate_fst
    (f : PointedBallApprox p (WithLp.toLp 2 (a, b)) R ε)
    (h : X → E) (hh : ∀ x : BallCarrier p R, (f.toFun x).fst = h x.val)
    (hδ : 0 < δ) (hδone : δ < 1) (hε : ε < δ / 2) (hR : δ⁻¹ ≤ R) (x : X) :
    ((f.toKleinerLottWithFirstCoordinate h hδ hδone hε hR).toFun x).fst = h x := by
  classical
  change (if hx : dist x p ≤ R then f.toFun ⟨x, hx⟩ else WithLp.toLp 2 (h x, b)).fst = h x
  split_ifs with hx
  · exact hh ⟨x, hx⟩
  · rfl

end GC.MetricGeometry.PointedBallApprox
