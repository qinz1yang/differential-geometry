import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Basic.ENNReal.Real

open Filter
open scoped ENNReal

universe u v

namespace Metric

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

noncomputable def mapEDistortion (f : X → Y) : ℝ≥0∞ :=
  ⨆ x, ⨆ x', ENNReal.ofReal |dist (f x) (f x') - dist x x'|

theorem ofReal_dist_error_le_mapEDistortion (f : X → Y) (x x' : X) :
    ENNReal.ofReal |dist (f x) (f x') - dist x x'| ≤ mapEDistortion f :=
  le_iSup_of_le x (le_iSup_of_le x' le_rfl)

theorem mapEDistortion_le_of_dist_error_le (f : X → Y) {ε : ℝ}
    (h : ∀ x x', |dist (f x) (f x') - dist x x'| ≤ ε) :
    mapEDistortion f ≤ ENNReal.ofReal ε :=
  iSup_le fun x => iSup_le fun x' => ENNReal.ofReal_le_ofReal (h x x')

theorem dist_error_lt_of_mapEDistortion_lt (f : X → Y) {ε : ℝ}
    (h : mapEDistortion f < ENNReal.ofReal ε) (x x' : X) :
    |dist (f x) (f x') - dist x x'| < ε :=
  (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp
    ((ofReal_dist_error_le_mapEDistortion f x x').trans_lt h)

end Metric

namespace GC.MetricGeometry

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

structure PointedBBIApprox (p : X) (q : Y) (R ε : ℝ) where
  radius_pos : 0 < R
  error_pos : 0 < ε
  toFun : Metric.ball p R → Y
  basepoint : toFun ⟨p, by simpa using radius_pos⟩ = q
  distortion : Metric.mapEDistortion toFun < ENNReal.ofReal ε
  coverage : ∀ y : Y, dist y q < R - ε → ∃ x, dist y (toFun x) < ε

namespace PointedBBIApprox

variable {p : X} {q : Y} {R ε s : ℝ}

theorem pairwise_distortion (f : PointedBBIApprox p q R ε)
    (x x' : Metric.ball p R) :
    |dist (f.toFun x) (f.toFun x') - dist x.val x'.val| < ε :=
  Metric.dist_error_lt_of_mapEDistortion_lt f.toFun f.distortion x x'

def toOpenBall (f : PointedBBIApprox p q R ε) (hεR : ε < R) :
    PointedOpenBallApprox p q R ε where
  error_pos := f.error_pos
  error_lt_radius := hεR
  toFun := f.toFun
  basepoint := f.basepoint
  distortion := f.pairwise_distortion
  coverage := f.coverage

def toClosedBall (f : PointedBBIApprox p q R ε) (hs : 2 * ε < s) (hsR : s < R) :
    PointedBallApprox p q s (2 * ε) :=
  (f.toOpenBall (by linarith [f.error_pos])).toClosedBall hs hsR

end PointedBBIApprox

namespace PointedOpenBallApprox

variable {p : X} {q : Y} {R ε η : ℝ}

def toBBIApprox (f : PointedOpenBallApprox p q R ε) (hεη : ε < η) :
    PointedBBIApprox p q R η where
  radius_pos := f.error_pos.trans f.error_lt_radius
  error_pos := f.error_pos.trans hεη
  toFun := f.toFun
  basepoint := f.basepoint
  distortion := by
    have h := Metric.mapEDistortion_le_of_dist_error_le f.toFun
      (fun x x' => (f.distortion x x').le)
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (f.error_pos.trans hεη)).mpr hεη)
  coverage y hy := by
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    exact ⟨x, hx.trans hεη⟩

end PointedOpenBallApprox

namespace PointedBallApprox

variable {p : X} {q : Y} {R ε s : ℝ}

def toBBIApprox (f : PointedBallApprox p q R ε) (hs : 2 * ε < s) (hsR : s < R) :
    PointedBBIApprox p q s (3 * ε) :=
  (f.toOpenBall hs hsR).toBBIApprox (by linarith [f.error_pos])

end PointedBallApprox

variable {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)]

def BBIPointedGHConverges (p : ∀ n, Z n) (q : Y) : Prop :=
  ∀ R ε : ℝ, 0 < R → 0 < ε →
    ∀ᶠ n in atTop, Nonempty (PointedBBIApprox (p n) q R ε)

theorem PointedGHConverges.bbi {p : ∀ n, Z n} {q : Y}
    (h : PointedGHConverges p q) : BBIPointedGHConverges p q := by
  intro R ε hR hε
  let δ := min (ε / 2) (R / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδR : δ < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  filter_upwards [h.eventually_open_approx hδ hδR] with n hn
  obtain ⟨f⟩ := hn
  exact ⟨f.toBBIApprox hδε⟩

theorem PointedGHConverges.of_bbi [CompleteSpace Y] {p : ∀ n, Z n} {q : Y}
    (h : BBIPointedGHConverges p q) : PointedGHConverges p q := by
  apply PointedGHConverges.of_eventually_open_approx
  intro R ε hε hεR
  filter_upwards [h R ε (hε.trans hεR) hε] with n hn
  obtain ⟨f⟩ := hn
  exact ⟨f.toOpenBall hεR⟩

theorem pointedGHConverges_iff_completeSpace_and_bbi {p : ∀ n, Z n} {q : Y} :
    PointedGHConverges p q ↔ CompleteSpace Y ∧ BBIPointedGHConverges p q := by
  constructor
  · intro h
    exact ⟨h.complete_space, h.bbi⟩
  · rintro ⟨hc, hb⟩
    let : CompleteSpace Y := hc
    exact PointedGHConverges.of_bbi hb

theorem bbiPointedGHConverges_iff_strict_threshold {p : ∀ n, Z n} {q : Y} :
    BBIPointedGHConverges p q ↔ ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → Nonempty (PointedBBIApprox (p n) q R ε) := by
  constructor
  · intro h R ε hR hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h R ε hR hε)
    exact ⟨N, fun n hn => hN n hn.le⟩
  · intro h R ε hR hε
    obtain ⟨N, hN⟩ := h R ε hR hε
    exact eventually_atTop.mpr ⟨N + 1, fun n hn => hN n (by omega)⟩

end GC.MetricGeometry
