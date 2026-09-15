import DifferentialGeometry.Topology.FixedPoint.NoRetraction
import DifferentialGeometry.Topology.InvarianceOfDomain
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Topology.FixedPoint

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def fixedPointRayScale (p x : E) : ℝ :=
  let d := x - p
  let a := ⟪d, d⟫_ℝ
  let b := ⟪p, d⟫_ℝ
  (-b + Real.sqrt (b ^ 2 + a * (1 - ⟪p, p⟫_ℝ))) / a

private lemma fixedPointRayScale_mul_inner (p x : E) (hpx : p ≠ x) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x =
      -⟪p, x - p⟫_ℝ + Real.sqrt
        (⟪p, x - p⟫_ℝ ^ 2 + ⟪x - p, x - p⟫_ℝ * (1 - ⟪p, p⟫_ℝ)) := by
  rw [fixedPointRayScale]
  have hdenom : ⟪x - p, x - p⟫_ℝ ≠ 0 :=
    inner_self_ne_zero.mpr (sub_ne_zero.mpr hpx.symm)
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hdenom]

private lemma quadratic_root (a b c : ℝ) (ha : 0 < a) (hc : c ≤ 1) :
    a * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) ^ 2 +
        2 * b * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) + c = 1 := by
  let D := b ^ 2 + a * (1 - c)
  let t := (-b + Real.sqrt D) / a
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have ht : a * t = -b + Real.sqrt D := by
    dsimp [t]
    field_simp [ha.ne']
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  change a * t ^ 2 + 2 * b * t + c = 1
  have htb : a * t + b = Real.sqrt D := by
    linarith
  calc
    a * t ^ 2 + 2 * b * t + c = ((a * t + b) ^ 2 - b ^ 2) / a + c := by
      field_simp [ha.ne']
      ring
    _ = (D - b ^ 2) / a + c := by rw [htb, hsqrt]
    _ = 1 := by
      dsimp [D]
      field_simp [ha.ne']
      ring

private lemma fixedPointRayScale_quadratic (p x : E) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x ^ 2 +
        2 * ⟪p, x - p⟫_ℝ * fixedPointRayScale p x + ⟪p, p⟫_ℝ = 1 := by
  have ha : 0 < ⟪x - p, x - p⟫_ℝ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpx.symm)
  have hc : ⟪p, p⟫_ℝ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg p]
  simpa [fixedPointRayScale] using quadratic_root
    ⟪x - p, x - p⟫_ℝ ⟪p, x - p⟫_ℝ ⟪p, p⟫_ℝ ha hc

private lemma fixedPointRayEndpoint_mem_sphere (p x : E) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    p + fixedPointRayScale p x • (x - p) ∈ Metric.sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hquad := fixedPointRayScale_quadratic p x hpx hp
  have hsq : ‖p + fixedPointRayScale p x • (x - p)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm p (x - p)]
    nlinarith [hquad]
  nlinarith [norm_nonneg (p + fixedPointRayScale p x • (x - p))]

private lemma fixedPointRayScale_eq_one_of_mem_sphere (p x : E) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) (hx : ‖x‖ = 1) :
    fixedPointRayScale p x = 1 := by
  let a := ⟪x - p, x - p⟫_ℝ
  let b := ⟪p, x - p⟫_ℝ
  let c := ⟪p, p⟫_ℝ
  let t := fixedPointRayScale p x
  have hroot : a * t ^ 2 + 2 * b * t + c = 1 := by
    simpa [a, b, c, t] using fixedPointRayScale_quadratic p x hpx hp
  have hxinner : ⟪x, x⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hx]
    norm_num
  have hrootOne : a + 2 * b + c = 1 := by
    rw [show x = p + (x - p) by abel] at hxinner
    simp only [inner_add_left, inner_add_right] at hxinner
    rw [real_inner_comm p (x - p)] at hxinner
    dsimp only [a, b, c]
    nlinarith [hxinner]
  let s : EuclideanGeometry.Sphere E := ⟨0, 1⟩
  have hxmem : x ∈ s := by
    change dist x (0 : E) = 1
    simpa [dist_zero_right] using hx
  have hple : dist p s.center ≤ s.radius := by
    simpa [s, dist_zero_right] using hp
  have hgeom : 0 < ⟪x - p, x⟫_ℝ := by
    simpa [s] using
      (EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius hxmem hple).resolve_right hpx.symm
  have hab : 0 < a + b := by
    have hinner : ⟪x - p, x⟫_ℝ = a + b := by
      calc
        ⟪x - p, x⟫_ℝ = ⟪x - p, (x - p) + p⟫_ℝ := by
          congr 1
          abel
        _ = a + b := by
          rw [inner_add_right, real_inner_comm p (x - p)]
    rwa [hinner] at hgeom
  have ht : a * t = -b + Real.sqrt (b ^ 2 + a * (1 - c)) := by
    simpa [a, b, c, t] using fixedPointRayScale_mul_inner p x hpx
  have hfactor : 0 < a * (t + 1) + 2 * b := by
    nlinarith [Real.sqrt_nonneg (b ^ 2 + a * (1 - c))]
  have hprod : (t - 1) * (a * (t + 1) + 2 * b) = 0 := by
    nlinarith [hroot, hrootOne]
  have htOne : t = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact False.elim (hfactor.ne' h)
  exact htOne

private lemma continuous_fixedPointRayScale
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) (hne : ∀ x, f x ≠ x) :
    Continuous fun x ↦ fixedPointRayScale (f x).1 x.1 := by
  have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
  have hxv : Continuous fun x : Metric.closedBall (0 : E) 1 ↦ x.1 :=
    continuous_subtype_val
  have hd : Continuous fun x ↦ x.1 - (f x).1 := hxv.sub hfv
  have ha : Continuous fun x ↦ ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ := hd.inner hd
  have hb : Continuous fun x ↦ ⟪(f x).1, x.1 - (f x).1⟫_ℝ := hfv.inner hd
  have hc : Continuous fun x ↦ ⟪(f x).1, (f x).1⟫_ℝ := hfv.inner hfv
  have hdisc : Continuous fun x ↦
      ⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ * (1 - ⟪(f x).1, (f x).1⟫_ℝ) :=
    hb.pow 2 |>.add (ha.mul (continuous_const.sub hc))
  have hdenom : ∀ x, ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ ≠ 0 := by
    intro x
    apply inner_self_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro h
    apply hne x
    exact Subtype.ext h.symm
  change Continuous fun x ↦
    (-⟪(f x).1, x.1 - (f x).1⟫_ℝ +
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ))) /
      ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ
  have hsqrt : Continuous fun x ↦
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ)) := by
    exact Real.continuous_sqrt.comp hdisc
  exact (hb.neg.add hsqrt).div ha hdenom

variable [FiniteDimensional ℝ E]

theorem exists_fixedPoint_closedBall_of_continuous
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) :
    ∃ x, f x = x := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact ⟨⟨0, by simp⟩, Subsingleton.elim _ _⟩
  have hd : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  by_contra hfixed
  have hne : ∀ x, f x ≠ x := by
    intro x hx
    exact hfixed ⟨x, hx⟩
  let r : Metric.closedBall (0 : E) 1 → Metric.sphere (0 : E) 1 := fun x ↦
    ⟨(f x).1 + fixedPointRayScale (f x).1 x.1 • (x.1 - (f x).1), by
      apply fixedPointRayEndpoint_mem_sphere
      · intro heq
        apply hne x
        exact Subtype.ext heq
      · have hp := (f x).2
        rw [Metric.mem_closedBall, dist_zero_right] at hp
        exact hp⟩
  apply not_exists_retraction_closedBall_sphere hd
  refine ⟨r, ?_, ?_⟩
  · apply Continuous.subtype_mk
    have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
    have hxv : Continuous fun x : Metric.closedBall (0 : E) 1 ↦ x.1 :=
      continuous_subtype_val
    exact hfv.add ((continuous_fixedPointRayScale f hf hne).smul (hxv.sub hfv))
  · intro z
    apply Subtype.ext
    let x : Metric.closedBall (0 : E) 1 :=
      ⟨z.1, Metric.sphere_subset_closedBall z.2⟩
    have hpx : (f x).1 ≠ z.1 := by
      intro heq
      apply hne x
      exact Subtype.ext heq
    have hp : ‖(f x).1‖ ≤ 1 := by
      have hp := (f x).2
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      exact hp
    have hz : ‖z.1‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp z.2
    have hscale := fixedPointRayScale_eq_one_of_mem_sphere (f x).1 z.1 hpx hp hz
    change (f x).1 + fixedPointRayScale (f x).1 z.1 • (z.1 - (f x).1) = z.1
    rw [hscale, one_smul]
    abel

instance : BrouwerFixedPoint E where
  brouwer_fixed_point := exists_fixedPoint_closedBall_of_continuous

end DifferentialGeometry.Topology.FixedPoint
