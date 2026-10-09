import DifferentialGeometry.Geometry.Collapse.MetricRank.NotSmallFactor
import DifferentialGeometry.Geometry.Collapse.FixtureC1.NoEdgeOfSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# A point with a thin line splitting is not a strong edge point (S-FIXTURE-C2b, K2, G2 file 6)

`isEdgePoint p Δ b s` gives a `b`-approximation `F` of `X` near `p` by `ℝ ×₂ Y` and an
`s`-approximation `G` of `Y` near `q` by `[0, C]`, `C > 200 Δ`, `q ↦ 0`. The map
`π(x) = (F(x).fst, G(F(x).snd))` has additive distortion `≤ b + s` on `B(p, 6)`
(the argument of `NoEdgeOfSplitting`) and covers the points `(-3, 0)`, `(3, 0)`, `(0, 4)` of the
half plane `ℝ × [0, C]` up to `4 b + 6 s`. Their preimages are three points of `B(p, 6)` at
mutual distances `6, 5, 5` up to `9/100`; if `X` also has a Kleiner-Lott approximation by
`ℝ ×₂ Z` with `δ + D ≤ 1/100`, `diam Z ≤ D` (a thin line at `p`), the three-point exclusion
`not_small_factor_of_three_points_SMR` (`s' = 11/2`, `κ = 59/100`) is violated.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

universe u v w

theorem sqrt_sq_add_sq_le_FXC2 (A B A' B' : ℝ) :
    √(A ^ 2 + B ^ 2) ≤ √(A' ^ 2 + B' ^ 2) + (|A - A'| + |B - B'|) := by
  have hQ0 : 0 ≤ √(A' ^ 2 + B' ^ 2) := Real.sqrt_nonneg _
  have hQ2 : √(A' ^ 2 + B' ^ 2) ^ 2 = A' ^ 2 + B' ^ 2 := Real.sq_sqrt (by positivity)
  set Q := √(A' ^ 2 + B' ^ 2) with hQ
  have hA' : |A'| ≤ Q := abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg B']) hQ0 |> fun h =>
    abs_le.mpr h
  have hB' : |B'| ≤ Q := abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg A']) hQ0 |> fun h =>
    abs_le.mpr h
  have h1 : A' * (A - A') ≤ Q * |A - A'| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hA' (abs_nonneg _)))
  have h2 : B' * (B - B') ≤ Q * |B - B'| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hB' (abs_nonneg _)))
  have h3 : (A - A') ^ 2 = |A - A'| ^ 2 := (sq_abs _).symm
  have h4 : (B - B') ^ 2 = |B - B'| ^ 2 := (sq_abs _).symm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (abs_nonneg (A - A')) (abs_nonneg (B - B'))]

theorem abs_sqrt_sub_le_FXC2 (A B A' B' : ℝ) :
    |√(A ^ 2 + B ^ 2) - √(A' ^ 2 + B' ^ 2)| ≤ |A - A'| + |B - B'| := by
  rw [abs_le]
  have h1 := sqrt_sq_add_sq_le_FXC2 A B A' B'
  have h2 := sqrt_sq_add_sq_le_FXC2 A' B' A B
  rw [abs_sub_comm A' A, abs_sub_comm B' B] at h2
  constructor <;> linarith

/-- **A point with a thin line splitting is not a strong edge point** (`b + s ≤ 1/100`,
`δ + D ≤ 1/100`, `1 ≤ Δ`). -/
theorem not_isEdgePoint_of_thin_line_FXC2 {X : Type u} [mX : MetricSpace X] {p : X}
    {Δ b s δ D : ℝ} (hΔ : 1 ≤ Δ) (hbs : b + s ≤ 1 / 100) (hδD : δ + D ≤ 1 / 100)
    (hthin : ∃ (Z : Type w) (mZ : MetricSpace Z) (z : Z), letI := mZ
      (∀ y y' : Z, dist y y' ≤ D) ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) δ)) :
    ¬ isEdgePoint.{u, v} p Δ b s := by
  rintro ⟨Y, mY, q, C, hC, hCΔ, ⟨F⟩, ⟨G⟩⟩
  obtain ⟨Z, mZ, z, hZ, ⟨f⟩⟩ := hthin
  have hb0 := F.error_pos
  have hs0 := G.error_pos
  have hδ0 := f.error_pos
  have hD0 : 0 ≤ D := le_trans dist_nonneg (hZ z z)
  have hb1 : b ≤ 1 / 100 := by linarith
  have hs1 : s ≤ 1 / 100 := by linarith
  have hδ1 : δ ≤ 1 / 100 := by linarith
  have hbinv : 100 ≤ b⁻¹ := (le_inv_comm₀ (by norm_num) hb0).mpr (by simpa using hb1)
  have hsinv : 100 ≤ s⁻¹ := (le_inv_comm₀ (by norm_num) hs0).mpr (by simpa using hs1)
  have hδinv : 100 ≤ δ⁻¹ := (le_inv_comm₀ (by norm_num) hδ0).mpr (by simpa using hδ1)
  have hC4 : 4 ≤ C := by linarith
  let g : X → ℝ := fun x => ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ)
  -- the second component of the image of a point near `p` lies in the domain of `G`
  have hnear : ∀ x : X, dist x p < 6 → dist (F.toFun x).snd q < s⁻¹ := by
    intro x hx
    have hxb : x ∈ ball p b⁻¹ := by
      rw [mem_ball]
      linarith
    have h1 := WithLp.dist_snd_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
    have h2 := F.radial_error x hxb
    simp only [WithLp.toLp_snd] at h1
    rw [abs_le] at h2
    linarith [h2.2]
  -- additive distortion of the projection to the half plane on `B(p, 6)`
  have hπ : ∀ x y : X, dist x p < 6 → dist y p < 6 →
      |dist x y - √(((F.toFun x).fst - (F.toFun y).fst) ^ 2 + (g x - g y) ^ 2)| ≤ b + s := by
    intro x y hx hy
    have hxb : x ∈ ball p b⁻¹ := by
      rw [mem_ball]
      linarith
    have hyb : y ∈ ball p b⁻¹ := by
      rw [mem_ball]
      linarith
    have hFd := F.distortion x hxb y hyb
    have hsq := WithLp.prod_dist_sq_eq_add_sq (F.toFun x) (F.toFun y)
    have hGd := G.distortion _ (mem_ball.mpr (hnear x hx)) _ (mem_ball.mpr (hnear y hy))
    have hGe : dist (G.toFun (F.toFun x).snd) (G.toFun (F.toFun y).snd) = |g x - g y| := by
      rw [Subtype.dist_eq, Real.dist_eq]
    rw [hGe] at hGd
    have hd1 : dist (F.toFun x).fst (F.toFun y).fst ^ 2 =
        ((F.toFun x).fst - (F.toFun y).fst) ^ 2 := by
      rw [Real.dist_eq, sq_abs]
    have hQ0 : 0 ≤ ((F.toFun x).fst - (F.toFun y).fst) ^ 2 + (g x - g y) ^ 2 := by positivity
    have hP := abs_sub_le_of_sq_FXC1 (P := dist (F.toFun x) (F.toFun y))
      (Q := √(((F.toFun x).fst - (F.toFun y).fst) ^ 2 + (g x - g y) ^ 2))
      (A := (F.toFun x).fst - (F.toFun y).fst)
      (d := dist (F.toFun x).snd (F.toFun y).snd) (e := |g x - g y|)
      dist_nonneg (Real.sqrt_nonneg _) dist_nonneg (abs_nonneg _) (by rw [hsq, hd1])
      (by rw [Real.sq_sqrt hQ0, sq_abs])
    have hGd' : |(dist (F.toFun x).snd (F.toFun y).snd - |g x - g y|)| ≤ s := by
      rw [abs_sub_comm]
      exact hGd
    have h5 := abs_sub (dist x y) (dist (F.toFun x) (F.toFun y))
    have h6 := abs_sub_le (dist x y) (dist (F.toFun x) (F.toFun y))
      (√(((F.toFun x).fst - (F.toFun y).fst) ^ 2 + (g x - g y) ^ 2))
    rw [abs_sub_comm (dist x y) (dist (F.toFun x) (F.toFun y))] at h6
    linarith
  -- preimages of the targets
  have hpt : ∀ u₁ u₂ : ℝ, |u₁| ≤ 3 → 0 ≤ u₂ → u₂ ≤ 4 → ∃ x : X, dist x p < 6 ∧
      |(F.toFun x).fst - u₁| < 2 * b ∧ |g x - u₂| < 2 * b + 3 * s := by
    intro u₁ u₂ hu₁ hu₂0 hu₂4
    let t : Icc (0 : ℝ) C := ⟨u₂, hu₂0, by linarith⟩
    have ht : dist t (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) < s⁻¹ - s := by
      rw [Subtype.dist_eq, Real.dist_eq]
      change |u₂ - 0| < s⁻¹ - s
      rw [sub_zero, abs_of_nonneg hu₂0]
      linarith
    obtain ⟨w, hw, hwt⟩ := G.coverage_witness t ht
    have hGw : dist (G.toFun w) (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) ≤ u₂ + 2 * s := by
      have h1 := dist_triangle (G.toFun w) t (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C)
      have h2 : dist t (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) = u₂ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        change |u₂ - 0| = u₂
        rw [sub_zero, abs_of_nonneg hu₂0]
      rw [dist_comm (G.toFun w) t] at h1
      linarith
    have hwq : dist w q ≤ u₂ + 3 * s := by
      have h1 := G.radial_error w hw
      rw [abs_le] at h1
      linarith [h1.1]
    let y : WithLp 2 (ℝ × Y) := WithLp.toLp 2 (u₁, w)
    have hyq : dist y (WithLp.toLp 2 ((0 : ℝ), q)) ≤ 51 / 10 := by
      have hsq := WithLp.prod_dist_sq_eq_add_sq y (WithLp.toLp 2 ((0 : ℝ), q))
      simp only [y, WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero, sq_abs] at hsq
      have hu : u₁ ^ 2 ≤ 9 := by
        have := sq_abs u₁
        nlinarith [abs_nonneg u₁]
      have hw2 : dist w q ^ 2 ≤ (41 / 10) ^ 2 := by
        have := dist_nonneg (x := w) (y := q)
        nlinarith
      refine (sq_le_sq₀ dist_nonneg (by norm_num)).1 ?_
      nlinarith
    have hy : dist y (WithLp.toLp 2 ((0 : ℝ), q)) < b⁻¹ - b := by linarith
    obtain ⟨x, hx, hxy⟩ := F.coverage_witness y hy
    have hxp : dist x p < 6 := by
      have h1 := F.radial_error x hx
      rw [abs_le] at h1
      have h2 : dist (F.toFun x) (WithLp.toLp 2 ((0 : ℝ), q)) ≤
          dist (F.toFun x) y + dist y (WithLp.toLp 2 ((0 : ℝ), q)) := dist_triangle _ _ _
      rw [dist_comm (F.toFun x) y] at h2
      linarith [h1.1, h1.2]
    refine ⟨x, hxp, ?_, ?_⟩
    · have h1 := WithLp.dist_fst_le y (F.toFun x)
      have h2 : |u₁ - (F.toFun x).fst| ≤ dist u₁ (F.toFun x).fst := by rw [Real.dist_eq]
      simp only [y, WithLp.toLp_fst] at h1
      rw [abs_sub_comm]
      rw [Real.dist_eq] at h1
      linarith
    · have h1 := WithLp.dist_snd_le y (F.toFun x)
      simp only [y, WithLp.toLp_snd] at h1
      have h2 : dist w (F.toFun x).snd < 2 * b := lt_of_le_of_lt h1 hxy
      have hGd := G.distortion _ (mem_ball.mpr (hnear x hxp)) w hw
      have hGd1 : dist (G.toFun (F.toFun x).snd) (G.toFun w) ≤ dist (F.toFun x).snd w + s := by
        rw [abs_le] at hGd
        linarith [hGd.2]
      rw [dist_comm (F.toFun x).snd w] at hGd1
      have h3 : |g x - ((G.toFun w : Icc (0 : ℝ) C) : ℝ)| < 2 * b + s := by
        have := hGd1
        rw [Subtype.dist_eq, Real.dist_eq] at this
        change |g x - ((G.toFun w : Icc (0 : ℝ) C) : ℝ)| ≤ _ at this
        linarith
      have h4 : |u₂ - ((G.toFun w : Icc (0 : ℝ) C) : ℝ)| < 2 * s := by
        have := hwt
        rw [Subtype.dist_eq, Real.dist_eq] at this
        exact this
      have h5 := abs_sub_le (g x) ((G.toFun w : Icc (0 : ℝ) C) : ℝ) u₂
      rw [abs_sub_comm ((G.toFun w : Icc (0 : ℝ) C) : ℝ) u₂] at h5
      linarith
  -- three points of the half plane at mutual distance `6, 5, 5`
  obtain ⟨x₁, hx₁p, hx₁a, hx₁g⟩ := hpt (-3) 0 (by norm_num) le_rfl (by norm_num)
  obtain ⟨x₂, hx₂p, hx₂a, hx₂g⟩ := hpt 3 0 (by norm_num) le_rfl (by norm_num)
  obtain ⟨x₃, hx₃p, hx₃a, hx₃g⟩ := hpt 0 4 (by norm_num) (by norm_num) le_rfl
  have hpair : ∀ (xa xb : X) (ua₁ ua₂ ub₁ ub₂ L : ℝ), dist xa p < 6 → dist xb p < 6 →
      |(F.toFun xa).fst - ua₁| < 2 * b → |g xa - ua₂| < 2 * b + 3 * s →
      |(F.toFun xb).fst - ub₁| < 2 * b → |g xb - ub₂| < 2 * b + 3 * s →
      L ^ 2 = (ua₁ - ub₁) ^ 2 + (ua₂ - ub₂) ^ 2 → 0 ≤ L → |dist xa xb - L| ≤ 9 / 100 := by
    intro xa xb ua₁ ua₂ ub₁ ub₂ L hxa hxb h1 h2 h3 h4 hL hL0
    have hQ := hπ xa xb hxa hxb
    have hsq := abs_sqrt_sub_le_FXC2 ((F.toFun xa).fst - (F.toFun xb).fst) (g xa - g xb)
      (ua₁ - ub₁) (ua₂ - ub₂)
    have hLs : √((ua₁ - ub₁) ^ 2 + (ua₂ - ub₂) ^ 2) = L := by
      rw [← hL, Real.sqrt_sq hL0]
    rw [hLs] at hsq
    have e1 : |((F.toFun xa).fst - (F.toFun xb).fst) - (ua₁ - ub₁)| < 4 * b := by
      have := abs_sub_le ((F.toFun xa).fst - ua₁) 0 ((F.toFun xb).fst - ub₁)
      rw [abs_lt] at h1 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
    have e2 : |(g xa - g xb) - (ua₂ - ub₂)| < 4 * b + 6 * s := by
      rw [abs_lt] at h2 h4 ⊢
      constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]
    have h5 := abs_sub_le (dist xa xb)
      (√(((F.toFun xa).fst - (F.toFun xb).fst) ^ 2 + (g xa - g xb) ^ 2)) L
    linarith
  have h12 : |dist x₁ x₂ - 11 / 2| ≤ 59 / 100 := by
    have h := hpair x₁ x₂ (-3) 0 3 0 6 hx₁p hx₂p hx₁a hx₁g hx₂a hx₂g (by norm_num) (by norm_num)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have h13 : |dist x₁ x₃ - 11 / 2| ≤ 59 / 100 := by
    have h := hpair x₁ x₃ (-3) 0 0 4 5 hx₁p hx₃p hx₁a hx₁g hx₃a hx₃g (by norm_num) (by norm_num)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have h23 : |dist x₂ x₃ - 11 / 2| ≤ 59 / 100 := by
    have h := hpair x₂ x₃ 3 0 0 4 5 hx₂p hx₃p hx₂a hx₂g hx₃a hx₃g (by norm_num) (by norm_num)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have hd : ∀ i j : Fin 3, i ≠ j → |dist (![x₁, x₂, x₃] i) (![x₁, x₂, x₃] j) - 11 / 2| ≤
      59 / 100 := by
    intro i j hij
    have key : ∀ a b : X, |dist a b - 11 / 2| ≤ 59 / 100 → |dist b a - 11 / 2| ≤ 59 / 100 :=
      fun a b h => by rwa [dist_comm]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h12
    · exact h13
    · exact key _ _ h12
    · exact absurd rfl hij
    · exact h23
    · exact key _ _ h13
    · exact key _ _ h23
    · exact absurd rfl hij
  refine not_small_factor_of_three_points_SMR.{w} (p := p) (β := δ) (D := D + 1 / 100)
    (κ := 59 / 100) (s := 11 / 2) ![x₁, x₂, x₃] (fun i => ?_) hd (by linarith) ?_
  · rw [mem_ball]
    fin_cases i
    · exact lt_of_lt_of_le hx₁p (by linarith)
    · exact lt_of_lt_of_le hx₂p (by linarith)
    · exact lt_of_lt_of_le hx₃p (by linarith)
  · refine ⟨Z, mZ, z, ?_, ?_, ⟨f⟩⟩
    · exact Metric.isBounded_iff.mpr ⟨D, fun a _ b _ => hZ a b⟩
    · have : Metric.diam (Set.univ : Set Z) ≤ D :=
        Metric.diam_le_of_forall_dist_le hD0 (fun a _ b _ => hZ a b)
      linarith

end GC.MetricGeometry
