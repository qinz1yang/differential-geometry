import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.DirectionTestIntegration
import DifferentialGeometry.Geometry.Metric.Approximation.LongTestValues
import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms
import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# FC16: long tests control coordinate values (Riemannian form)

Blueprint 207B, FC16 (`lem:fibration-adapted-values`, B:1036–1124), for a complete smooth
Riemannian manifold. The metric part is W4-FCa's `norm_coordinate_value_sub_le_of_long_tests`;
this file supplies its Riemannian step `hstep`:

* `axis_lift_slope_lower_bound` (metric): a lift `q` of the axis point `(s eₐ, z₀)` lies at
  distance `s ± 2δ` from `p`, and every point of `B(p, R)` sees it with coordinate slope at least
  `1 - (2R + 4δ)/(s - R - 2δ)`.
* `abs_sub_le_of_direction_saturation` (Riesz): a differential of norm at most `1 + α` that
  takes a value at least `1 - ε` on a unit vector `w` differs from `g(w, ·)` by at most
  `√(4ε + ε²)` in norm.
* `norm_coordinate_value_sub_le_of_long_tests_riemannian`: FC16. The step integrates the
  saturated test along the radial minimizing segment from `p` to `x`
  (`abs_sub_le_of_minimizingDirection_test`, upper first variation only).

Strengthenings: the row's hypothesis `ε ≤ 1` is not needed; the adapted test is assumed
componentwise (implied by the row's vector test); `η` need only be differentiable on
`B(p, R)` (the row assumes `C¹`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

/-- **Axis lifts (metric part of FC16's step).** -/
theorem axis_lift_slope_lower_bound {X Z : Type*} [MetricSpace X] [MetricSpace Z] {k : ℕ}
    (u : X → EuclideanSpace ℝ (Fin k)) (z : X → Z) {p q y : X} {z₀ : Z} {R s T δ : ℝ}
    (a : Fin k) (hδ : 0 ≤ δ) (hs : 2 * R + 4 * δ < s) (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p T, ∀ x' ∈ ball p T,
      |dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u x', z x')) -
        dist x x'| ≤ δ)
    (hpH : p ∈ ball p T) (hqH : q ∈ ball p T) (hyH : y ∈ ball p T) (hy : dist y p < R)
    (hq : dist (WithLp.toLp 2 (u q, z q) : WithLp 2 (_ × Z))
      (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)) ≤ δ) :
    |dist p q - s| ≤ 2 * δ ∧ R < dist y q ∧
      1 - (2 * R + 4 * δ) / (s - R - 2 * δ) ≤ (u q a - u y a) / dist y q := by
  set φ : X → WithLp 2 (EuclideanSpace ℝ (Fin k) × Z) := fun x => WithLp.toLp 2 (u x, z x)
  set tgt : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z) :=
    WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)
  have hR0 : 0 ≤ R := le_trans dist_nonneg hy.le
  have hs0 : 0 ≤ s := by linarith
  have hφp : φ p = WithLp.toLp 2 (0, z₀) := by simp only [φ, hup, hzp]
  have hptgt : dist (φ p) tgt = s := by
    have hiso := (WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin k)) z₀).dist_eq
      0 (s • EuclideanSpace.single a (1 : ℝ))
    have he1 : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1 := by simp
    rw [hφp]
    change dist (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z₀))
      (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)) = s
    rw [hiso, dist_eq_norm, zero_sub, norm_neg, norm_smul, he1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs0]
  have hpq : |dist p q - s| ≤ 2 * δ := by
    have h1 := abs_le.mp (hdist p hpH q hqH)
    have h2 := dist_triangle (φ p) (φ q) tgt
    have h3 := dist_triangle (φ p) tgt (φ q)
    rw [dist_comm tgt (φ q)] at h3
    rw [abs_le]; constructor <;> linarith
  have hyq_low : s - 2 * δ - R < dist y q := by
    have ht := dist_triangle p y q
    rw [dist_comm p y] at ht
    linarith [(abs_le.mp hpq).1]
  have hyq_up : dist y q < s + 2 * δ + R := by
    have ht := dist_triangle y p q
    linarith [(abs_le.mp hpq).2]
  have huy : u y a ≤ R + δ := by
    have h1 := (WithLp.dist_fst_le (φ y) (φ p)).trans
      (by linarith [(abs_le.mp (hdist y hyH p hpH)).2] : dist (φ y) (φ p) ≤ R + δ)
    change dist (u y) (u p) ≤ R + δ at h1
    rw [hup, dist_zero_right] at h1
    have h2 : |u y a| ≤ ‖u y‖ := by
      have h := PiLp.norm_apply_le (u y) a
      rwa [Real.norm_eq_abs] at h
    linarith [(abs_le.mp h2).2]
  have huq : s - δ ≤ u q a := by
    have h1 := (WithLp.dist_fst_le (φ q) tgt).trans hq
    change dist (u q) (s • EuclideanSpace.single a (1 : ℝ)) ≤ δ at h1
    rw [dist_eq_norm] at h1
    have h2 : |(u q - s • EuclideanSpace.single a (1 : ℝ)) a| ≤
        ‖u q - s • EuclideanSpace.single a (1 : ℝ)‖ := by
      have h := PiLp.norm_apply_le (u q - s • EuclideanSpace.single a (1 : ℝ)) a
      rwa [Real.norm_eq_abs] at h
    have h3 : (u q - s • EuclideanSpace.single a (1 : ℝ)) a = u q a - s := by simp
    rw [h3] at h2
    linarith [(abs_le.mp h2).1]
  refine ⟨hpq, by linarith, ?_⟩
  have hD : 0 < dist y q := by linarith
  have hgap : 0 < s - R - 2 * δ := by linarith
  have hnum : s - R - 2 * δ ≤ u q a - u y a := by linarith
  calc 1 - (2 * R + 4 * δ) / (s - R - 2 * δ)
      ≤ 1 - (2 * R + 4 * δ) / (s + R + 2 * δ) := by
        have := div_le_div_of_nonneg_left (by linarith : 0 ≤ 2 * R + 4 * δ) hgap
          (by linarith : s - R - 2 * δ ≤ s + R + 2 * δ)
        linarith
    _ = (s - R - 2 * δ) / (s + R + 2 * δ) := by
        have hpos2 : 0 < s + R + 2 * δ := by linarith
        rw [eq_div_iff hpos2.ne', sub_mul, div_mul_cancel₀ _ hpos2.ne']
        ring
    _ ≤ (s - R - 2 * δ) / dist y q :=
        div_le_div_of_nonneg_left hgap.le hD (by linarith)
    _ ≤ (u q a - u y a) / dist y q := div_le_div_of_nonneg_right hnum hD.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- **Riesz step of FC16.** A differential of `g`-norm at most `1 + α` taking a value at least
`1 - ε` (with `α ≤ ε`) on a `g`-unit vector `w` differs from `g(w, ·)` by at most `√(4ε + ε²)`
in `g`-norm. -/
theorem abs_sub_le_of_direction_saturation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {f : M → ℝ} {x : M} {α ε : ℝ} (hαε : α ≤ ε)
    (hε : 0 ≤ ε)
    (hlip : ∀ X : TangentSpace I x,
      |mvfderiv (I := I) f x X| ≤ (1 + α) * Real.sqrt (g.inner x X X))
    {w : TangentSpace I x} (hw : g.inner x w w = 1)
    (hsat : 1 - ε ≤ mvfderiv (I := I) f x w) (X : TangentSpace I x) :
    |mvfderiv (I := I) f x X - g.inner x w X| ≤
      Real.sqrt (4 * ε + ε ^ 2) * Real.sqrt (g.inner x X X) := by
  set v : TangentSpace I x := gradientFun g f x with hv
  have hnorm (Y : TangentSpace I x) : ‖Y‖ = Real.sqrt (g.inner x Y Y) := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq]
  have hder (Y : TangentSpace I x) : mvfderiv (I := I) f x Y = g.inner x v Y :=
    (inner_gradientFun g f x Y).symm
  have hvn : ‖v‖ ≤ 1 + ε := by
    have h := hlip v
    rw [hder, ← hnorm] at h
    have hvv : g.inner x v v = ‖v‖ ^ 2 := by
      rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq]
    rw [hvv, abs_of_nonneg (sq_nonneg _)] at h
    rcases (norm_nonneg v).eq_or_lt with h0 | hpos
    · rw [← h0]; linarith
    · have : ‖v‖ ≤ 1 + α := by nlinarith
      linarith
  have hwn : ‖w‖ = 1 := by rw [hnorm, hw, Real.sqrt_one]
  have hi : 1 - ε ≤ inner ℝ v w := by rw [hEnorm.inner_eq, ← hder]; exact hsat
  have hR := InnerProductSpace.norm_sub_le_sqrt_of_unit_saturation hε hvn hwn hi
  have hdiff : mvfderiv (I := I) f x X - g.inner x w X = inner ℝ (v - w) X := by
    rw [inner_sub_left, hEnorm.inner_eq, hEnorm.inner_eq, hder]
  rw [hdiff, ← hnorm]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hR (norm_nonneg X))

/-- **FC16 (Riemannian).** On a complete smooth Riemannian manifold, a product approximation
`φ = (u, z)` of distortion `δ` with coverage to `δ` on `B(p, T)` (the row's `H`), and `η : M → ℝᵏ` whose
components are differentiable on `B(p, R)` with differentials of norm at most `1 + α` and pass
the adapted test along EVERY minimizing unit direction of every segment from `B(p, R)` to
`B(p, T)` (the row's `H`) of length greater than `R`, satisfy
`‖η x - η p - u x‖ ≤ √k (R K + 4δ + (R + δ)² / (2(s - (R + δ))))` on `B(p, R)`,
`K = √(4ε + ε²)`, `ε = α + (2R + 4δ)/(s - R - 2δ)`. -/
theorem norm_coordinate_value_sub_le_of_long_tests_riemannian (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {k : ℕ} {Z : Type*} [MetricSpace Z]
    (u : M → EuclideanSpace ℝ (Fin k)) (z : M → Z) (η : M → EuclideanSpace ℝ (Fin k))
    {p : M} {z₀ : Z} {R s T δ α : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (hs : 2 * R + 4 * δ < s) (hH : s + R + 3 * δ < T) (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p T, ∀ y ∈ ball p T,
      |dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) -
        dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < T - δ →
        ∃ y ∈ ball p T, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hη : ∀ a : Fin k, ∀ x ∈ ball p R, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => η y a) x)
    (hlip : ∀ a : Fin k, ∀ x ∈ ball p R, ∀ X : TangentSpace I x,
      |mvfderiv (I := I) (fun y => η y a) x X| ≤ (1 + α) * Real.sqrt (g.inner x X X))
    (htest : ∀ a : Fin k, ∀ x ∈ ball p R, ∀ y ∈ ball p T, R < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) (fun y' => η y' a) x w - (u y a - u x a) / dist x y| ≤ α) :
    ∀ x ∈ ball p R, ‖η x - η p - u x‖ ≤
      Real.sqrt k * (R * Real.sqrt (4 * (α + (2 * R + 4 * δ) / (s - R - 2 * δ)) +
          (α + (2 * R + 4 * δ) / (s - R - 2 * δ)) ^ 2) +
        4 * δ + (R + δ) ^ 2 / (2 * (s - (R + δ)))) := by
  set ε : ℝ := α + (2 * R + 4 * δ) / (s - R - 2 * δ) with hεdef
  set K : ℝ := Real.sqrt (4 * ε + ε ^ 2) with hKdef
  have hgap : 0 < s - R - 2 * δ := by linarith
  have hε : 0 ≤ ε := by
    have : 0 ≤ (2 * R + 4 * δ) / (s - R - 2 * δ) := div_nonneg (by linarith) hgap.le
    linarith
  have hαε : α ≤ ε := by
    have : 0 ≤ (2 * R + 4 * δ) / (s - R - 2 * δ) := div_nonneg (by linarith) hgap.le
    linarith
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hpH : p ∈ ball p T := mem_ball_self (by linarith)
  have hRH : ball p R ⊆ ball p T := ball_subset_ball (by linarith)
  have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  refine norm_coordinate_value_sub_le_of_long_tests u z η hR hδ hs hH hup hzp hdist hcover ?_
  intro a q hqH hq x hx
  rcases eq_or_ne x p with rfl | hxp
  · have h0 : η x a - η x a - dist x q + dist x q = 0 := by ring
    rw [h0, abs_zero]
    exact mul_nonneg hR.le hK
  have hxp' : 0 < dist p x := dist_pos.mpr hxp.symm
  obtain ⟨v, hv, hvx⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm p x
    (by rw [hd]; exact hxp')
  rw [hd] at hvx
  set γ : ℝ → M := intrinsicGeodesic g hEnorm p v with hγ
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero g hEnorm p v
  have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm p v
  have hγball (t : ℝ) (ht : t ∈ Icc 0 (dist p x)) : γ t ∈ ball p R := by
    have hl := (lipschitzWith_one_intrinsicGeodesic g hEnorm p v hv).dist_le_mul t 0
    rw [← hγ, hγ0, NNReal.coe_one, one_mul, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hl
    have hxR : dist x p < R := hx
    rw [dist_comm] at hxR
    exact mem_ball.mpr (by linarith [ht.2])
  have hslope (t : ℝ) (ht : t ∈ Icc 0 (dist p x)) := axis_lift_slope_lower_bound u z a hδ hs
    hup hzp hdist hpH hqH (hRH (hγball t ht)) (hγball t ht) hq
  have hkernel := abs_sub_le_of_minimizingDirection_test g hEnorm (q := q)
    (η := fun y => η y a) (c := γ) (K := K) dist_nonneg
    (fun t _ => hγsmooth.contMDiffAt.mdifferentiableAt (by simp))
    (fun t ht => hη a (γ t) (hγball t ht))
    (fun t _ => by rw [hγ, intrinsicGeodesic_speedSq_eq, hv])
    (fun t ht hqt => by
      have h := (hslope t ht).2.1
      rw [hqt, dist_self] at h
      linarith)
    (fun t ht w hw X => by
      have hqt : R < dist (γ t) q := (hslope t ht).2.1
      have hwq : intrinsicGeodesic g hEnorm (γ t) w (dist (γ t) q) = q := by
        have h2 := hw.2
        simp only [Metric.infDist_singleton, mem_singleton_iff] at h2
        exact h2
      have htw := abs_le.mp (htest a (γ t) (hγball t ht) q hqH hqt w hw.1 hwq)
      have hsat : 1 - ε ≤ mvfderiv (I := I) (fun y => η y a) (γ t) w := by
        have := (hslope t ht).2.2
        rw [hεdef]
        linarith [htw.1]
      exact abs_sub_le_of_direction_saturation g hEnorm hαε hε
        (hlip a (γ t) (hγball t ht)) hw.1 hsat X)
  rw [hγ0, hvx, sub_zero] at hkernel
  have hxR : dist p x ≤ R := by rw [dist_comm]; exact (mem_ball.mp hx).le
  have hbound : K * dist p x ≤ R * K := by nlinarith
  calc |η x a - η p a - dist p q + dist x q|
      = |(η x a + dist x q) - (η p a + dist p q)| := by ring_nf
    _ ≤ K * dist p x := hkernel
    _ ≤ R * K := hbound

end DifferentialGeometry.Geometry.Collapse
