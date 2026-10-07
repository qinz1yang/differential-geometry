import DifferentialGeometry.Geometry.Comparison.Toponogov.BufferedRiemannianHinge
import DifferentialGeometry.Geometry.Comparison.ModelAngleFiniteDifference
import DifferentialGeometry.Geometry.Comparison.PairedPacket

/-!
# CH12-O8, package P1: linear Riemannian hinge bound and packet inner products

On a complete Riemannian manifold with `sec ≥ -1` on `B(o, 8R)`:
* `hinge_linear_O8`: for unit `U` toward `A` (minimizing) and unit `V` toward `y` (minimizing),
  `d(y, A) ≤ d(x, A) - t ⟨U, V⟩ + K t²`, `t = d(x, y)`, `K = 4 cosh(A₀+1)/sinh a₀`, when
  `a₀ ≤ d(x, A) ≤ A₀`, `t ≤ 1`, `t ≤ a₀/2`.
* `packet_opposite_inner_O8`, `packet_cross_inner_O8`: a paired comparison packet of quality `δ`
  at `x` forces `⟨U_a, U_b⟩ < -cos δ` and `⟨U_u, U_v⟩ < sin δ` for ALL minimizing unit directions.
-/

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold Real
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.LongTime.Ch12

theorem cos_comparisonAngle_one_eq_O8 {X : Type*} [MetricSpace X] (x A y : X)
    (hA : A ≠ x) (hy : y ≠ x) :
    Real.cos (comparisonAngleNegCurvature 1 (dist x A) (dist x y) (dist A y)) =
      hyperbolicComparisonCosine 1 (dist x A) (dist x y) (dist A y) := by
  have hlow : |dist x A - dist x y| ≤ dist A y := by
    rw [dist_comm x A, dist_comm x y]; exact abs_dist_sub_le A y x
  have hup : dist A y ≤ dist x A + dist x y := by
    rw [dist_comm x A]; exact dist_triangle A x y
  rw [cos_comparisonAngleNegCurvature_of_pos one_pos (dist_pos.mpr hA.symm)
    (dist_pos.mpr hy.symm) hlow hup]
  simp only [hyperbolicComparisonCosine, Real.sqrt_one, one_mul]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Inner product of minimizing unit directions is at most the cosine of the comparison angle
(curvature `-1`). -/
theorem inner_le_cos_comparisonAngle_O8
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A B : M) {R : ℝ}
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R) (hB : B ∈ Metric.ball o R)
    (hAx : A ≠ x) (hBx : B ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hVB : intrinsicGeodesic g hEnorm x V (dist x B) = B)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2)) :
    g.inner x U V ≤ Real.cos (comparisonAngleNegCurvature 1 (dist x A) (dist x B) (dist A B)) := by
  rw [cos_comparisonAngle_one_eq_O8 x A B hAx hBx]
  exact inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x A B one_pos hx hA hB hAx hBx U V hU hV hUA hVB hsec

/-- **Linear hinge bound.** -/
theorem hinge_linear_O8
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A y : M) {R a₀ A₀ : ℝ}
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R) (hy : y ∈ Metric.ball o R)
    (hAx : A ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hVy : intrinsicGeodesic g hEnorm x V (dist x y) = y)
    (hsec : ∀ z ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g z (-(1 : ℝ) ^ 2))
    (ha₀ : 0 < a₀) (har : a₀ ≤ dist x A) (hrA : dist x A ≤ A₀)
    (ht1 : dist x y ≤ 1) (hta : dist x y ≤ a₀ / 2) :
    dist y A ≤ dist x A - dist x y * g.inner x U V +
      (4 * cosh (A₀ + 1) / sinh a₀) * dist x y ^ 2 := by
  by_cases hyx : y = x
  · subst hyx; simp
  have hin := inner_le_cos_comparisonAngle_O8 g hEnorm o x A y hx hA hy hAx hyx U V hU hV hUA
    hVy hsec
  have hfd := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le x y A ha₀ har hrA
    (dist_pos.mpr (Ne.symm hyx)) ht1 hta
  rw [dist_comm y A] at hfd
  have h1 := (abs_le.mp hfd).2
  have ht0 : 0 ≤ dist x y := dist_nonneg
  have h2 : dist x y * g.inner x U V ≤
      dist x y * Real.cos (comparisonAngleNegCurvature 1 (dist x A) (dist x y) (dist A y)) :=
    mul_le_mul_of_nonneg_left hin ht0
  rw [dist_comm y A]
  linarith

section Packet

variable {ι : Type*}

theorem packet_opposite_inner_O8
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) {R δ : ℝ} {W : Set M} {a b : ι → M}
    (hpacket : PairedComparisonPacket δ W a b) (hδ : δ ≤ Real.pi)
    (x : M) (hxW : x ∈ W) (i : ι)
    (hx : x ∈ Metric.ball o R) (hA : a i ∈ Metric.ball o R) (hB : b i ∈ Metric.ball o R)
    (hAx : a i ≠ x) (hBx : b i ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x (a i)) = a i)
    (hVB : intrinsicGeodesic g hEnorm x V (dist x (b i)) = b i)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2)) :
    g.inner x U V < -Real.cos δ := by
  have hin := inner_le_cos_comparisonAngle_O8 g hEnorm o x (a i) (b i) hx hA hB hAx hBx U V hU hV
    hUA hVB hsec
  have hop := hpacket.opposite x hxW i
  have hmem := comparisonAngleNegCurvature_mem_Icc 1 (dist x (a i)) (dist x (b i))
    (dist (a i) (b i))
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hmem.2 hop
  rw [Real.cos_pi_sub] at hc
  linarith

theorem packet_cross_inner_O8
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) {R δ : ℝ} {W : Set M} {a b : ι → M}
    (hpacket : PairedComparisonPacket δ W a b) (hδ : δ ≤ Real.pi / 2)
    (x : M) (hxW : x ∈ W) (i j : ι) (hij : i ≠ j)
    (u v : M) (hu : u ∈ ({a i, b i} : Set M)) (hv : v ∈ ({a j, b j} : Set M))
    (hx : x ∈ Metric.ball o R) (hA : u ∈ Metric.ball o R) (hB : v ∈ Metric.ball o R)
    (hAx : u ≠ x) (hBx : v ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x u) = u)
    (hVB : intrinsicGeodesic g hEnorm x V (dist x v) = v)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2)) :
    g.inner x U V < Real.sin δ := by
  have hin := inner_le_cos_comparisonAngle_O8 g hEnorm o x u v hx hA hB hAx hBx U V hU hV
    hUA hVB hsec
  have hcr := hpacket.cross x hxW i j hij u hu v hv
  have hmem := comparisonAngleNegCurvature_mem_Icc 1 (dist x u) (dist x v) (dist u v)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hmem.2 hcr
  rw [Real.cos_pi_div_two_sub] at hc
  linarith

end Packet

end GC.LongTime.Ch12
