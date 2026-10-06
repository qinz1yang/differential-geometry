import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83HingeLinear_O8
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# CH12-O8, package P2: the two-point key estimate (KE) for paired packets

On a complete Riemannian manifold with `sec ≥ -1` on `B(o, 8R)`, let `(a, b)` be a paired
comparison packet of quality `δ` on `W ⊆ B(o, R)` with anchor distances in `[a₀, A₀]`.  For
`x, y ∈ W`, `t = d(x, y) ≤ min 1 (a₀/2)`, unit `V` at `x` toward `y` and unit `U` at `x` toward
`a j` (both minimizing):
`|d(y, a j) - d(x, a j) + t ⟨U, V⟩| ≤ 2 δ t + 3 K t²` (`ke_O8`), `K = 4 cosh(A₀+1)/sinh a₀`.
The proof uses hinge upper bounds only (at `x` for `a j`, `b j`; at `y` for the excess), and the
opposite condition at both endpoints.  Also: `|⟨U_j, U_k⟩| ≤ 2δ` (`cross_abs_le_O8`).
-/

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold Real
open scoped Manifold ContDiff ENNReal InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.LongTime.Ch12

theorem ne_a_of_mem_O8 {M : Type*} [MetricSpace M] {W : Set M} {a b : Fin 3 → M} {a₀ A₀ : ℝ}
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) {z : M} (hz : z ∈ W) (j : Fin 3) : a j ≠ z := by
  intro h
  have := (hbounds z hz j).1.1
  rw [h, dist_self] at this
  linarith

theorem ne_b_of_mem_O8 {M : Type*} [MetricSpace M] {W : Set M} {a b : Fin 3 → M} {a₀ A₀ : ℝ}
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) {z : M} (hz : z ∈ W) (j : Fin 3) : b j ≠ z := by
  intro h
  have := (hbounds z hz j).2.1
  rw [h, dist_self] at this
  linarith

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

/-- Hopf–Rinow, unit form (replica of `exists_unit_geodesic_eq_BCG7`). -/
theorem exists_unit_dir_O8 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (x z : M) (hxz : x ≠ z) :
    ∃ w : TangentSpace I x, g.inner x w w = 1 ∧ intrinsicGeodesic g hEnorm x w (dist x z) = z := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm x z (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x z)
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hlen
  have hdpos : 0 < dist x z := dist_pos.mpr hxz
  have hvv : g.inner x v v = dist x z ^ 2 := by
    rw [← hlen, Real.sq_sqrt (metric_inner_self_nonneg g x v)]
  refine ⟨(dist x z)⁻¹ • v, ?_, ?_⟩
  · have h1 : g.inner x ((dist x z)⁻¹ • v) ((dist x z)⁻¹ • v) =
        (dist x z)⁻¹ * ((dist x z)⁻¹ * g.inner x v v) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
    rw [h1, hvv]
    field_simp
  · rw [← intrinsicGeodesic_smul g hEnorm x ((dist x z)⁻¹ • v) (dist x z), smul_smul,
      mul_inv_cancel₀ hdpos.ne', one_smul]
    exact hv

/-- Short unit geodesics are minimizing. -/
theorem exists_geodesic_dist_eq_small_O8 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (x : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ V : TangentSpace I x, g.inner x V V = 1 → ∀ s : ℝ, 0 ≤ s → s < ρ →
      dist x (intrinsicGeodesic g hEnorm x V s) = s := by
  obtain ⟨ρ, hρ, h⟩ := radial_riemannianEDist_eq_of_small (I := I) g hEnorm x
  refine ⟨ρ, hρ, fun V hV s hs hsρ => ?_⟩
  have h1 := h hV hs hsρ
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul g hEnorm x V s,
    ← IsRiemannianManifold.out (I := I), edist_dist] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hs).mp h1

section Packet

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (o : M)
  {R δ a₀ A₀ : ℝ} {W : Set M} {a b : Fin 3 → M}

/-- `|⟨U, V⟩ + ⟨U', V⟩| ≤ δ` for minimizing unit directions `U` to `a j`, `U'` to `b j`. -/
theorem opp_sum_le_O8
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    {x : M} (hx : x ∈ W) (j : Fin 3) (U U' V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hU' : g.inner x U' U' = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x (a j)) = a j)
    (hUB : intrinsicGeodesic g hEnorm x U' (dist x (b j)) = b j) :
    |g.inner x U V + g.inner x U' V| ≤ δ := by
  have hpi : δ ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hop := packet_opposite_inner_O8 g hEnorm o hpacket hpi x hx j (hWo hx) (hao j) (hbo j)
    (ne_a_of_mem_O8 hbounds ha₀ hx j)
    (ne_b_of_mem_O8 hbounds ha₀ hx j)
    U U' hU hU' hUA hUB hsec
  rw [(fun x v w => (hEnorm.inner_eq x v w).symm)] at hop hU hU' hV
  rw [(fun x v w => (hEnorm.inner_eq x v w).symm), (fun x v w => (hEnorm.inner_eq x v w).symm), ← inner_add_left]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := δ)
  have hsq : ‖U + U'‖ ^ 2 ≤ δ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
    have hc := real_inner_comm U U'
    linarith
  have hn : ‖U + U'‖ ≤ δ := by
    have := norm_nonneg (U + U')
    nlinarith
  have hVn : ‖V‖ = 1 := by
    have h : ‖V‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hV]
    have := norm_nonneg V
    nlinarith
  calc |⟪U + U', V⟫_ℝ| ≤ ‖U + U'‖ * ‖V‖ := abs_real_inner_le_norm _ _
    _ ≤ δ := by rw [hVn, mul_one]; exact hn

/-- `|⟨U_j, U_k⟩| ≤ 2δ` for minimizing unit directions to `a j`, `a k`, `j ≠ k`. -/
theorem cross_abs_le_O8
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    {x : M} (hx : x ∈ W) (j k : Fin 3) (hjk : j ≠ k)
    (Uj Uk : TangentSpace I x) (hUj : g.inner x Uj Uj = 1) (hUk : g.inner x Uk Uk = 1)
    (hUjA : intrinsicGeodesic g hEnorm x Uj (dist x (a j)) = a j)
    (hUkA : intrinsicGeodesic g hEnorm x Uk (dist x (a k)) = a k) :
    |g.inner x Uj Uk| ≤ 2 * δ := by
  have hpi2 : δ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hna := ne_a_of_mem_O8 hbounds ha₀ hx
  have hnb := ne_b_of_mem_O8 hbounds ha₀ hx
  obtain ⟨Uk', hUk', hUkB⟩ := exists_unit_dir_O8 g hEnorm x (b k) (hnb k).symm
  have hc1 := packet_cross_inner_O8 g hEnorm o hpacket hpi2 x hx j k hjk (a j) (a k)
    (by simp) (by simp) (hWo hx) (hao j) (hao k) (hna j) (hna k) Uj Uk hUj hUk hUjA hUkA hsec
  have hc2 := packet_cross_inner_O8 g hEnorm o hpacket hpi2 x hx j k hjk (a j) (b k)
    (by simp) (by simp) (hWo hx) (hao j) (hbo k) (hna j) (hnb k) Uj Uk' hUj hUk' hUjA hUkB hsec
  have hs := opp_sum_le_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hx k Uk Uk' Uj
    hUk hUk' hUj hUkA hUkB
  have hsin := Real.sin_le hδ.le
  rw [g.symm x Uk Uj, g.symm x Uk' Uj] at hs
  have := abs_le.mp hs
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- **Key estimate (KE).** -/
theorem ke_O8
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    {x y : M} (hx : x ∈ W) (hy : y ∈ W) (j : Fin 3)
    (ht1 : dist x y ≤ 1) (hta : dist x y ≤ a₀ / 2)
    (U V : TangentSpace I x) (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x (a j)) = a j)
    (hVy : intrinsicGeodesic g hEnorm x V (dist x y) = y) :
    |dist y (a j) - dist x (a j) + dist x y * g.inner x U V| ≤
      2 * δ * dist x y + 3 * (4 * cosh (A₀ + 1) / sinh a₀) * dist x y ^ 2 := by
  set K := 4 * cosh (A₀ + 1) / sinh a₀ with hK
  have hKpos : 0 ≤ K := div_nonneg (by positivity) (Real.sinh_pos_iff.mpr ha₀).le
  by_cases hyx : y = x
  · subst hyx; simp
  set t := dist x y with ht
  have ht0 : 0 ≤ t := dist_nonneg
  have hna : ∀ {z : M}, z ∈ W → ∀ j, a j ≠ z := fun hz j => ne_a_of_mem_O8 hbounds ha₀ hz j
  have hnb : ∀ {z : M}, z ∈ W → ∀ j, b j ≠ z := fun hz j => ne_b_of_mem_O8 hbounds ha₀ hz j
  obtain ⟨U', hU', hUB⟩ := exists_unit_dir_O8 g hEnorm x (b j) (hnb hx j).symm
  obtain ⟨P, hP, hPA⟩ := exists_unit_dir_O8 g hEnorm y (a j) (hna hy j).symm
  obtain ⟨Q, hQ, hQB⟩ := exists_unit_dir_O8 g hEnorm y (b j) (hnb hy j).symm
  obtain ⟨Wv, hWv, hWx⟩ := exists_unit_dir_O8 g hEnorm y x hyx
  have hyt : dist y x = t := dist_comm y x
  have ht1' : dist y x ≤ 1 := hyt ▸ ht1
  have hta' : dist y x ≤ a₀ / 2 := hyt ▸ hta
  have h1 := hinge_linear_O8 g hEnorm o x (a j) y (hWo hx) (hao j) (hWo hy) (hna hx j) U V hU hV
    hUA hVy hsec ha₀ (hbounds x hx j).1.1 (hbounds x hx j).1.2 ht1 hta
  have h2 := hinge_linear_O8 g hEnorm o x (b j) y (hWo hx) (hbo j) (hWo hy) (hnb hx j) U' V hU'
    hV hUB hVy hsec ha₀ (hbounds x hx j).2.1 (hbounds x hx j).2.2 ht1 hta
  have h3 := hinge_linear_O8 g hEnorm o y (a j) x (hWo hy) (hao j) (hWo hx) (hna hy j) P Wv hP
    hWv hPA hWx hsec ha₀ (hbounds y hy j).1.1 (hbounds y hy j).1.2 ht1' hta'
  have h4 := hinge_linear_O8 g hEnorm o y (b j) x (hWo hy) (hbo j) (hWo hx) (hnb hy j) Q Wv hQ
    hWv hQB hWx hsec ha₀ (hbounds y hy j).2.1 (hbounds y hy j).2.2 ht1' hta'
  rw [hyt] at h3 h4
  have h5 := abs_le.mp (opp_sum_le_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hx j
    U U' V hU hU' hV hUA hUB)
  have h6 := abs_le.mp (opp_sum_le_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hy j
    P Q Wv hP hQ hWv hPA hQB)
  have m5a : t * (g.inner x U V + g.inner x U' V) ≥ -(t * δ) := by nlinarith [h5.1]
  have m6a : t * (g.inner y P Wv + g.inner y Q Wv) ≥ -(t * δ) := by nlinarith [h6.1]
  have hKt : 0 ≤ K * t ^ 2 := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end Packet

end GC.LongTime.Ch12
