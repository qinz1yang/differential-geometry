import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.AffineHeightDual
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

/-!
# BCG02's differential clause: the axis witness, the minimizing test direction, the slope budget (BCG-7, G3)

Blueprint 207B, BCG02 (`B:8889–8958`): "For `x ∈ D_a`, lift a reference product point in the `A_bᵀ`
direction from `u_a(x)`, keeping the residual coordinate fixed. Use length `400` for a circle, `400Δ`
for an edge, and `10L` for a slim reference. The original coverage and distortion give a witness `y`
and a minimizing initial unit vector `v` from `x` to `y`. … The raw alignment and axis lift make the
quotient close to `1`. … The endpoint distortions divided by their positive separations then give
saturation errors less than `θ²/10⁵` for both covectors."

* `dist_toLp_of_snd_eq_BCG7`, `norm_single_sub_BCG7`, `adjoint_single_BCG7`: `L²`-product distance
  with equal residual coordinates, `‖e₀a − v‖ = |a − v₀|` in `ℝ¹`, and for a unit row `A` (`AA† = id`)
  the vector `A†e₀` is a unit vector with `A(A†e₀) = e₀` (the `A_bᵀ` direction);
* `exists_axis_witness_BCG7`: for a Kleiner–Lott `ε`-approximation `ψ` into `ℝᵐ ×₂ Y` at `p`, a unit
  row `A`, a length `L` and `x ∈ B(p, r)` (`L + r + 1 ≤ ε⁻¹/2`, `ε ≤ 10⁻⁴`): a witness `y` with
  `d(y, p) < L + r + 3ε`, `|d(x, y) − L| ≤ 3ε` and `|A(ψ(y) − ψ(x))₀ − L| < 2ε` (coverage of the lifted
  product point `(ψ₁(x) + L A†e₀, ψ₂(x))`, distortion);
* `exists_test_direction_BCG7`: Hopf–Rinow at the normalized metric (rescaled instance stack of the
  `test` fields): for `x ≠ z` there is a `R⁻²g`-unit `w` whose intrinsic geodesic reaches `z` at time
  `R⁻¹d(x, z)` (`minExp_of_ne_top`);
* `bcg02_differential_of_witness_BCG7`: the slope budget — covectors `f` (`= DU_b`) and `h`
  (`= A_bDη_a`) with norms `≤ 1 + δ₀`, `|f w − Δu/ℓ| ≤ δ₁` (BCG02.b), `|h w − Δa/ℓ| ≤ γ` (adapted test),
  `|Δu − Δa| ≤ 2E` (raw alignment at both endpoints), `|Δa − L| ≤ 2β`, `|ℓ − L| ≤ 3β` (axis lift),
  `ℓ ≥ 1`, `δ₀ + δ₁ + γ + 2E + 5β ≤ θ²/10⁵` ⟹ `‖f − h‖_g < θ` (G1's kernel);
* consumer `exists_axis_witness_raw_BCG7`: the witness together with a raw alignment
  `|u − (Aψ₁)₀| < E` on `B(p, L + r + 1)`: `|(u(y) − u(x)) − A(ψ₁(y) − ψ₁(x))₀| ≤ 2E`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped Manifold ContDiff Topology ENNReal
open GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- In an `L²` product, points with the same second coordinate are at the distance of their first
coordinates. -/
theorem dist_toLp_of_snd_eq_BCG7 {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (a b : WithLp 2 (α × β)) (h : a.snd = b.snd) : dist a b = dist a.fst b.fst := by
  rw [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal), h, dist_self]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, Real.zero_rpow (by norm_num), add_zero, Real.rpow_two, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq dist_nonneg]

/-- In `ℝ¹`: `‖e₀ a − v‖ = |a − v₀|`. -/
theorem norm_single_sub_BCG7 (a : ℝ) (v : EuclideanSpace ℝ (Fin 1)) :
    ‖EuclideanSpace.single 0 a - v‖ = |a - v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  simp

/-- For a unit row `A : ℝᵐ → ℝ¹` (`AA† = id`), `A†e₀` is a unit vector with `A(A†e₀) = e₀`. -/
theorem adjoint_single_BCG7 {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) :
    A (ContinuousLinearMap.adjoint A (EuclideanSpace.single 0 1)) = EuclideanSpace.single 0 1 ∧
      ‖ContinuousLinearMap.adjoint A (EuclideanSpace.single 0 1)‖ = 1 := by
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with he
  have h1 : A (ContinuousLinearMap.adjoint A e) = e := by
    have := congrArg (fun B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) => B e) hA
    simpa using this
  refine ⟨h1, ?_⟩
  have hn : ‖ContinuousLinearMap.adjoint A e‖ ^ 2 = 1 := by
    have he1 : ‖e‖ = 1 := by simp [he]
    rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left, h1,
      real_inner_self_eq_norm_sq, he1, one_pow]
  have h0 := norm_nonneg (ContinuousLinearMap.adjoint A e)
  nlinarith

/-- **The axis witness.** For a Kleiner–Lott `ε`-approximation `ψ` of `(X, p)` into `ℝᵐ ×₂ Y`, a
unit row `A`, `L > 0` and `x ∈ B(p, r)` with `L + r + 1 ≤ ε⁻¹/2`, `ε ≤ 10⁻⁴`: there is `y` with
`d(y, p) < L + r + 3ε`, `|d(x, y) − L| ≤ 3ε` and `|A(ψ₁(y) − ψ₁(x))₀ − L| < 2ε`. -/
theorem exists_axis_witness_BCG7 {X Y : Type*} [MetricSpace X] [MetricSpace Y] {m : ℕ} {p : X}
    {a : Y} {ε : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), a)) ε)
    (hε : ε ≤ 1 / 10000) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) {L r : ℝ}
    (hL : 0 < L) (hLr : L + r + 1 ≤ ε⁻¹ / 2) (x : X) (hx : dist x p < r) :
    ∃ y : X, dist y p < L + r + 3 * ε ∧ |dist x y - L| ≤ 3 * ε ∧
      |A ((ψ.toFun y).fst - (ψ.toFun x).fst) 0 - L| < 2 * ε := by
  have hεpos := ψ.error_pos
  obtain ⟨hAv, hv1⟩ := adjoint_single_BCG7 A hA
  set v₀ := ContinuousLinearMap.adjoint A (EuclideanSpace.single 0 1) with hv₀
  set T : WithLp 2 (EuclideanSpace ℝ (Fin m) × Y) :=
    WithLp.toLp 2 ((ψ.toFun x).fst + L • v₀, (ψ.toFun x).snd) with hT
  have hεi : 10000 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hεpos]
    linarith
  have hxb : x ∈ ball p ε⁻¹ := mem_ball.mpr (by linarith)
  have hTx : dist T (ψ.toFun x) = L := by
    rw [dist_toLp_of_snd_eq_BCG7 T (ψ.toFun x) rfl]
    change dist ((ψ.toFun x).fst + L • v₀) (ψ.toFun x).fst = L
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv1, mul_one, Real.norm_eq_abs,
      abs_of_pos hL]
  have hxq := (abs_le.mp (ψ.radial_error x hxb)).2
  have hTq : dist T (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), a)) < ε⁻¹ - ε := by
    have := dist_triangle T (ψ.toFun x) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), a))
    linarith
  obtain ⟨y, hyb, hTy⟩ := ψ.coverage_witness T hTq
  have hdist := ψ.distortion x hxb y hyb
  have hψ1 := dist_triangle (ψ.toFun x) T (ψ.toFun y)
  have hψ2 := dist_triangle (ψ.toFun x) (ψ.toFun y) T
  rw [dist_comm T (ψ.toFun x)] at hTx
  rw [dist_comm (ψ.toFun y) T] at hψ2
  have hψ3 : |dist x y - L| ≤ 3 * ε := by
    rw [abs_le] at hdist ⊢
    constructor <;> linarith
  refine ⟨y, ?_, hψ3, ?_⟩
  · have h1 := dist_triangle y x p
    rw [dist_comm y x] at h1
    have h2 := (abs_le.mp hψ3).2
    linarith
  · have hsplit : (ψ.toFun y).fst - (ψ.toFun x).fst = L • v₀ + ((ψ.toFun y).fst - T.fst) := by
      change (ψ.toFun y).fst - (ψ.toFun x).fst =
        L • v₀ + ((ψ.toFun y).fst - ((ψ.toFun x).fst + L • v₀))
      abel
    have hAe : A (L • v₀) 0 = L := by
      rw [map_smul, hAv]
      simp
    have herr : |A ((ψ.toFun y).fst - T.fst) 0| < 2 * ε := by
      have h1 : |A ((ψ.toFun y).fst - T.fst) 0| ≤ ‖(ψ.toFun y).fst - T.fst‖ :=
        abs_row_apply_le_BCG7 A ((ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 A hA)) _
      have h2 : ‖(ψ.toFun y).fst - T.fst‖ ≤ dist (ψ.toFun y) T := by
        rw [← dist_eq_norm]
        exact WithLp.dist_fst_le _ _
      rw [dist_comm] at hTy
      linarith
    rw [hsplit, map_add, PiLp.add_apply, hAe, add_sub_cancel_left]
    exact herr

/-- **Consumer: axis witness with raw alignment.** Under the hypotheses of `exists_axis_witness_BCG7`
and a raw alignment `|u(y) − (Aψ₁(y))₀| < E` on `B(p, L + r + 1)`, the witness `y` satisfies
`|(u(y) − u(x)) − A(ψ₁(y) − ψ₁(x))₀| ≤ 2E` besides `|d(x, y) − L| ≤ 3ε`, `|A(ψ₁(y) − ψ₁(x))₀ − L| < 2ε`. -/
theorem exists_axis_witness_raw_BCG7 {X Y : Type*} [MetricSpace X] [MetricSpace Y] {m : ℕ}
    {p : X} {a : Y} {ε : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), a)) ε)
    (hε : ε ≤ 1 / 10000) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) {L r E : ℝ}
    (hL : 0 < L) (hLr : L + r + 1 ≤ ε⁻¹ / 2) (u : X → ℝ)
    (hraw : ∀ y, dist y p < L + r + 1 → |u y - A (ψ.toFun y).fst 0| < E) (x : X)
    (hx : dist x p < r) :
    ∃ y : X, dist y p < L + r + 3 * ε ∧ |dist x y - L| ≤ 3 * ε ∧
      |A ((ψ.toFun y).fst - (ψ.toFun x).fst) 0 - L| < 2 * ε ∧
      |(u y - u x) - A ((ψ.toFun y).fst - (ψ.toFun x).fst) 0| ≤ 2 * E := by
  obtain ⟨y, hy, hxy, hAy⟩ := exists_axis_witness_BCG7 ψ hε A hA hL hLr x hx
  have hεpos := ψ.error_pos
  have h1 := hraw y (by linarith)
  have h2 := hraw x (by have := dist_nonneg (x := x) (y := p); linarith)
  refine ⟨y, hy, hxy, hAy, ?_⟩
  have he : (u y - u x) - A ((ψ.toFun y).fst - (ψ.toFun x).fst) 0 =
      (u y - A (ψ.toFun y).fst 0) - (u x - A (ψ.toFun x).fst 0) := by
    simp only [map_sub, PiLp.sub_apply]
    ring
  rw [he]
  calc _ ≤ |u y - A (ψ.toFun y).fst 0| + |u x - A (ψ.toFun x).fst 0| := abs_sub _ _
    _ ≤ 2 * E := by linarith

section Slopes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The slope budget of BCG02's differential clause** (see the module docstring). -/
theorem bcg02_differential_of_witness_BCG7 (g : SmoothRiemannianMetric I M) (x : M)
    (f h : TangentSpace I x →L[ℝ] ℝ) {θ δ₀ δ₁ γ E β L ℓ Δu Δa : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hβ : 0 ≤ β)
    (hbud : δ₀ + δ₁ + γ + 2 * E + 5 * β ≤ θ ^ 2 / 100000)
    (hf : ∀ u : TangentSpace I x, |f u| ≤ (1 + δ₀) * Real.sqrt (g.inner x u u))
    (hh : ∀ u : TangentSpace I x, |h u| ≤ (1 + δ₀) * Real.sqrt (g.inner x u u))
    (w : TangentSpace I x) (hw : g.inner x w w = 1) (hℓ1 : 1 ≤ ℓ) (hℓ : |ℓ - L| ≤ 3 * β)
    (hfs : |f w - Δu / ℓ| ≤ δ₁) (hhs : |h w - Δa / ℓ| ≤ γ) (hΔ : |Δu - Δa| ≤ 2 * E)
    (ha : |Δa - L| ≤ 2 * β) :
    ∃ θ' < θ, ∀ u : TangentSpace I x, |f u - h u| ≤ θ' * Real.sqrt (g.inner x u u) := by
  have hℓpos : 0 < ℓ := by linarith
  have hℓL := (abs_le.mp hℓ).2
  have haL := (abs_le.mp ha).1
  have hΔl := (abs_le.mp hΔ).1
  have hs₂ : 1 - (5 * β + 2 * E) ≤ Δa / ℓ := by
    rw [le_div_iff₀ hℓpos]
    nlinarith
  have hs₁ : 1 - (5 * β + 2 * E) ≤ Δu / ℓ := by
    rw [le_div_iff₀ hℓpos]
    nlinarith
  exact exists_lt_abs_sub_le_of_slopes_BCG7 g x f h hθ hθ1 h0 h1 hγ (by positivity)
    (by linarith) hf hh w hw hfs hhs hs₁ hs₂

end Slopes

section Direction

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X]

/-- **Minimizing test direction (Hopf–Rinow at the normalized metric).** For `x ≠ z` there is a
`gR`-unit vector `w` (`gR = R⁻²g`, rescaled instance stack as in the `test` fields) with
`intrinsicGeodesic gR x w (d_R(x, z)) = z`, `d_R = R⁻¹d`. -/
theorem exists_test_direction_BCG7 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) (x z : X) (hxz : x ≠ z) :
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 ∧
      intrinsicGeodesic gR hnR x w (dist x z) = z := by
  have hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR := mX.rescale R⁻¹ (inv_pos.mpr hR)
  let _ := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  change ∃ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 ∧
    intrinsicGeodesic gR hnR x w (@dist X mR.toDist x z) = z
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top gR hnR x z (by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3))]
    exact edist_ne_top x z)
  rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), @edist_dist X mR.toPseudoMetricSpace,
    ENNReal.toReal_ofReal (@dist_nonneg X mR.toPseudoMetricSpace x z)] at hlen
  set d := @dist X mR.toDist x z with hd
  have hdpos : 0 < d := (@dist_pos X mR x z).mpr hxz
  have hvv : gR.inner x v v = d ^ 2 := by
    rw [← hlen, Real.sq_sqrt (metric_inner_self_nonneg gR x v)]
  refine ⟨d⁻¹ • v, ?_, ?_⟩
  · have h1 : gR.inner x (d⁻¹ • v) (d⁻¹ • v) = d⁻¹ * (d⁻¹ * gR.inner x v v) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
    rw [h1, hvv]
    field_simp
  · rw [← intrinsicGeodesic_smul gR hnR x (d⁻¹ • v) d, smul_smul, mul_inv_cancel₀ hdpos.ne',
      one_smul]
    exact hv

end Direction

end DifferentialGeometry.Geometry.Collapse
