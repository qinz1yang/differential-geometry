import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalCoordinates
import DifferentialGeometry.Analysis.Calculus.CurveProjection

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_physical_chart_projection_of_small_arcTotalCurvature (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ)
    {p q x₀ C K : ℝ} (hx₀ : x₀ ∈ Icc p q) (hC : 0 < C) (hK : 0 ≤ K) :
    let γ := fun x => c.physicalLift lambda x t
    let G := coverProductMetric (g t) 1 zero_lt_one
    let W := fun x => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ x))
    (∀ x ∈ Icc p q, γ x ∈ (chartAt (ModelProd H ℝ) β).source) →
    (∀ x ∈ Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x),
      Real.sqrt (G.inner (γ x) V V) ≤ C *
        ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
          ℝ (γ x) V)‖) →
    (∀ x ∈ Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ x) V)‖ ≤ C * Real.sqrt (G.inner (γ x) V V)) →
    (∀ x ∈ Icc p q, ∀ u v : E × ℝ,
      ‖A (chartChristoffelContraction G β u v (chartCurve (I := I.prod 𝓘(ℝ, ℝ)) β γ x))‖ ≤
        K * ‖A u‖ * ‖A v‖) →
    C ^ 2 * c.arcTotalCurvature g lambda p q t + K * C * c.arcLength g lambda p q t ≤ 1 / 2 →
    ∃ L : F →L[ℝ] ℝ, ‖L‖ = 1 ∧ ∀ x ∈ Icc p q, ∀ y ∈ Icc p q, x ≤ y →
      c.arcLength g lambda x y t / (2 * C) ≤ L (W y - W x) := by
  dsimp only
  intro hβ hlower hupper hΓ hsmall
  let γ := fun x => c.physicalLift lambda x t
  let V := fun x => c.physicalField lambda (c.unitTangent g lambda) x t
  let W := fun x => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ x))
  let Z := fun x => A (chartRepAtBase β γ V x)
  let T := fun x => NormedSpace.normalize (Z x)
  let v := fun x => c.speed g lambda x t * ‖Z x‖
  have hpq : p ≤ q := hx₀.1.trans hx₀.2
  have hV := c.physical_unitTangent_contMDiff g lambda hlambda hc hi t ht
  have hZ (x : ℝ) (hx : x ∈ Icc p q) : ContDiffAt ℝ 1 Z x :=
    A.contDiff.contDiffAt.comp x (contDiffAt_chartRepAtBase β ((hV x).of_le (by simp)) (hβ x hx))
  have hlow (x : ℝ) (hx : x ∈ Icc p q) : 1 ≤ C * ‖Z x‖ := by
    have h := hlower x hx (V x)
    rw [c.physical_unitTangent_inner_self g lambda hlambda hc hi t ht x,
      Real.sqrt_one] at h
    exact h
  have hZne (x : ℝ) (hx : x ∈ Icc p q) : Z x ≠ 0 := by
    intro hz
    have h := hlow x hx
    rw [hz, norm_zero, mul_zero] at h
    linarith
  have hT (x : ℝ) (hx : x ∈ Icc p q) : ContDiffAt ℝ 1 T x :=
    ((hZ x hx).norm ℝ (hZne x hx)).inv (norm_ne_zero_iff.mpr (hZne x hx)) |>.smul (hZ x hx)
  have hW (x : ℝ) (hx : x ∈ Icc p q) : ContDiffAt ℝ ∞ W x := by
    apply contDiffWithinAt_univ.mp
    exact (c.contDiffWithinAt_physical_chart lambda hc A β x t ht (hβ x hx)).comp
      (f := fun y : ℝ => (y, t)) x (contDiffWithinAt_id.prodMk contDiffWithinAt_const)
      (fun y _ => ⟨mem_univ y, ht⟩)
  have hdW (x : ℝ) (hx : x ∈ Ioo p q) : HasDerivAt W (v x • T x) x := by
    have hs := c.speed_pos_of_immersedOn g lambda hlambda hi x t ht
    have hd := c.physical_chart_arclength_derivative g lambda hlambda hc A β x t ht
      (hβ x (Ioo_subset_Icc_self hx))
    have heq : deriv W x = v x • T x := by
      calc
        deriv W x = c.speed g lambda x t • ((c.speed g lambda x t)⁻¹ • deriv W x) := by
          rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
        _ = c.speed g lambda x t • Z x := congrArg (fun z => c.speed g lambda x t • z) hd
        _ = v x • T x := by rw [show v x = c.speed g lambda x t * ‖Z x‖ from rfl,
          mul_smul, show T x = NormedSpace.normalize (Z x) from rfl, NormedSpace.norm_smul_normalize]
    exact heq ▸ ((hW x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt
  have hsp := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous
  have hvcont : ContinuousOn v (Icc p q) :=
    hsp.continuousOn.mul (fun x hx => (hZ x hx).continuousAt.norm.continuousWithinAt)
  have hvi : IntervalIntegrable v volume p q := hvcont.intervalIntegrable_of_Icc hpq
  have hti : IntervalIntegrable (fun x => ‖deriv T x‖) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    intro x hx
    exact (((hT x hx).derivWithin (m := 0) (by norm_num)).continuousAt.norm).continuousWithinAt
  have hvar : (∫ x in p..q, ‖deriv T x‖) ≤ 1 / 2 :=
    (c.integral_norm_deriv_normalize_physical_unitTangent_le g lambda hlambda hc hi t ht
      A β hpq hC hK hβ hlower hupper hΓ).trans hsmall
  have hunit : ‖T x₀‖ = 1 := NormedSpace.norm_normalize (hZne x₀ hx₀)
  refine ⟨innerSL ℝ (T x₀), by rw [innerSL_apply_norm, hunit], ?_⟩
  intro x hx y hy hxy
  have hproj := mul_integral_le_inner_sub_of_tangent_variation hx₀
    (fun z hz => (hW z hz).continuousAt.continuousWithinAt) hdW
    (fun z _ => mul_nonneg (c.speed_nonneg g lambda z t) (norm_nonneg _)) hvi
    (fun z hz => (hT z hz).continuousAt.continuousWithinAt)
    (fun z hz => ((hT z (Ioo_subset_Icc_self hz)).differentiableAt (by norm_num)).differentiableWithinAt)
    hti hvar hunit hx hy hxy
  have hsub : Icc x y ⊆ Icc p q := Icc_subset_Icc hx.1 hy.2
  have hvi' : IntervalIntegrable v volume x y := by
    apply hvi.mono_set
    rw [uIcc_of_le hxy, uIcc_of_le hpq]
    exact hsub
  have hlen : c.arcLength g lambda x y t ≤ C * (∫ z in x..y, v z) := by
    have h := intervalIntegral.integral_mono_on hxy (hsp.intervalIntegrable x y) (hvi'.const_mul C)
      (fun z hz => by
        have hl := mul_le_mul_of_nonneg_left (hlow z (hsub hz)) (c.speed_nonneg g lambda z t)
        simpa only [mul_one, v, mul_left_comm] using hl)
    exact h.trans_eq (intervalIntegral.integral_const_mul _ _)
  change _ ≤ ⟪T x₀, W y - W x⟫_ℝ
  rw [real_inner_comm]
  apply le_trans ((div_le_iff₀ (by positivity : 0 < 2 * C)).mpr ?_) hproj
  nlinarith only [hlen]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
