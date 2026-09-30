import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.AffineBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.NormEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound

open DifferentialGeometry.Analysis.Parabolic (scalar_subsolution_affine_bound)

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [T2Space M]

def NablaRm04NormHeatBoundOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (nablaRmNormSq nablaRmNormLap rmNormSq : Real -> M -> Real) (cReact : Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    ∃ d : Real,
      HasDerivWithinAt
        (fun s : Real => nablaRmNormSq s x)
        d
        D.carrier
        (t : Real) ∧
      d <= nablaRmNormLap (t : Real) x +
        cReact * Real.sqrt (rmNormSq (t : Real) x) * nablaRmNormSq (t : Real) x

def bernsteinConstant (cReact alpha : Real) : Real :=
  (1 + cReact * alpha) * (1 + 16 * alpha)

omit [CompleteSpace E] [T2Space M] in
theorem bernstein_first_derivative_estimate
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T)
    (u v uLap vLap reaction : Real -> M -> Real)
    (cReact K alpha : Real)
    (hcReact : 0 <= cReact) (hK : 0 < K) (halpha : 0 <= alpha)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hu_nonneg : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= u t x)
    (hv_nonneg : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= v t x)
    (hv_bound : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, v t x <= K ^ 2)
    (hTK : T <= alpha / K)
    (hu_heat : NablaRm04NormHeatBoundOn (D := D) u uLap v cReact)
    (hv_heat : Rm04NormHeatEquationOn (D := D) v vLap u reaction)
    (hreaction : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      |reaction t x| <= 16 * (v t x) ^ ((3 : Real) / 2))
    (huLap : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (u t) x = uLap t x)
    (hvLap : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (v t) x = vLap t x)
    (hu_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hv_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (v t) y) x)
    (hF_cont : ContinuousOn
      (fun p : Real × M =>
        ((1 + cReact * alpha) * K ^ 2 + ((1 + cReact * alpha) * (16 * K ^ 3)) * p.1) -
          (p.1 * u p.1 p.2 + (1 + cReact * alpha) * v p.1 p.2))
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T))
    (hF_time : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentiableWithinAt Real
        (fun s : Real => s * u s x + (1 + cReact * alpha) * v s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => t * u t z + (1 + cReact * alpha) * v t z) y)
    (hF_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t)
          (fun z : M => t * u t z + (1 + cReact * alpha) * v t z) y) x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      u t x <= bernsteinConstant cReact alpha * K ^ 2 / t := by
  classical
  set β : Real := 1 + cReact * alpha with hβdef
  have hβ_pos : 0 < β := by
    have : 0 <= cReact * alpha := mul_nonneg hcReact halpha
    simp only [hβdef]; linarith
  let F : Real -> M -> Real := fun s y => s * u s y + β * v s y
  let X : Real -> (x : M) -> TangentSpace I x := fun _t x => (0 : TangentSpace I x)
  set a : Real := β * K ^ 2 with hadef
  set b : Real := β * (16 * K ^ 3) with hbdef
  have hK2 : (0 : Real) <= K ^ 2 := by positivity
  have hsqrt_v_le : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      Real.sqrt (v t x) <= K := by
    intro t ht x
    have hle : v t x <= K ^ 2 := hv_bound t ht x
    have : Real.sqrt (v t x) <= Real.sqrt (K ^ 2) :=
      Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (le_of_lt hK)] at this
  have ht_sqrt_v_le : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      t * Real.sqrt (v t x) <= alpha := by
    intro t ht x
    have htK : t * K <= alpha := by
      have htle : t <= alpha / K := le_trans ht.2 hTK
      calc t * K <= (alpha / K) * K := by
              exact mul_le_mul_of_nonneg_right htle (le_of_lt hK)
        _ = alpha := by field_simp
    calc t * Real.sqrt (v t x) <= t * K :=
          mul_le_mul_of_nonneg_left (hsqrt_v_le t ht x) ht.1
      _ <= alpha := htK
  have hsub : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X F t x <=
        b := by
    intro t ht htpos x
    let τ : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
      ⟨t, hregular t ht htpos⟩
    obtain ⟨du, hdu_deriv, hdu_le⟩ := hu_heat τ x
    have hdv_deriv :
        HasDerivWithinAt (fun s : Real => v s x)
          (vLap t x + (-2 * u t x + reaction t x)) D.carrier (t : Real) :=
      hv_heat τ x
    have hdu_slab :
        HasDerivWithinAt (fun s : Real => u s x) du (Set.Icc 0 T) t := by
      simpa [τ] using hdu_deriv.mono hslab
    have hdv_slab :
        HasDerivWithinAt (fun s : Real => v s x)
          (vLap t x + (-2 * u t x + reaction t x)) (Set.Icc 0 T) t := by
      simpa [τ] using hdv_deriv.mono hslab
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    have hFtime :
        HasDerivWithinAt (fun s : Real => F s x)
          ((u t x + t * du) + β * (vLap t x + (-2 * u t x + reaction t x)))
          (Set.Icc 0 T) t := by
      have hprod :
          HasDerivWithinAt (fun s : Real => s * u s x)
            (u t x + t * du) (Set.Icc 0 T) t := by
        have hid : HasDerivWithinAt (fun s : Real => s) 1 (Set.Icc 0 T) t :=
          hasDerivWithinAt_id t (Set.Icc 0 T)
        have hmul := hid.mul hdu_slab
        have hfun : (fun s : Real => s * u s x) =
            (fun s : Real => s) * fun s : Real => u s x := by
          rfl
        rw [hfun, show u t x + t * du = 1 * u t x + t * du by ring]
        exact hmul
      have hscaled :
          HasDerivWithinAt (fun s : Real => β * v s x)
            (β * (vLap t x + (-2 * u t x + reaction t x))) (Set.Icc 0 T) t :=
        hdv_slab.const_mul β
      exact hprod.add hscaled
    have hderivWithin :
        derivWithin (fun s : Real => F s x) (Set.Icc 0 T) t =
          (u t x + t * du) + β * (vLap t x + (-2 * u t x + reaction t x)) :=
      hFtime.derivWithin huniq
    have hheatF :
        DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
            (fun _y : M => (0 : TangentSpace I _y)) (F t) x =
          t * uLap t x + β * vLap t x := by
      have hcombo :
          DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
              (fun _y : M => (0 : TangentSpace I _y))
              (fun z : M => t * u t z + β * v t z) x =
            t * DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
                (fun _y : M => (0 : TangentSpace I _y)) (u t) x +
              β * DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
                (fun _y : M => (0 : TangentSpace I _y)) (v t) x :=
        by
          simp only [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
          have htu := mdifferentiableAt_gradientFun_const_mul (G.metric t) t
            (Filter.Eventually.of_forall (hu_space t ht htpos)) (hu_grad t ht htpos x)
          have hβv := mdifferentiableAt_gradientFun_const_mul (G.metric t) β
            (Filter.Eventually.of_forall (hv_space t ht htpos)) (hv_grad t ht htpos x)
          calc
            _ = laplacianAt G t (t • u t) x + laplacianAt G t (β • v t) x :=
              laplacianAt_add G t
                (fun z => (hu_space t ht htpos z).const_smul t)
                (fun z => (hv_space t ht htpos z).const_smul β) htu hβv
            _ = _ := by
              rw [laplacianAt_smul G t t (hu_space t ht htpos) (hu_grad t ht htpos x),
                laplacianAt_smul G t β (hv_space t ht htpos) (hv_grad t ht htpos x)]
      have hFt : F t = (fun z : M => t * u t z + β * v t z) := rfl
      rw [hFt, hcombo, huLap t ht htpos x, hvLap t ht htpos x]
    have hParab :
        DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X F t x =
          u t x + (t * (du - uLap t x) + β * (-2 * u t x + reaction t x)) := by
      have hXt : X t = (fun _y : M => (0 : TangentSpace I _y)) := rfl
      rw [DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift_eq, hderivWithin, hXt,
        hheatF]
      ring
    rw [hParab]
    have hdu_diff : du - uLap t x <= cReact * Real.sqrt (v t x) * u t x := by
      have := hdu_le
      simp only [τ] at this
      linarith
    have hu_nn : 0 <= u t x := hu_nonneg t ht x
    have hv_nn : 0 <= v t x := hv_nonneg t ht x
    have hterm_u :
        t * (du - uLap t x) <= (cReact * alpha) * u t x := by
      have h1 : t * (du - uLap t x) <= t * (cReact * Real.sqrt (v t x) * u t x) :=
        mul_le_mul_of_nonneg_left hdu_diff ht.1
      have h2 : t * (cReact * Real.sqrt (v t x) * u t x)
          = cReact * (t * Real.sqrt (v t x)) * u t x := by ring
      have h3 : cReact * (t * Real.sqrt (v t x)) * u t x
          <= cReact * alpha * u t x := by
        have hca : cReact * (t * Real.sqrt (v t x)) <= cReact * alpha :=
          mul_le_mul_of_nonneg_left (ht_sqrt_v_le t ht x) hcReact
        exact mul_le_mul_of_nonneg_right hca hu_nn
      linarith [h1, h2.le, h2.ge, h3]
    have hreact_le : reaction t x <= 16 * K ^ 3 := by
      have habs : |reaction t x| <= 16 * (v t x) ^ ((3 : Real) / 2) := hreaction t ht x
      have hle1 : reaction t x <= 16 * (v t x) ^ ((3 : Real) / 2) :=
        le_trans (le_abs_self _) habs
      have hpow : (v t x) ^ ((3 : Real) / 2) <= K ^ 3 := by
        have hvle : v t x <= K ^ 2 := hv_bound t ht x
        have hbase : (v t x) ^ ((3 : Real) / 2) <= (K ^ 2) ^ ((3 : Real) / 2) :=
          Real.rpow_le_rpow hv_nn hvle (by norm_num)
        have hKpow : (K ^ 2 : Real) ^ ((3 : Real) / 2) = K ^ 3 := by
          rw [← Real.rpow_natCast K 2, ← Real.rpow_mul (le_of_lt hK),
            ← Real.rpow_natCast K 3]
          norm_num
        rw [hKpow] at hbase
        exact hbase
      calc reaction t x <= 16 * (v t x) ^ ((3 : Real) / 2) := hle1
        _ <= 16 * K ^ 3 := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hβ_react' : β * reaction t x <= β * (16 * K ^ 3) :=
      mul_le_mul_of_nonneg_left hreact_le (le_of_lt hβ_pos)
    have hu_cancel :
        u t x + (cReact * alpha) * u t x + β * (-2 * u t x) <= 0 := by
      have heq : u t x + (cReact * alpha) * u t x + β * (-2 * u t x)
          = -(1 + cReact * alpha) * u t x := by
        simp only [hβdef]; ring
      rw [heq]
      have hcoef : 0 <= (1 + cReact * alpha) := by
        have : 0 <= cReact * alpha := mul_nonneg hcReact halpha
        linarith
      have hmul : 0 <= (1 + cReact * alpha) * u t x := mul_nonneg hcoef hu_nn
      linarith
    rw [hbdef]
    calc u t x + (t * (du - uLap t x) + β * (-2 * u t x + reaction t x))
        <= u t x + ((cReact * alpha) * u t x + β * (-2 * u t x + reaction t x)) := by
            linarith [hterm_u]
      _ = (u t x + (cReact * alpha) * u t x + β * (-2 * u t x)) + β * reaction t x := by
            ring
      _ <= 0 + β * (16 * K ^ 3) := by
            linarith [hβ_react', hu_cancel]
      _ = β * (16 * K ^ 3) := by ring
  have hinitF : ∀ x : M, F 0 x <= a := by
    intro x
    have h0mem : (0 : Real) ∈ Set.Icc 0 T := ⟨le_rfl, le_of_lt hT⟩
    have hv0 : v 0 x <= K ^ 2 := hv_bound 0 h0mem x
    change (0 : Real) * u 0 x + β * v 0 x <= a
    rw [hadef]
    have hbv : β * v 0 x <= β * K ^ 2 :=
      mul_le_mul_of_nonneg_left hv0 (le_of_lt hβ_pos)
    simp only [zero_mul, zero_add]
    exact hbv
  have hPartA :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, F t x <= a + b * t := by
    apply scalar_subsolution_affine_bound (I := I) G T X F a b
    · simpa only [hadef, hbdef, F] using hF_cont
    · intro t ht htpos x; simpa only [F] using hF_time t ht htpos x
    · intro t ht htpos y; simpa only [F] using hF_space t ht htpos y
    · intro t ht htpos x; simpa only [F] using hF_grad t ht htpos x
    · exact hinitF
    · exact hsub
  intro t ht htpos x
  have hFle : F t x <= a + b * t := hPartA t ht x
  have hv_nn : 0 <= v t x := hv_nonneg t ht x
  have htu_le : t * u t x <= a + b * t := by
    have hβv : 0 <= β * v t x := mul_nonneg (le_of_lt hβ_pos) hv_nn
    have : t * u t x + β * v t x <= a + b * t := hFle
    linarith
  have hbt_le : a + b * t <= bernsteinConstant cReact alpha * K ^ 2 := by
    rw [hadef, hbdef, bernsteinConstant, hβdef]
    have htK : t * K <= alpha := by
      have htle : t <= alpha / K := le_trans ht.2 hTK
      calc t * K <= (alpha / K) * K := mul_le_mul_of_nonneg_right htle (le_of_lt hK)
        _ = alpha := by field_simp
    have hβpos' : 0 < (1 + cReact * alpha) := hβ_pos
    have hexpand : (1 + cReact * alpha) * (1 + 16 * alpha) * K ^ 2
        = (1 + cReact * alpha) * K ^ 2 + (1 + cReact * alpha) * (16 * K ^ 2 * alpha) := by
      ring
    rw [hexpand]
    have hKt : 16 * K ^ 3 * t <= 16 * K ^ 2 * alpha := by
      have hKt' : K * t <= alpha := by rw [mul_comm]; exact htK
      have hstep : K ^ 2 * (K * t) <= K ^ 2 * alpha :=
        mul_le_mul_of_nonneg_left hKt' hK2
      nlinarith [hstep]
    have hfactor : (1 + cReact * alpha) * (16 * K ^ 3) * t
        <= (1 + cReact * alpha) * (16 * K ^ 2 * alpha) := by
      have : (1 + cReact * alpha) * (16 * K ^ 3) * t
          = (1 + cReact * alpha) * (16 * K ^ 3 * t) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hKt (le_of_lt hβpos')
    linarith [hfactor]
  have htu_le' : t * u t x <= bernsteinConstant cReact alpha * K ^ 2 :=
    le_trans htu_le hbt_le
  rw [le_div_iff₀ htpos]
  calc u t x * t = t * u t x := by ring
    _ <= bernsteinConstant cReact alpha * K ^ 2 := htu_le'

end DifferentialGeometry.PDE.RicciFlow
