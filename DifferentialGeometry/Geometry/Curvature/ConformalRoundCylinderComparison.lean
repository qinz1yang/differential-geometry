import DifferentialGeometry.Geometry.Curvature.RoundCylinderOperatorPerturbation
import DifferentialGeometry.Geometry.Curvature.BivectorDifferential
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Operator.HessianComposition
import DifferentialGeometry.Geometry.Operator.ParallelPotential
import DifferentialGeometry.Geometry.Operator.Cylinder
import DifferentialGeometry.Analysis.FiniteDimensional.QuadraticNormBound
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

open DifferentialGeometry.SmoothRiemannianMetric
  (metric_inner_cauchy_schwarz_sq)

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem restricted_height_smooth (U : TopologicalSpace.Opens (Cyl (E := E))) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun y : U => (y : Cyl (E := E)).2) :=
  contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U))

private theorem restricted_height_geometry (U : TopologicalSpace.Opens (Cyl (E := E))) (x : U) :
    let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
    let u := fun y : U => (y : Cyl (E := E)).2
    g.inner x (gradFun g u x) (gradFun g u x) = 1 ∧
      ∀ v w : TangentSpace IC x, hessFun g u x v w = 0 := by
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  constructor
  · have h := gradFun_restrictOpen (roundCylinderMetric (E := E) (n := 2))
      U Prod.snd x mdifferentiableAt_snd
    rw [mfderiv_subtype_val_apply] at h
    have haxis := gradFun_height_eq_cylinderAxis gS (x : Cyl (E := E))
    have hgrad : gradFun ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        (fun y : U => (y : Cyl (E := E)).2) x =
        cylinderAxis (I := 𝓡 2) (x : Cyl (E := E)) := h.trans haxis
    change (roundCylinderMetric (E := E) (n := 2)).inner (x : Cyl (E := E)) _ _ = 1
    erw [hgrad]
    exact cylinderMetric_axis_unit gS (x : Cyl (E := E))
  · intro v w
    apply (hessFun_restrictOpen_of_contMDiff (roundCylinderMetric (E := E) (n := 2))
      U Prod.snd contMDiff_snd x v w).trans
    have h := hessFun_comp_height_cylinderMetric gS (f := id) contDiff_id (x : Cyl (E := E))
      (mfderiv IC IC (Subtype.val : U → Cyl (E := E)) x v)
      (mfderiv IC IC (Subtype.val : U → Cyl (E := E)) x w)
    rw [deriv_id', deriv_const] at h
    simpa only [id_eq, roundCylinderMetric, gS, zero_mul] using! h

private theorem old_quadratic_bound
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let v := NormedSpace.normalize (bivectorDifferentialAt u x B)
    ‖v‖ = 1 ∧ ∀ c : E3,
      |⟪(traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v) c, c⟫_ℝ| ≤
        7207 * ε * ‖c‖ ^ 2 := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let u := fun y : U => (y : Cyl (E := E)).2
  let v := NormedSpace.normalize (bivectorDifferentialAt u x B)
  obtain ⟨hv, hclose⟩ := normalize_bivectorDifferentialAt_spec
    g h u x B hB (restricted_height_geometry U x).1 ε hε (hsmall 0 (by norm_num))
  refine ⟨hv, ?_⟩
  intro c
  have hc := abs_traceNormalizedCurvatureOperatorAt_sub_height_sq_le U h x ε hε hsmall B hB c
  have hvq := hclose c
  have he : ⟪(traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v) c, c⟫_ℝ =
      (⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ - (mvfderiv IC u x (bivectorNormalAt x B c)) ^ 2) +
      ((mvfderiv IC u x (bivectorNormalAt x B c)) ^ 2 - ⟪v, c⟫_ℝ ^ 2) := by
    simp only [sub_apply, inner_sub_left, InnerProductSpace.rankOne_apply, real_inner_smul_left]
    ring
  change |⟪(traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v) c, c⟫_ℝ| ≤ _
  rw [he]
  apply (abs_add_le _ _).trans
  change |⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ -
    (mvfderiv IC u x (bivectorNormalAt x B c)) ^ 2| ≤ 7205 * ε * ‖c‖ ^ 2 at hc
  linarith only [hc, hvq]

theorem normalized_height_rankOne_approx_of_roundCylinder_metric_jets
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B) :
    let v := NormedSpace.normalize (bivectorDifferentialAt (fun y : U => (y : Cyl (E := E)).2) x B)
    ‖v‖ = 1 ∧ ‖traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v‖ ≤
      7207 * ε := by
  obtain ⟨hv, hquad⟩ := old_quadratic_bound U h x ε hε hsmall B hB
  refine ⟨hv, ?_⟩
  apply opNorm_le_of_abs_inner_self_le _
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (traceNormalizedCurvatureOperatorAt_isSelfAdjoint h x B)).sub
        (InnerProductSpace.isSymmetric_rankOne_self _)) (7207 * ε) ?_ hquad
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  positivity

private theorem restricted_height_directional_sq_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (c : E3) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let N := bivectorNormalAt x B c
    (mvfderiv IC u x N) ^ 2 ≤ 2 * ‖c‖ ^ 2 := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let u := fun y : U => (y : Cyl (E := E)).2
  let N := bivectorNormalAt x B c
  have hunit : g.inner x (gradFun g u x) (gradFun g u x) = 1 :=
    (restricted_height_geometry U x).1
  have hj : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε :=
    fun k hk => hsmall k (hk.trans (by norm_num))
  have hn : h.inner x N N = ‖c‖ ^ 2 := bivectorNormalAt_inner_self h x B hB c
  have hs : h.inner x (gradFun h u x) (gradFun h u x) ≤ 2 := by
    have hb := inner_gradFun_le_two_of_metricDerivNorm_le_half
      g h u x ((hj 0 (by norm_num)).trans hε)
    simpa only [hunit, mul_one] using hb
  have hb := metric_inner_cauchy_schwarz_sq h x (gradFun h u x) N
  rw [inner_gradFun, hn] at hb
  change (mvfderiv IC u x N) ^ 2 ≤
    h.inner x (gradFun h u x) (gradFun h u x) * ‖c‖ ^ 2 at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hs (sq_nonneg _))

private theorem abs_hessFun_restricted_height_comp_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : E3) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let F := fun y : U => f (u y)
    let N := bivectorNormalAt x B c
    let p := deriv f (u x)
    let d := deriv (deriv f) (u x)
    |hessFun h F x N N| ≤ (2 * |d| + 24 * ε * |p|) * ‖c‖ ^ 2 := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let N := bivectorNormalAt x B c
  let p := deriv f (u x)
  let d := deriv (deriv f) (u x)
  have hu := restricted_height_smooth U
  have hgeo := restricted_height_geometry U x
  have hj : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε :=
    fun k hk => hsmall k (hk.trans (by norm_num))
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hn : h.inner x N N = ‖c‖ ^ 2 := bivectorNormalAt_inner_self h x B hB c
  have ha := restricted_height_directional_sq_le U h x ε hε hsmall B hB c
  change (mvfderiv IC u x N) ^ 2 ≤ 2 * ‖c‖ ^ 2 at ha
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using (hj 0 (by norm_num)).trans hε)
  have hgN : g.inner x N N ≤ 2 * ‖c‖ ^ 2 := by
    simpa only [hn] using
      ((metricUniformEquivalentOn_symm heq).2 x (Set.mem_singleton x) N).2
  have hH : |hessFun h u x N N| ≤ 24 * ε * ‖c‖ ^ 2 := by
    have hb := abs_hessFun_sub_le_of_small_metric_derivatives
      g h u hu x ε hε hj N N
    rw [hgeo.2, sub_zero, hgeo.1, Real.sqrt_one, mul_one, mul_assoc,
      Real.mul_self_sqrt (metric_inner_self_nonneg g x N)] at hb
    exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hgN hε0])
  have he : hessFun h F x N N =
      d * (mvfderiv IC u x N) ^ 2 + p * hessFun h u x N N := by
    rw [hessFun_comp h hf hu]
    dsimp only [p, d]
    ring
  calc
    _ ≤ |d * (mvfderiv IC u x N) ^ 2| + |p * hessFun h u x N N| := by
      rw [he]
      exact abs_add_le _ _
    _ = |d| * (mvfderiv IC u x N) ^ 2 + |p| * |hessFun h u x N N| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (mvfderiv IC u x N))]
    _ ≤ |d| * (2 * ‖c‖ ^ 2) + |p| * (24 * ε * ‖c‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hH (abs_nonneg _))
    _ = _ := by ring

private theorem abs_laplacian_restricted_height_comp_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let F := fun y : U => f (u y)
    let p := deriv f (u x)
    let d := deriv (deriv f) (u x)
    |laplacian (LeviCivita h) h F x| ≤ 2 * |d| + 72 * ε * |p| := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let p := deriv f (u x)
  let d := deriv (deriv f) (u x)
  have hu := restricted_height_smooth U
  have hgeo := restricted_height_geometry U x
  have hj : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε :=
    fun k hk => hsmall k (hk.trans (by norm_num))
  have hb := abs_laplacian_comp_sub_le_of_parallel_unit_gradient
    g h u hu f hf x ε hε hj hgeo.1 hgeo.2
  norm_num only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hb
  change |laplacian (LeviCivita h) h F x - d| ≤
    2 * ε * |d| + 72 * ε * |p| at hb
  have ht : |laplacian (LeviCivita h) h F x| ≤
      |laplacian (LeviCivita h) h F x - d| + |d| := by
    simpa only [sub_add_cancel] using abs_add_le (laplacian (LeviCivita h) h F x - d) d
  have hb' := mul_le_mul_of_nonneg_right hε (abs_nonneg d)
  linarith

private theorem sq_mvfderiv_restricted_height_comp_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : E3) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let F := fun y : U => f (u y)
    let N := bivectorNormalAt x B c
    let p := deriv f (u x)
    (mvfderiv IC F x N) ^ 2 ≤ 2 * p ^ 2 * ‖c‖ ^ 2 := by
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let N := bivectorNormalAt x B c
  let p := deriv f (u x)
  have hu := restricted_height_smooth U
  have ha := restricted_height_directional_sq_le U h x ε hε hsmall B hB c
  change (mvfderiv IC u x N) ^ 2 ≤ 2 * ‖c‖ ^ 2 at ha
  have hdF : mvfderiv IC F x N = p * mvfderiv IC u x N := by
    have hg := gradientFun_comp h ((hf.differentiable (by simp)) (u x))
      (hu.mdifferentiable (by simp) x)
    have hb := congrArg (fun a : TangentSpace IC x => h.inner x a N) hg
    change h.inner x (gradFun h F x) N = h.inner x (p • gradFun h u x) N at hb
    rw [map_smul, smul_apply, smul_eq_mul, inner_gradFun, inner_gradFun] at hb
    exact hb
  change (mvfderiv IC F x N) ^ 2 ≤ 2 * p ^ 2 * ‖c‖ ^ 2
  rw [hdF, mul_pow]
  calc
    _ ≤ p ^ 2 * (2 * ‖c‖ ^ 2) := mul_le_mul_of_nonneg_left ha (sq_nonneg p)
    _ = _ := by ring

private theorem conformal_correction_bound
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : E3) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let F := fun y : U => f (u y)
    let N := bivectorNormalAt x B c
    |hessFun h F x N N - laplacian (LeviCivita h) h F x * ‖c‖ ^ 2 -
      (mvfderiv IC F x N) ^ 2| ≤
      (4 * |deriv (deriv f) (u x)| + 96 * ε * |deriv f (u x)| +
        2 * (deriv f (u x)) ^ 2) * ‖c‖ ^ 2 := by
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let N := bivectorNormalAt x B c
  let p := deriv f (u x)
  let d := deriv (deriv f) (u x)
  have hHC := abs_hessFun_restricted_height_comp_le U h x ε hε hsmall B hB f hf c
  change |hessFun h F x N N| ≤ (2 * |d| + 24 * ε * |p|) * ‖c‖ ^ 2 at hHC
  have hLC := abs_laplacian_restricted_height_comp_le U h x ε hε hsmall f hf
  change |laplacian (LeviCivita h) h F x| ≤ 2 * |d| + 72 * ε * |p| at hLC
  have hD := sq_mvfderiv_restricted_height_comp_le U h x ε hε hsmall B hB f hf c
  change (mvfderiv IC F x N) ^ 2 ≤ 2 * p ^ 2 * ‖c‖ ^ 2 at hD
  rcases abs_le.mp hHC with ⟨hHL, hHU⟩
  rcases abs_le.mp hLC with ⟨hLL, hLU⟩
  have hLLk := mul_le_mul_of_nonneg_right hLL (sq_nonneg ‖c‖)
  have hLUk := mul_le_mul_of_nonneg_right hLU (sq_nonneg ‖c‖)
  change |hessFun h F x N N - laplacian (LeviCivita h) h F x * ‖c‖ ^ 2 - (mvfderiv IC F x N) ^ 2| ≤
    (4 * |d| + 96 * ε * |p| + 2 * p ^ 2) * ‖c‖ ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith only [hHL, hHU, hLLk, hLUk, hD, sq_nonneg (mvfderiv IC F x N)]

theorem norm_conformal_roundCylinder_operator_sub_height_rankOne_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    let u := fun y : U => (y : Cyl (E := E)).2
    let F := fun y : U => f (u y)
    let t := Real.exp (-(2 * f (u x)))
    let p := deriv f (u x)
    let d := deriv (deriv f) (u x)
    let v := NormedSpace.normalize (bivectorDifferentialAt u x B)
    ‖traceNormalizedCurvatureOperatorAt
        (conformalMetricOfContDiff h F (hf.contMDiff.comp
          (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U))))) x
        (conformalBasisAt F x B) - InnerProductSpace.rankOne ℝ v v‖ ≤
      t * 7207 * ε + |t - 1| + 2 * t * (4 * |d| + 96 * ε * |p| + 2 * p ^ 2) := by
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let hF : ContMDiff IC 𝓘(ℝ) ∞ F := hf.contMDiff.comp (restricted_height_smooth U)
  let t := Real.exp (-(2 * f (u x)))
  let p := deriv f (u x)
  let d := deriv (deriv f) (u x)
  let K := 4 * |d| + 96 * ε * |p| + 2 * p ^ 2
  let v := NormedSpace.normalize (bivectorDifferentialAt u x B)
  let A := traceNormalizedCurvatureOperatorAt h x B
  let A' := traceNormalizedCurvatureOperatorAt (conformalMetricOfContDiff h F hF) x (conformalBasisAt F x B)
  let Q := InnerProductSpace.rankOne ℝ v v
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have ht : 0 < t := Real.exp_pos _
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨hv, hOld⟩ := old_quadratic_bound U h x ε hε hsmall B hB
  change ‖v‖ = 1 at hv
  change ‖A' - Q‖ ≤ t * 7207 * ε + |t - 1| + 2 * t * K
  apply opNorm_le_of_abs_inner_self_le _
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (traceNormalizedCurvatureOperatorAt_isSelfAdjoint (conformalMetricOfContDiff h F hF) x
        (conformalBasisAt F x B))).sub (InnerProductSpace.isSymmetric_rankOne_self v))
    (t * 7207 * ε + |t - 1| + 2 * t * K) (by positivity)
  intro c
  let N := bivectorNormalAt x B c
  let R := hessFun h F x N N - laplacian (LeviCivita h) h F x * ‖c‖ ^ 2 -
    (mvfderiv IC F x N) ^ 2
  have hR := conformal_correction_bound U h x ε hε hsmall B hB f hf c
  change |R| ≤ K * ‖c‖ ^ 2 at hR
  have ho := hOld c
  change |⟪(A - Q) c, c⟫_ℝ| ≤ 7207 * ε * ‖c‖ ^ 2 at ho
  have hvc : ⟪v, c⟫_ℝ ^ 2 ≤ ‖c‖ ^ 2 := by
    have hb := abs_real_inner_le_norm v c
    rw [hv, one_mul] at hb
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb
  have hc := traceNormalizedCurvatureOperatorAt_conformal_inner_self h F hF x B hB c
  change ⟪A' c, c⟫_ℝ = t * (⟪A c, c⟫_ℝ + 2 * R) at hc
  have he : ⟪(A' - Q) c, c⟫_ℝ =
      t * ⟪(A - Q) c, c⟫_ℝ + (t - 1) * ⟪v, c⟫_ℝ ^ 2 + 2 * t * R := by
    simp only [sub_apply, inner_sub_left, Q, InnerProductSpace.rankOne_apply, real_inner_smul_left]
    rw [hc]
    ring
  have h1 : |t * ⟪(A - Q) c, c⟫_ℝ| ≤ t * (7207 * ε * ‖c‖ ^ 2) := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left ho ht.le
  have h2 : |(t - 1) * ⟪v, c⟫_ℝ ^ 2| ≤ |t - 1| * ‖c‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ⟪v, c⟫_ℝ)]
    exact mul_le_mul_of_nonneg_left hvc (abs_nonneg _)
  have h3 : |2 * t * R| ≤ 2 * t * (K * ‖c‖ ^ 2) := by
    rw [abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht)]
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  rw [he]
  calc
    _ ≤ |t * ⟪(A - Q) c, c⟫_ℝ + (t - 1) * ⟪v, c⟫_ℝ ^ 2| + |2 * t * R| :=
      abs_add_le _ _
    _ ≤ (|t * ⟪(A - Q) c, c⟫_ℝ| + |(t - 1) * ⟪v, c⟫_ℝ ^ 2|) + |2 * t * R| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (t * (7207 * ε * ‖c‖ ^ 2) + |t - 1| * ‖c‖ ^ 2) + 2 * t * (K * ‖c‖ ^ 2) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end DifferentialGeometry.Geometry.Curvature
