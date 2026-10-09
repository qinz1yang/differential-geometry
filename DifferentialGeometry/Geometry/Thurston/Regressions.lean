import DifferentialGeometry.Geometry.Thurston.Descent
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness
import DifferentialGeometry.Geometry.Thurston.ModelAtlas.LocalPullback
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# M1d regression tests for the common geometry layer

API tests of blueprint chapter 7 (M1d acceptance tests and the unsigned-chart audit), not
applications of geometrization.

* `torusThreeGeometry`: the flat torus `T³ = E³ / ℤ³` (`TorusLattice` acting by integer
  translations, `TorusThree` compact) carries a `.euclidean` `GeometricStructure`, obtained by
  `GeometricStructure.quotientOfCompact`.
* Incomplete metrics are rejected for every tag. `HasThurstonAtlas.restrictOpen` keeps the model
  atlas on an open subset, `not_complete_restrictOpen_of_ray` shows that a ray of finite length
  leaving through a missing point makes the restriction incomplete, and
  `not_exists_geometricStructure_of_not_complete` turns this into the absence of a
  `GeometricStructure`. Each model minus one point keeps its atlas but is not complete:
  `euclideanModel_puncture_rejected` and `coordinateModel_puncture_rejected` (the five
  coordinate models) on `E³ \ {0}`, `sphericalProduct_puncture_rejected` on `S² × ℝ` and
  `sphericalModel_puncture_rejected` on `S³`.
* `coordinateHyperbolic_volume_eq_top`: the coordinate model of `H³` has infinite volume (it
  dominates the Euclidean volume on the half-space `z ≤ 0`), so it is not a `.hyperbolic`
  `GeometricStructure` (`no_geometricStructure_coordinateHyperbolic`).
* `nilReflectedGeometry`: the Nil model metric pulled back by the orientation-reversing linear
  diffeomorphism `nilReflection : (x, y, z) ↦ (x, y, -z)` (`det_fderiv_nilReflection`) is again a
  complete `.nil` structure, although the pullback is the other normal form
  `dx² + dy² + (dz + x dy)²` and differs from the model metric (`nilReflection_pullback_ne`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry Bundle
open scoped Manifold ContDiff Topology

namespace GC.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

@[ext]
structure TorusLattice where
  shift : Fin 3 → ℤ

namespace TorusLattice

instance : Mul TorusLattice := ⟨fun a b => ⟨a.shift + b.shift⟩⟩
instance : One TorusLattice := ⟨⟨0⟩⟩
instance : Inv TorusLattice := ⟨fun a => ⟨-a.shift⟩⟩

@[simp] theorem mul_shift (a b : TorusLattice) : (a * b).shift = a.shift + b.shift := rfl
@[simp] theorem one_shift : (1 : TorusLattice).shift = 0 := rfl
@[simp] theorem inv_shift (a : TorusLattice) : a⁻¹.shift = -a.shift := rfl

instance : Group TorusLattice :=
  Group.ofLeftAxioms (fun a b c => by ext1; simp [add_assoc]) (fun a => by ext1; simp)
    (fun a => by ext1; simp)

def translationPart (γ : TorusLattice) : E3 := WithLp.toLp 2 fun i => (γ.shift i : ℝ)

@[simp] theorem translationPart_apply (γ : TorusLattice) (i : Fin 3) :
    γ.translationPart i = γ.shift i := rfl

theorem translationPart_mul (a b : TorusLattice) :
    (a * b).translationPart = a.translationPart + b.translationPart := by
  ext i
  simp

instance : MulAction TorusLattice E3 where
  smul γ x := x + γ.translationPart
  one_smul x := by
    change x + (1 : TorusLattice).translationPart = x
    ext i
    simp
  mul_smul a b x := by
    change x + (a * b).translationPart = (x + b.translationPart) + a.translationPart
    rw [translationPart_mul]
    abel

theorem smul_def (γ : TorusLattice) (x : E3) :
    γ • x = LinearIsometryEquiv.refl ℝ E3 x + γ.translationPart :=
  rfl

theorem smul_apply (γ : TorusLattice) (x : E3) (i : Fin 3) :
    (γ • x) i = x i + γ.shift i :=
  rfl

theorem eq_one_of_smul_eq (γ : TorusLattice) (x : E3) (h : γ • x = x) : γ = 1 := by
  ext1
  funext i
  have hi := congrArg (fun y : E3 => y i) h
  simp only [smul_apply, add_eq_left, Int.cast_eq_zero] at hi
  exact hi

theorem finite_norm_translationPart_le (R : ℝ) :
    {γ : TorusLattice | ‖γ.translationPart‖ ≤ R}.Finite := by
  let B : ℤ := ⌈R⌉
  refine ((Set.Finite.pi (t := fun _ : Fin 3 => Set.Icc (-B) B)
    (fun _ => Set.finite_Icc _ _)).image TorusLattice.mk).subset ?_
  intro γ hγ
  refine ⟨γ.shift, fun i _ => ?_, rfl⟩
  have hR : ‖γ.translationPart‖ ≤ R := hγ
  have hi : |(γ.shift i : ℝ)| ≤ R := by
    have := PiLp.norm_apply_le γ.translationPart i
    rw [translationPart_apply, Real.norm_eq_abs] at this
    exact this.trans hR
  have hB : R ≤ B := Int.le_ceil R
  obtain ⟨h1, h2⟩ := abs_le.mp hi
  constructor
  · have : ((-B : ℤ) : ℝ) ≤ γ.shift i := by push_cast; linarith
    exact_mod_cast this
  · have : (γ.shift i : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this

end TorusLattice

instance : ProperlyDiscontinuousSMul TorusLattice E3 :=
  properlyDiscontinuousSMul_of_affine (fun _ => LinearIsometryEquiv.refl ℝ E3)
    TorusLattice.translationPart TorusLattice.smul_def
    TorusLattice.finite_norm_translationPart_le

instance : ContinuousConstSMul TorusLattice E3 :=
  continuousConstSMul_of_affine (fun _ => LinearIsometryEquiv.refl ℝ E3)
    TorusLattice.translationPart TorusLattice.smul_def

instance : ContMDiffConstSMul (𝓡 3) ∞ TorusLattice E3 :=
  contMDiffConstSMul_of_affine (fun _ => LinearIsometryEquiv.refl ℝ E3)
    TorusLattice.translationPart TorusLattice.smul_def

instance : IsCancelSMul TorusLattice E3 :=
  isCancelSMul_of_free TorusLattice.eq_one_of_smul_eq

abbrev TorusThree := MulAction.orbitRel.Quotient TorusLattice E3

def torusFundamentalCube : Set E3 :=
  WithLp.toLp 2 '' Set.univ.pi fun _ : Fin 3 => Set.Icc (0 : ℝ) 1

theorem isCompact_torusFundamentalCube : IsCompact torusFundamentalCube :=
  (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

theorem exists_smul_mem_torusFundamentalCube (x : E3) :
    ∃ γ : TorusLattice, γ • x ∈ torusFundamentalCube := by
  let γ : TorusLattice := ⟨fun i => -⌊x i⌋⟩
  refine ⟨γ, WithLp.ofLp (γ • x), fun i _ => ?_, rfl⟩
  change x i + ((-⌊x i⌋ : ℤ) : ℝ) ∈ Set.Icc (0 : ℝ) 1
  rw [Int.cast_neg, ← sub_eq_add_neg, ← Int.fract]
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem image_torusFundamentalCube_eq_univ :
    (Quotient.mk'' : E3 → TorusThree) '' torusFundamentalCube = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨γ, hγ⟩ := exists_smul_mem_torusFundamentalCube x
    exact ⟨γ • x, hγ, MulAction.orbitRel.Quotient.quotient_smul_eq⟩

instance : CompactSpace TorusThree :=
  ⟨image_torusFundamentalCube_eq_univ ▸
    isCompact_torusFundamentalCube.image continuous_quotient_mk'⟩

def torusThreeGeometry : GeometricStructure (𝓡 3) TorusThree :=
  euclideanGeometricStructure.quotientOfCompact TorusLattice
    (euclideanModelMetric_invariant_of_affine (fun _ => LinearIsometryEquiv.refl ℝ E3)
      TorusLattice.translationPart TorusLattice.smul_def)

theorem torusThreeGeometry_model : torusThreeGeometry.model = .euclidean :=
  rfl

theorem torusThreeGeometry_metric :
    torusThreeGeometry.metric = quotientMetric TorusLattice euclideanModelMetric
      (euclideanModelMetric_invariant_of_affine (fun _ => LinearIsometryEquiv.refl ℝ E3)
        TorusLattice.translationPart TorusLattice.smul_def) :=
  rfl

private abbrev axisProj (i : Fin 3) : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def fibreFlipLinear : E3 →L[ℝ] E3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![axisProj 0, axisProj 1, -axisProj 2])

theorem fibreFlipLinear_apply (p : E3) :
    fibreFlipLinear p = WithLp.toLp 2 ![p 0, p 1, -p 2] := by
  ext i
  fin_cases i <;> simp [fibreFlipLinear, axisProj]

theorem fibreFlipLinear_involutive (p : E3) : fibreFlipLinear (fibreFlipLinear p) = p := by
  ext i
  fin_cases i <;> simp [fibreFlipLinear_apply]

def fibreFlip : E3 ≃L[ℝ] E3 :=
  ContinuousLinearEquiv.equivOfInverse fibreFlipLinear fibreFlipLinear
    fibreFlipLinear_involutive fibreFlipLinear_involutive

def nilReflection : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ E3 := fibreFlip.toDiffeomorph

theorem nilReflection_apply (p : E3) :
    nilReflection p = WithLp.toLp 2 ![p 0, p 1, -p 2] :=
  fibreFlipLinear_apply p

theorem mfderiv_nilReflection (p : E3) :
    mfderiv (𝓡 3) (𝓡 3) nilReflection p = (fibreFlip : E3 →L[ℝ] E3) := by
  rw [mfderiv_eq_fderiv]
  exact fibreFlip.fderiv

theorem det_fderiv_nilReflection (p : E3) :
    LinearMap.det (fderiv ℝ nilReflection p : E3 →ₗ[ℝ] E3) = -1 := by
  have h : fderiv ℝ nilReflection p = (fibreFlip : E3 →L[ℝ] E3) := fibreFlip.fderiv
  rw [h, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, fibreFlip, fibreFlipLinear_apply]

theorem nilReflection_pullback_inner (p v w : E3) :
    (Diffeomorph.pullbackMetricCross (coordinateModelMetric .nil) nilReflection).inner p v w =
      v 0 * w 0 + v 1 * w 1 + (v 2 + p 0 * v 1) * (w 2 + p 0 * w 1) := by
  refine (Diffeomorph.pullbackMetricCross_inner _ _ p v w).trans ?_
  rw [mfderiv_nilReflection]
  change coordinateInner .nil (fibreFlipLinear p) (fibreFlipLinear v) (fibreFlipLinear w) = _
  simp [coordinateInner, coordinateCoframe, fibreFlipLinear_apply, Fin.sum_univ_three]
  ring

theorem nilReflection_pullback_ne :
    Diffeomorph.pullbackMetricCross (coordinateModelMetric .nil) nilReflection ≠
      coordinateModelMetric .nil := by
  intro h
  have h1 := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) E3 =>
    g.inner (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 2 1)) h
  simp only [nilReflection_pullback_inner, coordinateModelMetric_inner] at h1
  simp [coordinateInner, coordinateCoframe, Fin.sum_univ_three] at h1
  norm_num at h1

theorem nilReflection_hasThurstonAtlas :
    HasThurstonAtlas (Diffeomorph.pullbackMetricCross (coordinateModelMetric .nil) nilReflection)
      .nil :=
  (coordinateModelMetric_hasThurstonAtlas CoordinateModel.nil).pullback nilReflection

def nilReflectedGeometry : GeometricStructure (𝓡 3) E3 :=
  (coordinateGeometricStructure .nil (by decide)).pullback nilReflection

theorem nilReflectedGeometry_model : nilReflectedGeometry.model = .nil :=
  rfl

theorem nilReflectedGeometry_metric :
    nilReflectedGeometry.metric =
      Diffeomorph.pullbackMetricCross (coordinateModelMetric .nil) nilReflection :=
  rfl

section Restriction

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem ModelAtlas.restrictOpen {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric J N} (hg : ModelAtlas g h) (U : TopologicalSpace.Opens M) :
    ModelAtlas (g.restrictOpen U) h :=
  hg.pullback_of_localDiffeomorph (isLocalDiffeomorph_subtype_val U) fun x v w => by
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    rfl

theorem HasThurstonAtlas.restrictOpen {g : SmoothRiemannianMetric I M} {k : ThurstonModel}
    (hg : HasThurstonAtlas g k) (U : TopologicalSpace.Opens M) :
    HasThurstonAtlas (g.restrictOpen U) k := by
  cases k
  all_goals first
    | exact ModelAtlas.restrictOpen hg U
    | exact (coordinateModelAtlas_iff_actualModelAtlas _ _).mpr
        (ModelAtlas.restrictOpen ((coordinateModelAtlas_iff_actualModelAtlas _ _).mp hg) U)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_complete_restrictOpen_of_ray [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] (c : ℝ → U)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {p : M} (hp : p ∉ U)
    (hlim : Filter.Tendsto (fun t => (c t : M)) Filter.atBot (𝓝 p))
    (hspeed : ∀ t, (g.restrictOpen U).inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)
      (mfderiv 𝓘(ℝ, ℝ) I c t 1) ≤ Real.exp t ^ 2) :
    ¬ RiemannianMetricComplete (g.restrictOpen U) := by
  intro hcomp
  let : IsManifold I 1 U := IsManifold.of_le (I := I) (M := U) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace U := Manifold.metrizableSpace I U
  let : T3Space U := inferInstance
  let : RiemannianBundle (fun x : U => TangentSpace I x) :=
    ⟨(g.restrictOpen U).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x) :=
    ⟨⟨(g.restrictOpen U).inner, (g.restrictOpen U).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric I U
  let : CompleteSpace U := hcomp.complete
  let s : ℕ → U := fun n => c (-(n : ℝ))
  have hstep (n : ℕ) : edist (s n) (s (n + 1)) ≤ 1 * ENNReal.ofReal (Real.exp (-1)) ^ n := by
    have hab : -((n : ℝ) + 1) ≤ -(n : ℝ) := by linarith
    have hbound := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound
      (g.restrictOpen U) (C := Real.exp (-(n : ℝ))) hab hc.contMDiffOn (by
        intro t ht
        calc Real.sqrt _ ≤ Real.sqrt (Real.exp t ^ 2) := Real.sqrt_le_sqrt (hspeed t)
          _ = Real.exp t := Real.sqrt_sq (Real.exp_pos t).le
          _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr ht.2.le)
    have hs : s (n + 1) = c (-((n : ℝ) + 1)) := by
      simp only [s, Nat.cast_add, Nat.cast_one]
    calc edist (s n) (s (n + 1)) =
          riemannianEDistOf (g.restrictOpen U) (c (-((n : ℝ) + 1))) (c (-(n : ℝ))) := by
          rw [hs, edist_comm]
          rfl
      _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ))) *
          ENNReal.ofReal (-(n : ℝ) - -((n : ℝ) + 1)) := hbound
      _ = 1 * ENNReal.ofReal (Real.exp (-1)) ^ n := by
          rw [show -(n : ℝ) - -((n : ℝ) + 1) = 1 by ring, ENNReal.ofReal_one, mul_one,
            one_mul, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 2
          ring
  have hcauchy : CauchySeq s :=
    cauchySeq_of_edist_le_geometric _ 1 (by
      rw [ENNReal.ofReal_lt_one]
      exact Real.exp_lt_one_iff.mpr (by norm_num)) ENNReal.one_ne_top hstep
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hval : Filter.Tendsto (fun n : ℕ => (s n : M)) Filter.atTop (𝓝 (q : M)) :=
    (continuous_subtype_val.tendsto q).comp hq
  have hlimit : Filter.Tendsto (fun n : ℕ => (s n : M)) Filter.atTop (𝓝 p) :=
    hlim.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  exact hp (tendsto_nhds_unique hlimit hval ▸ q.2)

theorem not_exists_geometricStructure_of_not_complete [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : ¬ RiemannianMetricComplete g) :
    ¬ ∃ G : GeometricStructure I M, G.metric = g :=
  fun ⟨G, hG⟩ => hg (hG ▸ G.complete)

end Restriction

def modelZAxis : E3 := EuclideanSpace.single 2 1

theorem modelZAxis_ne_zero : modelZAxis ≠ 0 := by
  simp [modelZAxis]

def puncturedModel : TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩

instance : SigmaCompactSpace puncturedModel :=
  haveI : LocallyCompactSpace puncturedModel := puncturedModel.isOpen.locallyCompactSpace
  inferInstance

theorem exp_smul_modelZAxis_mem (t : ℝ) : Real.exp t • modelZAxis ∈ puncturedModel :=
  smul_ne_zero (Real.exp_ne_zero t) modelZAxis_ne_zero

def puncturedRay (t : ℝ) : puncturedModel := ⟨Real.exp t • modelZAxis, exp_smul_modelZAxis_mem t⟩

theorem puncturedRay_val : Subtype.val ∘ puncturedRay = fun t => Real.exp t • modelZAxis :=
  rfl

theorem contMDiff_puncturedRay : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 puncturedRay := by
  rw [← DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff, puncturedRay_val]
  exact (Real.contDiff_exp.smul contDiff_const).contMDiff

theorem mfderiv_puncturedRay (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) puncturedRay t 1 : E3) = Real.exp t • modelZAxis := by
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : puncturedModel → E3)
      (puncturedRay t) :=
    ((contMDiff_subtype_val (I := 𝓡 3) (U := puncturedModel)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hray : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) puncturedRay t :=
    (contMDiff_puncturedRay t).mdifferentiableAt (by decide)
  have hcomp := mfderiv_comp_apply t hval hray 1
  rw [mfderiv_subtype_val_apply, puncturedRay_val, mfderiv_eq_fderiv] at hcomp
  rw [← hcomp, ((Real.hasDerivAt_exp t).smul_const modelZAxis).hasFDerivAt.fderiv]
  change (1 : ℝ) • (Real.exp t • modelZAxis) = Real.exp t • modelZAxis
  exact one_smul ℝ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_complete_restrictOpen_puncturedModel (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hg : ∀ p, g.inner p modelZAxis modelZAxis ≤ 1) :
    ¬ RiemannianMetricComplete (g.restrictOpen puncturedModel) := by
  refine not_complete_restrictOpen_of_ray g puncturedModel puncturedRay contMDiff_puncturedRay
    (fun h => h rfl) ?_ fun t => ?_
  · have h := Real.tendsto_exp_atBot.smul_const modelZAxis
    rw [zero_smul] at h
    exact h
  · rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_puncturedRay]
    have h := hg (puncturedRay t : E3)
    have hsc (q : E3) (a : ℝ) (v : TangentSpace (𝓡 3) q) :
        g.inner q (a • v) (a • v) = a * (a * g.inner q v v) := by
      simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    refine (hsc _ (Real.exp t) modelZAxis).trans_le ?_
    calc Real.exp t * (Real.exp t * g.inner (puncturedRay t : E3) modelZAxis modelZAxis) =
          Real.exp t ^ 2 * g.inner (puncturedRay t : E3) modelZAxis modelZAxis := by ring
      _ ≤ Real.exp t ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = Real.exp t ^ 2 := mul_one _

theorem coordinateInner_modelZAxis (k : CoordinateModel) (p : E3) :
    coordinateInner k p modelZAxis modelZAxis = 1 := by
  cases k <;> simp [coordinateInner, coordinateCoframe, modelZAxis, Fin.sum_univ_three]

theorem coordinateModel_puncture_rejected (k : CoordinateModel) :
    HasThurstonAtlas ((coordinateModelMetric k).restrictOpen puncturedModel) k.thurstonModel ∧
      ¬ RiemannianMetricComplete ((coordinateModelMetric k).restrictOpen puncturedModel) :=
  ⟨(coordinateModelMetric_hasThurstonAtlas k).restrictOpen puncturedModel,
    not_complete_restrictOpen_puncturedModel _ fun p => by
      rw [coordinateModelMetric_inner, coordinateInner_modelZAxis]⟩

theorem euclideanModel_puncture_rejected :
    HasThurstonAtlas (euclideanModelMetric.restrictOpen puncturedModel) .euclidean ∧
      ¬ RiemannianMetricComplete (euclideanModelMetric.restrictOpen puncturedModel) :=
  ⟨ModelAtlas.restrictOpen (ModelAtlas.refl _) puncturedModel,
    not_complete_restrictOpen_puncturedModel _ fun p => by
      change inner ℝ modelZAxis modelZAxis ≤ 1
      simp [modelZAxis]⟩

theorem no_geometricStructure_puncturedModel (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hg : ∀ p, g.inner p modelZAxis modelZAxis ≤ 1) :
    ¬ ∃ G : GeometricStructure (𝓡 3) puncturedModel, G.metric = g.restrictOpen puncturedModel :=
  not_exists_geometricStructure_of_not_complete (not_complete_restrictOpen_puncturedModel g hg)

section SphericalProduct

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def neckPole : SpatialNeckSphere := ⟨EuclideanSpace.single 0 1, by simp⟩

def puncturedCylinder : TopologicalSpace.Opens SpatialNeckCylinder :=
  ⟨{(neckPole, 0)}ᶜ, isOpen_compl_singleton⟩

instance : SigmaCompactSpace puncturedCylinder :=
  haveI : LocallyCompactSpace puncturedCylinder := puncturedCylinder.isOpen.locallyCompactSpace
  inferInstance

def cylinderRay (t : ℝ) : puncturedCylinder :=
  ⟨(neckPole, Real.exp t), fun h => Real.exp_ne_zero t (congrArg Prod.snd h)⟩

theorem cylinderRay_val :
    Subtype.val ∘ cylinderRay = fun t => (neckPole, Real.exp t) :=
  rfl

theorem contMDiff_cylinderRay : ContMDiff 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 cylinderRay := by
  rw [← DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff, cylinderRay_val]
  exact contMDiff_const.prodMk Real.contDiff_exp.contMDiff

theorem mfderiv_cylinderRay (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel cylinderRay t 1 :
      EuclideanSpace ℝ (Fin 2) × ℝ) = (0, Real.exp t) := by
  have hval : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : puncturedCylinder → SpatialNeckCylinder) (cylinderRay t) :=
    ((contMDiff_subtype_val (I := SpatialNeckCylinderModel)
      (U := puncturedCylinder)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hray : MDifferentiableAt 𝓘(ℝ, ℝ) SpatialNeckCylinderModel cylinderRay t :=
    (contMDiff_cylinderRay t).mdifferentiableAt (by decide)
  have hcomp := mfderiv_comp_apply t hval hray 1
  rw [mfderiv_subtype_val_apply, cylinderRay_val] at hcomp
  rw [← hcomp, mfderiv_prodMk mdifferentiableAt_const
    (mdifferentiableAt_iff_differentiableAt.mpr Real.differentiableAt_exp), mfderiv_const,
    mfderiv_eq_fderiv, Real.hasDerivAt_exp t |>.hasFDerivAt.fderiv]
  refine Prod.ext rfl ?_
  change (1 : ℝ) • Real.exp t = Real.exp t
  exact one_smul ℝ _

theorem sphericalProduct_puncture_rejected :
    HasThurstonAtlas (sphericalProductModelMetric.restrictOpen puncturedCylinder)
        .sphericalProduct ∧
      ¬ RiemannianMetricComplete (sphericalProductModelMetric.restrictOpen puncturedCylinder) := by
  refine ⟨ModelAtlas.restrictOpen (ModelAtlas.refl _) puncturedCylinder,
    not_complete_restrictOpen_of_ray _ puncturedCylinder cylinderRay contMDiff_cylinderRay
      (fun h => h rfl) ?_ fun t => ?_⟩
  · exact tendsto_const_nhds.prodMk_nhds (Real.tendsto_exp_atBot)
  · rw [SmoothRiemannianMetric.restrictOpen_inner]
    have key (q : SpatialNeckCylinder) (v : TangentSpace SpatialNeckCylinderModel q)
        (hv : (v : EuclideanSpace ℝ (Fin 2) × ℝ) = (0, Real.exp t)) :
        sphericalProductModelMetric.inner q v v = Real.exp t ^ 2 := by
      rw [sphericalProductModelMetric_eq_prod]
      refine (SmoothRiemannianMetric.prod_inner _ _ q v v).trans ?_
      have h1 : v.1 = 0 := congrArg Prod.fst hv
      have h2 : v.2 = Real.exp t := congrArg Prod.snd hv
      rw [h1, h2]
      have hz : (Geometry.roundMetric (E := E3) (n := 2)).inner q.1
          (0 : TangentSpace (𝓡 2) q.1) (0 : TangentSpace (𝓡 2) q.1) = 0 := by
        simp
      have he : euclideanMetric.inner q.2 (Real.exp t : TangentSpace 𝓘(ℝ, ℝ) q.2)
          (Real.exp t : TangentSpace 𝓘(ℝ, ℝ) q.2) = Real.exp t ^ 2 := by
        change inner ℝ (Real.exp t) (Real.exp t) = Real.exp t ^ 2
        rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      exact (congrArg₂ (· + ·) hz he).trans (zero_add _)
    exact (key _ _ (mfderiv_cylinderRay t)).le

end SphericalProduct

section Spherical

local notation "E4" => EuclideanSpace ℝ (Fin 4)

local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

def sphereAngle (t : ℝ) : ℝ := Real.arctan (Real.exp t)

theorem sphereAngle_pos (t : ℝ) : 0 < sphereAngle t :=
  Real.arctan_pos.mpr (Real.exp_pos t)

theorem sphereAngle_lt_pi (t : ℝ) : sphereAngle t < Real.pi := by
  have := Real.arctan_lt_pi_div_two (Real.exp t)
  unfold sphereAngle
  linarith [Real.pi_pos]

theorem hasDerivAt_sphereAngle (t : ℝ) :
    HasDerivAt sphereAngle (1 / (1 + Real.exp t ^ 2) * Real.exp t) t :=
  (Real.hasDerivAt_arctan (Real.exp t)).comp t (Real.hasDerivAt_exp t)

def sphereCurve (t : ℝ) : E4 :=
  Real.cos (sphereAngle t) • EuclideanSpace.single 0 1 +
    Real.sin (sphereAngle t) • EuclideanSpace.single 1 1

theorem norm_cos_smul_add_sin_smul (a b : ℝ) :
    ‖a • (EuclideanSpace.single 0 1 : E4) + b • EuclideanSpace.single 1 1‖ ^ 2 =
      a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp

theorem sphereCurve_mem (t : ℝ) : sphereCurve t ∈ Metric.sphere (0 : E4) 1 := by
  have h := norm_cos_smul_add_sin_smul (Real.cos (sphereAngle t)) (Real.sin (sphereAngle t))
  rw [Real.cos_sq_add_sin_sq] at h
  rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow]
  exact h

def spherePole : RoundThree := ⟨EuclideanSpace.single 0 1, by simp⟩

def puncturedSphere : TopologicalSpace.Opens RoundThree :=
  ⟨{spherePole}ᶜ, isOpen_compl_singleton⟩

instance : SigmaCompactSpace puncturedSphere :=
  haveI : LocallyCompactSpace puncturedSphere := puncturedSphere.isOpen.locallyCompactSpace
  inferInstance

theorem sphereCurve_ne_pole (t : ℝ) :
    (⟨sphereCurve t, sphereCurve_mem t⟩ : RoundThree) ∈ puncturedSphere := by
  intro h
  have h1 := congrArg (fun x : RoundThree => (x : E4) 1) h
  have hs := Real.sin_pos_of_pos_of_lt_pi (sphereAngle_pos t) (sphereAngle_lt_pi t)
  have h0 : Real.sin (sphereAngle t) = 0 := by simpa [sphereCurve, spherePole] using h1
  exact hs.ne' h0

def sphereRay (t : ℝ) : puncturedSphere :=
  ⟨⟨sphereCurve t, sphereCurve_mem t⟩, sphereCurve_ne_pole t⟩

theorem contDiff_sphereCurve {n : WithTop ℕ∞} : ContDiff ℝ n sphereCurve :=
  ((Real.contDiff_cos.comp (Real.contDiff_arctan.comp Real.contDiff_exp)).smul
    contDiff_const).add
    ((Real.contDiff_sin.comp (Real.contDiff_arctan.comp Real.contDiff_exp)).smul contDiff_const)

theorem contMDiff_sphereRay : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 sphereRay := by
  rw [← DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff]
  exact contDiff_sphereCurve.contMDiff.codRestrict_sphere sphereCurve_mem

theorem hasDerivAt_sphereCurve (t : ℝ) :
    HasDerivAt sphereCurve
      ((-Real.sin (sphereAngle t) * (1 / (1 + Real.exp t ^ 2) * Real.exp t)) •
          (EuclideanSpace.single 0 1 : E4) +
        (Real.cos (sphereAngle t) * (1 / (1 + Real.exp t ^ 2) * Real.exp t)) •
          EuclideanSpace.single 1 1) t :=
  (((Real.hasDerivAt_cos _).comp t (hasDerivAt_sphereAngle t)).smul_const _).add
    (((Real.hasDerivAt_sin _).comp t (hasDerivAt_sphereAngle t)).smul_const _)

theorem dIncl_mfderiv_sphereRay (t : ℝ) :
    Geometry.dIncl (n := 3) (sphereRay t : RoundThree) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) sphereRay t 1) =
      (-Real.sin (sphereAngle t) * (1 / (1 + Real.exp t ^ 2) * Real.exp t)) •
          (EuclideanSpace.single 0 1 : E4) +
        (Real.cos (sphereAngle t) * (1 / (1 + Real.exp t ^ 2) * Real.exp t)) •
          EuclideanSpace.single 1 1 := by
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : puncturedSphere → RoundThree)
      (sphereRay t) :=
    ((contMDiff_subtype_val (I := 𝓡 3) (U := puncturedSphere)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hray : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) sphereRay t :=
    (contMDiff_sphereRay t).mdifferentiableAt one_ne_zero
  have hcomp := mfderiv_comp_apply t hval hray 1
  rw [mfderiv_subtype_val_apply] at hcomp
  have hcoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, E4) ((↑) : RoundThree → E4)
      (sphereRay t : RoundThree) :=
    ((contMDiff_coe_sphere (n := 3) (m := ∞)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h2 := mvfderiv_comp_apply t hcoe (hval.comp t hray) 1
  rw [hcomp] at h2
  unfold Geometry.dIncl
  refine Eq.trans h2.symm ?_
  change mvfderiv 𝓘(ℝ, ℝ) sphereCurve t 1 = _
  rw [mvfderiv_eq_fderiv, (hasDerivAt_sphereCurve t).hasFDerivAt.fderiv]
  exact one_smul ℝ _

theorem sphericalModel_puncture_rejected :
    HasThurstonAtlas (sphericalModelMetric.restrictOpen puncturedSphere) .spherical ∧
      ¬ RiemannianMetricComplete (sphericalModelMetric.restrictOpen puncturedSphere) := by
  refine ⟨ModelAtlas.restrictOpen (ModelAtlas.refl _) puncturedSphere,
    not_complete_restrictOpen_of_ray _ puncturedSphere sphereRay contMDiff_sphereRay
      (fun h => h rfl) ?_ fun t => ?_⟩
  · have hθ : Filter.Tendsto sphereAngle Filter.atBot (𝓝 0) := by
      have h := (Real.continuous_arctan.tendsto 0).comp Real.tendsto_exp_atBot
      rwa [Real.arctan_zero] at h
    have h := (((Real.continuous_cos.tendsto 0).comp hθ).smul_const
      (EuclideanSpace.single 0 1 : E4)).add
      (((Real.continuous_sin.tendsto 0).comp hθ).smul_const (EuclideanSpace.single 1 1 : E4))
    rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at h
    exact tendsto_subtype_rng.mpr h
  · rw [SmoothRiemannianMetric.restrictOpen_inner]
    change inner ℝ (Geometry.dIncl (n := 3) (sphereRay t : RoundThree)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) sphereRay t 1))
      (Geometry.dIncl (n := 3) (sphereRay t : RoundThree)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) sphereRay t 1)) ≤ _
    rw [dIncl_mfderiv_sphereRay, real_inner_self_eq_norm_sq, norm_cos_smul_add_sin_smul]
    set d := 1 / (1 + Real.exp t ^ 2) * Real.exp t
    have hd : 0 ≤ d := by positivity
    have hle : d ≤ Real.exp t := by
      have h1 : 1 / (1 + Real.exp t ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg (Real.exp t)]
      exact (mul_le_of_le_one_left (Real.exp_pos t).le h1)
    calc (-Real.sin (sphereAngle t) * d) ^ 2 + (Real.cos (sphereAngle t) * d) ^ 2 =
          d ^ 2 * (Real.sin (sphereAngle t) ^ 2 + Real.cos (sphereAngle t) ^ 2) := by ring
      _ = d ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
      _ ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hd hle 2

end Spherical

theorem inner_self_le_coordinateInner_hyperbolic (p v : E3) (hp : p 2 ≤ 0) :
    inner ℝ v v ≤ coordinateInner .hyperbolic p v v := by
  have he : 1 ≤ Real.exp (-p 2) := Real.one_le_exp (neg_nonneg.mpr hp)
  have he2 : 1 ≤ Real.exp (-p 2) * Real.exp (-p 2) := by nlinarith
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  simp [coordinateInner, coordinateCoframe, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

theorem addHaar_lowerHalfSpace_eq_top [MeasurableSpace E3] [BorelSpace E3]
    (μ : MeasureTheory.Measure E3) [μ.IsAddHaarMeasure] : μ {p : E3 | p 2 ≤ 0} = ⊤ := by
  have hball (n : ℕ) : Metric.closedBall (-(n : ℝ) • modelZAxis) n ⊆ {p : E3 | p 2 ≤ 0} := by
    intro p hp
    have h1 := PiLp.norm_apply_le (p - (-(n : ℝ) • modelZAxis)) 2
    have h2 : ‖p - (-(n : ℝ) • modelZAxis)‖ ≤ n := mem_closedBall_iff_norm.mp hp
    have h3 : (p - (-(n : ℝ) • modelZAxis)) 2 = p 2 + n := by simp [modelZAxis]
    rw [h3, Real.norm_eq_abs] at h1
    change p 2 ≤ 0
    linarith [(abs_le.mp (h1.trans h2)).2]
  have hpos : μ (Metric.ball 0 1) ≠ 0 := (Metric.measure_ball_pos μ 0 one_pos).ne'
  have hlim : Filter.Tendsto (fun n : ℕ => μ (Metric.closedBall (-(n : ℝ) • modelZAxis) n))
      Filter.atTop (𝓝 ⊤) := by
    have hpow : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ Module.finrank ℝ E3))
        Filter.atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp ((Filter.tendsto_pow_atTop (by simp)).comp
        tendsto_natCast_atTop_atTop)
    have h := ENNReal.Tendsto.mul_const (b := μ (Metric.ball 0 1)) hpow
      (Or.inl ENNReal.top_ne_zero)
    rw [ENNReal.top_mul hpos] at h
    refine h.congr fun n => ?_
    rw [MeasureTheory.Measure.addHaar_closedBall μ _ (Nat.cast_nonneg n)]
  exact top_unique (le_of_tendsto' hlim fun n => MeasureTheory.measure_mono (hball n))

theorem coordinateHyperbolic_volume_eq_top :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) E3 (coordinateModelMetric .hyperbolic)
      Set.univ = ⊤ := by
  let s : Set E3 := {p | p 2 ≤ 0}
  have hs : @MeasurableSet E3 (borel E3) s := by
    let : MeasurableSpace E3 := borel E3
    have : BorelSpace E3 := ⟨rfl⟩
    exact (isClosed_le (PiLp.continuous_apply 2 _ 2) continuous_const).measurableSet
  have hle := Integral.Measure.volumeMeasure_restrict_le (coordinateModelMetric .hyperbolic)
    euclideanModelMetric one_pos hs (fun x hx v => by
      have h := inner_self_le_coordinateInner_hyperbolic x v hx
      rw [one_mul]
      exact h.trans_eq (coordinateModelMetric_inner .hyperbolic x v v).symm)
  have heuc : Integral.Measure.riemannianVolumeMeasure (𝓡 3) E3 euclideanModelMetric s = ⊤ := by
    let : MeasurableSpace E3 := borel E3
    have : BorelSpace E3 := ⟨rfl⟩
    have hv : Integral.Measure.riemannianVolumeMeasure (𝓡 3) E3 euclideanModelMetric =
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      Integral.Measure.riemannianVolumeMeasure_euclideanMetric
    rw [hv]
    exact addHaar_lowerHalfSpace_eq_top _
  have h1 := MeasureTheory.Measure.le_iff'.mp hle Set.univ
  rw [MeasureTheory.Measure.restrict_apply_univ, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.restrict_apply_univ, one_pow, Real.sqrt_one, ENNReal.ofReal_one,
    one_smul, heuc] at h1
  exact top_unique (h1.trans (MeasureTheory.measure_mono (Set.subset_univ s)))

theorem no_geometricStructure_coordinateHyperbolic :
    ¬ ∃ G : GeometricStructure (𝓡 3) E3,
      G.model = .hyperbolic ∧ G.metric = coordinateModelMetric .hyperbolic := by
  rintro ⟨G, hmodel, hmetric⟩
  have h := G.hyperbolic_finite_volume hmodel
  rw [hmetric, coordinateHyperbolic_volume_eq_top] at h
  exact lt_irrefl _ h

end GC.Geometry
