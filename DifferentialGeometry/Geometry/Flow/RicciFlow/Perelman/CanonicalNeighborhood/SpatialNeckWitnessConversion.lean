import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance spatialNeckConversionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem cylinderReference_zero_eq_double (C : CylinderReference) :
    C.metric 0 = doubleSphereCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := C.inner_eq 0 le_rfl z v w
  have hD := doubleSphereCylinderMetric_inner z.1 z.2 v.1 w.1 v.2 w.2
  simp only [sub_zero, mul_one] at hC
  apply hC.trans
  have hr : (DifferentialGeometry.Geometry.roundMetric
      (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner z.1 v.1 w.1 =
      inner ℝ
        (show ThreeSpace from mfderiv I2 I3 (fun y : Sphere 2 => (y : ThreeSpace)) z.1 v.1)
        (show ThreeSpace from mfderiv I2 I3 (fun y : Sphere 2 => (y : ThreeSpace)) z.1 w.1) := rfl
  rw [hr] at hD
  exact hD.symm

private theorem metricDerivNorm_eq_tensor02_error
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) N]
    [IsManifold SpatialNeckCylinderModel ∞ N] [T2Space N]
    (g h : SmoothRiemannianMetric SpatialNeckCylinderModel N) (a : ℕ) (z : N) :
    metricDerivNorm a g h h z = tensor02CovDerivNormWith a
      (metricTensorField g - metricTensorField h) h h z := by
  unfold metricDerivNorm tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_sub]
  rfl

private theorem cylinderReference_axial_normalized_inner (C : CylinderReference)
    (w : SpatialNeckCylinder) (v v' : TangentSpace SpatialNeckCylinderModel w) :
    unitCylinderMetric.inner w v v' = (1 / 2) * (C.metric 0).inner
      (cylinderAxialScale (Real.sqrt 2) (by positivity) w)
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale (Real.sqrt 2) (by positivity)) w v)
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale (Real.sqrt 2) (by positivity)) w v') := by
  let D := cylinderAxialScale (Real.sqrt 2) (by positivity)
  let gD := DifferentialGeometry.Diffeomorph.pullbackMetricCross (C.metric 0) D
  have href : scaleMetric (1 / 2) (by norm_num) gD = unitCylinderMetric := by
    dsimp only [gD]
    rw [cylinderReference_zero_eq_double,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact cylinderAxialScale_normalized_doubleSphereCylinderMetric
  calc
    unitCylinderMetric.inner w v v' =
        (scaleMetric (1 / 2) (by norm_num) gD).inner w v v' :=
      congrArg (fun h => h.inner w v v') href.symm
    _ = (1 / 2) * gD.inner w v v' := scaleMetric_inner _ _ _ _ _ _
    _ = _ := congrArg (fun q => (1 / 2 : ℝ) * q)
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner (C.metric 0) D w v v')

private theorem spatialNeck_axial_embedding_deriv
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eta eps : ℝ}
    (nk : SpatialNeck g eta p)
    (Phi : C(spatialNeckBuffer eps, M))
    (hPhi : ∀ z : spatialNeckBuffer eps,
      Phi z = nk.map (cylinderAxialScale (Real.sqrt 2) (by positivity) z.val))
    (hdomain : ∀ z : spatialNeckBuffer eps,
      cylinderAxialScale (Real.sqrt 2) (by positivity) z.val ∈
        univ ×ˢ Ioo (-eta⁻¹) eta⁻¹)
    (w : spatialNeckBuffer eps) (v : TangentSpace SpatialNeckCylinderModel w) :
    mfderiv SpatialNeckCylinderModel I3 Phi w v =
      mfderiv SpatialNeckCylinderModel I3 nk.map
        (cylinderAxialScale (Real.sqrt 2) (by positivity) w.val)
        (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
          (cylinderAxialScale (Real.sqrt 2) (by positivity)) w.val v) := by
  let D := cylinderAxialScale (Real.sqrt 2) (by positivity)
  have hfun : (Phi : spatialNeckBuffer eps → M) = fun z => nk.map (D z.val) := funext hPhi
  have hnk := nk.map.mdifferentiableAt (by simp) (nk.domain (hdomain w))
  have hD := D.mdifferentiable (by simp) w.val
  have hval := (hasMFDerivAt_subtype_val (I := SpatialNeckCylinderModel)
    (spatialNeckBuffer eps) w).mdifferentiableAt
  rw [hfun]
  have hh := mfderiv_comp_apply w (hnk.comp w.val hD) hval v
  rw [mfderiv_subtype_val_apply] at hh
  exact hh.trans (mfderiv_comp_apply w.val hnk hD v)

private theorem spatialNeck_normalized_error
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eta eps : ℝ}
    (nk : SpatialNeck g eta p)
    (Phi : C(spatialNeckBuffer eps, M))
    (hemb : Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ Phi)
    (hPhi : ∀ z : spatialNeckBuffer eps,
      Phi z = nk.map (cylinderAxialScale (Real.sqrt 2) (by positivity) z.val))
    (hdomain : ∀ z : spatialNeckBuffer eps,
      cylinderAxialScale (Real.sqrt 2) (by positivity) z.val ∈
        univ ×ˢ Ioo (-eta⁻¹) eta⁻¹)
    : metricTensorField (spatialNeckNormalizedMetric g p nk.Q_pos hemb) -
        metricTensorField (unitCylinderMetric.restrictOpen (spatialNeckBuffer eps)) =
      restrictOpen0S (I := SpatialNeckCylinderModel) 2 (V := spatialNeckBuffer eps)
        ((1 / 2 : ℝ) • pullbackTensor02FieldCross
          (cylinderAxialScale (Real.sqrt 2) (by positivity)) (nk.comparison.jet 0 0)) := by
  let D := cylinderAxialScale (Real.sqrt 2) (by positivity)
  ext w v
  have hG := spatialNeckNormalizedMetric_inner g p nk.Q_pos hemb w (v 0) (v 1)
  rw [spatialNeckScale_inv_sq g p nk.Q_pos,
    spatialNeck_axial_embedding_deriv nk Phi hPhi hdomain,
    spatialNeck_axial_embedding_deriv nk Phi hPhi hdomain, hPhi] at hG
  have hE := pullbackTensor02FieldCross_apply D (nk.comparison.jet 0 0) w.val v
  rw [nk.comparison.jet_zero, nk.comparison.pullback_eq 0 (D w.val) (hdomain w)] at hE
  simp only [scaleMetric_inner] at hE
  change (spatialNeckNormalizedMetric g p nk.Q_pos hemb).inner w (v 0) (v 1) -
      unitCylinderMetric.inner w.val (v 0) (v 1) =
    (1 / 2) * (pullbackTensor02FieldCross D (nk.comparison.jet 0 0)) w.val v
  calc
    _ = _ := congrArg₂ (fun q r : ℝ => q - r) hG
      (cylinderReference_axial_normalized_inner nk.cylinder w.val (v 0) (v 1))
    _ = _ := by rw [hE]; ring

private theorem spatialNeck_normalized_derivNorm
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eta eps : ℝ}
    (nk : SpatialNeck g eta p)
    (Phi : C(spatialNeckBuffer eps, M))
    (hemb : Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ Phi)
    (hPhi : ∀ z : spatialNeckBuffer eps,
      Phi z = nk.map (cylinderAxialScale (Real.sqrt 2) (by positivity) z.val))
    (hdomain : ∀ z : spatialNeckBuffer eps,
      cylinderAxialScale (Real.sqrt 2) (by positivity) z.val ∈
        univ ×ˢ Ioo (-eta⁻¹) eta⁻¹)
    (a : ℕ) (z : spatialNeckBuffer eps) :
    metricDerivNorm a (spatialNeckNormalizedMetric g p nk.Q_pos hemb)
        (unitCylinderMetric.restrictOpen (spatialNeckBuffer eps))
        (unitCylinderMetric.restrictOpen (spatialNeckBuffer eps)) z =
      (Real.sqrt (2 ^ (a + 2)) * (1 / 2)) *
        tensor02CovDerivNormWith a (nk.comparison.jet 0 0)
          (nk.cylinder.metric 0) (nk.cylinder.metric 0)
          (cylinderAxialScale (Real.sqrt 2) (by positivity) z.val) := by
  let D := cylinderAxialScale (Real.sqrt 2) (by positivity)
  let U := spatialNeckBuffer eps
  let G := spatialNeckNormalizedMetric g p nk.Q_pos hemb
  let gD := DifferentialGeometry.Diffeomorph.pullbackMetricCross (nk.cylinder.metric 0) D
  have href : scaleMetric (1 / 2) (by norm_num) gD = unitCylinderMetric := by
    dsimp only [gD]
    rw [cylinderReference_zero_eq_double,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact cylinderAxialScale_normalized_doubleSphereCylinderMetric
  let A := (1 / 2 : ℝ) • pullbackTensor02FieldCross D (nk.comparison.jet 0 0)
  have herror := spatialNeck_normalized_error nk Phi hemb hPhi hdomain
  calc
    metricDerivNorm a G (unitCylinderMetric.restrictOpen U)
        (unitCylinderMetric.restrictOpen U) z =
      tensor02CovDerivNormWith a (restrictOpen0S 2 (V := U) A)
        (unitCylinderMetric.restrictOpen U) (unitCylinderMetric.restrictOpen U) z := by
          rw [metricDerivNorm_eq_tensor02_error, herror]
    _ = tensor02CovDerivNormWith a A unitCylinderMetric unitCylinderMetric z.val :=
      tensor02CovDerivNormWith_restrictOpen0S U unitCylinderMetric unitCylinderMetric A a z
    _ = _ := by
      rw [← href]
      change tensor02CovDerivNormWith a
        ((1 / 2 : ℝ) • pullbackTensor02FieldCross D (nk.comparison.jet 0 0))
        (scaleMetric (1 / 2) (by norm_num) gD)
        (scaleMetric (1 / 2) (by norm_num) gD) z.val = _
      rw [tensor02CovDerivNormWith_smul_scaleMetric]
      norm_num only [one_div, inv_inv, abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact congrArg (fun v => (Real.sqrt (2 ^ (a + 2)) * (1 / 2)) * v)
        (tensor02CovDerivNormWith_pullbackTensor02FieldCross
          (nk.cylinder.metric 0) (nk.cylinder.metric 0) D (nk.comparison.jet 0 0) a z.val)

theorem exists_spatialNeckWitness_of_spatialNeck {eps : ℝ} (heps : 0 < eps) :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
        ∀ (p : M) (eta : ℝ), eta ≤ eta₀ →
        ∀ nk : SpatialNeck g eta p,
        ∃ W : SpatialNeckWitness g nk.center p eps,
          ∀ z : spatialNeckBuffer eps,
            W.embedding z = nk.map (cylinderAxialScale (Real.sqrt 2) (by positivity) z.val) := by
  let n := ⌈eps⁻¹⌉₊
  let B : ℝ := 2 ^ (n + 2)
  let R := eps⁻¹ + 1
  have hB : 0 < B := by positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  let eta₀ := min eps (min (2 * Real.sqrt 2 * R)⁻¹ (eps / (2 * B)))
  refine ⟨eta₀, lt_min heps (lt_min (by positivity) (by positivity)), ?_⟩
  intro M _ _ _ _ _ g hg p eta heta nk
  have hepsle : eta ≤ eps := heta.trans (min_le_left _ _)
  have hrest := heta.trans (min_le_right _ _)
  have hrad : eta ≤ (2 * Real.sqrt 2 * R)⁻¹ := hrest.trans (min_le_left _ _)
  have hbudget : eta ≤ eps / (2 * B) := hrest.trans (min_le_right _ _)
  have hrad' : 2 * Real.sqrt 2 * R ≤ eta⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ nk.eps_pos hrad
  have hord : n ≤ ⌈eta⁻¹⌉₊ := Nat.ceil_le_ceil (inv_anti₀ nk.eps_pos hepsle)
  let D := cylinderAxialScale (Real.sqrt 2) hsqrt.ne'
  let U := spatialNeckBuffer eps
  have hdomain (z : U) : D z.val ∈ univ ×ˢ Ioo (-eta⁻¹) eta⁻¹ := by
    have hz' : -eps⁻¹ - 1 < z.val.2 ∧ z.val.2 < eps⁻¹ + 1 := z.property
    have hz : -R < z.val.2 ∧ z.val.2 < R := by
      dsimp only [R]
      constructor <;> linarith [hz'.1, hz'.2]
    have hlo := mul_lt_mul_of_pos_left hz.1 hsqrt
    have hhi := mul_lt_mul_of_pos_left hz.2 hsqrt
    refine ⟨mem_univ _, ?_, ?_⟩ <;>
      dsimp only [D, cylinderAxialScale_apply] <;> nlinarith
  let P := D.toPartialDiffeomorph.trans nk.map
  have hUsource (z : U) : z.val ∈ P.source := ⟨mem_univ _, nk.domain (hdomain z)⟩
  have hlocal : IsLocalDiffeomorph SpatialNeckCylinderModel I3 ∞ (fun z : U => nk.map (D z.val)) :=
    isLocalDiffeomorph_restrict_open U (fun z => ⟨P, hUsource z, fun _ _ => rfl⟩)
  have hinj : Function.Injective (fun z : U => nk.map (D z.val)) := by
    intro z w hzw
    exact Subtype.ext (D.injective (nk.map.toPartialEquiv.injOn
      (nk.domain (hdomain z)) (nk.domain (hdomain w)) hzw))
  have hemb := localDiffeomorph_isSmoothEmbedding_of_injective hlocal hinj
  let Phi : C(U, M) := ⟨fun z => nk.map (D z.val), hemb.contMDiff.continuous⟩
  have hemb' : Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ Phi := hemb
  let G := spatialNeckNormalizedMetric g p nk.Q_pos (Phi := Phi) hemb'
  have hnorm (a : ℕ) (z : U) :=
    spatialNeck_normalized_derivNorm nk Phi hemb' (fun _ => rfl) hdomain a z
  have hweight (a : ℕ) (ha : a ≤ n) : Real.sqrt (2 ^ (a + 2)) * (1 / 2) ≤ B := by
    have hpow : (2 : ℝ) ^ (a + 2) ≤ B :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hs : Real.sqrt ((2 : ℝ) ^ (a + 2)) ≤ (2 : ℝ) ^ (a + 2) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ (by norm_num)))
    nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ (a + 2))]
  have hclose : metricDerivNormSupOn (I := SpatialNeckCylinderModel) (spatialNeckClosedCore eps) n
      G (unitCylinderMetric.restrictOpen U) (unitCylinderMetric.restrictOpen U) < eps := by
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall _ _ _ _ _ (B * eta)
      (mul_nonneg hB.le nk.eps_pos.le) ?_) ?_
    · intro a ha z _hz
      rw [hnorm]
      have hc := nk.comparison.close a 0 (by simpa using ha.trans hord) 0 (by simp)
        (D z.val) (hdomain z)
      exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
        (mul_le_mul_of_nonneg_right (hweight a ha) nk.eps_pos.le)
    · have hh := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hbudget
      nlinarith
  refine ⟨SpatialNeckWitness.ofEmbedding g nk.center p eps (by simp [ThreeSpace])
    hg heps nk.Q_pos Phi hemb' ?_ hclose, fun _ => rfl⟩
  change nk.map (D (nk.center, 0)) = p
  rw [cylinderAxialScale_central]
  exact nk.center_eq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
