import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Scaling
import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Metric.Construction.TensorOpenExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Locality
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

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

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance inverseNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {yStar : SpatialNeckSphere} {p : M} {eta eps : ℝ}

private theorem spatialNeckWitness_partialDiffeomorph
    (W : SpatialNeckWitness g yStar p eta) :
    ∃ F : PartialDiffeomorph IC I3 Cylinder M ∞,
      F.source = spatialNeckBuffer eta ∧
      ∀ z : spatialNeckBuffer eta, F z.val = W.embedding z := by
  let U := spatialNeckBuffer eta
  have hUne : Nonempty U := ⟨spatialNeckCentralPoint eta W.epsilon_pos yStar⟩
  obtain ⟨V, C, _hV, hC, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      W.embedding W.smooth_embedding.contMDiff W.smooth_embedding.isEmbedding.injective
      W.differential_injective
      (by simp [Module.finrank_prod, ThreeSpace])
  have hVne : Nonempty V := ⟨C (spatialNeckCentralPoint eta W.epsilon_pos yStar)⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph IC U hUne
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 V hVne
  let F := (iU.symm.trans C.toPartialDiffeomorph).trans iV
  have hsource : F.source = U := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      C (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  refine ⟨F, hsource, ?_⟩
  intro z
  change (C (iU.symm z.val) : M) = W.embedding z
  rw [show iU.symm z.val = z from
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
      IC U hUne z.property]
  exact hC z

private theorem cylinderReference_zero_eq_inverse_axial :
    cylinderReferenceMetric 0 = scaleMetric 2 (by norm_num)
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross unitCylinderMetric
        (cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity))) := by
  rw [← DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric,
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    ← cylinderAxialScale_symm]
  change cylinderReferenceMetric 0 = doubleSphereCylinderMetric
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := cylinderReferenceMetric_zero_inner z v w
  have hD := doubleSphereCylinderMetric_inner z.1 z.2 v.1 w.1 v.2 w.2
  exact hC.trans hD.symm

private theorem spatialNeckWitness_embedding_deriv
    (W : SpatialNeckWitness g yStar p eta)
    (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : F.source = spatialNeckBuffer eta)
    (hmap : ∀ z : spatialNeckBuffer eta, F z.val = W.embedding z)
    (x : spatialNeckBuffer eta) (v : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel I3 W.embedding x v =
      mfderiv SpatialNeckCylinderModel I3 F x.val v := by
  have hfun : (F ∘ (Subtype.val : spatialNeckBuffer eta → Cylinder)) = W.embedding := funext hmap
  have hF := F.mdifferentiableAt (by simp) (by rw [hsource]; exact x.property)
  have hval : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : spatialNeckBuffer eta → Cylinder) x :=
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (U := spatialNeckBuffer eta)
      (n := ∞)).mdifferentiableAt (by decide)
  have h := mfderiv_comp x hF hval
  rw [hfun, mfderiv_subtype_val] at h
  exact DFunLike.congr_fun h v

private theorem spatialNeckWitness_inverse_derivNorm
    (W : SpatialNeckWitness g yStar p eta)
    (Eext : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2)
    (hEext : ∀ x : spatialNeckBuffer eta, x.val ∈ univ ×ˢ Icc (-eta⁻¹) eta⁻¹ →
      ∀ v : Fin 2 → TangentSpace IC x,
        Eext x.val v =
          (metricTensorField W.normalizedMetric -
            metricTensorField (unitCylinderMetric.restrictOpen (spatialNeckBuffer eta))) x v)
    (a : ℕ) (z : Cylinder)
    (hz : cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z ∈ univ ×ˢ Ioo (-eta⁻¹) eta⁻¹)
    (hzu : cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z ∈ spatialNeckBuffer eta) :
    tensor02CovDerivNormWith a
      ((2 : ℝ) • pullbackTensor02FieldCross
        (cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)) Eext)
      (cylinderReferenceMetric 0) (cylinderReferenceMetric 0) z =
    (Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2) *
      metricDerivNorm a W.normalizedMetric
        (unitCylinderMetric.restrictOpen (spatialNeckBuffer eta))
        (unitCylinderMetric.restrictOpen (spatialNeckBuffer eta))
        ⟨cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z, hzu⟩ := by
  let D := cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)
  let U := spatialNeckBuffer eta
  let V : Set Cylinder := univ ×ˢ Ioo (-eta⁻¹) eta⁻¹
  let E : Tensor0SField (I := IC) (M := U) (n := ∞) 2 :=
    metricTensorField W.normalizedMetric - metricTensorField (unitCylinderMetric.restrictOpen U)
  let x : U := ⟨D z, hzu⟩
  have hnear : {w : U | w.val ∈ V} ∈ 𝓝 x :=
    ((isOpen_univ.prod isOpen_Ioo).preimage continuous_subtype_val).mem_nhds hz
  have heq : ∀ᶠ w : U in 𝓝 x, restrictOpen0S (I := IC) 2 (V := U) Eext w = E w := by
    filter_upwards [hnear] with w hw
    ext v
    exact hEext w ⟨hw.1, hw.2.1.le, hw.2.2.le⟩ v
  calc
    tensor02CovDerivNormWith a ((2 : ℝ) • pullbackTensor02FieldCross D Eext)
        (cylinderReferenceMetric 0) (cylinderReferenceMetric 0) z =
        (Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2) *
          tensor02CovDerivNormWith a Eext unitCylinderMetric unitCylinderMetric (D z) := by
      rw [cylinderReference_zero_eq_inverse_axial]
      change tensor02CovDerivNormWith a ((2 : ℝ) • pullbackTensor02FieldCross D Eext)
        (scaleMetric 2 (by norm_num)
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross unitCylinderMetric D))
        (scaleMetric 2 (by norm_num)
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross unitCylinderMetric D)) z = _
      rw [tensor02CovDerivNormWith_smul_scaleMetric,
        tensor02CovDerivNormWith_pullbackTensor02FieldCross]
      norm_num
    _ = (Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2) *
        tensor02CovDerivNormWith a (restrictOpen0S (I := IC) 2 (V := U) Eext)
          (unitCylinderMetric.restrictOpen U) (unitCylinderMetric.restrictOpen U) x := by
      rw [tensor02CovDerivNormWith_restrictOpen0S]
    _ = (Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2) *
        tensor02CovDerivNormWith a E (unitCylinderMetric.restrictOpen U)
          (unitCylinderMetric.restrictOpen U) x := by
      rw [tensor02CovDerivNormWith_eq_of_eventuallyEq _ _ _ _ a x heq]
    _ = _ := by
      rw [tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm]

private theorem spatialNeckWitness_inverse_tensor
    (W : SpatialNeckWitness g yStar p eta)
    (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : F.source = spatialNeckBuffer eta)
    (hmap : ∀ z : spatialNeckBuffer eta, F z.val = W.embedding z)
    (Eext : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2)
    (hEext : ∀ x : spatialNeckBuffer eta, x.val ∈ univ ×ˢ Icc (-eta⁻¹) eta⁻¹ →
      ∀ v : Fin 2 → TangentSpace IC x,
        Eext x.val v =
          (metricTensorField W.normalizedMetric -
            metricTensorField (unitCylinderMetric.restrictOpen (spatialNeckBuffer eta))) x v)
    (z : Cylinder)
    (hz : cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z ∈ univ ×ˢ Icc (-eta⁻¹) eta⁻¹)
    (hzu : cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z ∈ spatialNeckBuffer eta)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel z) :
    (((2 : ℝ) • pullbackTensor02FieldCross
      (cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)) Eext) +
      metricTensorField (cylinderReferenceMetric 0)) z v =
      (scaleMetric (metricScalarAt g p) W.scalar_pos g).inner
        (((cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)).toPartialDiffeomorph.trans F) z)
        (mfderiv SpatialNeckCylinderModel I3
          ((cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)).toPartialDiffeomorph.trans F) z (v 0))
        (mfderiv SpatialNeckCylinderModel I3
          ((cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)).toPartialDiffeomorph.trans F) z (v 1)) := by
  let D := cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)
  let Phi := D.toPartialDiffeomorph.trans F
  let x : spatialNeckBuffer eta := ⟨D z, hzu⟩
  have hF := F.mdifferentiableAt (by simp) (by rw [hsource]; exact x.property)
  have hD := D.mdifferentiable (by simp) z
  have hcomp (w : TangentSpace SpatialNeckCylinderModel z) :
      mfderiv SpatialNeckCylinderModel I3 Phi z w =
        mfderiv SpatialNeckCylinderModel I3 F (D z)
          (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z w) :=
    mfderiv_comp_apply z hF hD w
  have hnormalized := W.normalized_inner x
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 0))
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 1))
  rw [spatialNeckScale_inv_sq g p W.scalar_pos] at hnormalized
  erw [spatialNeckWitness_embedding_deriv W F hsource hmap x
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 0)),
    spatialNeckWitness_embedding_deriv W F hsource hmap x
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 1))] at hnormalized
  have href := congrArg (fun h : SmoothRiemannianMetric IC Cylinder => h.inner z (v 0) (v 1))
    cylinderReference_zero_eq_inverse_axial
  rw [scaleMetric_inner, DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner] at href
  change 2 * pullbackTensor02FieldCross D Eext z v +
    (cylinderReferenceMetric 0).inner z (v 0) (v 1) =
    (scaleMetric (metricScalarAt g p) W.scalar_pos g).inner (Phi z)
      (mfderiv SpatialNeckCylinderModel I3 Phi z (v 0))
      (mfderiv SpatialNeckCylinderModel I3 Phi z (v 1))
  rw [pullbackTensor02FieldCross_apply]
  erw [hEext x hz (fun j => mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v j))]
  change 2 * (W.normalizedMetric.inner x
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 0))
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 1)) -
    unitCylinderMetric.inner (D z) (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 0))
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel D z (v 1))) + _ = _
  rw [hnormalized, href, scaleMetric_inner, show Phi z = W.embedding x from hmap x]
  erw [hcomp (v 0), hcomp (v 1)]
  ring

theorem _root_.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_spatialNeck
    (W : SpatialNeckWitness g yStar p eta) (heps : 0 < eps)
    (hsmall : eps < 1 / 11) (heta : eta ≤ eps) :
    ∃ nk : SpatialNeck g eps p,
      nk.center = yStar ∧
      nk.map.source =
        (cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)) ⁻¹' spatialNeckBuffer eta ∧
      ∀ z : Cylinder,
        ∀ hz : cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z ∈ spatialNeckBuffer eta,
          nk.map z = W.embedding ⟨cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity) z, hz⟩ := by
  classical
  let D := cylinderAxialScale (Real.sqrt 2)⁻¹ (by positivity)
  let U := spatialNeckBuffer eta
  let K : Set Cylinder := univ ×ˢ Icc (-eta⁻¹) eta⁻¹
  let V : Set Cylinder := univ ×ˢ Ioo (-eta⁻¹) eta⁻¹
  let A : Set Cylinder := univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hKU : K ⊆ U := by
    intro z hz
    change -eta⁻¹ - 1 < z.2 ∧ z.2 < eta⁻¹ + 1
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hVK : V ⊆ K := fun z hz => ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hinv : eps⁻¹ ≤ eta⁻¹ := inv_anti₀ W.epsilon_pos heta
  have hord : Nat.ceil eps⁻¹ ≤ Nat.ceil eta⁻¹ := Nat.ceil_le_ceil hinv
  have hcpos : 0 < (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  have hcle : (Real.sqrt (2 : ℝ))⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : 0 < Real.sqrt (2 : ℝ))).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hdomain (z : Cylinder) (hz : z ∈ A) : D z ∈ V := by
    have hlo := mul_lt_mul_of_pos_left hz.2.1 hcpos
    have hhi := mul_lt_mul_of_pos_left hz.2.2 hcpos
    have hprod := mul_le_mul_of_nonneg_right hcle (inv_nonneg.mpr heps.le)
    refine ⟨mem_univ _, ?_, ?_⟩ <;>
      dsimp only [D, cylinderAxialScale_apply] <;> nlinarith
  obtain ⟨F, hsource, hmap⟩ := spatialNeckWitness_partialDiffeomorph W
  let Phi := D.toPartialDiffeomorph.trans F
  have hPhiSource : Phi.source = D ⁻¹' U := by
    ext z
    change (z ∈ (univ : Set Cylinder) ∧ D z ∈ F.source) ↔ D z ∈ U
    rw [hsource]
    simp only [mem_univ, true_and]
    change D z ∈ (spatialNeckBuffer eta : Set _) ↔ D z ∈ (spatialNeckBuffer eta : Set _)
    rfl
  have hPhi (z : Cylinder) (hz : D z ∈ U) : Phi z = W.embedding ⟨D z, hz⟩ :=
    hmap ⟨D z, hz⟩
  let E : Tensor0SField (I := IC) (M := U) (n := ∞) 2 :=
    metricTensorField W.normalizedMetric - metricTensorField (unitCylinderMetric.restrictOpen U)
  obtain ⟨Eext, hEext⟩ := exists_tensor0SField_eqOn_openSubtype 2 U hK hKU E
  let T : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 :=
    (2 : ℝ) • pullbackTensor02FieldCross D Eext
  let P : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 :=
    T + metricTensorField (cylinderReferenceMetric 0)
  have hbound (a : ℕ) (ha : a ≤ Nat.ceil eps⁻¹) (z : Cylinder) (hz : z ∈ A) :
      tensor02CovDerivNormWith a T (cylinderReferenceMetric 0)
        (cylinderReferenceMetric 0) z ≤ eps := by
    rw [spatialNeckWitness_inverse_derivNorm W Eext hEext a z
      (hdomain z hz) (hKU (hVK (hdomain z hz)))]
    have hpow : (2 : ℝ)⁻¹ ^ (a + 2) ≤ (2 : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hsqrt : Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2 ≤ 1 := by
      norm_num at hpow
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ (a + 2)),
        Real.sqrt_nonneg ((2 : ℝ)⁻¹ ^ (a + 2))]
    have hmetric := W.metricDerivNorm_lt a (ha.trans hord)
      ⟨D z, hKU (hVK (hdomain z hz))⟩
      ⟨(hdomain z hz).2.1.le, (hdomain z hz).2.2.le⟩
    calc
      _ ≤ (Real.sqrt ((2 : ℝ)⁻¹ ^ (a + 2)) * 2) * eta :=
        mul_le_mul_of_nonneg_left hmetric.le (by positivity)
      _ ≤ eta := by nlinarith [W.epsilon_pos]
      _ ≤ eps := heta
  let cmp : MetricComparisonOn (fun _ => cylinderReferenceMetric 0)
      (fun _ => scaleMetric (metricScalarAt g p) W.scalar_pos g) Phi A {0}
      (Nat.ceil eps⁻¹) eps :=
    { pullback := fun _ => P
      pullback_eq := fun _ z hz v => spatialNeckWitness_inverse_tensor W F hsource hmap Eext hEext
        z (hVK (hdomain z hz)) (hKU (hVK (hdomain z hz))) v
      jet := fun b _ => if b = 0 then T else 0
      jet_zero := by
        intro s z v
        change T z v = T z v + (cylinderReferenceMetric 0).inner z (v 0) (v 1) -
          (cylinderReferenceMetric 0).inner z (v 0) (v 1)
        ring
      jet_succ := by
        intro b s _hs z _hz v
        simp only [ite_eq_right (Nat.add_one_ne_zero b)]
        change 0 = derivWithin (fun _ => (if b = 0 then T else 0) z v) ({0} : Set ℝ) s
        simp only [derivWithin_fun_const, Pi.zero_apply]
      equivalence := by
        intro s _hs z hz v
        apply tensor_apply_bounds_of_metricTensorErrorNorm_le P (cylinderReferenceMetric 0) _ v
        have hPT : P - metricTensorField (cylinderReferenceMetric 0) = T := by
          dsimp only [P]
          abel
        have hh := hbound 0 (by omega) z hz
        rw [← hPT] at hh
        exact hh
      close := by
        intro a b hab s _hs z hz
        by_cases hb : b = 0
        · simpa only [ite_eq_left hb] using hbound a (by omega) z hz
        · rw [ite_eq_right hb, tensor02CovDerivNormWith,
            tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
          simpa only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
            MetricFiberData.inner, map_zero, Real.sqrt_zero] using heps.le }
  refine ⟨{
    eps_pos := heps
    eps_small := hsmall
    Q_pos := W.scalar_pos
    cylinder := cylinderReference
    map := Phi
    center := yStar
    center_eq := ?_
    domain := ?_
    comparison := cmp }, rfl, hPhiSource, hPhi⟩
  · have hz : D (yStar, 0) ∈ U := by
      rw [cylinderAxialScale_central]
      exact (spatialNeckCentralPoint eta W.epsilon_pos yStar).property
    rw [hPhi (yStar, 0) hz]
    convert W.marked using 1
    apply congrArg W.embedding
    exact Subtype.ext (cylinderAxialScale_central _ _ _)
  · intro z hz
    rw [hPhiSource]
    exact hKU (hVK (hdomain z hz))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
