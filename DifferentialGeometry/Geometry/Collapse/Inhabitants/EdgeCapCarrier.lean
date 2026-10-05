import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapDistance
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallFlatCircle
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EuclideanProductCoordinates
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionNormalForm
import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelInputs
import DifferentialGeometry.Geometry.Comparison.LineSplitting

/-! Actual capped Edge metric, affine axis and canonical splitting coordinate. -/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open scoped Manifold ContDiff Topology InnerProductSpace

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier

def capExampleEpsilon : ℝ := smallFlatCircleScale / (2 * Real.pi * Real.sqrt 2)
theorem capExampleEpsilon_pos : 0 < capExampleEpsilon := by
  have hs := smallFlatCircleScale_pos
  have hp := Real.pi_pos
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact div_pos hs (mul_pos (mul_pos (by norm_num) hp) hr)

def capExampleMetric : SmoothRiemannianMetric (𝓡 3) E3 :=
  capThreeMetric capExampleEpsilon capExampleEpsilon_pos
local instance capExampleSigma : SigmaCompactSpace E3 := inferInstance
local instance capExampleMetricSpace : MetricSpace E3 := inducedMetricSpace capExampleMetric
local instance capExampleEDist : EDist E3 := capExampleMetricSpace.toEDist
local instance capExampleDist : Dist E3 := capExampleMetricSpace.toDist
local instance capExampleUniform : UniformSpace E3 := capExampleMetricSpace.toUniformSpace
local instance capExampleEMetric : PseudoEMetricSpace E3 :=
  capExampleMetricSpace.toPseudoEMetricSpace
local instance capExamplePseudo : PseudoMetricSpace E3 :=
  capExampleMetricSpace.toPseudoMetricSpace
local instance capExampleBundle : RiemannianBundle (TangentSpace (𝓡 3) : E3 → Type _) :=
  ⟨capExampleMetric.toRiemannianMetric⟩
local instance capExampleRiemannian : IsRiemannianManifold (𝓡 3) E3 :=
  inducedMetricSpace_isRiemannianManifold capExampleMetric
local instance capExampleContinuous :
    IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : E3 → Type _) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric capExampleMetric
local instance capExampleComplete : CompleteSpace E3 :=
  (capThreeComplete capExampleEpsilon capExampleEpsilon_pos).complete
local instance capExampleProper : ProperSpace E3 :=
  inducedMetricSpace_properSpace_of_riemannianMetricComplete
    (capThreeComplete capExampleEpsilon capExampleEpsilon_pos)
local instance capExampleDimension : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

theorem capExampleMetricNorm : IsMetricNorm capExampleMetric :=
  isMetricNorm_of_smoothRiemannianMetric capExampleMetric

def capExampleAxis (t : ℝ) : E3 := capProductCoordinates (t, 0)

theorem capExample_axis_edist (s t : ℝ) : edist (capExampleAxis s) (capExampleAxis t) =
    edist s t := by
  change riemannianEDistOf capExampleMetric (capExampleAxis s) (capExampleAxis t) = edist s t
  simp only [capExampleMetric, capThreeMetric, capExampleAxis,
    riemannianEDistOf_pullbackMetricCross, Diffeomorph.symm_apply_apply]
  rw [capProductMetric, riemannianEDistOf_prod_left]
  rw [show euclideanMetric (E := ℝ) = standardEuclideanMetric ℝ from rfl,
    riemannianEDistOf_standardEuclideanMetric]

theorem capExample_axis_isometry : Isometry capExampleAxis := capExample_axis_edist

theorem capExample_coord_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ capThreeCoord :=
  contMDiff_fst.comp capProductCoordinates.symm.contMDiff

theorem capExample_sectional (x : E3) : SectionalBoundedBelowAt capExampleMetric x 0 :=
  capThreeSectional capExampleEpsilon capExampleEpsilon_pos x


open DifferentialGeometry.Geometry.Operator

theorem capExample_product_grad (p : ℝ × E2) :
    gradientFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Prod.fst p =
      ((1 : ℝ), (0 : E2)) := by
  let U : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p := (1, 0)
  change gradFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Prod.fst p = U
  symm
  apply Connection.gradFun_unique
  intro v
  have hi : (capProductMetric capExampleEpsilon capExampleEpsilon_pos).inner p U v =
      U.1 * v.1 + (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner p.2 U.2 v.2 :=
    (capThree_physical_inner capExampleEpsilon capExampleEpsilon_pos p U v).symm.trans
      (capThree_physical_product capExampleEpsilon capExampleEpsilon_pos p U v)
  have hd : @Eq ℝ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) Prod.fst p v) v.1 := by
    rw [mfderiv_fst]
    rfl
  have hz : (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner p.2 U.2 v.2 = 0 := by
    change (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner p.2
      (0 : TangentSpace (𝓡 2) p.2) v.2 = 0
    exact ((scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).symm p.2 0 v.2).trans
      (((scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner p.2 v.2).map_zero)
  have hv : @Eq ℝ (U.1 * v.1 +
      (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner p.2 U.2 v.2) v.1 :=
    (congrArg (fun a : ℝ => U.1 * v.1 + a) hz).trans (by simp [U])
  exact hi.trans (hv.trans hd.symm)

theorem capExample_coord_hess (x : E3) : hessFun capExampleMetric capThreeCoord x = 0 := by
  ext v w
  let f : C^∞⟮𝓘(ℝ, ℝ).prod (𝓡 2), ℝ × E2; ℝ⟯ := ⟨Prod.fst, contMDiff_fst⟩
  have h := hessFun_pullbackCross
    (capProductMetric capExampleEpsilon capExampleEpsilon_pos)
    capProductCoordinates.symm f x v w
  change hessFun capExampleMetric capThreeCoord x v w = _ at h
  have hzero := hessFun_euclideanProduct_coordinate
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
    (ContinuousLinearMap.id ℝ ℝ) (capProductCoordinates.symm x)
  change hessFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Prod.fst
    (capProductCoordinates.symm x) = 0 at hzero
  rw [h]
  change (hessFun (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Prod.fst
    (capProductCoordinates.symm x)) _ _ = _
  rw [hzero]
  rfl

theorem capExample_coord_unit (x : E3) :
    capExampleMetric.inner x (gradientFun capExampleMetric capThreeCoord x)
      (gradientFun capExampleMetric capThreeCoord x) = 1 := by
  let Φ := capProductCoordinates.symm
  let L := Φ.mfderivToContinuousLinearEquiv (by simp) x
  let U : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) (Φ x) := (1, 0)
  have hL : mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Φ x = L.toContinuousLinearMap :=
    (Φ.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)).symm
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : (ℝ × E2) → ℝ) := contMDiff_fst
  have hg := gradientFun_pullbackCross
    (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Φ Prod.fst x
    (hf.mdifferentiableAt (by decide))
  have hgrad : gradientFun capExampleMetric capThreeCoord x = L.symm U := by
    rw [capExample_product_grad] at hg
    change gradientFun capExampleMetric capThreeCoord x = L.symm U at hg
    exact hg
  rw [hgrad]
  change (Diffeomorph.pullbackMetricCross
    (capProductMetric capExampleEpsilon capExampleEpsilon_pos) Φ).inner x
      (L.symm U) (L.symm U) = 1
  rw [Diffeomorph.pullbackMetricCross_inner, hL]
  change (capProductMetric capExampleEpsilon capExampleEpsilon_pos).inner (Φ x)
    (L (L.symm U)) (L (L.symm U)) = 1
  rw [L.apply_symm_apply U]
  have hi : (capProductMetric capExampleEpsilon capExampleEpsilon_pos).inner (Φ x) U U =
      U.1 * U.1 + (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner
        (Φ x).2 U.2 U.2 :=
    (capThree_physical_inner capExampleEpsilon capExampleEpsilon_pos (Φ x) U U).symm.trans
      (capThree_physical_product capExampleEpsilon capExampleEpsilon_pos (Φ x) U U)
  rw [hi]
  change (1 : ℝ) * 1 +
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner (Φ x).2 0 0 = 1
  have hz := ((scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner (Φ x).2
    (0 : TangentSpace (𝓡 2) (Φ x).2)).map_zero
  exact (congrArg (fun a : ℝ => 1 * 1 + a) hz).trans (by norm_num)

theorem capExample_axis_nearest (x : E3) :
    dist x (capExampleAxis (capThreeCoord x)) =
      capExampleEpsilon * ‖(capProductCoordinates.symm x).2‖ := by
  have he : riemannianEDistOf capExampleMetric x (capExampleAxis (capThreeCoord x)) =
      ENNReal.ofReal (capExampleEpsilon * ‖(capProductCoordinates.symm x).2‖) := by
    simp only [capExampleMetric, capThreeMetric, capExampleAxis, capThreeCoord,
      riemannianEDistOf_pullbackMetricCross, Diffeomorph.symm_apply_apply]
    rw [capProductMetric, riemannianEDistOf_prod_right, riemannianEDistOf_comm,
      scaledCap_edist_zero]
  rw [inducedMetricSpace_hmetric capExampleMetric] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_ofReal (mul_nonneg capExampleEpsilon_pos.le (norm_nonneg _))] at hr
  exact hr

theorem capExample_axis_infDist (x : E3) : Metric.infDist x capThreeAxis =
    capExampleEpsilon * ‖(capProductCoordinates.symm x).2‖ := by
  have h := capThree_axis_infDist capExampleEpsilon capExampleEpsilon_pos x
  change Metric.infDist x capThreeAxis = _ at h
  exact h

theorem capExample_axis_mem (t : ℝ) : capExampleAxis t ∈ capThreeAxis := by
  simp only [capExampleAxis, capThreeAxis, capProductAxis, Set.mem_preimage,
    Set.mem_ofPred_eq, Diffeomorph.symm_apply_apply]

theorem capExample_fourPoint : Comparison.Toponogov.fourPointComparison 0 (univ : Set E3) :=
  (model_lcp04_clauses_of_sectional_nonneg capExampleMetric capExampleMetricNorm
    capExample_sectional).2.1

theorem capExample_segments (x y : E3) : ∃ f : Icc (0 : ℝ) 1 → E3,
    Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t :=
  (model_lcp04_clauses_of_sectional_nonneg capExampleMetric capExampleMetricNorm
    capExample_sectional).2.2 x y

theorem capExample_canonical_coord (x : E3) :
    capThreeCoord x = Comparison.Toponogov.lineCoordinate capExampleAxis x := by
  have hp := Comparison.Toponogov.sq_dist_isometry_line_projection
    capExample_fourPoint capExample_axis_isometry x (capThreeCoord x)
  have hm := Metric.infDist_le_dist_of_mem (x := x)
    (capExample_axis_mem (Comparison.Toponogov.lineCoordinate capExampleAxis x))
  rw [capExample_axis_infDist] at hm
  rw [capExample_axis_nearest] at hp
  have hr : 0 ≤ capExampleEpsilon * ‖(capProductCoordinates.symm x).2‖ :=
    mul_nonneg capExampleEpsilon_pos.le (norm_nonneg _)
  have hd : 0 ≤ dist x
      (capExampleAxis (Comparison.Toponogov.lineCoordinate capExampleAxis x)) := dist_nonneg
  have hz : (capThreeCoord x - Comparison.Toponogov.lineCoordinate capExampleAxis x) ^ 2 = 0 := by
    nlinarith [sq_nonneg
      (capThreeCoord x - Comparison.Toponogov.lineCoordinate capExampleAxis x)]
  have hzero := (sq_eq_zero_iff).mp hz
  exact sub_eq_zero.mp hzero

end DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
