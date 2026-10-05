import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartApplications
import DifferentialGeometry.Geometry.Comparison.LineSplitting
import DifferentialGeometry.Geometry.Curvature.Cylinder.ProductMetric
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Product
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds
import Mathlib.Analysis.Normed.Module.Connected

/-!
The round sphere cylinder carries its actual intrinsic product metric and a genuine exact
rank-one metric splitting. Its bounded factor supplies a nondegenerate slim chart.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
open GC.MetricGeometry
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "M" => S2 × ℝ
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local instance sphereDimension : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩
local instance cylinderDimension : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  ⟨by simp⟩
local instance sphereCompact : CompactSpace S2 :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
local instance sphereConnected : ConnectedSpace S2 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
def slimSphereMetric : SmoothRiemannianMetric IC M :=
  (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prod (euclideanMetric (E := ℝ))
abbrev slimSphereMetricSpace : MetricSpace M := inducedMetricSpace slimSphereMetric

local instance intrinsicMetric : MetricSpace M := slimSphereMetricSpace
local instance intrinsicUniform : UniformSpace M := intrinsicMetric.toUniformSpace
local instance intrinsicEMetric : PseudoEMetricSpace M := intrinsicMetric.toPseudoEMetricSpace
local instance intrinsicPseudoMetric : PseudoMetricSpace M := intrinsicMetric.toPseudoMetricSpace
abbrev slimSphereRiemannianBundle : Bundle.RiemannianBundle (fun x : M => TangentSpace IC x) :=
  ⟨slimSphereMetric.toRiemannianMetric⟩

local instance intrinsicBundle : Bundle.RiemannianBundle (fun x : M => TangentSpace IC x) :=
  slimSphereRiemannianBundle
theorem slimSphereMetricNorm : IsMetricNorm slimSphereMetric :=
  isMetricNorm_of_smoothRiemannianMetric slimSphereMetric
local instance cylinderRiemannian : IsRiemannianManifold IC M :=
  inducedMetricSpace_isRiemannianManifold slimSphereMetric
local instance cylinderContinuous :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2) × ℝ)
      (fun x : M => TangentSpace IC x) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric slimSphereMetric
local instance cylinderComplete : CompleteSpace M :=
  ((RiemannianMetricComplete.of_compact
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
      (euclideanMetric_complete (E := ℝ))).complete

theorem slimSphereMetric_sectional_nonneg (x : M) :
    SectionalBoundedBelowAt slimSphereMetric x 0 := by
  intro v w
  rw [zero_mul]
  let g := roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  have hnum : Curvature.metricRm04StandardAt slimSphereMetric x v w w v =
      Curvature.metricRm04StandardAt g x.1 v.1 w.1 w.1 v.1 :=
    (rm04_eq_inner_riem slimSphereMetric x v w w v).trans
      ((Curvature.inner_riemannOp_cylinderMetric g x v v w w).trans
        (rm04_eq_inner_riem g x.1 v.1 w.1 w.1 v.1).symm)
  have hval := roundMetric_sec_value x.1 v.1 w.1
  have hden := sectionalCurvatureDenominator_nonneg g x.1 v.1 w.1
  change 0 ≤ g.inner x.1 v.1 v.1 * g.inner x.1 w.1 w.1 - (g.inner x.1 v.1 w.1) ^ 2 at hden
  have hresult : 0 ≤ Curvature.metricRm04StandardAt g x.1 v.1 w.1 w.1 v.1 := by
    nlinarith only [hval, hden]
  exact hnum.symm ▸ hresult

theorem exists_slimSphere_curvature_bounds (K : ℕ) :
    ∃ A : ℝ, ∀ k ≤ K, ∀ x : M,
      CheegerGromovCompactness.curvDerivNorm k slimSphereMetric x ≤ A := by
  obtain ⟨A, hA⟩ := CheegerGromovCompactness.exists_curvDerivNorm_bound_of_isCompact
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) K
    (isCompact_univ : IsCompact (univ : Set S2))
  refine ⟨A, fun k hk x => ?_⟩
  rw [slimSphereMetric,
    PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_prod_real]
  exact hA k hk x.1 (mem_univ x.1)

def slimSpherePole : S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp [PiLp.norm_single]⟩

def slimSphereLine (t : ℝ) : M := (slimSpherePole, t)

private theorem slimSphereLine_isometry : Isometry slimSphereLine := by
  apply Isometry.of_dist_eq
  intro s t
  change (riemannianEDistOf slimSphereMetric (slimSpherePole, s) (slimSpherePole, t)).toReal =
    dist s t
  rw [slimSphereMetric, riemannianEDistOf_prod_right]
  change (riemannianEDist 𝓘(ℝ, ℝ) s t).toReal = dist s t
  rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem slimSphere_factor_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : S2,
      riemannianEDistOf (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) a b ≤
        ENNReal.ofReal D := by
  let sphereIntrinsic := inducedMetricSpace
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  let sphereIntrinsicPseudo : PseudoMetricSpace S2 := sphereIntrinsic.toPseudoMetricSpace
  let sphereIntrinsicEMetric : PseudoEMetricSpace S2 := sphereIntrinsic.toPseudoEMetricSpace
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (isCompact_univ : IsCompact (univ : Set S2)).isBounded
  refine ⟨max D 0, le_max_right D 0, ?_⟩
  intro a b
  have hbound := (hD (mem_univ a) (mem_univ b)).trans (le_max_left D 0)
  exact (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) a b)).symm.trans_le
      (ENNReal.ofReal_le_ofReal hbound)

private theorem slimSphere_dist_upper (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ a b : S2,
      riemannianEDistOf (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) a b ≤
        ENNReal.ofReal D) (x y : M) :
    dist x y ≤ D + |x.2 - y.2| := by
  have htri := riemannianEDistOf_triangle slimSphereMetric x (y.1, x.2) y
  rw [slimSphereMetric, riemannianEDistOf_prod_left, riemannianEDistOf_prod_right] at htri
  have hr : riemannianEDistOf (euclideanMetric (E := ℝ)) x.2 y.2 =
      ENNReal.ofReal |x.2 - y.2| := by
    change riemannianEDist 𝓘(ℝ, ℝ) x.2 y.2 = _
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), edist_dist, Real.dist_eq]
  rw [hr] at htri
  have hd := htri.trans (add_le_add (hb x.1 y.1) le_rfl)
  rw [← ENNReal.ofReal_add hD (abs_nonneg _)] at hd
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  change (riemannianEDistOf slimSphereMetric x y).toReal ≤ _
  exact hreal.trans_eq (ENNReal.toReal_ofReal (add_nonneg hD (abs_nonneg _)))

theorem exists_slimSphereChart :
    ∃ Δ β : ℝ, 1 ≤ Δ ∧ 0 < β ∧ β < 1 ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (y : Y) (p : M) (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y)) β),
        (∀ a b : Y, dist a b ≤ 10 ^ 3 * Δ) ∧
        Nonempty (SlimChart slimSphereMetric slimSphereMetricNorm Δ (1 / 100) α) := by
  obtain ⟨hproper, hcomp, hsegments⟩ := model_lcp04_clauses_of_sectional_nonneg
    slimSphereMetric slimSphereMetricNorm slimSphereMetric_sectional_nonneg
  let cylinderProper : ProperSpace M := hproper
  obtain ⟨D, hD, hb⟩ := slimSphere_factor_bound
  let Y := {x : M // Comparison.Toponogov.lineCoordinate slimSphereLine x = 0}
  let y : Y := ⟨slimSphereLine 0,
    Comparison.Toponogov.lineCoordinate_apply_isometry slimSphereLine_isometry 0⟩
  let e := Comparison.Toponogov.lineSplitting hcomp slimSphereLine_isometry hsegments
  have he : e (slimSphereLine 0) = WithLp.toLp 2 ((0 : ℝ), y) :=
    Comparison.Toponogov.lineSplitting_apply_line hcomp slimSphereLine_isometry hsegments 0
  have hheight (a : Y) : |a.val.2| ≤ D := by
    have hcoord := (Comparison.Toponogov.lipschitzWith_lineCoordinate hcomp
      slimSphereLine_isometry).dist_le_mul a.val (slimSphereLine a.val.2)
    rw [a.property, Comparison.Toponogov.lineCoordinate_apply_isometry
      slimSphereLine_isometry, Real.dist_eq, zero_sub, abs_neg] at hcoord
    have hupper := slimSphere_dist_upper D hD hb a.val (slimSphereLine a.val.2)
    simp only [slimSphereLine, sub_self, abs_zero, add_zero] at hupper
    simp only [NNReal.coe_one, one_mul] at hcoord
    exact hcoord.trans hupper
  have hybound (a b : Y) : dist a b ≤ 3 * D := by
    have hupper := slimSphere_dist_upper D hD hb a.val b.val
    have hab := abs_sub_le a.val.2 0 b.val.2
    rw [sub_zero, zero_sub, abs_neg] at hab
    change dist a.val b.val ≤ _
    linarith [hheight a, hheight b]
  let Δ := max 1 (3 * D)
  have hΔ : 1 ≤ Δ := le_max_left _ _
  have hfactor (a b : Y) : dist a b ≤ 10 ^ 3 * Δ := by
    have hDΔ : 3 * D ≤ Δ := le_max_right _ _
    nlinarith [hybound a b]
  obtain ⟨β₀, hβ₀, hchart⟩ := exists_slimChart hΔ
    (by norm_num : 0 < (1 / 100 : ℝ)) le_rfl
  let β := min β₀ 1 / 2
  have hβ : 0 < β := half_pos (lt_min hβ₀ zero_lt_one)
  have hβlt : β < β₀ := (half_lt_self (lt_min hβ₀ zero_lt_one)).trans_le (min_le_left _ _)
  have hβone : β < 1 := (half_lt_self (lt_min hβ₀ zero_lt_one)).trans_le (min_le_right _ _)
  let α : KleinerLottApprox (slimSphereLine 0) (WithLp.toLp 2 ((0 : ℝ), y)) β :=
    { error_pos := hβ
      error_lt_one := hβone
      toFun := e
      basepoint := he
      distortion := fun a ha b hbb => by
        rw [e.dist_eq, sub_self, abs_zero]
        exact hβ.le
      coverage := fun a ha => by
        have hrad : dist (e.symm a) (slimSphereLine 0) < β⁻¹ := by
          rw [← e.dist_eq, e.apply_symm_apply, he]
          linarith
        have hmem : a ∈ e '' ball (slimSphereLine 0) β⁻¹ :=
          ⟨e.symm a, hrad, e.apply_symm_apply a⟩
        exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using hβ.le) }
  let cylinderBoundaryless : (IC).Boundaryless :=
    ModelWithCorners.range_eq_univ_prod (𝓡 2) 𝓘(ℝ, ℝ)
  have hc := hchart β hβ hβlt (EuclideanSpace ℝ (Fin 2) × ℝ)
    (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) IC M slimSphereMetric slimSphereMetricNorm Y
    (slimSphereLine 0) y α hfactor (fun a ha => by
      have hs := slimSphereMetric_sectional_nonneg a
      intro v w
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg β))
        (sectionalCurvatureDenominator_nonneg slimSphereMetric a v w)).trans
          (by simpa only [zero_mul] using hs v w))
  exact ⟨Δ, β, hΔ, hβ, hβone, Y, inferInstance, y, slimSphereLine 0, α, hfactor, hc⟩

end DifferentialGeometry.Geometry.Collapse
