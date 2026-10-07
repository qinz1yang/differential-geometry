import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingFiniteJet
import DifferentialGeometry.Geometry.Hyperbolic.CuspWarpedCurvature
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectionalDerivatives
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectionalNorm
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Curvature.Bounds.MetricPerturbation
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCovariantJets
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open GC.Endpoint Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Collapse

local instance cuspPickCircleHausdorff : T2Space Circle := inferInstance

local instance cuspPickTorusHausdorff : T2Space Torus :=
  inferInstanceAs (T2Space (Circle × Circle))

local instance cuspPickHalfSpaceHausdorff : T2Space (EuclideanHalfSpace 1) :=
  inferInstanceAs (T2Space {x : EuclideanSpace ℝ (Fin 1) | 0 ≤ x 0})

local instance cuspPickHalfSpaceProdHausdorff : T2Space CuspHalfSpace :=
  inferInstanceAs (T2Space (Torus × EuclideanHalfSpace 1))

universe u

private local instance : SigmaCompactSpace (EuclideanHalfSpace 1) :=
  IsClosed.sigmaCompactSpace
    (isClosed_Ici.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous)

private abbrev fixedCuspInterior : Opens CuspHalfSpace :=
  Manifold.intrinsicInterior halfCollarModel ∞ (by simp)

private local instance : SigmaCompactSpace fixedCuspInterior :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen halfCollarModel fixedCuspInterior.isOpen)

private theorem cusp_reference_derivative_norm_le_one
    (H : HyperbolicCusp) (j : ℕ) (p : CuspHalfSpace) :
    curvatureDerivativeNorm H.metric j p ≤ 1 := by
  cases j with
  | zero =>
      have hdim : Module.finrank ℝ (TangentSpace halfCollarModel p) = 3 := by
        change Module.finrank ℝ
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
            EuclideanSpace ℝ (Fin 1)) = 3
        simp
      exact curvatureDerivativeNorm_zero_le_one_of_constant_sectional_neg_quarter
        H.metric p hdim (H.metricRm04StandardAt_eq_neg_quarter_gram p)
  | succ j =>
      have hzero (k : ℕ) : iterCov H.metric 4 (metricRm04 H.metric) (k + 1) = 0 := by
        induction k with
        | zero =>
            change covStep H.metric 4 (metricRm04 H.metric) = 0
            exact covStep_metricRm04_eq_zero_of_constant_sectional H.metric
              (-(1 / 4 : ℝ)) H.metricRm04StandardAt_eq_neg_quarter_gram
        | succ k ih => rw [iterCov_succ, ih, covStep_zero]
      have hz : iterCov H.metric 4 (metricRm04 H.metric) (j + 1) p = 0 := by
        rw [hzero j]
        rfl
      simp only [curvatureDerivativeNorm, tensor0SFiberNorm,
        iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov]
      rw [hz, (normSq0S_eq_zero_iff H.metric p (4 + (j + 1)) 0).mpr rfl,
        Real.sqrt_zero]
      norm_num

private theorem exists_same_carrier_pullback_metric
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (H : HyperbolicCusp)
    (Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier ∞)
    {p : CuspHalfSpace} (hp : p ∈ Φ.source) :
    ∃ (q : SmoothRiemannianMetric halfCollarModel CuspHalfSpace)
      (O : Opens CuspHalfSpace),
      p ∈ O ∧ (O : Set CuspHalfSpace) ⊆ Φ.source ∧
      ∀ z ∈ O, ∀ a b : TangentSpace halfCollarModel z,
        q.inner z a b = g.inner (Φ z)
          (mfderiv halfCollarModel W.model Φ z a)
          (mfderiv halfCollarModel W.model Φ z b) := by
  have hK : ({Φ p} : Set W.Carrier) ⊆ Φ.symm.source := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Φ.map_source' hp
  obtain ⟨q, U, hKU, _, hmetric, _⟩ :=
    Φ.symm.exists_metric_preserving_on_neighborhood_of_is_compact
      g H.metric isCompact_singleton hK
  let O : Opens CuspHalfSpace :=
    ⟨Φ.source ∩ (Φ : CuspHalfSpace → W.Carrier) ⁻¹' U,
      Φ.toOpenPartialHomeomorph.isOpen_inter_preimage U.isOpen⟩
  refine ⟨q, O, ⟨hp, hKU (by simp)⟩, fun _ hz => hz.1, ?_⟩
  intro z hz a b
  have hzsource : z ∈ Φ.source := hz.1
  have hzd := Φ.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hzsource
  have hyd := Φ.symm.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    (Φ.map_source' hzsource)
  have heq : (Φ.symm : W.Carrier → CuspHalfSpace) ∘ Φ =ᶠ[𝓝 z] id := by
    filter_upwards [Φ.open_source.mem_nhds hzsource] with y hy
    exact Φ.left_inv' hy
  have hinverse (v : TangentSpace halfCollarModel z) :
      mfderiv W.model halfCollarModel Φ.symm (Φ z)
        (mfderiv halfCollarModel W.model Φ z v) = v := by
    have hc := mfderiv_comp_apply z hyd hzd v
    rw [heq.mfderiv_eq, mfderiv_id] at hc
    exact hc.symm
  have hg := hmetric (Φ z) hz.2 (mfderiv halfCollarModel W.model Φ z a)
    (mfderiv halfCollarModel W.model Φ z b)
  rw [hinverse a, hinverse b] at hg
  exact (congrArg (fun y : CuspHalfSpace => q.inner y a b)
    (Φ.left_inv' hzsource)).symm.trans hg.symm

private theorem curvatureDerivativeNorm_eq_of_local_pullback
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (q : SmoothRiemannianMetric halfCollarModel CuspHalfSpace)
    (Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier ∞)
    (O : Opens CuspHalfSpace) (hO : (O : Set CuspHalfSpace) ⊆ Φ.source)
    (hmetric : ∀ z ∈ O, ∀ a b : TangentSpace halfCollarModel z,
      q.inner z a b = g.inner (Φ z)
        (mfderiv halfCollarModel W.model Φ z a)
        (mfderiv halfCollarModel W.model Φ z b))
    (j : ℕ) (p : O) :
    curvatureDerivativeNorm q j p.val = curvatureDerivativeNorm g j (Φ p.val) := by
  let : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen halfCollarModel O.isOpen)
  let V : Opens W.Carrier :=
    ⟨(Φ : CuspHalfSpace → W.Carrier) '' (O : Set CuspHalfSpace), image_opens_isOpen Φ hO⟩
  let D : Diffeomorph halfCollarModel W.model O V ∞ := Φ.toOpensDiffeo hO
  have hDmetric (z : O) (a b : TangentSpace halfCollarModel z) :
      (q.restrictOpen O).inner z a b = (g.restrictOpen V).inner (D z)
        (mfderiv halfCollarModel W.model D z a)
        (mfderiv halfCollarModel W.model D z b) := by
    change q.inner z.val a b = g.inner (Φ z.val)
      (mfderiv halfCollarModel W.model (Φ.toOpensDiffeo hO) z a)
      (mfderiv halfCollarModel W.model (Φ.toOpensDiffeo hO) z b)
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact hmetric z.val z.property a b
  have hn := curvatureDerivativeNorm_of_injective_local_isometry
    (q.restrictOpen O) (g.restrictOpen V) D D.isLocalDiffeomorph D.injective hDmetric j p
  rw [curvatureDerivativeNorm_restrictOpen, curvatureDerivativeNorm_restrictOpen] at hn
  exact hn

/-- A single constant bounds the original target metric's curvature derivatives
through order `K` on every positive-height cusp image. Only the actual finite
map jets through `K+3` and metric-error derivatives through `K+2` are needed. -/
theorem exists_bound_curvatureDerivativeNorm_of_cuspEmbedding (K : ℕ) :
    ∃ C > 0, ∀ (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier)
      {L : ℕ} {δ : ℝ} {X : Set W.Carrier}
      (e : CuspEmbedding W g L δ X),
      K + 2 ≤ L → δ ≤ 1 / 2 →
      ∀ j : ℕ, j ≤ K → ∀ p ∈ cuspDomain, 0 < p.2.val 0 →
        curvatureDerivativeNorm g j (e.toFun p) ≤ C := by
  classical
  choose B hB hbound using fun j : ℕ =>
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_error
      (I := halfCollarModel) (M := fixedCuspInterior) j (1 / 2 : ℝ) 1 (by norm_num)
  let C := 1 + ∑ i ∈ Finset.range (K + 1), B i
  have hsum : 0 ≤ ∑ i ∈ Finset.range (K + 1), B i :=
    Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro W g L δ X e hL hδ j hj p hp hpos
  have hpint : halfCollarModel.IsInteriorPoint p := by
    change p ∈ (torusModel.prod (𝓡∂ 1)).interior (Torus × EuclideanHalfSpace 1)
    rw [ModelWithCorners.interior_prod]
    refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
    change (𝓡∂ 1).IsInteriorPoint p.2
    simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply,
      interior_range_modelWithCornersEuclideanHalfSpace, mem_setOf_eq,
      modelWithCornersEuclideanHalfSpace_apply] using hpos
  have hepint : W.model.IsInteriorPoint (e.toFun p) := by
    rw [W.model.isInteriorPoint_iff_not_isBoundaryPoint]
    intro hb
    exact (ne_of_gt hpos) ((e.boundary_preimage hp).mp hb)
  obtain ⟨Φ, hpΦ, _, _, hΦp, _, hΦjets⟩ :=
    e.exists_partialDiffeomorph_eq_finiteJet hp hpos
  obtain ⟨q, O, hpO, hO, hmetric⟩ :=
    exists_same_carrier_pullback_metric g e.cusp Φ hpΦ
  have hdomain : IsOpen cuspDomain := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hf : ContMDiffAt halfCollarModel W.model (j + 2 + 1) e.toFun p :=
    (e.contMDiffOn.contMDiffAt (hdomain.mem_nhds hp)).of_le
      (by exact_mod_cast (show j + 2 + 1 ≤ L + 1 by omega))
  have hΦ : ContMDiffAt halfCollarModel W.model (j + 2 + 1) Φ p :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hpΦ)).of_le (by simp)
  have hgerm : ∀ᶠ z in 𝓝 p, q.inner z = localPullInner g Φ z := by
    filter_upwards [O.isOpen.mem_nhds hpO] with z hz
    ext a b
    exact hmetric z hz a b
  have herror (k : ℕ) (hk : k ≤ j + 2) :
      metricDerivNorm k q e.cusp.metric e.cusp.metric p ≤ 1 / 2 := by
    rw [metricDerivNorm_eq_raw_pullbackError_of_map_jets (n := j + 2)
      g e.cusp.metric q hpint hepint hΦp.symm hf hΦ
      (fun i hi => (hΦjets i (by omega)).symm) hgerm k hk]
    exact (e.metric_error k (by omega) p hp).trans hδ
  let pP : fixedCuspInterior := ⟨p, hpint⟩
  let G := e.cusp.metric.restrictOpen fixedCuspInterior
  let qP := q.restrictOpen fixedCuspInterior
  have hsmall (k : ℕ) (hk : k ≤ j + 2) : metricDerivNorm k qP G G pP ≤ 1 / 2 := by
    dsimp only [qP, G]
    rw [metricDerivNorm_restrictOpen]
    exact herror k hk
  have hreference : ∀ s ≤ j, Real.sqrt (normSq0S G pP (4 + s)
      (iterCov G 4 (metricRm04 G) s pP)) ≤ 1 := by
    intro s _
    have hc : curvatureDerivativeNorm G s pP ≤ 1 := by
      dsimp only [G]
      rw [curvatureDerivativeNorm_restrictOpen]
      exact cusp_reference_derivative_norm_le_one e.cusp s p
    simpa only [curvatureDerivativeNorm, tensor0SFiberNorm,
      iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov] using hc
  have hq : curvatureDerivativeNorm q j p ≤ B j := by
    have hb : curvatureDerivativeNorm qP j pP ≤ B j := by
      simpa only [curvatureDerivativeNorm, tensor0SFiberNorm,
        iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov] using
        hbound j G qP pP hsmall hreference
    dsimp only [qP] at hb
    rwa [curvatureDerivativeNorm_restrictOpen] at hb
  have htransport := curvatureDerivativeNorm_eq_of_local_pullback
    g q Φ O hO hmetric j (⟨p, hpO⟩ : O)
  rw [hΦp] at htransport
  have hBj : B j ≤ C := by
    have hle : B j ≤ ∑ i ∈ Finset.range (K + 1), B i :=
      Finset.single_le_sum (fun i _ => (hB i).le) (Finset.mem_range.mpr (by omega))
    dsimp only [C]
    linarith
  calc
    curvatureDerivativeNorm g j (e.toFun p) = curvatureDerivativeNorm q j p :=
      htransport.symm
    _ ≤ C := hq.trans hBj

end DifferentialGeometry.Geometry.Collapse
