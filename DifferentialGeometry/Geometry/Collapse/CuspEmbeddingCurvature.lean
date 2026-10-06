import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingFiniteJet
import DifferentialGeometry.Geometry.Hyperbolic.CuspWarpedCurvature
import DifferentialGeometry.Geometry.Curvature.ConstantSectional
import DifferentialGeometry.Geometry.Curvature.NegativeSectionalStability
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCovariantJets
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle GC.Endpoint Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

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

private theorem exists_same_carrier_pullback_metric
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (H : HyperbolicCusp)
    (Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier ∞)
    {p : CuspHalfSpace} (hp : p ∈ Φ.source) :
    ∃ (q : SmoothRiemannianMetric halfCollarModel CuspHalfSpace)
      (O : TopologicalSpace.Opens CuspHalfSpace),
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
  let O : TopologicalSpace.Opens CuspHalfSpace :=
    ⟨Φ.source ∩ (Φ : CuspHalfSpace → W.Carrier) ⁻¹' U,
      Φ.toOpenPartialHomeomorph.isOpen_inter_preimage U.isOpen⟩
  refine ⟨q, O, ⟨hp, hKU (by simp)⟩, fun _ hz => hz.1, ?_⟩
  intro z hz a b
  have hzsource : z ∈ Φ.source := hz.1
  have hzd : MDifferentiableAt halfCollarModel W.model Φ z :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds hzsource)).mdifferentiableAt (by simp)
  have hyd : MDifferentiableAt W.model halfCollarModel Φ.symm (Φ z) :=
    (Φ.contMDiffOn_invFun.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source' hzsource))).mdifferentiableAt (by simp)
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

/-- Small order-two raw errors against the exact cusp metric keep a reference-orthonormal
plane below `-1/8`; this is the interior-restriction half of the positive-height estimate. -/
private theorem cusp_metricRm04_lt_neg_one_eighth_of_small_errors
    (H : HyperbolicCusp) (q : SmoothRiemannianMetric halfCollarModel CuspHalfSpace)
    {δ : ℝ} (hδ : δ ≤ 1 / 10000) (p : CuspHalfSpace)
    (hpint : halfCollarModel.IsInteriorPoint p)
    (herror : ∀ k ≤ 2, metricDerivNorm k q H.metric H.metric p ≤ δ)
    (u v : TangentSpace halfCollarModel p)
    (hu : H.metric.inner p u u = 1) (hv : H.metric.inner p v v = 1)
    (huv : H.metric.inner p u v = 0) :
    metricRm04StandardAt q p u v v u <
      -(1 / 8 : ℝ) * (q.inner p u u * q.inner p v v - q.inner p u v ^ 2) := by
  let P := Manifold.intrinsicInterior halfCollarModel ∞ (by simp) (M := CuspHalfSpace)
  let : SigmaCompactSpace P := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen halfCollarModel P.isOpen)
  let pP : P := ⟨p, hpint⟩
  let G := H.metric.restrictOpen P
  let qP := q.restrictOpen P
  have hsmall (k : ℕ) (hk : k ≤ 2) : metricDerivNorm k qP G G pP ≤ δ := by
    dsimp only [qP, G]
    rw [metricDerivNorm_restrictOpen]
    exact herror k hk
  have hunitU : G.inner pP u u = 1 := hu
  have hunitV : G.inner pP v v = 1 := hv
  have horth : G.inner pP u v = 0 := huv
  have hreference (a b : TangentSpace halfCollarModel pP) :
      metricRm04StandardAt G pP a b b a =
        -(1 / 4 : ℝ) * (G.inner pP a a * G.inner pP b b - G.inner pP a b ^ 2) := by
    dsimp only [G]
    rw [metricRm04StandardAt_restrictOpen]
    simp only [mfderiv_subtype_val_apply, SmoothRiemannianMetric.restrictOpen_inner]
    exact H.metricRm04StandardAt_eq_neg_quarter_gram p a b
  have hcurv : metricRm04StandardAt G pP u v v u ≤ -(1 / 4 : ℝ) := by
    refine (hreference u v).le.trans ?_
    rw [hunitU, hunitV, horth]
    norm_num
  have hmodel : Real.sqrt (G.inner pP (riemannOp (LeviCivita G) pP u v v)
      (riemannOp (LeviCivita G) pP u v v)) ≤ 2 := by
    refine (sqrt_inner_riemannOp_self_eq_abs_of_constant_sectional_numerator
      G pP (-(1 / 4 : ℝ)) hreference u v hunitU hunitV horth).trans_le ?_
    norm_num
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hbudget : δ * (360 + (2 : ℝ)) + (1 / 8 : ℝ) * (1 + δ) ^ 2 < 1 / 4 := by
    have hquad : δ ^ 2 ≤ δ / 10000 := by
      nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδ)]
    have hsq : (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
    rw [hsq]
    linarith
  have hnegative := metricRm04_lt_neg_mul_gram_of_small_metric_derivatives
    qP G pP (eps := δ) (c := 1 / 4) (a := 1 / 8) (K := 2) (by linarith) (by norm_num)
    hsmall u v hunitU hunitV hcurv hmodel hbudget
  have hnegative' : metricRm04StandardAt q p u v v u <
      -(1 / 8 : ℝ) * (q.inner p u u * q.inner p v v - q.inner p u v ^ 2) := by
    dsimp only [qP] at hnegative
    have hres := metricRm04StandardAt_restrictOpen q P pP u v v u
    rw [hres, mfderiv_subtype_val_apply P pP u, mfderiv_subtype_val_apply P pP v] at hnegative
    exact hnegative
  exact hnegative'

/-- The original finite cusp embedding transports every reference-orthonormal
plane at positive height to a plane with sectional curvature below `-1/8`.
Only its actual raw metric errors through order two are used. -/
theorem CuspEmbedding.metricRm04_lt_neg_one_eighth_of_positive_height
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) (hδ : δ ≤ 1 / 10000)
    (p : CuspHalfSpace) (hp : p ∈ cuspDomain) (hpos : 0 < p.2.val 0)
    (u v : TangentSpace halfCollarModel p)
    (hu : e.cusp.metric.inner p u u = 1)
    (hv : e.cusp.metric.inner p v v = 1)
    (huv : e.cusp.metric.inner p u v = 0) :
    let a := mfderiv halfCollarModel W.model e.toFun p u
    let b := mfderiv halfCollarModel W.model e.toFun p v
    metricRm04StandardAt g (e.toFun p) a b b a <
      -(1 / 8 : ℝ) *
        (g.inner (e.toFun p) a a * g.inner (e.toFun p) b b -
          g.inner (e.toFun p) a b ^ 2) := by
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
  obtain ⟨Φ, hpΦ, _, _, hΦp, hΦD, hΦjets⟩ :=
    e.exists_partialDiffeomorph_eq_finiteJet hp hpos
  obtain ⟨q, O, hpO, hO, hmetric⟩ :=
    exists_same_carrier_pullback_metric g e.cusp Φ hpΦ
  have hdomain : IsOpen cuspDomain := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hf : ContMDiffAt halfCollarModel W.model (2 + 1 : ℕ) e.toFun p :=
    (e.contMDiffOn.contMDiffAt (hdomain.mem_nhds hp)).of_le
      (by exact_mod_cast (show 2 + 1 ≤ K + 1 by omega))
  have hΦ : ContMDiffAt halfCollarModel W.model (2 + 1 : ℕ) Φ p :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hpΦ)).of_le (by simp)
  have hjets : ∀ j ≤ 2 + 1,
      iteratedFDeriv ℝ j
          (extChartAt W.model (e.toFun p) ∘ e.toFun ∘ (extChartAt halfCollarModel p).symm)
          (extChartAt halfCollarModel p p) =
        iteratedFDeriv ℝ j
          (extChartAt W.model (e.toFun p) ∘ Φ ∘ (extChartAt halfCollarModel p).symm)
          (extChartAt halfCollarModel p p) := by
    intro j hj
    exact (hΦjets j (by omega)).symm
  have hmetricGerm : ∀ᶠ z in 𝓝 p, q.inner z = localPullInner g Φ z := by
    filter_upwards [O.isOpen.mem_nhds hpO] with z hz
    ext a b
    exact hmetric z hz a b
  have herror (k : ℕ) (hk : k ≤ 2) :
      metricDerivNorm k q e.cusp.metric e.cusp.metric p ≤ δ := by
    rw [metricDerivNorm_eq_raw_pullbackError_of_map_jets g e.cusp.metric q
      hpint hepint hΦp.symm hf hΦ hjets hmetricGerm k hk]
    exact e.metric_error k (hk.trans hK) p hp
  have hnegative' := cusp_metricRm04_lt_neg_one_eighth_of_small_errors e.cusp q hδ p hpint
    herror u v hu hv huv
  have hcurvature : metricRm04StandardAt q p u v v u =
      metricRm04StandardAt g (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p u)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p u) := by
    have h : metricRm04StandardAt q p u v v u =
        metricRm04StandardAt g (Φ p)
          (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p u)
          (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p v)
          (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p v)
          (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p u) :=
      metricRm04StandardAt_eq_of_partialDiffeomorph_restriction Φ O hO q g
        (fun z a b => hmetric z.val z.property a b) (⟨p, hpO⟩ : O) u v v u
    rw [hΦp, hΦD] at h
    exact h
  have hinner (a b : TangentSpace halfCollarModel p) :
      q.inner p a b = g.inner (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p a)
        (mfderiv halfCollarModel W.model e.toFun p b) := by
    have h : q.inner p a b = g.inner (Φ p)
        (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p a)
        (mfderiv halfCollarModel W.model (Φ : CuspHalfSpace → W.Carrier) p b) :=
      hmetric p hpO a b
    rw [hΦp, hΦD] at h
    exact h
  rw [hcurvature, hinner, hinner, hinner] at hnegative'
  exact hnegative'

end DifferentialGeometry.Geometry.Collapse
