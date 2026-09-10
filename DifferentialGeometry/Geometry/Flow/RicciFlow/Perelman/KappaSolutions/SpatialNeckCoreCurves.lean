import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckExitLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderConnector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedNeckNumerics

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance coreCurveSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance coreCurveC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

theorem lift_core_curve {γ : ℝ → N} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hcore : ∀ t ∈ Icc a b, γ t ∈ W.core) :
    ∃ β : ℝ → spatialNeckBuffer epsilon,
      ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (Icc a b) ∧
      (∀ t ∈ Icc a b, β t ∈ spatialNeckClosedCore epsilon) ∧
      (∀ t ∈ Icc a b, W.embedding (β t) = γ t) := by
  let _ : Nonempty (spatialNeckBuffer epsilon) :=
    ⟨spatialNeckCentralPoint epsilon W.epsilon_pos yStar⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E := by
    simpa [Module.finrank_prod] using W.dimension_three.symm
  have hlocal : IsLocalDiffeomorph SpatialNeckCylinderModel I ∞ W.embedding := fun x =>
    immersionAt_isLocalDiffeomorphAt_of_finrank_eq hdim
      (W.smooth_embedding.isImmersion.isImmersionAt x)
  let F := partialDiffeomorphOfInjectiveLocalDiffeomorph W.embedding hlocal
    W.smooth_embedding.isEmbedding.injective
  have hsource : F.source = univ := partialDiffeomorphOfInjectiveLocalDiffeomorph_source _ _ _
  have htarget : F.target = W.image := partialDiffeomorphOfInjectiveLocalDiffeomorph_target _ _ _
  have hleft (x : spatialNeckBuffer epsilon) : F.symm (W.embedding x) = x :=
    F.toPartialEquiv.left_inv (by rw [hsource]; trivial)
  have htarget_curve (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ F.target := by
    rw [htarget]
    obtain ⟨x, _hx, heq⟩ := hcore t ht
    exact ⟨x, heq⟩
  let β : ℝ → spatialNeckBuffer epsilon := (F.symm : N → spatialNeckBuffer epsilon) ∘ γ
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (Icc a b) :=
    (F.contMDiffOn_invFun.of_le (by decide)).comp hγ htarget_curve
  refine ⟨β, hβ, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, heq⟩ := hcore t ht
    change F.symm (γ t) ∈ spatialNeckClosedCore epsilon
    rw [← heq, hleft]
    exact hx
  · intro t ht
    exact F.toPartialEquiv.right_inv (htarget_curve t ht)

omit [I.Boundaryless] in
theorem exists_core_connector (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x ∈ spatialNeckClosedCore epsilon) (hy : y ∈ spatialNeckClosedCore epsilon) :
    ∃ γ : ℝ → N, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) ∧
      γ 0 = W.embedding x ∧ γ 1 = W.embedding y ∧
      (∀ t : ℝ, γ t ∈ W.core) ∧
      metricPathELength (I := I) h γ 0 1 ≤
        ENNReal.ofReal ((13 / 12 * spatialNeckScale h p) *
          Real.sqrt (Real.pi ^ 2 + (y.val.2 - x.val.2) ^ 2)) := by
  obtain ⟨β, hβ, hβ0, hβ1, hβcore, hβlength⟩ :=
    unitCylinder_exists_short_core_connector epsilon x y hx hy
  let γ : ℝ → N := (W.embedding : spatialNeckBuffer epsilon → N) ∘ β
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (W.smooth_embedding.contMDiff.of_le (by decide)).comp_contMDiffOn hβ
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hl := (W.pathELength_bilipschitz hsmall hβ (fun t _ => hβcore t)).2
  have hbound := hl.trans (mul_le_mul_of_nonneg_left hβlength
    (zero_le : 0 ≤ ENNReal.ofReal (13 / 12 * spatialNeckScale h p)))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 13 / 12 * spatialNeckScale h p)] at hbound
  exact ⟨γ, hγ, congrArg W.embedding hβ0, congrArg W.embedding hβ1,
    fun t => ⟨β t, hβcore t, rfl⟩, hbound⟩

omit [I.Boundaryless] in
theorem core_edist_upper (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x ∈ spatialNeckClosedCore epsilon) (hy : y ∈ spatialNeckClosedCore epsilon) :
    riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) ≤
      ENNReal.ofReal ((13 / 12 * spatialNeckScale h p) *
        Real.sqrt (Real.pi ^ 2 + (y.val.2 - x.val.2) ^ 2)) := by
  obtain ⟨γ, hγ, hγ0, hγ1, _hcore, hlength⟩ := W.exists_core_connector hsmall x y hx hy
  let _ : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
  exact (Manifold.riemannianEDist_le_pathELength hγ hγ0 hγ1 zero_le_one).trans hlength

private theorem band_mem_core (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : |x.val.2| ≤ 5 * Real.pi) :
    x ∈ spatialNeckClosedCore epsilon := by
  have hgap := spatialNeckControlEpsilon_inverse_gap hepsilon hsmall
  have hbounds := abs_le.mp hx
  change -epsilon⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ epsilon⁻¹
  constructor <;> linarith [Real.pi_pos]

omit [I.Boundaryless] in
theorem band_edist_lt (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi) :
    riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) <
      ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p) := by
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hupper := W.core_edist_upper hsmall x y (band_mem_core W.epsilon_pos hsmall x hx)
    (band_mem_core W.epsilon_pos hsmall y hy)
  have htriangle := abs_sub_le y.val.2 0 x.val.2
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  have hdelta : |y.val.2 - x.val.2| ≤ 10 * Real.pi := by linarith
  have hsqrt : Real.sqrt (Real.pi ^ 2 + (y.val.2 - x.val.2) ^ 2) ≤
      Real.sqrt ((10 * Real.pi) ^ 2 + Real.pi ^ 2) := by
    apply Real.sqrt_le_sqrt
    have hsquare := (sq_le_sq₀ (abs_nonneg (y.val.2 - x.val.2))
      (by positivity : 0 ≤ 10 * Real.pi)).mpr hdelta
    nlinarith [sq_abs (y.val.2 - x.val.2)]
  have hreal : (13 / 12 * spatialNeckScale h p) *
      Real.sqrt (Real.pi ^ 2 + (y.val.2 - x.val.2) ^ 2) <
      11 * Real.pi * spatialNeckScale h p := by
    calc
      _ ≤ (13 / 12 * spatialNeckScale h p) *
          Real.sqrt ((10 * Real.pi) ^ 2 + Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (13 / 12 : ℝ) * Real.sqrt ((10 * Real.pi) ^ 2 + Real.pi ^ 2) *
          spatialNeckScale h p := by ring
      _ < _ := bufferedNeck_band_connector_bound hscale
  exact hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal)

theorem minimizing_curve_stays_core (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hstart : γ 0 = W.embedding x)
    (hmin : metricPathELength (I := I) h γ 0 1 =
      riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y)) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ W.core := by
  apply W.short_curve_stays_core hsmall x hx hγ hstart
  rw [hmin]
  exact (W.band_edist_lt hsmall x y hx hy).le

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
