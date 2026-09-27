import DifferentialGeometry.Geometry.Comparison.Soul.SbrCorayDirection
import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientVelocity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem intrinsicGeneralizedGradient_eq_of_unit_value
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} (hF : LipschitzWith 1 F)
    (hconc : ∀ (q : M) (v : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q v t)))
    (p : M) (U : TangentSpace I p)
    (hU : g.inner p U U = 1)
    (hvalue : intrinsicRightDerivative g hEnorm F p U = 1) :
    intrinsicGeneralizedGradient g hEnorm hF hconc p = U := by
  let D : TangentSpace I p → ℝ := intrinsicRightDerivative g hEnorm F p
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
  change G = U
  have hs : ∀ v : TangentSpace I p, D v ≤ g.inner p G v :=
    (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1
  have hbound : Real.sqrt (g.inner p G G) ≤ 1 := by
    simpa only [NNReal.coe_one] using
      intrinsicGeneralizedGradient_norm_le g hEnorm hF hconc p
  have hvalue' : D U = 1 := hvalue
  let K : InnerProductSpace.Core ℝ (TangentSpace I p) := g.toRiemannianMetric.toCore p
  have hKcont : ContinuousAt (fun v : TangentSpace I p => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt p
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded p
  let : NormedAddCommGroup (TangentSpace I p) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let : InnerProductSpace ℝ (TangentSpace I p) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have hinner (v w : TangentSpace I p) : inner ℝ v w = g.inner p v w := rfl
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) := by
    rw [norm_eq_sqrt_real_inner, hinner]
  have hs' : ∀ v : TangentSpace I p, D v ≤ inner ℝ G v := hs
  have hGnorm : ‖G‖ ≤ 1 := by rwa [hnorm]
  have hUnorm : ‖U‖ = 1 := by rw [hnorm, hU, Real.sqrt_one]
  have heq : G = (1 : ℝ) • U :=
    superadditive_gradient_eq_of_unit_value hs' (zero_le_one : (0 : ℝ) ≤ 1)
      hGnorm hUnorm hvalue'
  simpa only [one_smul] using heq

set_option backward.isDefEq.respectTransparency false in
theorem exists_busemann_reversed_coray_ascent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) (C : ℝ)
    (hlevel : busemann c p < C)
    (hF : LipschitzWith 1 (fun q => C - busemann c q))
    (hconc : ∀ (q : M) (v : TangentSpace I q),
      ConcaveOn ℝ univ
        (fun t => C - busemann c (intrinsicGeodesic g hEnorm q v t))) :
    let T := C - busemann c p
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      let gamma := intrinsicGeodesic g hEnorm p u
      let delta := fun s => gamma (T - s)
      ContMDiff 𝓘(ℝ, ℝ) I ∞ delta ∧
      busemann c (delta 0) = C ∧ delta T = p ∧
      (∀ s ∈ Icc 0 T, C - busemann c (delta s) = s) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist (delta s) (delta t) = dist s t) ∧
      (∀ s ∈ Ico 0 T,
        let G := intrinsicGeneralizedGradient g hEnorm hF hconc (delta s)
        G = curveVelocity (I := I) delta s ∧
        g.inner (delta s) G G = 1 ∧
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I delta (Ici s) s
          (ContinuousLinearMap.toSpanSingleton ℝ
            ((g.inner (delta s) G G)⁻¹ • G))) := by
  let T := C - busemann c p
  obtain ⟨u, hu, hsmooth, _, hderiv, hstart, hend, hlevels, hdist, hcal⟩ :=
    exists_busemann_reversed_coray g hEnorm c hc p C hlevel.le
  let gamma := intrinsicGeodesic g hEnorm p u
  let delta := fun s => gamma (T - s)
  refine ⟨u, hu, hsmooth, hstart, hend, hlevels, hdist, ?_⟩
  intro s hs
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc (delta s)
  have hunit : g.inner (delta s) (curveVelocity (I := I) delta s)
      (curveVelocity (I := I) delta s) = 1 := (hcal s hs).1
  have hG : G = curveVelocity (I := I) delta s :=
    intrinsicGeneralizedGradient_eq_of_unit_value g hEnorm hF hconc
      (delta s) (curveVelocity (I := I) delta s) hunit (hcal s hs).2
  refine ⟨hG, ?_, ?_⟩
  · change g.inner (delta s) G G = 1
    rw [hG]
    exact hunit
  · change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I delta (Ici s) s
      (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (delta s) G G)⁻¹ • G))
    rw [hG, hunit, inv_one, one_smul]
    have h := hderiv s
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _] at h
    exact h

end DifferentialGeometry.Geometry.Topology
