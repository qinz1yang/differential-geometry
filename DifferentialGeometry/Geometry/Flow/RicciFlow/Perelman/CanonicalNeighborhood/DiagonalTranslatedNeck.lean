import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CenteredCylinderMetric
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Topology.ProjectiveSpace.SphereHalfTurnFrame
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonReflexive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarFromConnection

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_partialDiffeomorph_diagonal_projection_translate
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M) (a : ℝ) :
    ∃ e : PartialDiffeomorph IC I3 Cylinder M ∞,
      e.source = univ ×ˢ Ioi (-a) ∧
      e.target = (fun z : Cylinder => d (cylinderDiagonalQuotientMap (z.1, z.2 + a))) ''
        (univ ×ˢ Ioi (-a)) ∧
      ∀ z : Cylinder, e z = d (cylinderDiagonalQuotientMap (z.1, z.2 + a)) := by
  let j : Cylinder → M := (d ∘ cylinderDiagonalQuotientMap) ∘ cylinderLineTranslation a
  have hj : IsLocalDiffeomorph IC I3 ∞ j :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
      (cylinderLineTranslation a).isLocalDiffeomorph
  have hinj : InjOn j (univ ×ˢ Ioi (-a)) := by
    intro z hz w hw heq
    have hq : cylinderDiagonalQuotientMap (z.1, z.2 + a) =
        cylinderDiagonalQuotientMap (w.1, w.2 + a) := d.injective heq
    rcases cylinderDiagonalQuotientMap_eq_iff.mp hq with h | h
    · exact (cylinderLineTranslation a).injective h
    · have hh := congrArg Prod.snd h
      change z.2 + a = -(w.2 + a) at hh
      have hz' : -a < z.2 := hz.2
      have hw' : -a < w.2 := hw.2
      linarith
  obtain ⟨e, hs, ht, he⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hj.isLocalDiffeomorphOn _) (isOpen_univ.prod isOpen_Ioi)
    ⟨(sphereEquator 0, -a + 1), mem_univ _, by change -a < -a + 1; linarith⟩ hinj
  exact ⟨e, hs, ht, congrFun he⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem localPullMetric_diagonal_projection_translate
    (g : SmoothRiemannianMetric I3 M)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (a t : ℝ) (ht : t < 1)
    (hmetric : localPullMetric (Diffeomorph.pullbackMetricCross g d) cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph = scalarOneShrinkingCylinderMetric t ht) :
    let j : Cylinder → M := (d ∘ cylinderDiagonalQuotientMap) ∘ cylinderLineTranslation a
    let hj := isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
      (cylinderLineTranslation a).isLocalDiffeomorph
    localPullMetric g j hj = scalarOneShrinkingCylinderMetric t ht := by
  dsimp only
  have hfun : localPullMetric g ((d ∘ cylinderDiagonalQuotientMap) ∘ cylinderLineTranslation a)
      (isLocalDiffeomorph_comp
        (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
        (cylinderLineTranslation a).isLocalDiffeomorph) =
      Diffeomorph.pullbackMetricCross
        (localPullMetric (Diffeomorph.pullbackMetricCross g d) cylinderDiagonalQuotientMap
          cylinderDiagonalQuotientMap_isLocalDiffeomorph) (cylinderLineTranslation a) := by
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    rw [localPullMetric_comp g d cylinderDiagonalQuotientMap d.isLocalDiffeomorph
      cylinderDiagonalQuotientMap_isLocalDiffeomorph
        (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)]
    rw [localPullMetric_comp]
  rw [hfun, hmetric, scalarOneShrinkingCylinderMetric_pullback_lineTranslation]

omit [SigmaCompactSpace M] in
theorem exists_strongNeck_diagonal_projection_translate
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (p : Sphere 2) (a : ℝ) (ha : eps⁻¹ ≤ a) :
    ∃ nk : StrongNeck S eps (d (cylinderDiagonalQuotientMap (p, a))) 0,
      nk.center = p ∧ nk.map.source = univ ×ˢ Ioi (-a) ∧
      ∀ z : Cylinder, nk.map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + a)) := by
  let j : Cylinder → M := (d ∘ cylinderDiagonalQuotientMap) ∘ cylinderLineTranslation a
  let hj := isLocalDiffeomorph_comp
    (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
    (cylinderLineTranslation a).isLocalDiffeomorph
  have hlocal (t : ℝ) (ht : t ≤ 0) : localPullMetric (S.base.metric t) j hj =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) :=
    localPullMetric_diagonal_projection_translate (S.base.metric t) d a t _ (hmetric t ht)
  have hscalar : S.scalar 0 (d (cylinderDiagonalQuotientMap (p, a))) = 1 := by
    have hh := metricScalarAt_localPull (S.base.metric 0) j hj (p, 0)
    rw [hlocal 0 le_rfl, scalarOneShrinkingCylinderMetric_zero,
      doubleSphereCylinderMetric_scalar_native] at hh
    change metricScalarAt (S.base.metric 0) (d (cylinderDiagonalQuotientMap (p, a))) = 1
    simpa only [j, Function.comp_apply, cylinderLineTranslation_apply, zero_add] using hh.symm
  have hQ : 0 < S.scalar 0 (d (cylinderDiagonalQuotientMap (p, a))) := by rw [hscalar]; norm_num
  obtain ⟨e, he_source, _he_target, he⟩ := exists_partialDiffeomorph_diagonal_projection_translate d a
  have hmap : (e : Cylinder → M) = j := funext he
  let C : CylinderReference := {
    metric := fun t => localPullMetric (S.base.metric t) j hj
    inner_eq := fun t ht y v w => by
      rw [hlocal t ht]
      exact scalarOneShrinkingCylinderMetric_inner t _ y.1 y.2 v.1 w.1 v.2 w.2 }
  have hscale : rescaledMetric S 0 (S.scalar 0 (d (cylinderDiagonalQuotientMap (p, a)))) hQ =
      S.base.metric := by
    funext s
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [rescaledMetric, hscalar, parabolicTime, zero_add, div_one, scaleMetric_inner, one_mul]
  let nk : StrongNeck S eps (d (cylinderDiagonalQuotientMap (p, a))) 0 := {
    eps_pos := heps
    eps_small := hsmall
    Q_pos := hQ
    cylinder := C
    map := e
    center := p
    center_eq := by simpa only [zero_add] using he (p, 0)
    domain := fun y hy => by
      rw [he_source]
      exact ⟨mem_univ _, lt_of_le_of_lt (neg_le_neg ha) hy.2.1⟩
    time_domain := fun _ hs => hs.2
    comparison := {
      pullback := fun s => metricTensorField (C.metric s)
      pullback_eq := by
        intro s y _hy v
        rw [metricTensorField_apply, hscale, hmap]
        exact localPullMetric_inner (S.base.metric s) j hj y (v 0) (v 1)
      jet := fun _ _ => 0
      jet_zero := by intro s y v; simp [metricTensorField_apply]
      jet_succ := by intro b s hs y hy v; simp
      equivalence := by
        intro s hs y hy v
        have hnn := inner_self_nonneg (C.metric s) y v
        simp only [metricTensorField_apply]
        constructor <;> nlinarith
      close := by
        intro b c hbc s hs y hy
        have hz : tensor02CovDerivNormWith b 0 (C.metric s) (C.metric s) y = 0 := by
          rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
          simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
            MetricFiberData.inner, map_zero, Real.sqrt_zero]
        exact hz.le.trans heps.le } }
  exact ⟨nk, rfl, he_source, he⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
