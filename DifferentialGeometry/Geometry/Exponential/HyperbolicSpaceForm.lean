import DifferentialGeometry.Geometry.Exponential.HyperbolicComparison
import DifferentialGeometry.Geometry.Metric.LocalIsometry.Covering
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Topology.Covering.SimplyConnected

noncomputable section

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [SimplyConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def hyperbolicComparisonIsometryEquiv (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    (E ≃ₗᵢ[ℝ] TangentSpace I p) → Hyperboloid E ≃ᵢ M := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  intro i
  let F := hyperbolicComparison g hg p i
  have hlocal := isLocalDiffeomorph_hyperbolicComparison g hg p hR i
  have hcover : IsCoveringMap F := isCoveringMap_of_complete
    Hyperboloid.riemannianMetric g hlocal Hyperboloid.riemannianMetric_complete
      (fun x v w => (hyperbolicComparison_inner g hg p hR i x v w).symm)
  let _ : PathConnectedSpace (Hyperboloid E) :=
    (Hyperboloid.spaceHomeomorph (E := E)).symm.pathConnectedSpace
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let Φ : Hyperboloid E ≃ₘ⟮𝓘(ℝ, E), I⟯ M := hcover.diffeomorphSc hlocal
  have hpull : Diffeomorph.pullbackMetricCross g Φ = Hyperboloid.riemannianMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hyperbolicComparison_inner g hg p hR i x v w
  refine { toEquiv := Φ.toEquiv, isometry_toFun := ?_ }
  intro x y
  change riemannianEDistOf g (Φ x) (Φ y) = edist x y
  rw [← Geometry.Metric.edistOf_pullbackMetricCross g Φ x y, hpull,
    Hyperboloid.riemannianEDistOf_eq_edist]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparisonIsometryEquiv_apply (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p) (x : Hyperboloid E),
      hyperbolicComparisonIsometryEquiv g hg p hR i x = hyperbolicComparison g hg p i x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  intro i x
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[simp] theorem hyperbolicComparisonIsometryEquiv_origin (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p),
      hyperbolicComparisonIsometryEquiv g hg p hR i Hyperboloid.origin = p := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  intro i
  rw [hyperbolicComparisonIsometryEquiv_apply, hyperbolicComparison_apply,
    Hyperboloid.expMapIntrinsicOriginDiffeomorph_symm_apply, Hyperboloid.origin_space,
    smul_zero, map_zero]
  let hnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  rw [← expMap_eq_expMapIntrinsic g hnorm, expMap_zero]

end DifferentialGeometry.Geometry.Riemannian.Exponential
