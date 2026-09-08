import DifferentialGeometry.Geometry.Curvature.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorLaplacianScaling
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorScaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem ricci_ode_parabolic_scaling
    (g : ℝ → SmoothRiemannianMetric I M) (τ c : ℝ) (hc : 0 < c)
    (x : M) {Z : ℝ → TangentSpace I x} {J : Set ℝ} {s : ℝ}
    (hZ : HasDerivWithinAt Z (ricciSharp (g (paraTime τ c s)) x
      (Z (paraTime τ c s))) J (paraTime τ c s)) :
    HasDerivWithinAt (fun r => (Real.sqrt c)⁻¹ • Z (paraTime τ c r))
      (ricciSharp (scaleMetric c hc (g (paraTime τ c s))) x
        ((Real.sqrt c)⁻¹ • Z (paraTime τ c s)))
      {r | paraTime τ c r ∈ J} s := by
  let _ : NormedAddCommGroup (TangentSpace I x) := Tensor0SBundle.tangentSpaceNormedAddCommGroup x
  let _ : NormedSpace ℝ (TangentSpace I x) := Tensor0SBundle.tangentSpaceNormedSpace x
  have ha : HasDerivAt (fun r => paraTime τ c r) c⁻¹ s := by
    simpa only [paraTime, one_div, id_eq] using ((hasDerivAt_id s).div_const c).const_add τ
  have hd := (hZ.scomp s ha.hasDerivWithinAt (fun _ hr => hr)).const_smul (Real.sqrt c)⁻¹
  exact hd.congr_deriv (by
    simp only [ricciSharp_scaleMetric, smul_apply, map_smul, smul_smul, mul_comm])

end DifferentialGeometry.PDE.RicciFlow

open scoped Bundle RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem exists_uhlenbeck_parabolic_scaling
    (g : ℝ → SmoothRiemannianMetric I M) (τ c : ℝ) (hc : 0 < c)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) (J : Set ℝ)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x) (ι p.1 p.2).toContinuousLinearMap)
      (J ×ˢ (Set.univ : Set M)))
    (hode : ∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun r => ι r x v)
      (ricciSharp (g t) x (ι t x v)) J t)
    (hmetric : ∀ t ∈ J, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = ⟪v,w⟫) :
    ∃ κ : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ s x v, κ s x v = (Real.sqrt c)⁻¹ • ι (paraTime τ c s) x v) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x) (κ p.1 p.2).toContinuousLinearMap)
        ({s | paraTime τ c s ∈ J} ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x) (κ p.1 p.2).symm.toContinuousLinearMap)
        ({s | paraTime τ c s ∈ J} ×ˢ (Set.univ : Set M)) ∧
      (∀ s, paraTime τ c s ∈ J → ∀ x v, HasDerivWithinAt (fun r => κ r x v)
        (ricciSharp (scaleMetric c hc (g (paraTime τ c s))) x (κ s x v))
        {r | paraTime τ c r ∈ J} s) ∧
      (∀ s, paraTime τ c s ∈ J → ∀ x v w,
        (scaleMetric c hc (g (paraTime τ c s))).inner x (κ s x v) (κ s x w) = ⟪v,w⟫) := by
  let a : ℝˣ := Units.mk0 ((Real.sqrt c)⁻¹) (inv_ne_zero (Real.sqrt_ne_zero'.mpr hc))
  let κ := fun s x => a • ι (paraTime τ c s) x
  have heq (s : ℝ) (x : M) (v : V x) :
      κ s x v = (Real.sqrt c)⁻¹ • ι (paraTime τ c s) x v := rfl
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (paraTime τ c p.1, p.2)) := by
    apply ContMDiff.prodMk _ contMDiff_snd
    exact contMDiff_const.add (contMDiff_fst.div_const c)
  have hcomp := hι.comp htime.contMDiffOn
    (s := {s | paraTime τ c s ∈ J} ×ˢ (Set.univ : Set M)) (fun p hp => hp)
  have hκ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x) (κ p.1 p.2).toContinuousLinearMap)
      ({s | paraTime τ c s ∈ J} ×ˢ (Set.univ : Set M)) := by
    exact (contMDiffOn_const.smul_bundle hcomp).congr (fun p hp => rfl)
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hκinv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x) (κ p.1 p.2).symm.toContinuousLinearMap)
      ({s | paraTime τ c s ∈ J} ×ˢ (Set.univ : Set M)) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hκ.clm_bundle_inverse (fun _ _ => ContinuousLinearMap.isInvertible_equiv)
  refine ⟨κ, heq, hκ, hκinv, ?_, ?_⟩
  · intro s hs x v
    exact ricci_ode_parabolic_scaling g τ c hc x (hode _ hs x v)
  · intro s hs x v w
    rw [heq, heq, scaleMetric_inner_inv_sqrt_smul, hmetric _ hs]

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private local instance exteriorGroup : NormedAddCommGroup (⋀[ℝ]^2 F) := inferInstance

private local instance exteriorInner : InnerProductSpace ℝ (⋀[ℝ]^2 F) := inferInstance

private local instance exteriorComplete : CompleteSpace (⋀[ℝ]^2 F) := inferInstance

private local instance endoGroup : NormedAddCommGroup ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) := inferInstance

private local instance endoSpace : NormedSpace ℝ ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) := inferInstance

theorem traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_parabolic_scaling
    (g : ℝ → SmoothRiemannianMetric I M) (τ c : ℝ) (hc : 0 < c)
    (x : M) (e : ℝ → F →L[ℝ] TangentSpace I x) {J : Set ℝ} {s : ℝ}
    (R' : selfAdjoint ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)) :
    let R := fun t => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (g t) x).compContinuousLinearMap (fun _ => e t))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g t) x)).compContinuousLinearMap (e t))
    let Q := fun r => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (scaleMetric c hc (g (paraTime τ c r))) x).compContinuousLinearMap
        (fun _ => (Real.sqrt c)⁻¹ • e (paraTime τ c r)))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc (g (paraTime τ c r))) x)).compContinuousLinearMap
        ((Real.sqrt c)⁻¹ • e (paraTime τ c r)))
    HasDerivWithinAt R R' J (paraTime τ c s) →
      HasDerivWithinAt Q ((c⁻¹ * c⁻¹) • R') {r | paraTime τ c r ∈ J} s := by
  dsimp only
  intro hR
  have htime : HasDerivAt (fun r => paraTime τ c r) c⁻¹ s := by
    simpa only [paraTime, one_div, id_eq] using ((hasDerivAt_id s).div_const c).const_add τ
  have h := (hR.scomp s htime.hasDerivWithinAt (fun _ hr => hr)).const_smul c⁻¹
  apply (h.congr_deriv (smul_smul _ _ _)).congr
  · intro r _
    exact traceNormalizedCurvatureSelfAdjoint_scaleMetric_pullback c hc (g (paraTime τ c r)) x
      (e (paraTime τ c r))
  · exact traceNormalizedCurvatureSelfAdjoint_scaleMetric_pullback c hc (g (paraTime τ c s)) x
      (e (paraTime τ c s))

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]


variable [∀ y, FiniteDimensional ℝ (V y)]

private local instance exteriorTopology :
    TopologicalSpace (TotalSpace (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))) :=
  Bundle.ExteriorPower.totalSpaceTopology F V 2

private local instance exteriorFiberBundle : FiberBundle (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
  Bundle.ExteriorPower.fiberBundle F V 2

private local instance exteriorVectorBundle : VectorBundle ℝ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
  Bundle.ExteriorPower.vector_bundle F V 2

private local instance exteriorSmooth :
    ContMDiffVectorBundle ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) I :=
  Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2

private local instance exteriorMetricSmooth :
    IsContMDiffRiemannianBundle I ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
  Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2

private abbrev exteriorSelfAdjoint := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
  (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)

private local instance selfAdjointTopology :
    TopologicalSpace (TotalSpace (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
      (fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)) :=
  (exteriorSelfAdjoint (I := I) (F := F) (V := V)).totalSpaceTopology

private local instance selfAdjointFiberBundle :
    FiberBundle (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
      (fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y) :=
  (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiberBundle



private local instance exteriorFiberGroup (y : M) : NormedAddCommGroup (⋀[ℝ]^2 (V y)) := inferInstance

private local instance exteriorFiberInner (y : M) : InnerProductSpace ℝ (⋀[ℝ]^2 (V y)) := inferInstance

private local instance selfAdjointFiberGroup (y : M) :
    NormedAddCommGroup ((exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y) := inferInstance

private local instance selfAdjointFiberSpace (y : M) :
    NormedSpace ℝ ((exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y) := inferInstance

private def metricOp (g : SmoothRiemannianMetric I M)
    (ι : ∀ y, V y ≃L[ℝ] TangentSpace I y) (x : M) :
    (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber x :=
  exteriorPower.traceNormalizedCurvatureSelfAdjoint
    ((metricRm04At g x).compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)).compContinuousLinearMap
      (ι x).toContinuousLinearMap)

private def metricLap (g : SmoothRiemannianMetric I M)
    (ι : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι y).toContinuousLinearMap))
    (hmetric : ∀ y v w, g.inner y (ι y v) (ι y w) = ⟪v, w⟫) (x : M) :
    (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber x :=
  let D := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)
  let hD := isMetricCompatible_pullback_leviCivita g ι hι hmetric
  rawBundleConnLap
    (F := Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
    (V := fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)
    g ((D.exteriorPower 2).selfAdjoint (hD.exteriorPower 2)) (metricOp (F := F) g ι) x

private def metricReaction (g : SmoothRiemannianMetric I M)
    (ι : ∀ y, V y ≃L[ℝ] TangentSpace I y) (x : M) :
    (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber x :=
  DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorReactionSelfAdjoint3
    (metricOp (F := F) g ι x)

omit [BoundarylessManifold I M] in
private theorem metricOp_scale (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hscale : ∀ y v, κ y v = (Real.sqrt c)⁻¹ • ι y v) (x : M) :
    metricOp (F := F) (scaleMetric c hc g) κ x = c⁻¹ • metricOp (F := F) g ι x := by
  have heq : (κ x).toContinuousLinearMap = (Real.sqrt c)⁻¹ • (ι x).toContinuousLinearMap := by
    ext v
    exact hscale x v
  unfold metricOp
  simp only [heq]
  exact traceNormalizedCurvatureSelfAdjoint_scaleMetric_pullback c hc g x (ι x).toContinuousLinearMap

omit [BoundarylessManifold I M] in
private theorem metricReaction_scale (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hscale : ∀ y v, κ y v = (Real.sqrt c)⁻¹ • ι y v) (x : M) :
    metricReaction (F := F) (scaleMetric c hc g) κ x =
      (c⁻¹ * c⁻¹) • metricReaction (F := F) g ι x := by
  unfold metricReaction
  rw [metricOp_scale c hc g ι κ hscale]
  exact (DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorReactionSelfAdjoint3_smul
    c⁻¹ (metricOp (F := F) g ι x)).trans (by rw [pow_two]; rfl)

private theorem metricLap_scale (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι y).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (κ y).toContinuousLinearMap))
    (hscale : ∀ y v, κ y v = (Real.sqrt c)⁻¹ • ι y v)
    (hmetric : ∀ y v w, g.inner y (ι y v) (ι y w) = ⟪v, w⟫)
    (hκmetric : ∀ y v w, (scaleMetric c hc g).inner y (κ y v) (κ y w) = ⟪v, w⟫)
    (x : M) :
    metricLap (F := F) (scaleMetric c hc g) κ hκ hκmetric x =
      (c⁻¹ * c⁻¹) • metricLap (F := F) g ι
        (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hmetric x := by
  exact traceNormalizedCurvatureSelfAdjoint_pullback_laplacian_scaleMetric c hc g ι κ hι hscale hmetric x

private theorem metric_evolution_scale (g : ℝ → SmoothRiemannianMetric I M) (τ c : ℝ) (hc : 0 < c)
    (ι κ : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (J : Set ℝ) (s : ℝ)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι (paraTime τ c s) y).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (κ s y).toContinuousLinearMap))
    (hscale : ∀ r y v, κ r y v = (Real.sqrt c)⁻¹ • ι (paraTime τ c r) y v)
    (hmetric : ∀ y v w, (g (paraTime τ c s)).inner y
      (ι (paraTime τ c s) y v) (ι (paraTime τ c s) y w) = ⟪v, w⟫)
    (hκmetric : ∀ y v w, (scaleMetric c hc (g (paraTime τ c s))).inner y
      (κ s y v) (κ s y w) = ⟪v, w⟫)
    (x : M) :
    let R : ℝ → ∀ y, (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y :=
      fun t y => metricOp (F := F) (g t) (ι t) y
    let Q : ℝ → ∀ y, (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y :=
      fun r y => metricOp (F := F) (scaleMetric c hc (g (paraTime τ c r))) (κ r) y
    let L := metricLap (F := F) (g (paraTime τ c s)) (ι (paraTime τ c s))
      (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hmetric x
    let K := metricLap (F := F) (scaleMetric c hc (g (paraTime τ c s))) (κ s) hκ hκmetric x
    let N := metricReaction (F := F) (g (paraTime τ c s)) (ι (paraTime τ c s)) x
    let O := metricReaction (F := F) (scaleMetric c hc (g (paraTime τ c s))) (κ s) x
    HasDerivWithinAt (fun t => R t x) (L + N) J (paraTime τ c s) →
      HasDerivWithinAt (fun r => Q r x) (K + O) {r | paraTime τ c r ∈ J} s := by
  dsimp only
  intro h
  have htime : HasDerivAt (fun r => paraTime τ c r) c⁻¹ s := by
    simpa only [paraTime, one_div, id_eq] using ((hasDerivAt_id s).div_const c).const_add τ
  have hd := (h.scomp s htime.hasDerivWithinAt (fun _ hr => hr)).const_smul c⁻¹
  have heq : c⁻¹ • c⁻¹ •
      (metricLap (F := F) (g (paraTime τ c s)) (ι (paraTime τ c s))
        (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hmetric x +
        metricReaction (F := F) (g (paraTime τ c s)) (ι (paraTime τ c s)) x) =
      metricLap (F := F) (scaleMetric c hc (g (paraTime τ c s))) (κ s) hκ hκmetric x +
        metricReaction (F := F) (scaleMetric c hc (g (paraTime τ c s))) (κ s) x := by
    calc
      _ = (c⁻¹ * c⁻¹) • _ := smul_smul _ _ _
      _ = (c⁻¹ * c⁻¹) • metricLap (F := F) (g (paraTime τ c s))
          (ι (paraTime τ c s)) (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hmetric x +
          (c⁻¹ * c⁻¹) • metricReaction (F := F) (g (paraTime τ c s))
            (ι (paraTime τ c s)) x := smul_add _ _ _
      _ = _ := congrArg₂ (fun a b => a + b)
        (metricLap_scale c hc (g (paraTime τ c s)) (ι (paraTime τ c s)) (κ s)
          hι hκ (hscale s) hmetric hκmetric x).symm
        (metricReaction_scale c hc (g (paraTime τ c s))
          (ι (paraTime τ c s)) (κ s) (hscale s) x).symm
  apply (hd.congr_deriv heq).congr
  · intro r _
    exact metricOp_scale c hc (g (paraTime τ c r)) (ι (paraTime τ c r)) (κ r) (hscale r) x
  · exact metricOp_scale c hc (g (paraTime τ c s)) (ι (paraTime τ c s)) (κ s) (hscale s) x

omit [∀ y, FiniteDimensional ℝ (V y)] in
theorem traceNormalizedCurvatureSelfAdjoint_pullback_evolution_parabolic_scaling
    (g : ℝ → SmoothRiemannianMetric I M) (τ c : ℝ) (hc : 0 < c)
    (ι κ : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) (J : Set ℝ) (s : ℝ)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι (paraTime τ c s) x).toContinuousLinearMap))
    (hscale : ∀ r x v, κ r x v = (Real.sqrt c)⁻¹ • ι (paraTime τ c r) x v)
    (hmetric : ∀ x v w, (g (paraTime τ c s)).inner x (ι (paraTime τ c s) x v) (ι (paraTime τ c s) x w) = ⟪v, w⟫) (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
    letI := P.totalSpaceTopology
    letI := P.fiberBundle
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let hκ₁ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
        (fun x => TotalSpace.mk' (F →L[ℝ] E) x (κ s x).toContinuousLinearMap) :=
      ((hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).const_smul_section
        (a := (Real.sqrt c)⁻¹)).congr (fun y => by
          congr 1
          ext v
          exact hscale s y v)
    let D := pullbackFiberwiseLinearEquiv (fun y => (ι (paraTime τ c s) y).toLinearEquiv)
      hι₁.clm_bundle_map (LeviCivita (g (paraTime τ c s)))
    let C := pullbackFiberwiseLinearEquiv (fun y => (κ s y).toLinearEquiv)
      hκ₁.clm_bundle_map (LeviCivita (scaleMetric c hc (g (paraTime τ c s))))
    let hD := isMetricCompatible_pullback_leviCivita (g (paraTime τ c s)) (ι (paraTime τ c s)) hι₁ hmetric
    let hC := isMetricCompatible_pullback_leviCivita (scaleMetric c hc (g (paraTime τ c s))) (κ s) hκ₁
      (fun x v w => by rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric])
    let R : ℝ → ∀ y, P.fiber y := fun t y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (g t) y).compContinuousLinearMap (fun _ => (ι t y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g t) y)).compContinuousLinearMap
        (ι t y).toContinuousLinearMap)
    let Q : ℝ → ∀ y, P.fiber y := fun r y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (scaleMetric c hc (g (paraTime τ c r))) y).compContinuousLinearMap
        (fun _ => (κ r y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc (g (paraTime τ c r))) y)).compContinuousLinearMap
        (κ r y).toContinuousLinearMap)
    let N : P.fiber x := DimensionThree.curvatureOperatorReactionSelfAdjoint3 (R (paraTime τ c s) x)
    let O : P.fiber x := DimensionThree.curvatureOperatorReactionSelfAdjoint3 (Q s x)
    HasDerivWithinAt (fun t => R t x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (g (paraTime τ c s)) ((D.exteriorPower 2).selfAdjoint (hD.exteriorPower 2))
        (R (paraTime τ c s)) x + N) J (paraTime τ c s) →
    HasDerivWithinAt (fun r => Q r x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (scaleMetric c hc (g (paraTime τ c s))) ((C.exteriorPower 2).selfAdjoint (hC.exteriorPower 2))
        (Q s) x + O) {r | paraTime τ c r ∈ J} s := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  have hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (κ s y).toContinuousLinearMap) :=
    ((hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).const_smul_section
      (a := (Real.sqrt c)⁻¹)).congr (fun y => by
        congr 1
        ext v
        exact hscale s y v)
  have hκmetric : ∀ y v w, (scaleMetric c hc (g (paraTime τ c s))).inner y
      (κ s y v) (κ s y w) = ⟪v, w⟫ := by
    intro y v w
    rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric]
  exact metric_evolution_scale g τ c hc ι κ J s hι hκ hscale hmetric hκmetric x

end DifferentialGeometry.PDE.RicciFlow
