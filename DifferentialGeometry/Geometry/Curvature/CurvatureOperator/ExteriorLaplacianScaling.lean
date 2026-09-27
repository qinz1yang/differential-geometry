import DifferentialGeometry.Geometry.Connection.Laplacian.SelfAdjointScaling
import DifferentialGeometry.Geometry.Connection.TensorNabla.Congruence
import DifferentialGeometry.Geometry.Connection.PullbackScaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorScaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Connection
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature

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

private theorem scaled_selfAdjoint_laplacian (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (κ x).toContinuousLinearMap))
    (hscale : ∀ x v, κ x v = (Real.sqrt c)⁻¹ • ι x v)
    (hmetric : ∀ x v w, g.inner x (ι x v) (ι x w) = ⟪v, w⟫) :
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let hκ₁ := hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let D := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv)
      hι₁.clm_bundle_map (LeviCivita g)
    let C := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv)
      hκ₁.clm_bundle_map (LeviCivita (scaleMetric c hc g))
    let hD := isMetricCompatible_pullback_leviCivita g ι hι₁ hmetric
    let hC := isMetricCompatible_pullback_leviCivita (scaleMetric c hc g) κ hκ₁
      (fun x v w => by rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric])
    ∀ (A : Cₛ^∞⟮I; Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ,
      fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y⟯) (x : M),
      rawBundleConnLap (F := Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
        (V := fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)
        (scaleMetric c hc g) ((C.exteriorPower 2).selfAdjoint (hC.exteriorPower 2))
        (fun y => c⁻¹ • A y) x =
      (c⁻¹ * c⁻¹) • rawBundleConnLap (F := Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
        (V := fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)
        g ((D.exteriorPower 2).selfAdjoint (hD.exteriorPower 2)) A x := by
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let hκ₁ := hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let D := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv)
    hι₁.clm_bundle_map (LeviCivita g)
  let C := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv)
    hκ₁.clm_bundle_map (LeviCivita (scaleMetric c hc g))
  let hD := isMetricCompatible_pullback_leviCivita g ι hι₁ hmetric
  let hC := isMetricCompatible_pullback_leviCivita (scaleMetric c hc g) κ hκ₁
    (fun x v w => by rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric])
  dsimp only
  intro A x
  have hDC (σ : ∀ y, V y) (y : M)
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) y) : C σ y = D σ y := by
    apply ContinuousLinearMap.ext
    intro X
    change pullbackFiberwiseLinearEquiv _ _ (LeviCivita (scaleMetric c hc g)) σ y X = _
    rw [show LeviCivita (scaleMetric c hc g) = LeviCivita g from lcConn_scaleMetric c hc g]
    exact pullbackFiberwiseLinearEquiv_apply_eq_of_const_smul _ hι₁.clm_bundle_map
      (LeviCivita g) ((Real.sqrt c)⁻¹) _ hκ₁.clm_bundle_map hscale hσ X
  have hEC (σ : ∀ y, ⋀[ℝ]^2 (V y)) (y : M)
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^2 F))
        (fun z => (⟨z, σ z⟩ : TotalSpace (⋀[ℝ]^2 F) (fun w => ⋀[ℝ]^2 (V w)))) y) :
      C.exteriorPower 2 σ y = D.exteriorPower 2 σ y := by
    apply ContinuousLinearMap.ext
    intro X
    exact exteriorPower_apply_congr C D (fun σ hσ => hDC σ y hσ) 2 σ X hσ
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hιinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  let : ContMDiffCovariantDerivative D ∞ :=
    ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv _ hι.clm_bundle_map
      hιinv.clm_bundle_map (LeviCivita g)
  exact rawBundleConnLap_selfAdjoint_scaleMetric_const_smul c hc g
    (D.exteriorPower 2) (C.exteriorPower 2) (hD.exteriorPower 2) (hC.exteriorPower 2)
    (exteriorPower_contMDiff D 2) hEC c⁻¹ A x

private theorem metric_curvature_selfAdjoint_laplacian_scaled
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (κ x).toContinuousLinearMap))
    (hscale : ∀ x v, κ x v = (Real.sqrt c)⁻¹ • ι x v)
    (hmetric : ∀ x v w, g.inner x (ι x v) (ι x w) = ⟪v, w⟫) (x : M) :
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let hκ₁ := hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let D := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv)
      hι₁.clm_bundle_map (LeviCivita g)
    let C := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv)
      hκ₁.clm_bundle_map (LeviCivita (scaleMetric c hc g))
    let hD := isMetricCompatible_pullback_leviCivita g ι hι₁ hmetric
    let hC := isMetricCompatible_pullback_leviCivita (scaleMetric c hc g) κ hκ₁
      (fun x v w => by rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric])
    let R := fun y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At g y).compContinuousLinearMap (fun _ => (ι y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
        (ι y).toContinuousLinearMap)
    let Q := fun y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (scaleMetric c hc g) y).compContinuousLinearMap
        (fun _ => (κ y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc g) y)).compContinuousLinearMap
        (κ y).toContinuousLinearMap)
    rawBundleConnLap (F := Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
      (V := fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)
      (scaleMetric c hc g) ((C.exteriorPower 2).selfAdjoint (hC.exteriorPower 2)) Q x =
    (c⁻¹ * c⁻¹) • rawBundleConnLap
      (F := Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V)).rank → ℝ)
      (V := fun y => (exteriorSelfAdjoint (I := I) (F := F) (V := V)).fiber y)
      g ((D.exteriorPower 2).selfAdjoint (hD.exteriorPower 2)) R x := by
  let T := fun y => (metricRm04At g y).compContinuousLinearMap
    (fun _ => (ι y).toContinuousLinearMap)
  let hT : ∀ y, IsAlgCurvForm (fun a b c d => T y ![a,b,c,d]) := fun y =>
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
      (ι y).toContinuousLinearMap
  have hTsmooth : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun y => TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) y (T y)) :=
    (metricRm04 g).contMDiff.multilinear_bundle_comp (fun _ => hι)
  let A := Bundle.ExteriorPower.traceNormalizedCurvatureSelfAdjointSection F V T hT hTsmooth
  have hscaled := scaled_selfAdjoint_laplacian c hc g ι κ hι hκ hscale hmetric A x
  have hmap (y : M) : (κ y).toContinuousLinearMap = (Real.sqrt c)⁻¹ • (ι y).toContinuousLinearMap := by
    ext v
    exact hscale y v
  have hR (y : M) : exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (scaleMetric c hc g) y).compContinuousLinearMap
        (fun _ => (κ y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc g) y)).compContinuousLinearMap
        (κ y).toContinuousLinearMap) = c⁻¹ • A y := by
    simp only [hmap]
    exact traceNormalizedCurvatureSelfAdjoint_scaleMetric_pullback c hc g y (ι y).toContinuousLinearMap
  dsimp only
  simp only [hR]
  exact hscaled

omit [∀ y, FiniteDimensional ℝ (V y)] in
theorem traceNormalizedCurvatureSelfAdjoint_pullback_laplacian_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (ι κ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hscale : ∀ x v, κ x v = (Real.sqrt c)⁻¹ • ι x v)
    (hmetric : ∀ x v w, g.inner x (ι x v) (ι x w) = ⟪v, w⟫) (x : M) :
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
        (fun x => TotalSpace.mk' (F →L[ℝ] E) x (κ x).toContinuousLinearMap) :=
      ((hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).const_smul_section
        (a := (Real.sqrt c)⁻¹)).congr (fun y => by
          congr 1
          ext v
          exact hscale y v)
    let D := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv)
      hι₁.clm_bundle_map (LeviCivita g)
    let C := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv)
      hκ₁.clm_bundle_map (LeviCivita (scaleMetric c hc g))
    let hD := isMetricCompatible_pullback_leviCivita g ι hι₁ hmetric
    let hC := isMetricCompatible_pullback_leviCivita (scaleMetric c hc g) κ hκ₁
      (fun x v w => by rw [hscale, hscale, scaleMetric_inner_inv_sqrt_smul, hmetric])
    let R := fun y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At g y).compContinuousLinearMap (fun _ => (ι y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
        (ι y).toContinuousLinearMap)
    let Q := fun y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((metricRm04At (scaleMetric c hc g) y).compContinuousLinearMap
        (fun _ => (κ y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc g) y)).compContinuousLinearMap
        (κ y).toContinuousLinearMap)
    rawBundleConnLap (F := Fin P.rank → ℝ)
      (V := fun y => P.fiber y)
      (scaleMetric c hc g) ((C.exteriorPower 2).selfAdjoint (hC.exteriorPower 2)) Q x =
    (c⁻¹ * c⁻¹) • rawBundleConnLap
      (F := Fin P.rank → ℝ)
      (V := fun y => P.fiber y)
      g ((D.exteriorPower 2).selfAdjoint (hD.exteriorPower 2)) R x := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  have hκ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (κ x).toContinuousLinearMap) :=
    (hι.const_smul_section (a := (Real.sqrt c)⁻¹)).congr (fun y => by
      congr 1
      ext v
      exact hscale y v)
  exact metric_curvature_selfAdjoint_laplacian_scaled c hc g ι κ hι hκ hscale hmetric x

end DifferentialGeometry.Geometry.Curvature
