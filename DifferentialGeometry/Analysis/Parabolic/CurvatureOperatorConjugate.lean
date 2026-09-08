import DifferentialGeometry.Analysis.Parabolic.CurvatureReactionConjugate
import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPowerEndomorphismPullback
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorConjugation
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Connection.Laplacian.ExteriorPowerSelfAdjointPullback

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.HomConnectionGen
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic


section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

private theorem hom_exterior_pulled_leviCivita_initial_map_eq_zero
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (U : ∀ x, W x ≃L[ℝ] V x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ x).toContinuousLinearMap))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) 1
      (fun x => TotalSpace.mk' (G →L[ℝ] F) x (U x).toContinuousLinearMap))
    (heq : ∀ x, κ x = (U x).trans (ι x)) (k : ℕ) :
    let d := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv) hκ.clm_bundle_map
      (LeviCivita g)
    let c := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map
      (LeviCivita g)
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI : ∀ y, FiniteDimensional ℝ (W y) := fun y => VectorBundle.finiteDimensional ℝ G W y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    letI := Bundle.ExteriorPower.totalSpaceTopology G W k
    letI := Bundle.ExteriorPower.fiberBundle G W k
    letI := Bundle.ExteriorPower.vector_bundle G W k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) G W k
    homBundleCovariantDerivativeGen I M _ _ _ _ (d.exteriorPower k) (c.exteriorPower k)
      (fun y => exteriorPower.mapContinuousLinearMap k (U y).toContinuousLinearMap) = 0 := by
  let d := pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv) hκ.clm_bundle_map
    (LeviCivita g)
  let c := pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map
    (LeviCivita g)
  have hconn := pullback_leviCivita_conjugate g ι κ U hι hκ hU heq
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ : ∀ y, FiniteDimensional ℝ (W y) := fun y => VectorBundle.finiteDimensional ℝ G W y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V k
  let _ := Bundle.ExteriorPower.fiberBundle F V k
  let _ := Bundle.ExteriorPower.vector_bundle F V k
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  let _ := Bundle.ExteriorPower.totalSpaceTopology G W k
  let _ := Bundle.ExteriorPower.fiberBundle G W k
  let _ := Bundle.ExteriorPower.vector_bundle G W k
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) G W k
  change homBundleCovariantDerivativeGen I M _ _ _ _ (d.exteriorPower k) (c.exteriorPower k)
    (fun y => exteriorPower.mapContinuousLinearMap k (U y).toContinuousLinearMap) = 0
  have hd : d = pullbackFiberwiseLinearEquiv (fun y => (U y).toLinearEquiv) hU.clm_bundle_map c :=
    hconn
  rw [hd]
  exact homBundleCovariantDerivativeGen_exteriorPower_map U hU c k


end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private def pulledMetricCurvatureSliceSmooth
    (g : SmoothRiemannianMetric I M) (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x) : Prop :=
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
  let T := fun y => (metricRm04At (I := I) g y).compContinuousLinearMap
    (fun _ => (ι y).toContinuousLinearMap)
  let hT := fun y =>
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
        (ι y).toContinuousLinearMap
  let R : ∀ y, P.fiber y := fun y =>
    exteriorPower.traceNormalizedCurvatureSelfAdjoint (T y) (hT y)
  ContMDiff I (I.prod 𝓘(ℝ, Fin P.rank → ℝ)) ∞
    (fun y => TotalSpace.mk' (Fin P.rank → ℝ) y (R y))

private theorem pulledMetricCurvatureSlice_contMDiff
    (g : SmoothRiemannianMetric I M) (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap)) :
    pulledMetricCurvatureSliceSmooth (F := F) g ι := by
  unfold pulledMetricCurvatureSliceSmooth
  intro P T hT R
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let _ := P.totalSpaceTopology
  let _ := P.fiberBundle
  have hTsmooth := (metricRm04 (I := I) g).contMDiff.multilinear_bundle_comp (fun _ => hι)
  let Rsection := Bundle.ExteriorPower.traceNormalizedCurvatureSelfAdjointSection F V T hT hTsmooth
  exact Rsection.contMDiff


end


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
  [IsContMDiffRiemannianBundle I ∞ G W]

omit [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem pullback_leviCivita_contMDiff
    (g : SmoothRiemannianMetric I M)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap)) :
    ContMDiffCovariantDerivative (pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv)
      (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita g)) ∞ := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hιinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map hιinv.clm_bundle_map (LeviCivita g)

private def metricCurvatureHeat
    (g : ℝ → SmoothRiemannianMetric I M)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (J : Set ℝ) (t : ℝ)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hιmetric : ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) : Prop :=
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let c := pullbackFiberwiseLinearEquiv (fun y => (ι t y).toLinearEquiv)
    hι₁.clm_bundle_map (LeviCivita (g t))
  let hc := isMetricCompatible_pullback_leviCivita (g t) (ι t) hι₁ hιmetric
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
  let T := fun s y => metricRm04At (g s) y
  let hT : ∀ s y, IsAlgCurvForm (fun a b c d => T s y ![a, b, c, d]) := fun s y =>
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g s) y)
  let R : ℝ → ∀ y, P.fiber y := fun s y => exteriorPower.traceNormalizedCurvatureSelfAdjoint
    ((T s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
    ((hT s y).compContinuousLinearMap (ι s y).toContinuousLinearMap)
  let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
  HasDerivWithinAt (fun s => R s x)
    (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y) (g t)
      ((c.exteriorPower 2).selfAdjoint (F := ⋀[ℝ]^2 F)
        (V := fun y => ⋀[ℝ]^2 (V y)) (hc.exteriorPower 2)) (R t) x + Q) J t


private theorem metric_curvature_heat_gauge_iff
    (g : ℝ → SmoothRiemannianMetric I M)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ℝ → ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (φ : ∀ x, W x ≃ₗᵢ[ℝ] V x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] F) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (J : Set ℝ) (t : ℝ) (ht : t ∈ J)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ t x).toContinuousLinearMap))
    (hιmetric : ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hκmetric : ∀ x v w, (g t).inner x (κ t x v) (κ t x w) = ⟪v, w⟫)
    (heq : ∀ s ∈ J, ∀ x, κ s x = (φ x).toContinuousLinearEquiv.trans (ι s x)) :
    ∀ x, metricCurvatureHeat g κ J t hκ hκmetric x ↔
      metricCurvatureHeat g ι J t hι hιmetric x := by
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let hκ₁ := hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let c := pullbackFiberwiseLinearEquiv (fun y => (ι t y).toLinearEquiv)
    hι₁.clm_bundle_map (LeviCivita (g t))
  let d := pullbackFiberwiseLinearEquiv (fun y => (κ t y).toLinearEquiv)
    hκ₁.clm_bundle_map (LeviCivita (g t))
  let hc := isMetricCompatible_pullback_leviCivita (g t) (ι t) hι₁ hιmetric
  let hd := isMetricCompatible_pullback_leviCivita (g t) (κ t) hκ₁ hκmetric
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ : ∀ x, FiniteDimensional ℝ (W x) := fun x => VectorBundle.finiteDimensional ℝ G W x
  let _ : ∀ x, NormedAddCommGroup (⋀[ℝ]^2 (V x)) := fun x => inferInstance
  let _ : ∀ x, InnerProductSpace ℝ (⋀[ℝ]^2 (V x)) := fun x => inferInstance
  let _ : ∀ x, NormedSpace ℝ (⋀[ℝ]^2 (V x)) := fun x => inferInstance
  let _ : ∀ x, NormedAddCommGroup (⋀[ℝ]^2 (W x)) := fun x => inferInstance
  let _ : ∀ x, InnerProductSpace ℝ (⋀[ℝ]^2 (W x)) := fun x => inferInstance
  let _ : ∀ x, NormedSpace ℝ (⋀[ℝ]^2 (W x)) := fun x => inferInstance
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.totalSpaceTopology G W 2
  let _ := Bundle.ExteriorPower.fiberBundle G W 2
  let _ := Bundle.ExteriorPower.vector_bundle G W 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) G W 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) G W 2
  let T := fun s x => metricRm04At (g s) x
  let hT : ∀ s x, IsAlgCurvForm (fun a b c d => T s x ![a, b, c, d]) := fun s x =>
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g s) x)
  let R : ℝ → ∀ x, selfAdjoint ((⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) := fun s x => exteriorPower.traceNormalizedCurvatureSelfAdjoint
    ((T s x).compContinuousLinearMap (fun _ => (ι s x).toContinuousLinearMap))
    ((hT s x).compContinuousLinearMap (ι s x).toContinuousLinearMap)
  let Rhat : ℝ → ∀ x, selfAdjoint ((⋀[ℝ]^2 (W x)) →L[ℝ] ⋀[ℝ]^2 (W x)) := fun s x => exteriorPower.traceNormalizedCurvatureSelfAdjoint
    ((T s x).compContinuousLinearMap (fun _ => (κ s x).toContinuousLinearMap))
    ((hT s x).compContinuousLinearMap (κ s x).toContinuousLinearMap)
  let e := fun x => exteriorPower.mapLinearIsometryEquiv 2 (φ x)
  have he : ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^2 G) →L[ℝ] ⋀[ℝ]^2 F)) ∞
      (fun x => TotalSpace.mk' ((⋀[ℝ]^2 G) →L[ℝ] ⋀[ℝ]^2 F) x
        (e x).toContinuousLinearEquiv.toContinuousLinearMap) :=
    Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap 2 ∞
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) hφ
  have hparallel := hom_exterior_pulled_leviCivita_initial_map_eq_zero
    (g t) (ι t) (κ t) (fun x => (φ x).toContinuousLinearEquiv) hι₁ hκ₁
      (hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) (heq t ht) 2
  let _ : ContMDiffCovariantDerivative c ∞ := pullback_leviCivita_contMDiff (g t) (ι t) hι
  let _ : ContMDiffCovariantDerivative d ∞ := pullback_leviCivita_contMDiff (g t) (κ t) hκ
  let _ := c.exteriorPower_contMDiff 2
  let _ := d.exteriorPower_contMDiff 2
  have hRsmooth := pulledMetricCurvatureSlice_contMDiff (g t) (ι t) hι
  have hconj : ∀ s ∈ J, ∀ x, (Rhat s x : (⋀[ℝ]^2 (W x)) →L[ℝ] ⋀[ℝ]^2 (W x)) =
      (e x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((R s x : (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)).comp
          (e x).toContinuousLinearEquiv.toContinuousLinearMap) := by
    intro s hs x
    exact exteriorPower.traceNormalizedCurvatureEndomorphism_pullback_conjugate (T s x) (hT s x) (ι s x) (κ s x) (φ x) (heq s hs x)
  exact hasDerivWithinAt_selfAdjoint_reaction_heat_conjugate_iff e he
    (d.exteriorPower 2) (hd.exteriorPower 2) (c.exteriorPower 2) (hc.exteriorPower 2)
    hparallel (g t) Rhat R J t ht hRsmooth hconj

theorem hasDerivWithinAt_curvatureOperator_pullback_conjugate_iff
    (g : ℝ → SmoothRiemannianMetric I M)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ℝ → ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (φ : ∀ x, W x ≃ₗᵢ[ℝ] V x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] F) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (J : Set ℝ) (t : ℝ) (ht : t ∈ J)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ t x).toContinuousLinearMap))
    (hιmetric : ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hκmetric : ∀ x v w, (g t).inner x (κ t x v) (κ t x w) = ⟪v, w⟫)
    (heq : ∀ s ∈ J, ∀ x, κ s x = (φ x).toContinuousLinearEquiv.trans (ι s x)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, FiniteDimensional ℝ (W x) := fun x => VectorBundle.finiteDimensional ℝ G W x
    let c := pullbackFiberwiseLinearEquiv (fun x => (ι t x).toLinearEquiv)
      (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t))
    let d := pullbackFiberwiseLinearEquiv (fun x => (κ t x).toLinearEquiv)
      (hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t))
    let hc := isMetricCompatible_pullback_leviCivita (g t) (ι t)
      (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hιmetric
    let hd := isMetricCompatible_pullback_leviCivita (g t) (κ t)
      (hκ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) hκmetric
    let T := fun s x => metricRm04At (g s) x
    let hT := fun s x => mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g s) x)
    let R := fun s x => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((T s x).compContinuousLinearMap (fun _ => (ι s x).toContinuousLinearMap))
      ((hT s x).compContinuousLinearMap (ι s x).toContinuousLinearMap)
    let Rhat := fun s x => exteriorPower.traceNormalizedCurvatureSelfAdjoint
      ((T s x).compContinuousLinearMap (fun _ => (κ s x).toContinuousLinearMap))
      ((hT s x).compContinuousLinearMap (κ s x).toContinuousLinearMap)
    ∀ x, HasDerivWithinAt (fun s => Rhat s x)
      (d.exteriorPowerSelfAdjointLaplacian 2 hd (g t) (Rhat t) x +
        curvatureOperatorReactionSelfAdjoint3 (Rhat t x)) J t ↔
      HasDerivWithinAt (fun s => R s x)
      (c.exteriorPowerSelfAdjointLaplacian 2 hc (g t) (R t) x +
        curvatureOperatorReactionSelfAdjoint3 (R t x)) J t := by
  exact metric_curvature_heat_gauge_iff g ι κ φ hφ J t ht hι hκ hιmetric hκmetric heq

end DifferentialGeometry.Analysis.Parabolic
