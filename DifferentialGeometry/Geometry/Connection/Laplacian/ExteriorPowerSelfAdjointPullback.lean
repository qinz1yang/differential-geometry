import DifferentialGeometry.Geometry.Connection.Laplacian.SelfAdjointConjugate
import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPowerEndomorphismPullback
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower

noncomputable section

open Bundle
open DifferentialGeometry.HomConnectionGen
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]

variable [∀ x, FiniteDimensional ℝ (V x)]

private local instance exteriorTotalSpaceTopology (k : ℕ) :
    TopologicalSpace (TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))) :=
  Bundle.ExteriorPower.totalSpaceTopology F V k

private local instance exteriorFiberBundle (k : ℕ) : FiberBundle (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) :=
  Bundle.ExteriorPower.fiberBundle F V k

private local instance exteriorVectorBundle (k : ℕ) : VectorBundle ℝ (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) :=
  Bundle.ExteriorPower.vector_bundle F V k

private local instance exteriorContMDiffVectorBundle (k : ℕ) :
    ContMDiffVectorBundle ∞ (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) I :=
  Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k

private local instance exteriorRiemannianBundle (k : ℕ) :
    IsContMDiffRiemannianBundle I ∞ (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) :=
  Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V k

private def exteriorSelfAdjoint (k : ℕ) :=
  selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^k F) (V := fun x => ⋀[ℝ]^k (V x)) (n := ∞)

private local instance selfAdjointTotalSpaceTopology (k : ℕ) : TopologicalSpace
    (TotalSpace (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ)
      (fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x)) :=
  (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).totalSpaceTopology

private local instance selfAdjointFiberBundle (k : ℕ) : FiberBundle
    (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ)
    (fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x) :=
  (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiberBundle

private local instance selfAdjointVectorBundle (k : ℕ) : VectorBundle ℝ
    (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ)
    (fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x) :=
  (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).vector_bundle

private def exteriorSelfAdjointConnection (k : ℕ)
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    CovariantDerivative I
      (Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ)
      (fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x) :=
  (cov.exteriorPower k).selfAdjoint (hcov.exteriorPower k)

private def exteriorSelfAdjointHessian (k : ℕ)
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Cₛ^∞⟮I; Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ,
      fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x⟯)
    (x : M) (X Y : TangentSpace I x) : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x) :=
  ((exteriorSelfAdjointConnection k cov hcov).hessian base A x X Y :
    (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x))

private def exteriorSelfAdjointLaplacian (k : ℕ)
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (A : Cₛ^∞⟮I; Fin (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).rank → ℝ,
      fun x => (exteriorSelfAdjoint (I := I) (F := F) (V := V) k).fiber x⟯)
    (x : M) : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x) :=
  (DifferentialGeometry.Geometry.Connection.rawBundleConnLap g
    (exteriorSelfAdjointConnection k cov hcov) A x :
      (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x))

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ I] [IsContMDiffRiemannianBundle I ∞ F₂ V₂]

variable (k : ℕ)

local notation "W₁" => (fun x : M => (⋀[ℝ]^k (V₁ x) : Type _))
local notation "W₂" => (fun x : M => (⋀[ℝ]^k (V₂ x) : Type _))
local notation "S₂" => exteriorSelfAdjoint (I := I) (F := F₂) (V := V₂) k

namespace CovariantDerivative

omit [ContMDiffVectorBundle ∞ F₁ V₁ I] [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₂ V₂ I] [IsContMDiffRiemannianBundle I ∞ F₂ V₂] in
private theorem contMDiff_pullback_isometry
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
        (hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map cov) ∞ := by
  let : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
  have hφinv : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) ∞
      (fun y => TotalSpace.mk' (F₂ →L[ℝ] F₁) y
        (φ y).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv,
      LinearIsometryEquiv.toContinuousLinearEquiv_symm] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map hφinv.clm_bundle_map cov

private def pullbackIsometryConnection
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) : CovariantDerivative I F₁ V₁ :=
  pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
    (hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map cov

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem pullbackIsometryConnection_metric
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) (hcov : cov.IsMetricCompatible) :
    (pullbackIsometryConnection φ hφ cov).IsMetricCompatible :=
  hcov.pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
    (hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map
    (fun y v w => (φ y).inner_map_map v w)

section

variable [∀ y, FiniteDimensional ℝ (V₁ y)] [∀ y, FiniteDimensional ℝ (V₂ y)]

private def exteriorSelfAdjointConjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (A : Cₛ^∞⟮I; Fin (S₂).rank → ℝ, fun x => (S₂).fiber x⟯) :
    Cₛ^∞⟮I; Fin (exteriorSelfAdjoint (I := I) (F := F₁) (V := V₁) k).rank → ℝ,
      fun x => (exteriorSelfAdjoint (I := I) (F := F₁) (V := V₁) k).fiber x⟯ :=
  ContMDiffSection.selfAdjointConjugate
    (fun y => _root_.exteriorPower.mapLinearIsometryEquiv k (φ y))
    (Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k ∞
      (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap) hφ) A

end

theorem map_exteriorPower_selfAdjoint_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) (hcov : cov.IsMetricCompatible) :
    letI : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
    letI : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
    ∀ (A : Cₛ^∞⟮I; Fin (S₂).rank → ℝ, fun x => (S₂).fiber x⟯)
      (x : M) (X : TangentSpace I x),
    let Q := fun y => _root_.exteriorPower.mapLinearIsometryEquiv k (φ y)
    let hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k ∞
      (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap) hφ
    let hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let d := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov
    let hd := hcov.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map
      (fun y v w => (φ y).inner_map_map v w)
    let B := ContMDiffSection.selfAdjointConjugate Q hQ A
    (Q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (exteriorSelfAdjointConnection k d hd B x X : W₁ x →L[ℝ] W₁ x) =
      (exteriorSelfAdjointConnection k cov hcov A x X : W₂ x →L[ℝ] W₂ x).comp
        (Q x).toContinuousLinearEquiv.toContinuousLinearMap := by
  let : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
  let : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
  dsimp only
  intro A x X
  let Q := fun y => _root_.exteriorPower.mapLinearIsometryEquiv k (φ y)
  have hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k ∞
    (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap) hφ
  have hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let d := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov
  have hd := hcov.pullbackFiberwiseLinearEquiv
    (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map (fun y v w => (φ y).inner_map_map v w)
  exact map_selfAdjoint_conjugate Q hQ (d.exteriorPower k) (hd.exteriorPower k)
    (cov.exteriorPower k) (hcov.exteriorPower k)
    (homBundleCovariantDerivativeGen_exteriorPower_map
      (fun y => (φ y).toContinuousLinearEquiv) hφ₁ cov k) A x X

theorem map_exteriorPower_selfAdjoint_hessian_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) (hcov : cov.IsMetricCompatible)
    [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    letI : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
    letI : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
    ∀ (A : Cₛ^∞⟮I; Fin (S₂).rank → ℝ, fun x => (S₂).fiber x⟯)
      (x : M) (X Y : TangentSpace I x),
    let q := (_root_.exteriorPower.mapLinearIsometryEquiv k (φ x)).toContinuousLinearEquiv
      |>.toContinuousLinearMap
    q.comp
        (exteriorSelfAdjointHessian k (pullbackIsometryConnection φ hφ cov)
          (pullbackIsometryConnection_metric φ hφ cov hcov) base
          (exteriorSelfAdjointConjugate k φ hφ A) x X Y) =
      (exteriorSelfAdjointHessian k cov hcov base A x X Y).comp
        q := by
  let : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
  let : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
  dsimp only
  intro A x X Y
  let Q := fun y => _root_.exteriorPower.mapLinearIsometryEquiv k (φ y)
  have hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k ∞
    (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap) hφ
  have hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let d := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov
  have hd := hcov.pullbackFiberwiseLinearEquiv
    (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map (fun y v w => (φ y).inner_map_map v w)
  let : ContMDiffCovariantDerivative d ∞ := contMDiff_pullback_isometry φ hφ cov
  let := d.exteriorPower_contMDiff k
  let := cov.exteriorPower_contMDiff k
  exact map_selfAdjoint_hessian_conjugate Q hQ (d.exteriorPower k) (hd.exteriorPower k)
    (cov.exteriorPower k) (hcov.exteriorPower k)
    (homBundleCovariantDerivativeGen_exteriorPower_map
      (fun y => (φ y).toContinuousLinearEquiv) hφ₁ cov k) base A x X Y

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

open CovariantDerivative

theorem map_rawBundleConnLap_exteriorPower_selfAdjoint_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) (hcov : cov.IsMetricCompatible)
    [ContMDiffCovariantDerivative cov ∞] (g : SmoothRiemannianMetric I M) :
    letI : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
    letI : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
    ∀ (A : Cₛ^∞⟮I; Fin (S₂).rank → ℝ, fun x => (S₂).fiber x⟯) (x : M),
    let q := (_root_.exteriorPower.mapLinearIsometryEquiv k (φ x)).toContinuousLinearEquiv
      |>.toContinuousLinearMap
    q.comp
        (exteriorSelfAdjointLaplacian k (pullbackIsometryConnection φ hφ cov)
          (pullbackIsometryConnection_metric φ hφ cov hcov) g
          (exteriorSelfAdjointConjugate k φ hφ A) x) =
      (exteriorSelfAdjointLaplacian k cov hcov g A x).comp q := by
  let : ∀ y, FiniteDimensional ℝ (V₁ y) := fun y => VectorBundle.finiteDimensional ℝ F₁ V₁ y
  let : ∀ y, FiniteDimensional ℝ (V₂ y) := fun y => VectorBundle.finiteDimensional ℝ F₂ V₂ y
  dsimp only
  intro A x
  let Q := fun y => _root_.exteriorPower.mapLinearIsometryEquiv k (φ y)
  have hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k ∞
    (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap) hφ
  have hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let d := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov
  have hd := hcov.pullbackFiberwiseLinearEquiv
    (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map (fun y v w => (φ y).inner_map_map v w)
  let : ContMDiffCovariantDerivative d ∞ := contMDiff_pullback_isometry φ hφ cov
  let := d.exteriorPower_contMDiff k
  let := cov.exteriorPower_contMDiff k
  exact map_rawBundleConnLap_selfAdjoint_conjugate Q hQ (d.exteriorPower k) (hd.exteriorPower k)
    (cov.exteriorPower k) (hcov.exteriorPower k)
    (homBundleCovariantDerivativeGen_exteriorPower_map
      (fun y => (φ y).toContinuousLinearEquiv) hφ₁ cov k) g A x

end DifferentialGeometry.Geometry.Connection
