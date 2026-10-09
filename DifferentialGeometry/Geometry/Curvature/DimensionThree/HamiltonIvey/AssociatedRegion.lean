import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance
import DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Associated
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.SelfAdjointRegion
import DifferentialGeometry.Geometry.Metric.SelfAdjointAssociated
import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

section

variable {B : Type*} (G : Type*) (V : B → Type*)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]

def hamiltonIveyTotalSpaceRegion (K : ℝ) :
    Set (TotalSpace G (fun x => selfAdjoint (V x →L[ℝ] V x))) :=
  {z | z.snd ∈ hamiltonIveyRegion K}

@[simp]
theorem mem_hamiltonIveyTotalSpaceRegion
    (z : TotalSpace G (fun x => selfAdjoint (V x →L[ℝ] V x))) (K : ℝ) :
    z ∈ hamiltonIveyTotalSpaceRegion G V K ↔ z.snd ∈ hamiltonIveyRegion K := Iff.rfl

end

variable {F B : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Torsor (F ≃ₗᵢ[ℝ] F) (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace (F ≃ₗᵢ[ℝ] F) P)]
  [FiberBundle (F ≃ₗᵢ[ℝ] F) P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners ℝ EP HP)
  [ChartedSpace HP (TotalSpace (F ≃ₗᵢ[ℝ] F) P)]

private local instance selfAdjointNormedAddCommGroup : NormedAddCommGroup (selfAdjoint.submodule ℝ (F →L[ℝ] F)) :=
  (selfAdjoint.submodule ℝ (F →L[ℝ] F)).normedAddCommGroup

private local instance selfAdjointNormedSpace : NormedSpace ℝ (selfAdjoint.submodule ℝ (F →L[ℝ] F)) :=
  (selfAdjoint.submodule ℝ (F →L[ℝ] F)).normedSpace

theorem isParallelClosedConvexFamily_associated_hamiltonIveyRegion
    {Q : Type*} [IsManifold I 1 B] [IsManifold IP 1 (TotalSpace (F ≃ₗᵢ[ℝ] F) P)]
    (A₀ : Set (Trivialization (F ≃ₗᵢ[ℝ] F) (π (F ≃ₗᵢ[ℝ] F) P)))
    (hA : ∀ e ∈ A₀, MemTrivializationAtlas e)
    (e₀ : B → Trivialization (F ≃ₗᵢ[ℝ] F) (π (F ≃ₗᵢ[ℝ] F) P))
    (he₀ : ∀ x, e₀ x ∈ A₀) (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A₀,
      ContMDiffOn IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) 1 e e.source ∧
      ContMDiffOn (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) IP 1
        e.toOpenPartialHomeomorph.symm e.target)
    {n : ℕ∞ω}
    (form : Q → PrincipalConnectionForm
      𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) (F ≃ₗᵢ[ℝ] F) IP P n)
    (hdim : Module.finrank ℝ F = 3) {K : ℝ} (hK : 0 < K) :
    let ρ := ContRepresentation.selfAdjointConjugation (W := F)
    let hρ := ContRepresentation.contMDiff_selfAdjointConjugation (W := F) (n := 1)
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A₀ hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A₀ hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I
      𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) 1 IP hρ A₀ hA e₀ he₀ hx₀ hP
    CovariantDerivative.IsParallelClosedConvexFamily
      (fun q => ρ.associatedCovariantDerivative I
        𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) IP
        hρ.continuous A₀ hA e₀ he₀ hx₀ (form q))
      {v : TotalSpace (selfAdjoint.submodule ℝ (F →L[ℝ] F))
        (fun y => P y →ₑ[ρ.toRepresentation] selfAdjoint.submodule ℝ (F →L[ℝ] F)) |
        v.snd ∈ ρ.toRepresentation.associatedSet (P v.proj) (hamiltonIveyRegion K)} := by
  apply ContRepresentation.selfAdjointConjugation.isParallelClosedConvexFamily_associatedSet
    I 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) IP
    (ContRepresentation.contMDiff_selfAdjointConjugation (W := F) (n := 1))
    A₀ hA e₀ he₀ hx₀ hP form
    (isClosed_hamiltonIveyRegion hK) (nonempty_hamiltonIveyRegion hK.le)
    (convex_hamiltonIveyRegion hdim hK)
  intro g A hA
  exact (mem_hamiltonIveyRegion_conj_iff g A K).mpr hA

section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Nonempty (V ≃ₗᵢ[ℝ] W)]

theorem selfAdjointAssociatedEquiv_mem_hamiltonIveyRegion_iff
    (A : selfAdjoint.submodule ℝ (V →L[ℝ] V)) (K : ℝ) :
    LinearIsometryEquiv.selfAdjointAssociatedEquiv (W := W) A ∈
      (ContRepresentation.selfAdjointConjugation (W := W)).toRepresentation.associatedSet
        (V ≃ₗᵢ[ℝ] W) (hamiltonIveyRegion K) ↔ A ∈ hamiltonIveyRegion K := by
  change (∀ p : V ≃ₗᵢ[ℝ] W, _ ∈ hamiltonIveyRegion K) ↔ _
  constructor
  · intro h
    let p := Classical.choice (inferInstance : Nonempty (V ≃ₗᵢ[ℝ] W))
    exact (mem_hamiltonIveyRegion_conj_iff p A K).mp (h p)
  · intro h p
    exact (mem_hamiltonIveyRegion_conj_iff p A K).mpr h

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsContMDiffRiemannianBundle I n F V]

theorem isClosed_totalSpace_hamiltonIveyRegion {K : ℝ} (hK : 0 < K) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := n)
    letI := S.totalSpaceTopology
    IsClosed {z : TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x) |
      z.snd ∈ hamiltonIveyRegion K} := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := n)
  let := S.totalSpaceTopology
  let := S.fiberBundle
  let := S.vector_bundle
  let := S.contMDiffVectorBundle
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  let G := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))
  let p₀ : V z.proj ≃ₗᵢ[ℝ] G :=
    ((stdOrthonormalBasis ℝ (V z.proj)).reindex
      (finCongr (VectorBundle.finrank_eq ℝ F V z.proj))).repr
  obtain ⟨U, hU, hzU, q, _, hq⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe_to (I := I) (F := F) (n := n) z.proj p₀
  let T := TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x)
  let c : T → selfAdjoint (G →L[ℝ] G) := fun y =>
    ⟨(q y.proj).conjStarAlgEquiv (y.snd : V y.proj →L[ℝ] V y.proj),
      y.snd.property.map (q y.proj).conjStarAlgEquiv⟩
  have hproj : ContMDiff (I.prod 𝓘(ℝ, Fin S.rank → ℝ)) I n (TotalSpace.proj : T → M) :=
    (Bundle.contMDiff_proj _).of_le le_top
  have hcoords := LinearIsometryEquiv.contMDiffOn_coframe_conjugate
    (q := fun y : T => q y.proj) (A := fun y : T => (y.snd : V y.proj →L[ℝ] V y.proj))
    (s := TotalSpace.proj ⁻¹' U)
    (fun w => (hq w).comp hproj.contMDiffOn (fun y hy => hy))
    (S.contMDiff_subtypeVal.contMDiffOn)
  have hdom : TotalSpace.proj ⁻¹' U ∈ 𝓝 z :=
    hproj.continuous.continuousAt (hU.mem_nhds hzU)
  have hc : ContinuousAt c z := by
    apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    exact hcoords.continuousOn.continuousAt hdom
  have hn : c z ∉ hamiltonIveyRegion K := by
    intro h
    exact hz ((mem_hamiltonIveyRegion_conj_iff (q z.proj) z.snd K).mp h)
  have hne := hc ((isClosed_hamiltonIveyRegion hK).isOpen_compl.mem_nhds hn)
  change c ⁻¹' (hamiltonIveyRegion K)ᶜ ∈ 𝓝 z at hne
  apply Filter.mem_of_superset hne
  intro y hy h
  exact hy ((mem_hamiltonIveyRegion_conj_iff (q y.proj) y.snd K).mpr h)

end

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffVectorBundle ∞ F V I]

theorem isParallelSet_selfAdjoint_hamiltonIveyRegion
    (cov : CovariantDerivative I F V) (hmetric : cov.IsMetricCompatible)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞) (K : ℝ) :
    let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    let := S.totalSpaceTopology
    let := S.fiberBundle
    let := S.vector_bundle
    let := S.contMDiffVectorBundle
    (cov.selfAdjoint hmetric).IsParallelSet
      {z : TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x) |
        z.snd ∈ hamiltonIveyRegion K} := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let := S.totalSpaceTopology
  let := S.fiberBundle
  let := S.vector_bundle
  let := S.contMDiffVectorBundle
  let D := HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
  let hS := HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
    cov hmetric
  have hinc := (ContMDiff.clm_bundle_of_map
    (φ := fun x => (S.fiber x).subtypeL) S.contMDiff_subtypeVal).mdifferentiable (by simp)
  have hincpar := CovariantDerivative.homBundleCovariantDerivativeGen_subtypeL_restrict D S hS
  constructor
  intro a b t₀ γ Z ht₀ hγ hZ hZpar hinit t ht
  have hγd := hγ.mdifferentiableOn (by simp)
  let A := fun s => (Z s : V (γ s) →L[ℝ] V (γ s))
  have hA : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F →L[ℝ] F))
      (fun s => (⟨γ s, A s⟩ : TotalSpace (F →L[ℝ] F)
        (fun x => V x →L[ℝ] V x))) (Icc a b) := by
    intro s hs
    exact (S.contMDiff_subtypeVal.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt s (hZ s hs)
  have hApar : ∀ s ∈ Icc a b, D.derivAlongWithin γ A (Icc a b) s = 0 := by
    intro s hs
    change D.derivAlongWithin γ (fun r => (S.fiber (γ r)).subtypeL (Z r)) (Icc a b) s = 0
    rw [CovariantDerivative.derivAlongWithin_clm_section_apply_of_parallel
      (D.restrict S hS) D (fun x => (S.fiber x).subtypeL) (hinc (γ s))
      (congrFun hincpar (γ s)) (hγd s hs) (hZ s hs)]
    change (S.fiber (γ s)).subtypeL ((cov.selfAdjoint hmetric).derivAlongWithin
      γ Z (Icc a b) s) = 0
    rw [hZpar s hs, map_zero]
  obtain ⟨e, he⟩ := CovariantDerivative.exists_linearIsometryEquiv_conj_of_parallel_endomorphism hmetric
    hcov ht₀ ht hγ hA hApar
  have hconj : (⟨e.conjStarAlgEquiv (Z t₀ : V (γ t₀) →L[ℝ] V (γ t₀)),
      (Z t₀).property.map e.conjStarAlgEquiv⟩ : selfAdjoint (V (γ t) →L[ℝ] V (γ t))) = Z t := by
    apply Subtype.ext
    ext v
    exact congrArg (fun B => B v) he
  change Z t ∈ hamiltonIveyRegion K
  rw [← hconj]
  exact (mem_hamiltonIveyRegion_conj_iff e (Z t₀) K).mpr hinit

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffVectorBundle ∞ F V I]

theorem isParallelClosedConvexFamily_selfAdjoint_hamiltonIveyRegion
    {Q : Type*} (cov : Q → CovariantDerivative I F V)
    (hmetric : ∀ q, (cov q).IsMetricCompatible)
    (hcov : ∀ q, CovariantDerivative.ContMDiffCovariantDerivative (cov q) ∞)
    (hdim : Module.finrank ℝ F = 3) {K : ℝ} (hK : 0 < K) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    letI := S.contMDiffVectorBundle
    CovariantDerivative.IsParallelClosedConvexFamily
      (fun q => (cov q).selfAdjoint (hmetric q))
      {z : TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x) |
        z.snd ∈ hamiltonIveyRegion K} := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let := S.totalSpaceTopology
  let := S.fiberBundle
  let := S.vector_bundle
  let := S.contMDiffVectorBundle
  refine ⟨isClosed_totalSpace_hamiltonIveyRegion (I := I) (F := F) (V := V) hK,
    ?_, ?_, ?_⟩
  · intro x
    exact nonempty_hamiltonIveyRegion hK.le
  · intro x
    apply convex_hamiltonIveyRegion _ hK
    exact (VectorBundle.finrank_eq ℝ F V x).trans hdim
  · intro q
    exact isParallelSet_selfAdjoint_hamiltonIveyRegion (cov q) (hmetric q) (hcov q) K

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffVectorBundle ∞ F V I]

theorem isParallelClosedConvexFamily_selfAdjoint_exteriorPower_hamiltonIveyRegion
    {Q : Type*} (cov : Q → CovariantDerivative I F V)
    (hmetric : ∀ q, (cov q).IsMetricCompatible)
    (hcov : ∀ q, CovariantDerivative.ContMDiffCovariantDerivative (cov q) ∞)
    (hdim : Module.finrank ℝ F = 3) {K : ℝ} (hK : 0 < K) :
    let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let := Bundle.ExteriorPower.totalSpaceTopology F V 2
    let := Bundle.ExteriorPower.fiberBundle F V 2
    let := Bundle.ExteriorPower.vector_bundle F V 2
    let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let S := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
    let := S.totalSpaceTopology
    let := S.fiberBundle
    let := S.vector_bundle
    let := S.contMDiffVectorBundle
    CovariantDerivative.IsParallelClosedConvexFamily
      (fun q => ((cov q).exteriorPower 2).selfAdjoint ((hmetric q).exteriorPower 2))
      (hamiltonIveyTotalSpaceRegion (Fin S.rank → ℝ) (fun x => ⋀[ℝ]^2 (V x)) K) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  apply isParallelClosedConvexFamily_selfAdjoint_hamiltonIveyRegion
    (fun q => (cov q).exteriorPower 2) (fun q => (hmetric q).exteriorPower 2) _ _ hK
  · intro q
    let := hcov q
    exact (cov q).exteriorPower_contMDiff 2
  · rw [_root_.exteriorPower.finrank_eq, hdim]
    decide

end

end DifferentialGeometry.Geometry.Curvature.DimensionThree
