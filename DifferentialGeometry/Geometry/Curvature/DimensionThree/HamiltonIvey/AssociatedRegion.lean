import DifferentialGeometry.Geometry.Connection.ParallelTransport.Associated
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.SelfAdjointRegion
import DifferentialGeometry.Geometry.Metric.SelfAdjointAssociated
import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

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
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
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
  obtain ⟨U, hU, hzU, q, _, hq⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (F := F) (n := n) z.proj
      (FiberBundle.linearIsometryEquivAt (F := F) V z.proj)
  let T := TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x)
  let c : T → selfAdjoint (F →L[ℝ] F) := fun y =>
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
