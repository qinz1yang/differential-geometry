import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmOperatorFieldApplication
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieArm2DivSlotPermA : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

def deTurckLieArm2DivSlotPermAT : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

theorem deTurckLieArm2DivSlotPermA_apply :
    deTurckLieArm2DivSlotPermA 0 = 2 ∧ deTurckLieArm2DivSlotPermA 1 = 0 ∧
      deTurckLieArm2DivSlotPermA 2 = 3 ∧ deTurckLieArm2DivSlotPermA 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem deTurckLieArm2DivSlotPermAT_apply :
    deTurckLieArm2DivSlotPermAT 0 = 3 ∧ deTurckLieArm2DivSlotPermAT 1 = 0 ∧
      deTurckLieArm2DivSlotPermAT 2 = 2 ∧ deTurckLieArm2DivSlotPermAT 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def domDomCongrFibPerm (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrFibPerm_apply (σ : Equiv.Perm (Fin 4)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFibPerm (I := I) σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibPerm]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def deTurckLieTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFibPerm (I := I) σ x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongr_section_contMDiff_local {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j)))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckLieTraceFib_contMDiff (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (deTurckLieTraceFib (I := I) g₁ σ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => deTurckLieTraceFib (I := I) g₁ σ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff_local (I := I) σ (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

noncomputable def deTurckLieTraceCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x)
      contMDiff_toFun := deTurckLieTraceFib_contMDiff (I := I) g₁ σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
@[simp] theorem deTurckLieTraceCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieTraceCoeff_metricPerturbationPath_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieTraceCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) σ).toSection p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => deTurckLieTraceFib (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) σ p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hYρ := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hCDT := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYρ
  refine hCDT.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  change deTurckLieTraceFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) σ p.1 (Y p.1) = _
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)


def deTurckLieArm2PrincipalCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA
    + deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT
    - traceHessianCoeff (I := I) (M := M) g₀ g₁

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieArm2PrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hA := deTurckLieTraceCoeff_metricPerturbationPath_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermA
  have hAT := deTurckLieTraceCoeff_metricPerturbationPath_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermAT
  have hH := traceHessianCoeff_metricPerturbationPath_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add_local (I := I) (r := 4) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1)
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    hA hAT
  have hsub := jointTotalSpaceRS_sub_local (I := I) (r := 4) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1
        + (deTurckLieTraceCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    (fun p : M × ℝ => (traceHessianCoeff (I := I) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hadd hH
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckLieArm2PrincipalCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckLieArm2PrincipalCoeff (I := I) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') :=
  deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointContMDiff (I := I) g₀ T T' hδ hδ'

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma operatorFieldApplication_sub_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma operatorFieldApplication_add_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ + Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W + operatorFieldApply (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W +
      operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x +
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    add_apply, Tensor0SSpace.toModel_add, add_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_sub2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (S - S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v - unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply, Tensor0SSpace.toModel_sub, sub_apply]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckLieTraceCoeff_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (D : SmoothCcTensor g₀ 0 4) (x : M)
    (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ) D) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g₀ 4 D x)
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) =
      deTurckLieTraceFib (I := I) g₁ σ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply,
    cometricDoubleTraceFib_toModel, Tensor0SSpace.toModel_ofModel, modelDoubleTrace_apply]
  simp only [unitModel]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem traceHessianCoeff_operatorFieldApplication_eq_local
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 4 I x from W.toSection x)
                (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  exact traceHessianCoeff_apply_eq (I := I) (M := M) g₀ g₁ W x v


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckLieArm2PrincipalCoeff_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁) D) x v =
      ((∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              v 1, (Module.finBasis ℝ E) k])
        + ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 D x
              ![v 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, (Module.finBasis ℝ E) k])
      - ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0, v 1,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (Module.finBasis ℝ E) k] := by
  rw [deTurckLieArm2PrincipalCoeff, operatorFieldApplication_sub_left_local, operatorFieldApplication_add_left_local,
    unitModel_sub2_apply_local, unitModel_add2_apply_local,
    deTurckLieTraceCoeff_operatorFieldApplication_eq, deTurckLieTraceCoeff_operatorFieldApplication_eq,
    traceHessianCoeff_operatorFieldApplication_eq_local]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
      (by funext i; fin_cases i <;> rfl)


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
