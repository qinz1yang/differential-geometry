import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFibPerm_apply (σ : Equiv.Perm (Fin 4)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFibPerm (I := I) σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibPerm]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def deTurckLieTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFibPerm (I := I) σ x)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem domDomCongr_section_contMDiff_local {d : ℕ} (ρ : Equiv.Perm (Fin d))
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
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem deTurckLieTraceFib_contMDiff (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (deTurckLieTraceFib (I := I) g₁ σ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => deTurckLieTraceFib (I := I) g₁ σ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff_local (I := I) σ (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]
  rfl

noncomputable def deTurckLieTraceCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x)
      contMDiff_toFun := deTurckLieTraceFib_contMDiff (I := I) g₁ σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem deTurckLieTraceCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x) := rfl

theorem deTurckLieTraceCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieTraceCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => deTurckLieTraceFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hYρ := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hCDT := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYρ
  refine hCDT.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  change deTurckLieTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1 (Y p.1) = _
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
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

private theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
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

set_option linter.unusedVariables false in

def deTurckLieArm2PrincipalCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA
    + deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT
    - traceHessianCoeff (I := I) (M := M) g₀ g₁

theorem deTurckLieArm2PrincipalCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hA := deTurckLieTraceCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermA
  have hAT := deTurckLieTraceCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermAT
  have hH := traceHessianCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add_local (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1)
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    hA hAT
  have hsub := jointTotalSpaceRS_sub_local (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1
        + (deTurckLieTraceCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    (fun p : M × ℝ => (traceHessianCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hadd hH
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckLieArm2PrincipalCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

theorem deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckLieArm2PrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieArm2PrincipalCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

noncomputable def domDomCongrFibRank (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFibRank_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    domDomCongrFibRank (I := I) d σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibRank]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

private noncomputable def modelProdCLM (p q : ℕ) :
    Tensor0SBundle.Tensor0SModel p ℝ E →L[ℝ]
      Tensor0SBundle.Tensor0SModel q ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + q) ℝ E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun B =>
              Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B
            map_add' := fun B B' => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [ContinuousMultilinearMap.add_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.add_apply]
              ring
            map_smul' := fun c B => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [RingHom.id_apply, ContinuousMultilinearMap.smul_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.smul_apply]
              simp only [smul_eq_mul]
              ring }
      map_add' := fun A A' => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply]
        ring
      map_smul' := fun c A => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply]
        simp only [smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in

private theorem modelProdCLM_apply (p q : ℕ)
    (A : Tensor0SBundle.Tensor0SModel p ℝ E) (B : Tensor0SBundle.Tensor0SModel q ℝ E) :
    modelProdCLM (E := E) p q A B =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B := by
  rw [modelProdCLM]
  rfl

noncomputable def tensor0SProdKappaFib {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) :
    Tensor0SBundle.Tensor0SSpace p I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + q) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (p + q)
      x).symm.toContinuousLinearMap.comp
    (((modelProdCLM (E := E) p q).flip
        (Tensor0SBundle.Tensor0SSpace.toModel κ)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) p x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem tensor0SProdKappaFib_apply {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) (D : Tensor0SBundle.Tensor0SSpace p I x) :
    tensor0SProdKappaFib (I := I) x κ D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel D) (Tensor0SBundle.Tensor0SSpace.toModel κ)) := by
  rw [tensor0SProdKappaFib]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.flip_apply]
  rw [modelProdCLM_apply]
  rfl

private noncomputable def trilinFormToModel (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (bilinFormToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.toLinearEquiv

private theorem trilinFormToModel_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    trilinFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (bilinFormToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [show ((bilinFormToModelₗᵢ F) (B (v 0)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
      = bilinFormToModel F (B (v 0)) from rfl]
  rw [bilinFormToModel_apply]
  rfl

noncomputable def metricConnDiffLoweredTrilin (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (gm.inner x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)

set_option linter.unusedSectionVars false in

theorem metricConnDiffLoweredTrilin_apply (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    metricConnDiffLoweredTrilin (I := I) gm gA gB x a b c =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [metricConnDiffLoweredTrilin]
  rfl

noncomputable def metricConnDiffLoweredFib (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (metricConnDiffLoweredTrilin (I := I) gm gA gB x))

set_option linter.unusedSectionVars false in

theorem metricConnDiffLoweredFib_toModel (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) gm gA gB x) v =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [metricConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (metricConnDiffLoweredTrilin (I := I) gm gA gB x) v = _
  rw [trilinFormToModel_apply, metricConnDiffLoweredTrilin_apply]

noncomputable def ccBilinConnDiffLoweredTrilin (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (ccTensorBilinSymm (I := I) g₀ V x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)

set_option linter.unusedSectionVars false in

theorem ccBilinConnDiffLoweredTrilin_apply (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x a b c =
      ccTensorBilinSymm (I := I) g₀ V x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [ccBilinConnDiffLoweredTrilin]
  rfl

noncomputable def ccBilinConnDiffLoweredFib (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x))

set_option linter.unusedSectionVars false in

theorem ccBilinConnDiffLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x) v =
      ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [ccBilinConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) v = _
  rw [trilinFormToModel_apply, ccBilinConnDiffLoweredTrilin_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem trilinKernel_section_contMDiff
    (K : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hK : ∀ (Y0 Y1 Y2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M => K x (Y0 x) (Y1 x) (Y2 x)) x₀) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (trilinFormToModel (TangentSpace I x) (K x)))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x : M => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (trilinFormToModel (TangentSpace I x) (K x)) :
          Tensor0SBundle.Tensor0SSpace 3 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  refine (hK (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀).congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
    rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (trilinFormToModel (TangentSpace I x) (K x))
      (fun j : Fin 3 => e₁.symmL ℝ x (b (σ j))) = _
  rw [trilinFormToModel_apply]
  rw [hframe0, hframe1, hframe2]

theorem metricConnDiffLoweredFib_contMDiff (gm gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (metricConnDiffLoweredFib (I := I) gm gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => metricConnDiffLoweredTrilin (I := I) gm gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) gm
      ⟨fun x => PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x), hconn⟩ Y2
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [metricConnDiffLoweredTrilin_apply]

theorem ccBilinConnDiffLoweredFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      (ccTensorBilinSymm_contMDiff (I := I) g₀ V).contMDiffOn hconn.contMDiffOn
      Y2.contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  refine (h_total.2).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [ccBilinConnDiffLoweredTrilin_apply]
  rfl

def deTurckLieArm1PairPermCorr : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 1, 3, 5], ![1, 3, 2, 4, 0, 5], by decide, by decide⟩

def deTurckLieArm1PairPermOuterZero : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermOuterTwo : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 1, 3], ![0, 4, 2, 5, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermInnerTwo : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 5, 1, 3], ![1, 4, 2, 5, 0, 3], by decide, by decide⟩

def deTurckLieArm1VecSlotPerm : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

def deTurckLieArm1KoszulMidPerm : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def deTurckLieArm1KoszulZeroPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

noncomputable def deTurckLiePairTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (κ : Tensor0SBundle.Tensor0SSpace 3 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp
      ((cometricDoubleTraceFib (I := I) g₁ 4 x).comp
        (domDomCongrFibRank (I := I) 6 σ x))).comp
    (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x κ)

noncomputable def deTurckLieKoszulTraceFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x).comp
    ((cometricDoubleTraceFib (I := I) g₁ 1 x).comp
      (domDomCongrFibRank (I := I) 3 σ x))

noncomputable def deTurckLieArm1CoreFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermInnerTwo x
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermCorr x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    - (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)).comp
        (domDomCongrFibRank (I := I) 3 deTurckLieArm1VecSlotPerm x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterZero x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulMidPerm x
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)

noncomputable def deTurckLieArm1Fib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    + deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x
    + (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x).comp
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x)
    + deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulZeroPerm x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem tensor0SProd_section_contMDiff {p q : ℕ}
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace p I x)
    (K : ∀ x : M, Tensor0SBundle.Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
            (Tensor0SBundle.Tensor0SSpace.toModel (K x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
          (Tensor0SBundle.Tensor0SSpace.toModel (K x))) :
          Tensor0SBundle.Tensor0SSpace (p + q) I x))).mpr ?_
  have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Y x)).mp hY
  have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => K x)).mp hK
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
        (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)) (Tensor0SBundle.Tensor0SSpace.toModel (K x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLiePairTraceFib_apply_section_contMDiff
    (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6))
    (κ : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (κ x)))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLiePairTraceFib (I := I) g₁ σ x (κ x) (Y x))) := by
  classical
  have hprod := tensor0SProd_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => Y x) κ Y.contMDiff hκ
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 6) σ
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
        (Tensor0SBundle.Tensor0SSpace.toModel (κ x)))) hprod
  have htr4 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 4) hperm
  have htr2 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) htr4
  refine htr2.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLieKoszulTraceFib_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x (Y x))) := by
  classical
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 3) σ
    (fun x => Y x) Y.contMDiff
  have htr1 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) hperm
  have hkos := ContMDiff.clm_bundle_apply (b := id)
    (connDiffFib_contMDiff (I := I) g₁ g₀) htr1
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLieArm1CoreFib_apply_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hS2 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermInnerTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hB := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermCorr
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg) Y
  have hpermY := domDomCongr_section_contMDiff_local (I := I) (d := 3)
    deTurckLieArm1VecSlotPerm (fun x => Y x) Y.contMDiff
  have hT2 := interiorProductField_contMDiff (I := I) 2
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))) hpermY
    (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)
  have hT3 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterZero
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hT4 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hsum := ((((hS2.sub_section hB).sub_section hT2).sub_section hT3).sub_section
    hT4).sub_section hT5
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

theorem deTurckLieArm1Fib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hW := interiorProductField_contMDiff (I := I) 2 (fun x => Y x) Y.contMDiff
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg)
  have hcore := deTurckLieArm1CoreFib_apply_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hcoreswap := domDomCongr_section_contMDiff_local (I := I) (d := 2)
    (Equiv.swap (0 : Fin 2) 1)
    (fun x => deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x)) hcore
  have hS3 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulZeroPerm Y
  have hsum := ((hW.add_section hcore).add_section hcoreswap).add_section hS3
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

noncomputable def deTurckLieArm1Coeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
      contMDiff_toFun := deTurckLieArm1Fib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem deTurckLieArm1Coeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x) := rfl

private theorem jointTotalSpace0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

private theorem jointTotalSpace0S_sub_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem jointTotalSpace0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

theorem jointTensor0SProd_local {p q : ℕ} {S : Set ℝ}
    (A : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace p I pp.1)
    (B : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace q I pp.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) pp.1 (A pp))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) pp.1 (B pp))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) pp.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := pp.1)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
            (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) p
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) q
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + q)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel q ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z)).mp (hB p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E) ∞
      (fun pp : M × ℝ => modelProdCLM (E := E) p q
        ((trivializationAt (Tensor0SBundle.Tensor0SModel p ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x₀ ⟨pp.1, A pp⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel q ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x₀ ⟨pp.1, B pp⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := modelProdCLM (E := E) p q)).clm_apply
      hA'.2).clm_apply hB'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Filter.univ_mem] with pp _
    apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  · apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl

private theorem realizedFam_chartDeTurckVFComp_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_chartDeTurckVFComp (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG g_bg k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

private theorem deTurckVFChartLocal_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1) •
            chartBasisVecFiber (I := I) α k p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hcoeff : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun k => realizedFam_chartDeTurckVFComp_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg α k
  set e := trivializationAt E (TangentSpace I) α with he
  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2 =
        ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            (chartModelBasis E) k := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [trivializationAt_chartBasisVec_snd (I := I) α k hqbase]
  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finset_sum (fun k _ => ?_)
    exact (hcoeff k).smul contMDiffOn_const
  haveI : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

theorem deTurckVF_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
          Π b : M, TangentSpace I b) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp
  have hlocal := deTurckVFChartLocal_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg p.1
  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (∑ k : Fin (Module.finrank ℝ E),
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
              chartBasisVecFiber (I := I) p.1 k q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg :
            Π b : M, TangentSpace I b) q.1) := by
    rintro q ⟨hqx, _⟩
    have hqgood : q.1 ∈ chartLeviCivitaGoodSet (I := I) p.1 := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I), extChartAt_source (I := I)]
      exact hqx
    rw [PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 hqgood]
  have hpmem : p ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') :=
    ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') ∈
      nhdsWithin p ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (chartAt H p.1).open_source.prod realizedSmallSet_isOpen, hpmem, fun q hq => hq.1⟩
  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
            chartBasisVecFiber (I := I) p.1 k q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd
  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

private def arm1LowerSwapPermA : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def arm1LowerSwapPermC : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

private noncomputable def covGradSymmSValue (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SBundle.Tensor0SSpace 3 I x :=
  (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ V)).toSection x)
    (unitTensor (I := I) (M := M) x)

set_option linter.unusedSectionVars false in

private theorem covGradSymmSValue_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (covGradSymmSValue (I := I) g₀ V x)) := by
  have h := ContMDiff.clm_bundle_apply (b := id)
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ V)).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  refine h.congr (fun x => ?_)
  rfl

set_option linter.unusedSectionVars false in

private theorem covGradSymmSValue_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) :
    covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x =
      (1 - s) • covGradSymmSValue (I := I) g₀ T' x +
        s • covGradSymmSValue (I := I) g₀ T x := by
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2
      (symmS (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) =
      (1 - s) • covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T')
        + s • covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) := by
    rw [convexPerturbation, symmS_add, symmS_smul, symmS_smul, covGrad_add,
      covGrad_smul, covGrad_smul]
  rw [covGradSymmSValue, hsplit, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul]
  rfl

set_option linter.unusedVariables false in

private theorem covGradSymmSValueFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hP' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T' p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T').comp_contMDiffOn contMDiffOn_fst
  have hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T' p.1) hP'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T p.1) hP
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (1 - p.2) • covGradSymmSValue (I := I) g₀ T' p.1)
    (fun p : M × ℝ => p.2 • covGradSymmSValue (I := I) g₀ T p.1) h1 h2
  refine hsum.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [covGradSymmSValue_convexPerturbation]

private theorem connDiff_split_middle (gA gC gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v +
        PDE.DeTurck.connDiff (I := I) gC gB x u v := by
  classical
  set σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x u, smoothExtensionTangent_contMDiff (I := I) x u⟩ with hσdef
  have hσx : σ x = u := smoothExtensionTangent_eq (I := I) x u
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (σ y)) x :=
    (σ.contMDiff x).mdifferentiableAt (by simp)
  have h1 := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => σ y) hmd v
  have h2 := PDE.DeTurck.connDiff_apply (I := I) gA gC (σ := fun y => σ y) hmd v
  have h3 := PDE.DeTurck.connDiff_apply (I := I) gC gB (σ := fun y => σ y) hmd v
  rw [hσx] at h1 h2 h3
  rw [h1, h2, h3]
  exact (sub_add_sub_cancel _ _ _).symm

set_option linter.unusedSectionVars false in

private theorem metricConnDiffLoweredFib_split (gm gA gC gB : SmoothRiemannianMetric I M)
    (x : M) :
    metricConnDiffLoweredFib (I := I) gm gA gB x =
      metricConnDiffLoweredFib (I := I) gm gA gC x +
        metricConnDiffLoweredFib (I := I) gm gC gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, metricConnDiffLoweredFib_toModel,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    connDiff_split_middle (I := I) gA gC gB, map_add, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in

private theorem metricConnDiffLowered_fixedPair_affine (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gB : SmoothRiemannianMetric I M) {s : ℝ}
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) :
    metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ gB x =
      metricConnDiffLoweredFib (I := I) g₀ g₀ gB x
        + (1 - s) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ gB x
        + s • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    ccBilinConnDiffLoweredFib_toModel, ccBilinConnDiffLoweredFib_toModel]
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    ccTensorBilinSymm_convexPerturbation]
  simp only [smul_eq_mul]
  ring

theorem metricConnDiffLowered_selfFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set Vfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1 :=
    fun p => covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1
    with hVfamdef
  have hV : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Vfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    covGradSymmSValueFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hU1 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hU3 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermC
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    Vfam hU1 hV
  have hsub := jointTotalSpace0S_sub_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
          (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p)
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsum hU3
  have hhalf := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const
    (fun p : M × ℝ =>
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p) -
        Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsub
  refine hhalf.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  apply ContinuousMultilinearMap.ext
  intro v
  rw [metricConnDiffLoweredFib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner b u w =
        g₀.inner b u w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) b u w :=
    fun b u w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hp.2 b u w
  have hid := connDiffInner_g1_eq_half_covGradSymmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (convexPerturbation (I := I) g₀ T T' p.2) hg₁ p.1 (v 0) (v 1) (v 2)
  rw [hid]
  have h1 : (fun j => v (arm1LowerSwapPermA j)) = ![v 1, v 0, v 2] := by
    funext j; fin_cases j <;> rfl
  have h3 : (fun j => v (arm1LowerSwapPermC j)) = ![v 2, v 1, v 0] := by
    funext j; fin_cases j <;> rfl
  rw [h1, h3]
  have huM : ∀ vv : Fin 3 → TangentSpace I p.1,
      unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2
          (symmS (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2))) p.1 vv =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) vv := fun vv => rfl
  rw [huM ![v 1, v 0, v 2], huM ![v 0, v 1, v 2], huM ![v 2, v 1, v 0]]
  have hv012 : Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) v =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) ![v 0, v 1, v 2] := by
    congr 1
    funext j; fin_cases j <;> rfl
  rw [hv012]
  simp only [smul_eq_mul]

theorem metricConnDiffLowered_bgFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hself := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hfix0 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T' g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1) hfixT'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1) hfixT
  have hsum1 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1)
    (fun p : M × ℝ => (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    hfix0 h1
  have hsum2 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
      (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    (fun p : M × ℝ => p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hsum1 h2
  have hsum3 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
        (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1 +
      p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hself hsum2
  refine hsum3.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [metricConnDiffLoweredFib_split (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ g_bg p.1]
  congr 1
  exact metricConnDiffLowered_fixedPair_affine (I := I) g₀ T T' hδ hδ' g_bg hp.2 p.1

private theorem connDiffFib_comp_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SBundle.Tensor0SSpace 1 I x) :
    (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x) om =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x om)) := by
  rw [connDiffFib_apply, raisedKoszulFib_apply]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [connDiffPairing_apply, raisedKoszulPairing_apply]
  set D : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hD
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  have hLHS : om (fun _ : Fin 1 => D) = g₁.inner x u D := by
    rw [← cotangentToDual_apply (I := I) (x := x) om D]
    rw [show cotangentToDual (I := I) (x := x) om D
          = cotangentToDualLinear (I := I) (x := x) om D from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₁ x om D]
  rw [hLHS]
  set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hPdef
  rw [show (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u)
        (fun _ : Fin 1 => P)
      = cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u) P from
      (cotangentToDual_apply (I := I) (x := x) _ P).symm]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₀ x u P]
  rw [g₀.symm x u P]
  have hPval : P = inverseMetricSharpFib (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) := by
    rw [hPdef, raisedKoszulVec_apply]
  have hPinner : g₀.inner x P u = cotangentToDual (I := I) (x := x)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u := by
    rw [hPval,
      show cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        = cotangentToDualLinear (I := I) (x := x)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        from rfl]
    rw [inverseMetricSharpFib_inner (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u]
  rw [hPinner, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₁ x D u]
  rw [g₁.symm x D u, hu]

private theorem deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieKoszulTraceFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have htr1 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 1)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))))
    hperm
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') htr1
  have hflatfield : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ]
      Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have hflat := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatfield hsharp
  have hkos := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hflat
  refine hkos.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply, connDiffFib_comp_eq]

private theorem deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 6))
    (κfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1)
    (hκ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (κfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLiePairTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (κfam p) (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hprod := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Y p.1) κfam hYjoint hκ
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
        (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))) hprod
  have htr4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
              (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
              (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))))))
    hperm
  have htr2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => cometricDoubleTraceFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 4 p.1
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
              (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
                (Tensor0SBundle.Tensor0SSpace.toModel (κfam p))))))))
    htr4
  refine htr2.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]

private theorem deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1CoreFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hκA := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hκB := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hS2 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermInnerTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hB := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermCorr
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    hκB Y
  have hpermY := domDomCongrField_jointContMDiffOn (I := I) deTurckLieArm1VecSlotPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hW0 := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hT2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ : Π b : M, TangentSpace I b) p.1) hW0
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hpermY
  have hT3 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterZero
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hT4 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hs1 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hS2 hB
  have hs2 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs1 hT2
  have hs3 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs2 hT3
  have hs4 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs3 hT4
  have hs5 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs4 hT5
  refine hs5.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

private theorem deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hWbg := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hW := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1) hWbg
    (fun p : M × ℝ => Y p.1) hYjoint
  have hcore := deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' g_bg Y
  have hcoreswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => deTurckLieArm1CoreFib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1)) hcore
  have hS3 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' deTurckLieArm1KoszulZeroPerm Y
  have ha1 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hW hcore
  have ha2 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha1 hcoreswap
  have ha3 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha2 hS3
  refine ha3.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

theorem deTurckLieArm1Coeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        ((deTurckLieArm1Coeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn (I := I)
      g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Coeff_toSection]

theorem deTurckLieArm1Coeff_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => deTurckLieArm1Coeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieArm1Coeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

private theorem jointTangent_add_local {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E)
    (E := fun z : M => TangentSpace I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := E)
    (E := fun z : M => TangentSpace I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

private theorem jointTotalSpace0S_smulScalar_local {d : ℕ} {S : Set ℝ}
    (c : M × ℝ → ℝ)
    (hc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ c ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (c p • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((hc p₀ hp₀).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (c p) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (c p₀) (A p₀)

set_option linter.unusedSectionVars false in

private theorem dLieEvalScalar_section_contMDiff
    (U : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 0 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x (U x)) := by
  have h := TensorMultilinear.contMDiff_section_apply (I := I) (M := M) (n := 0)
    (fun x => U x) U.contMDiff (fun i => i.elim0) (fun i => i.elim0)
  refine h.congr (fun x => ?_)
  rw [Tensor0SBundle.tensor0SSpace_evalScalar, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.apply_apply, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  exact congrArg _ (Subsingleton.elim _ _)

set_option linter.unusedSectionVars false in

private theorem dLieEmbedRS_section_contMDiff {d : ℕ}
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) x
        (show Tensor0SBundle.TensorRSSpace 0 d I x from embedRS (I := I) (M := M) x d (A x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
    (φ := fun x : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x from
        embedRS (I := I) (M := M) x d (A x)))
  intro U
  have hscalar := dLieEvalScalar_section_contMDiff (I := I) U
  have hsmul := ContMDiff.smul_section
    (f := fun x : M => Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x (U x))
    (s := fun x : M => A x) hscalar hA
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) ?_
  rfl

private noncomputable def dLiePack0S {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    SmoothCcTensor g₀ 0 d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 0 d I x from embedRS (I := I) (M := M) x d (A x))
      contMDiff_toFun := dLieEmbedRS_section_contMDiff (I := I) A hA }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

private theorem dLiePack0S_unitEval {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace d I y from
      (dLiePack0S (I := I) g₀ A hA).toSection y) (unitZeroSec (I := I) (M := M) y) = A y :=
  embedRS_unitZeroSec_apply (I := I) (M := M) y d (A y)

set_option linter.unusedSectionVars false in

private theorem dLiePack0S_unitEvalSection {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    unitEvalSection (I := I) (M := M) g₀ d (dLiePack0S (I := I) g₀ A hA) = A := by
  funext y
  rw [unitEvalSection_apply]
  exact dLiePack0S_unitEval (I := I) g₀ A hA y

private theorem dLiePack0S_family_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hslice : ∀ s : ℝ, ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A (x, s))))
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) p.1
        ((dLiePack0S (I := I) g₀ (fun x : M => A (x, p.2)) (hslice p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace d I p.1 from
        embedRS (I := I) (M := M) p.1 d (A p)))
    (S := S) ?_
  · refine hCLM.congr (fun p _ => ?_)
    rfl
  · intro U
    have hscalar : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) p.1 (U p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      (dLieEvalScalar_section_contMDiff (I := I) U).comp_contMDiffOn contMDiffOn_fst
    have hsmul := jointTotalSpace0S_smulScalar_local (I := I) (d := d) (S := S)
      (fun p : M × ℝ =>
        Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) p.1 (U p.1))
      hscalar A hA
    refine hsmul.congr (fun p _ => ?_)
    rfl

private theorem dLieCovGradVal_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g₀ : SmoothRiemannianMetric I M) (F : ℝ → SmoothCcTensor g₀ 0 d)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) q.1 ((F q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (d + 1) I p.1 from
          (covGrad (I := I) (M := M) g₀ 0 d (F p.2)).toSection p.1)
          (unitZeroSec (I := I) (M := M) p.1)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hstep := covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ 0 d F S hF
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hstep hunit

set_option linter.unusedSectionVars false in

private theorem dLieCovGradVal_toNabla {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothCcTensor g₀ 0 d) (x : M) (v0 : TangentSpace I x)
    (m : Fin d → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (d + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 d F).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v0 m) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M d (LeviCivita (I := I) g₀)
          (unitEvalSection (I := I) (M := M) g₀ d F) x v0) m := by
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ d F x (Fin.cons v0 m)]
  have hzero : (Fin.cons v0 m : Fin (d + 1) → TangentSpace I x) 0 = v0 := rfl
  have htail : Matrix.vecTail (Fin.cons v0 m) = m := by
    funext j
    simp [Matrix.vecTail]
  rw [hzero, htail, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 d F x v0,
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ d F.toSection x v0]
  rfl

private def dLieTriEvalFn (V : Π b : M, Tensor0SBundle.Tensor0SSpace 3 I b)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SBundle.Tensor0SSpace.toModel (V b) (Fin.cons (A b) (Fin.cons (B b) ![C b]))

set_option linter.unusedSectionVars false in

private lemma dLieTriMDiffAt_curried
    (s : ℕ) (W : Π x : M, Tensor0SBundle.Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

set_option linter.unusedSectionVars false in

private theorem dLieNabla3_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SBundle.Tensor0SSpace 3 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 3 V x)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x])) =
      directionalDerivAt (I := I) (dLieTriEvalFn (I := I) (M := M) V A B C) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons (A x)
              (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
  classical
  set W₂ : Π b : M, Tensor0SBundle.Tensor0SSpace 2 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (A b) with hW₂
  have hW₂_mdiff : TensorSectionMDiffAt (I := I) 2 W₂ x :=
    dLieTriMDiffAt_curried (I := I) (M := M) 2 V hV A
  set W₁ : Π b : M, Tensor0SBundle.Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M W₂ b (B b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    dLieTriMDiffAt_curried (I := I) (M := M) 1 W₂ hW₂_mdiff B
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 2 V hV A v (Fin.cons (B x) ![C x])
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 W₂ hW₂_mdiff B v ![C x]
  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff C v (fun i => Fin.elim0 i)
  have hbase : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I) (dLieTriEvalFn (I := I) (M := M) V A B C) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) =
        dLieTriEvalFn (I := I) (M := M) V A B C := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
      change Tensor0SBundle.Tensor0SSpace.toModel (W₁ b)
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [hW₁]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M W₂ b (B b))
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
      rw [hW₂]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M V b (A b))
        (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := A b)
        (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
      rw [dLieTriEvalFn]
      apply congrArg
      funext k
      fin_cases k <;> rfl
    rw [hscalar]
  have hcorrC : Tensor0SBundle.Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SBundle.Tensor0SSpace.toModel (V x)
        (Fin.cons (A x)
          (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
    rw [hW₁]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W₂ x (B x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ x) (v0 := B x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  have hcorrB : Tensor0SBundle.Tensor0SSpace.toModel (W₂ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
          (Fin.cons (C x) (fun i => Fin.elim0 i))) =
      Tensor0SBundle.Tensor0SSpace.toModel (V x)
        (Fin.cons (A x)
          (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x])) := by
    rw [hW₂]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (A y)) = W₂ from rfl]
  rw [hpeel2]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M W₂ y (B y)) = W₁ from rfl]
  rw [show (![C x] : Fin 1 → TangentSpace I x) = Fin.cons (C x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel3, hbase, hcorrC, hcorrB]
  have hfin1 : ∀ (u : TangentSpace I x), (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons u (fun i => Fin.elim0 i) := by
    intro u; funext k; refine Fin.cases rfl (fun j => j.elim0) k
  rw [hfin1 ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v), hfin1 (C x)]
  ring

set_option linter.unusedSectionVars false in

private theorem dLie_toModel_g0Flat (g : SmoothRiemannianMetric I M) (x : M)
    (w t : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (Fin.cons t (fun i => Fin.elim0 i)) = g.inner x w t := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) =
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (fun _ : Fin 1 => t) := by
    change (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) = _
    congr 1
    funext j
    refine Fin.cases rfl (fun j => j.elim0) j
  rw [h1, ← cotangentToDual_apply (I := I) (x := x) _ t]
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g x w t

private theorem dLieFlatSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (V x))) :=
  ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) V.contMDiff

private noncomputable def dLieFlatPack (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : SmoothCcTensor g₀ 0 1 :=
  dLiePack0S (I := I) g₀
    (fun x : M =>
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (V x))
    (dLieFlatSection_contMDiff (I := I) g₀ V)

set_option linter.unusedSectionVars false in

private theorem dLieFlatCovGradVal_eval (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (z t : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          (covGrad (I := I) (M := M) g₀ 0 1 (dLieFlatPack (I := I) g₀ V)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons z (Fin.cons t (fun i => Fin.elim0 i))) =
      g₀.inner x ((LeviCivita (I := I) g₀).toFun (fun b => V b) x z) t := by
  classical
  rw [dLieCovGradVal_toNabla (I := I) g₀ (dLieFlatPack (I := I) g₀ V) x z
    (Fin.cons t (fun i => Fin.elim0 i))]
  rw [show unitEvalSection (I := I) (M := M) g₀ 1 (dLieFlatPack (I := I) g₀ V) =
      (fun b : M =>
        DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ b (V b)) from
    dLiePack0S_unitEvalSection (I := I) g₀ _ _]
  set β : Π b : M, Tensor0SBundle.Tensor0SSpace 1 I b :=
    fun b => DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ b (V b)
    with hβdef
  set Tf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x t, smoothExtensionTangent_contMDiff (I := I) x t⟩
    with hTfdef
  have hTfx : Tf x = t := smoothExtensionTangent_eq (I := I) x t
  have hβm : TensorSectionMDiffAt (I := I) 1 β x :=
    (dLieFlatSection_contMDiff (I := I) g₀ V x).mdifferentiableAt (by simp)
  rw [show (Fin.cons t (fun i => Fin.elim0 i) : Fin 1 → TangentSpace I x) =
      Fin.cons (Tf x) (fun i => Fin.elim0 i) from by rw [hTfx]]
  rw [tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g₀ 0 β hβm Tf z
    (fun i => Fin.elim0 i)]
  rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
    (fun y : M => Tensor0SNabla.curriedSection I M β y (Tf y)) x z]
  have hscalar : Tensor0SNabla.scalarFn I M
      (fun y : M => Tensor0SNabla.curriedSection I M β y (Tf y)) =
      (fun y : M => g₀.inner y (V y) (Tf y)) := by
    funext y
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := β)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := β y) (v0 := Tf y) (vs := (fun i => Fin.elim0 i))]
    exact dLie_toModel_g0Flat (I := I) g₀ y (V y) (Tf y)
  rw [hscalar]
  have hVm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V b)) x :=
    V.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hTfm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Tf b)) x :=
    Tf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc : IsMetricCompatibleOn (I := I) (LeviCivita (I := I) g₀).toFun g₀ Set.univ :=
    LeviCivita_isMetricCompatible (I := I) g₀
  have hcompat := hmc.apply (Y := fun b => V b) (Z := fun b => Tf b) hVm hTfm
    (Set.mem_univ x) z
  rw [hcompat]
  rw [dLie_toModel_g0Flat (I := I) g₀ x (V x)
    ((LeviCivita (I := I) g₀).toFun (fun y => Tf y) x z)]
  rw [hTfx]
  ring

private noncomputable def dLieLoweredPack (g₀ gm gA gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 3 :=
  dLiePack0S (I := I) g₀
    (fun x : M => metricConnDiffLoweredFib (I := I) gm gA gB x)
    (metricConnDiffLoweredFib_contMDiff (I := I) gm gA gB)

set_option linter.unusedSectionVars false in

private theorem dLieDiagTrace_toModel (g₁ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I x) (u : Fin p → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ p x D) u =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) u)) := by
  classical
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ p x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D]
  rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (p + 1) x D)
      (smoothOrthoFrame (I := I) g₁ x e x))
    (v0 := smoothOrthoFrame (I := I) g₁ x e x) (vs := u)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x e x)
    (vs := Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) u)]

set_option linter.unusedSectionVars false in

private theorem dLieFrameExpand_update (g₁ : SmoothRiemannianMetric I M) (x : M)
    (L3 : Tensor0SBundle.Tensor0SSpace 3 I x)
    (base : Fin 3 → TangentSpace I x) (i : Fin 3) (w : TangentSpace I x) :
    ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel L3
            (Function.update base i (smoothOrthoFrame (I := I) g₁ x e x)) *
          g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) =
      Tensor0SBundle.Tensor0SSpace.toModel L3 (Function.update base i w) := by
  classical
  have hexp := orthonormal_frame_vector_expansion (I := I) g₁ x w
    (fun e => smoothOrthoFrame (I := I) g₁ x e x)
    (fun e f => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x e f)
  calc ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel L3
            (Function.update base i (smoothOrthoFrame (I := I) g₁ x e x)) *
          g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) =
      ∑ e : Fin (Module.finrank ℝ E),
        (Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap
          (Function.update base i
            (g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
              smoothOrthoFrame (I := I) g₁ x e x)) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [(Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap.map_update_smul
          base i (g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x))
          (smoothOrthoFrame (I := I) g₁ x e x)]
        rw [smul_eq_mul, mul_comm]
        rfl
    _ = (Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap
          (Function.update base i
            (∑ e : Fin (Module.finrank ℝ E),
              g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
                smoothOrthoFrame (I := I) g₁ x e x)) :=
        ((Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap.map_update_sum
          (t := Finset.univ) (i := i)
          (g := fun e : Fin (Module.finrank ℝ E) =>
            g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
              smoothOrthoFrame (I := I) g₁ x e x) (m := base)).symm
    _ = Tensor0SBundle.Tensor0SSpace.toModel L3 (Function.update base i w) := by
        rw [← hexp]
        rfl

private def dLieBiPairPerm : Equiv.Perm (Fin 6) :=
  ⟨![2, 0, 4, 5, 3, 1], ![1, 5, 0, 4, 2, 3], by decide, by decide⟩

private def dLieCorrPermA : Equiv.Perm (Fin 6) :=
  ⟨![0, 4, 5, 3, 2, 1], ![0, 5, 4, 3, 1, 2], by decide, by decide⟩

private def dLieCorrPermB : Equiv.Perm (Fin 6) :=
  ⟨![3, 0, 5, 4, 2, 1], ![1, 5, 4, 0, 3, 2], by decide, by decide⟩

private def dLieCorrPermC : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 0, 5, 2, 1], ![2, 5, 4, 0, 1, 3], by decide, by decide⟩

private def dLieXiPermA : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

private def dLieXiPermB : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

set_option linter.unusedSectionVars false in

private theorem dLieUpdateZero (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 0 u = ![u, b, c] := by
  funext j
  fin_cases j <;> simp [Function.update]

set_option linter.unusedSectionVars false in

private theorem dLieUpdateOne (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 1 u = ![a, u, c] := by
  funext j
  fin_cases j <;> simp [Function.update]

set_option linter.unusedSectionVars false in

private theorem dLieUpdateTwo (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 2 u = ![a, b, u] := by
  funext j
  fin_cases j <;> simp [Function.update]

set_option linter.unusedSectionVars false in

private theorem dLieCorrA_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermA i)) ∘ Fin.castAdd 3) =
        ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermA i)) ∘ Fin.natAdd 3) =
        ![w 1, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![u, w 2, w 3] : Fin 3 → TangentSpace I x) =
        Function.update
          (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] :
            Fin 3 → TangentSpace I x) 0 u :=
    fun u => (dLieUpdateZero (I := I) x _ (w 2) (w 3) u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] :
              Fin 3 → TangentSpace I x) 0 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3]) 0
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))]
  exact congrArg _ (hupd _).symm

set_option linter.unusedSectionVars false in

private theorem dLieCorrB_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermB i)) ∘ Fin.castAdd 3) =
        ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermB i)) ∘ Fin.natAdd 3) =
        ![w 2, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![w 1, u, w 3] : Fin 3 → TangentSpace I x) =
        Function.update
          (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] :
            Fin 3 → TangentSpace I x) 1 u :=
    fun u => (dLieUpdateOne (I := I) x (w 1) _ (w 3) u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] :
              Fin 3 → TangentSpace I x) 1 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3]) 1
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))]
  exact congrArg _ (hupd _).symm

set_option linter.unusedSectionVars false in

private theorem dLieCorrC_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermC i)) ∘ Fin.castAdd 3) =
        ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermC i)) ∘ Fin.natAdd 3) =
        ![w 3, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![w 1, w 2, u] : Fin 3 → TangentSpace I x) =
        Function.update
          (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] :
            Fin 3 → TangentSpace I x) 2 u :=
    fun u => (dLieUpdateTwo (I := I) x (w 1) (w 2) _ u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] :
              Fin 3 → TangentSpace I x) 2 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)]) 2
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))]
  exact congrArg _ (hupd _).symm

set_option linter.unusedSectionVars false in

private theorem dLieTheta_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w0 w1 w2 w3 : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g₀ 0 3
            (dLieLoweredPack (I := I) g₀ g₁ g₁ g_bg)).toSection x)
          (unitZeroSec (I := I) (M := M) x)
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x))))))
        ![w0, w1, w2, w3] =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x w0 w1 w2) w3 := by
  classical
  set Af : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w1, smoothExtensionTangent_contMDiff (I := I) x w1⟩
    with hAfdef
  set Bf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w2, smoothExtensionTangent_contMDiff (I := I) x w2⟩
    with hBfdef
  set Uf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w3, smoothExtensionTangent_contMDiff (I := I) x w3⟩
    with hUfdef
  set V0f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w0, smoothExtensionTangent_contMDiff (I := I) x w0⟩
    with hV0fdef
  have hAfx : Af x = w1 := smoothExtensionTangent_eq (I := I) x w1
  have hBfx : Bf x = w2 := smoothExtensionTangent_eq (I := I) x w2
  have hUfx : Uf x = w3 := smoothExtensionTangent_eq (I := I) x w3
  have hV0fx : V0f x = w0 := smoothExtensionTangent_eq (I := I) x w0
  have hCa : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0, w2, w3] :=
    dLieCorrA_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  have hCb : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0, w3] :=
    dLieCorrB_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  have hCu : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w1, w2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0] :=
    dLieCorrC_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [hCa, hCb, hCu]
  rw [show (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) =
      Fin.cons w0 ![w1, w2, w3] from rfl]
  rw [dLieCovGradVal_toNabla (I := I) g₀ (dLieLoweredPack (I := I) g₀ g₁ g₁ g_bg) x w0
    ![w1, w2, w3]]
  rw [dLieLoweredPack, dLiePack0S_unitEvalSection (I := I) g₀ _ _]
  rw [show (![w1, w2, w3] : Fin 3 → TangentSpace I x) =
      Fin.cons (Af x) (Fin.cons (Bf x) ![Uf x]) from by rw [hAfx, hBfx, hUfx]; rfl]
  have hVsec : TensorSectionMDiffAt (I := I) 3
      (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) x :=
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg x).mdifferentiableAt (by simp)
  rw [dLieNabla3_consEval_leibnizDefect (I := I) g₀
    (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) hVsec Af Bf Uf w0]
  have htri : dLieTriEvalFn (I := I) (M := M)
      (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) Af Bf Uf =
      (fun b : M => g₁.inner b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b)) (Uf b)) := by
    funext b
    change Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b)
      (Fin.cons (Af b) (Fin.cons (Bf b) ![Uf b])) = _
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  rw [htri, directionalDerivAt_eq]
  have hDsec := PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg
    (σ := fun b => Af b) (τ := fun b => Bf b) Af.contMDiff Bf.contMDiff
  have hYm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b))) x :=
    (hDsec x).mdifferentiableAt (by simp)
  have hUm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Uf b)) x :=
    (Uf.contMDiff x).mdifferentiableAt (by simp)
  have hmc : IsMetricCompatibleOn (I := I) (LeviCivita (I := I) g₁).toFun g₁ Set.univ :=
    LeviCivita_isMetricCompatible (I := I) g₁
  have hcompat := hmc.apply
    (Y := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b))
    (Z := fun b => Uf b) hYm hUm (Set.mem_univ x) w0
  rw [hcompat]
  have hc1 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Af b) x w0)
        (Fin.cons (Bf x) ![Uf x])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₀).toFun (fun b => Af b) x w0) (Bf x)) (Uf x) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hc2 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons (Af x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Bf b) x w0) ![Uf x])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Af x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Bf b) x w0)) (Uf x) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hc3 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons (Af x)
        (Fin.cons (Bf x) ![(LeviCivita (I := I) g₀).toFun (fun b => Uf b) x w0])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Af x) (Bf x))
        ((LeviCivita (I := I) g₀).toFun (fun b => Uf b) x w0) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk1 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0, w2, w3] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0) w2) w3 := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk2 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![w1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0, w3] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w1
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0)) w3 := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk3 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![w1, w2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w1 w2)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  rw [hc1, hc2, hc3, hk1, hk2, hk3]
  have hker : dLaCovKernel (I := I) g₁ g_bg x w0 w1 w2 =
      deTurckLieCovDerivA (I := I) g₁ g_bg (fun b => V0f b) (fun b => Af b)
        (fun b => Bf b) x := by
    have hV0m : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V0f b)) x :=
      (V0f.contMDiff x).mdifferentiableAt (by simp)
    have hAm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Af b)) x :=
      (Af.contMDiff x).mdifferentiableAt (by simp)
    have hBm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Bf b)) x :=
      (Bf.contMDiff x).mdifferentiableAt (by simp)
    have h3 := dLaCovKernel_apply_field3 (I := I) g₁ g_bg x (fun b => V0f b)
      (fun b => Af b) (fun b => Bf b) hV0m hAm hBm
    beta_reduce at h3
    rw [hV0fx, hAfx, hBfx] at h3
    exact h3
  rw [hker, deTurckLieCovDerivA]
  rw [hV0fx]
  have hsplit : ∀ (Yf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (LeviCivita (I := I) g₀).toFun (fun b => Yf b) x w0 =
        (LeviCivita (I := I) g₁).toFun (fun b => Yf b) x w0
          - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x) w0 := by
    intro Yf
    have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Yf b)) x :=
      (Yf.contMDiff x).mdifferentiableAt (by simp)
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => Yf b) hmd w0
    rw [h]
    abel
  rw [hsplit Af, hsplit Bf, hsplit Uf, hAfx, hBfx, hUfx]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

theorem dLieFlatFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hflatfield : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatfield
    (deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg)

private theorem dLieWEndoA_apply_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set F : ℝ → SmoothCcTensor g₀ 0 1 := fun s : ℝ =>
    dLieFlatPack (I := I) g₀
      (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
    with hFdef
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 1 I z) q.1 ((F q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hpack := dLiePack0S_family_jointContMDiffOn (I := I) g₀
      (A := fun p : M × ℝ =>
        DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1))
      (hslice := fun s : ℝ => dLieFlatSection_contMDiff (I := I) g₀
        (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
      (dLieFlatFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg)
    exact hpack.congr (fun p _ => rfl)
  have hCovVal := dLieCovGradVal_jointContMDiffOn (I := I) (d := 1) g₀ F hF
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
        (unitZeroSec (I := I) (M := M) p.1)) hCovVal
  have hsharpField : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (inverseMetricSharpField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharpField hι
  refine happ.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
        (unitZeroSec (I := I) (M := M) p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
        ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
            (unitZeroSec (I := I) (M := M) p.1))) m =
        g₀.inner p.1 ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) (m 0) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
          (unitZeroSec (I := I) (M := M) p.1))
        (Fin.cons (Z p.1) m) = _
      refine Eq.trans (congrArg (fun args : Fin 1 → TangentSpace I p.1 =>
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
            (unitZeroSec (I := I) (M := M) p.1))
          (Fin.cons (Z p.1) args)) hm) ?_
      exact dLieFlatCovGradVal_eval (I := I) g₀
        (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg)
        p.1 (Z p.1) (m 0)
    have e2 : Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((LeviCivita (I := I) g₀).toFun
            (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) b) p.1 (Z p.1))) m =
        g₀.inner p.1 ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((LeviCivita (I := I) g₀).toFun
            (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) b) p.1 (Z p.1)))) hm) ?_
      exact dLie_toModel_g0Flat (I := I) g₀ p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

private theorem dLieWEndoB_apply_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1) (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hW := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hι1 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1) hW
    (α := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1) hM
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1)
      (metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) hι1
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hι2
  refine hsharp.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1)
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1) (Z p.1)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1)
            (metricConnDiffLoweredFib (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
        (Fin.cons ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1)
          (Fin.cons (Z p.1) m)) = _
      rw [metricConnDiffLoweredFib_toModel]
      rfl
    have e2 : Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)))) hm) ?_
      exact dLie_toModel_g0Flat (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

theorem deTurckLieWEndo_realizedFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Z
  have hA := dLieWEndoA_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Z
  have hB := dLieWEndoB_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Z
  have hsum := jointTangent_add_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
            Π b : M, TangentSpace I b) b)) p.1 :=
    ((PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).contMDiff
        p.1).mdifferentiableAt (by simp)
  have hcd := PDE.DeTurck.connDiff_apply (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀
    (σ := fun b : M => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) b) hmd (Z p.1)
  change deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
      (Z p.1) = _
  rw [show deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
      (Z p.1) =
    (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toFun
      (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
          Π b : M, TangentSpace I b) b) p.1 (Z p.1) from rfl]
  rw [show (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) p.1 =
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) b) p.1 from rfl]
  rw [hcd]
  abel

private theorem deTurckLieDLbFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hΛ := deTurckLieWEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h0 := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) hΛ
    (A := fun p : M × ℝ => Y p.1) hY
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀
    (Λ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) hΛ
    (A := fun p : M × ℝ => Y p.1) hY
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h0 h1
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieDLbFib, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in

private theorem dLieBiArgY (x : M) (u0 u1 u2 u3 : TangentSpace I x)
    (v : Fin 2 → TangentSpace I x) :
    ((fun i : Fin 6 =>
      (Fin.cons u0 (Fin.cons u1 (Fin.cons u2 (Fin.cons u3 v))) : Fin 6 → TangentSpace I x)
        (dLieBiPairPerm i)) ∘ Fin.castAdd 4) = ![u2, u0] := by
  funext j
  fin_cases j <;> rfl

set_option linter.unusedSectionVars false in

private theorem dLieBiArgXi (x : M) (u0 u1 u2 u3 : TangentSpace I x)
    (v : Fin 2 → TangentSpace I x) :
    ((fun i : Fin 6 =>
      (Fin.cons u0 (Fin.cons u1 (Fin.cons u2 (Fin.cons u3 v))) : Fin 6 → TangentSpace I x)
        (dLieBiPairPerm i)) ∘ Fin.natAdd 2) = ![v 0, v 1, u3, u1] := by
  funext j
  fin_cases j <;> rfl

set_option linter.unusedSectionVars false in

private theorem dLieXiArgA (x : M) (a0 a1 a2 a3 : TangentSpace I x) :
    (fun i : Fin 4 => (![a0, a1, a2, a3] : Fin 4 → TangentSpace I x) (dLieXiPermA i)) =
      ![a0, a2, a3, a1] := by
  funext j
  fin_cases j <;> rfl

set_option linter.unusedSectionVars false in

private theorem dLieXiArgB (x : M) (a0 a1 a2 a3 : TangentSpace I x) :
    (fun i : Fin 4 => (![a0, a1, a2, a3] : Fin 4 → TangentSpace I x) (dLieXiPermB i)) =
      ![a1, a2, a3, a0] := by
  funext j
  fin_cases j <;> rfl

private theorem dLaBiContrFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hLraw := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hMraw := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hprodLM := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hLraw hMraw
  have hpermA := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hpermB := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermB
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hpermC := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermC
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hCa := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermA
  have hCb := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermB
  have hCu := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermC
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 3 I z) q.1
        (((fun s : ℝ => dLieLoweredPack (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hpack := dLiePack0S_family_jointContMDiffOn (I := I) g₀
      (A := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
      (hslice := fun s : ℝ => metricConnDiffLoweredFib_contMDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      hLraw
    exact hpack.congr (fun p _ => rfl)
  have hGrad := dLieCovGradVal_jointContMDiffOn (I := I) (d := 3) g₀
    (fun s : ℝ => dLieLoweredPack (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) hF
  have hs1 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hGrad hCa
  have hs2 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs1 hCb
  have hs3 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs2 hCu
  have hXi1 := domDomCongrField_jointContMDiffOn (I := I) dLieXiPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hs3
  have hXi2 := domDomCongrField_jointContMDiffOn (I := I) dLieXiPermB
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hs3
  have hXi := jointTotalSpace0S_add_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hXi1 hXi2
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hprodYXi := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Y p.1) _ hYjoint hXi
  have hperm := domDomCongrField_jointContMDiffOn (I := I) dLieBiPairPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodYXi
  have htr4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hperm
  have htr2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
    g₀ T T' hδ hδ' _ htr4
  have hneg := jointTotalSpace0S_smulFun_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ htr2
  refine hneg.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  simp only [dLieDiagTrace_toModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [neg_one_mul, neg_one_mul, neg_inj]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Bundle.continuousMultilinearMap.modelProduct_apply, dLieBiArgY, dLieBiArgXi,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    dLieXiArgA, dLieXiArgB, dLieTheta_eval, dLieTheta_eval]
  exact mul_comm _ _

theorem dLaBiContrFib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  exact dLaBiContrFib_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y

private theorem deTurckLieFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hA := dLaBiContrFib_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hB := deTurckLieDLbFib_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieFib, ContinuousLinearMap.add_apply]

theorem deTurckLieCoeffField_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      deTurckLieFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => deTurckLieFib_realizedFam_apply_jointContMDiffOn (I := I)
      g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [deTurckLieCoeffField_toSection]
  rfl

theorem deTurckLieCoeffField_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieCoeffField_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
