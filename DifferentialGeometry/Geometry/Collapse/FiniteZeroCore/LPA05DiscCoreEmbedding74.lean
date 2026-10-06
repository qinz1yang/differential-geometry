import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceStandardParam
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport

/-!
# Draft 74, G32: a disc core carried back to the source is a smooth embedding

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. LPA05's sublevel clauses (`PointSoulCoreSublevel` and
its four siblings) carry a sublevel `A` of the original source `X` by an ambient partial
diffeomorphism `Ψ : X ⇀ Nc` onto a disc core `D_T = {‖(D⁻¹ ·).2‖ ≤ T}` of the model `Nc`. The
model `Nc` is only a charted space (`ChartedSpace E3 Nc`, no `IsManifold`), so the inclusion of
the core into `Nc` cannot be called an embedding; but the composite into `X` can:

* `discCore_comp_isSmoothEmbedding_R74`: `y ↦ Ψ⁻¹ y : D_T → X` is a smooth embedding for the
  core's boundary charts (model `morseModelWithCornersHalfSpace`), whenever `D_T ⊆ Ψ.target`.
  Route: the regular-sublevel embedding of the closed disc bundle into its total space
  (`isSmoothEmbedding_sublevel_val`), precomposed with the pull-back diffeomorphism of the core,
  seen in the total space with the model `𝓘(ℝ, E3)` (model change by a linear equivalence), then
  the partial diffeomorphism `Ψ⁻¹ ∘ D` into the manifold `X`
  (`isSmoothEmbedding_comp_partialDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Manifold.RegularLevel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section DiscCore

variable {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
  {N : Type} [TopologicalSpace N] [ChartedSpace E3 N]

/-- The core inclusion into the total space (`x ↦ D⁻¹ x`) is a smooth embedding. -/
theorem discCore_symm_isSmoothEmbedding_R74
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (EB × F) = 2 + 1) (T : ℝ) (hT : 0 < T) :
    let := discCoreChartedSpace D hd T hT
    IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (IB.prod 𝓘(ℝ, F)) ∞
      (fun y : {x : N // ‖(D.symm x).2‖ ≤ T} => D.symm y.1) := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace D hd T hT
  let := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) (discCoreHomeomorph D T).symm
  have hf : ContMDiff ((IB.prod 𝓘(ℝ, F)).transContinuousLinearEquiv (bundleRadiusBoundaryEquiv hd))
      𝓘(ℝ, ℝ) ∞ (fiberRadiusSquared (F := F) (V := V)) :=
    (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      contMDiff_fiberRadiusSquared
  have hr : ∀ z : TotalSpace F V, fiberRadiusSquared z = T ^ 2 →
      mfderiv ((IB.prod 𝓘(ℝ, F)).transContinuousLinearEquiv (bundleRadiusBoundaryEquiv hd))
        𝓘(ℝ, ℝ) (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
    intro z hz hzero
    apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) hT z hz
    exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
      (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero
  have hemb := ZeroModel.SublevelEmbedding.isSmoothEmbedding_sublevel_val
    (J := IB.prod 𝓘(ℝ, F)) (e := bundleRadiusBoundaryEquiv hd) hf hr
  let Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
      {x : N // ‖(D.symm x).2‖ ≤ T}
      {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} ∞ :=
    (discCoreDiffeomorph D hd T hT).symm.trans
      (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
        (I := morseModelWithCornersHalfSpace 2) (n := ∞)
        (normClosedDiscSublevelHomeomorph (F := F) (V := V) T hT))
  have h1 := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (Subtype.val : {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} → TotalSpace F V)
    hemb Φ
  exact h1

/-- **A disc core carried back to the source is a smooth embedding.** For a diffeomorphism `D` of
the total space onto the model `N` and an ambient partial diffeomorphism `Ψ : X ⇀ N` whose target
contains the disc core `{x | ‖(D.symm x).2‖ ≤ T}`, the map `y ↦ Ψ.symm y` of the core (with its
boundary charts) into `X` is a smooth embedding. -/
theorem discCore_comp_isSmoothEmbedding_R74
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (EB × F) = 2 + 1) (T : ℝ) (hT : 0 < T)
    (Ψ : PartialDiffeomorph I3 I3 X N ∞)
    (hsub : {x : N | ‖(D.symm x).2‖ ≤ T} ⊆ Ψ.target) :
    let := discCoreChartedSpace D hd T hT
    IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) I3 ∞
      (fun y : {x : N // ‖(D.symm x).2‖ ≤ T} => Ψ.symm y.1) := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace D hd T hT
  let := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) (discCoreHomeomorph D T).symm
  have h1 := discCore_symm_isSmoothEmbedding_R74 D hd T hT
  let J : ModelWithCorners ℝ (EB × F) (ModelProd HB F) := IB.prod 𝓘(ℝ, F)
  let L : (EB × F) ≃L[ℝ] E3 := ContinuousLinearEquiv.ofFinrankEq (by rw [hd]; simp)
  let e : ModelProd HB F ≃ₜ E3 := J.toHomeomorph.trans L.toHomeomorph
  have hc : ∀ y, I3 (e y) = L (J y) := fun y => rfl
  let _ := DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
    (M := TotalSpace F V) e
  have h2 := DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_target
    J I3 e L hc (morseModelWithCornersHalfSpace 2) h1
  let D' : Diffeomorph I3 I3 (TotalSpace F V) N ∞ :=
    { toEquiv := D.toEquiv
      contMDiff_toFun :=
        (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_source_iff
          J I3 e L hc I3).mpr D.contMDiff
      contMDiff_invFun :=
        (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
          J I3 e L hc I3).mpr D.symm.contMDiff }
  let Θ : PartialDiffeomorph I3 I3 (TotalSpace F V) X ∞ :=
    D'.toPartialDiffeomorph.trans Ψ.symm
  have hsrc : range (fun y : {x : N // ‖(D.symm x).2‖ ≤ T} => D.symm y.1) ⊆ Θ.source := by
    rintro _ ⟨y, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    change D (D.symm y.1) ∈ Ψ.symm.source
    rw [D.apply_symm_apply]
    exact hsub y.2
  have h3 := DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph Θ h2 hsrc
  have hfun : (Θ ∘ fun y : {x : N // ‖(D.symm x).2‖ ≤ T} => D.symm y.1) =
      fun y : {x : N // ‖(D.symm x).2‖ ≤ T} => Ψ.symm y.1 := by
    funext y
    change Ψ.symm (D (D.symm y.1)) = Ψ.symm y.1
    rw [D.apply_symm_apply]
  rw [hfun] at h3
  exact h3

end DiscCore

end DifferentialGeometry.Geometry.Collapse
