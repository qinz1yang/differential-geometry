import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Tensor.Multilinear.BundleEvaluation
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.Basis
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0SOne_apply_add (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => a + b) =
    _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0SOne_apply_smul (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => c • a) =
    _
  rw [hca, ha, map_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0SOne_apply_neg (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0SOne_apply_sub (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a - b) = om (fun _ : Fin 1 => a) - om (fun _ : Fin 1 => b) := by
  rw [show (fun _ : Fin 1 => a - b) = (fun _ : Fin 1 => a + (-b)) from by
    funext _; rw [sub_eq_add_neg]]
  rw [tensor0SOne_apply_add (I := I) x om, tensor0SOne_apply_neg (I := I) x om, sub_eq_add_neg]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
def connectionDifferencePairing (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              add_apply, map_add]
            rw [tensor0SOne_apply_add (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              smul_apply, map_smul]
            rw [tensor0SOne_apply_smul (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) :=
          (connectionDifference (I := I) g₁ g₀ x).continuous₂.comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] in
@[simp] lemma connectionDifferencePairing_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connectionDifferencePairing (I := I) g₁ g₀ x om) YZ =
      om (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] in
lemma connectionDifferencePairing_add (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connectionDifferencePairing (I := I) g₁ g₀ x (om + om') =
      connectionDifferencePairing (I := I) g₁ g₀ x om + connectionDifferencePairing (I := I) g₁ g₀ x om' := by
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] in
lemma connectionDifferencePairing_smul (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connectionDifferencePairing (I := I) g₁ g₀ x (c • om) =
      c • connectionDifferencePairing (I := I) g₁ g₀ x om := by
  rfl

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
def connectionDifferenceFib (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connectionDifferencePairing (I := I) g₁ g₀ x om
        map_add' := connectionDifferencePairing_add g₁ g₀ x
        map_smul' := connectionDifferencePairing_smul g₁ g₀ x })

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] in
@[simp] lemma connectionDifferenceFib_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connectionDifferenceFib (I := I) g₁ g₀ x) om =
      connectionDifferencePairing (I := I) g₁ g₀ x om := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] in
lemma connectionDifferenceFib_apply_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connectionDifferenceFib (I := I) g₁ g₀ x) om) YZ =
      om (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
  rw [connectionDifferenceFib_apply, connectionDifferencePairing_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceFib_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (connectionDifferenceFib (I := I) g₁ g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connectionDifferenceFib (I := I) g₁ g₀ x))
  intro om
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connectionDifferencePairing (I := I) g₁ g₀ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connectionDifferencePairing (I := I) g₁ g₀ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((connectionDifference (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) :=
      connectionDifference_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((connectionDifference (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((connectionDifference (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp only [Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply]
      exact e₁.symmL_apply hx₁ (b (σ 0))
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp only [Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply]
      exact e₁.symmL_apply hx₁ (b (σ 1))
    change (connectionDifferencePairing (I := I) g₁ g₀ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [connectionDifferencePairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

def connectionDifferenceSection (g₁ g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connectionDifferenceFib (I := I) g₁ g₀ x
      contMDiff_toFun := connectionDifferenceFib_contMDiff (I := I) g₁ g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def connectionDifferenceSectionWith (gBase g₁ g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor gBase 1 2 where
  toSection :=
    { toFun := fun x : M => connectionDifferenceFib (I := I) g₁ g₀ x
      contMDiff_toFun := connectionDifferenceFib_contMDiff (I := I) g₁ g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connectionDifferenceSection_toSection (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    (connectionDifferenceSection (I := I) g₁ g₀).toSection x = connectionDifferenceFib (I := I) g₁ g₀ x := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem connectionDifferenceSection_self (g : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) g g = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connectionDifferenceSection_toSection]
  apply ContinuousLinearMap.ext
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  change (connectionDifferencePairing (I := I) g g x om) YZ = 0
  rw [connectionDifferencePairing_apply, PDE.DeTurck.connectionDifference_self]
  change om (0 : Fin 1 → TangentSpace I x) = 0
  exact ContinuousMultilinearMap.map_zero om

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connectionDifferenceSectionWith_toSection
    (gBase g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    (connectionDifferenceSectionWith (I := I) gBase g₁ g₀).toSection x =
      connectionDifferenceFib (I := I) g₁ g₀ x := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma connectionDifferenceSection_tensorCovDerivAt_homSplit
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 1 2
          (connectionDifferenceSection (I := I) g₁ g₀) x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x)))
        (om x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) x (X x) -
        connectionDifferencePairing (I := I) g₁ g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)) := by
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((connectionDifferenceSection (I := I) g₁ g₀).toSection y)) x :=
    (connectionDifferenceSection (I := I) g₁ g₀).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 1 2
    (connectionDifferenceSection (I := I) g₁ g₀) x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x)),
    ContinuousLinearEquiv.symm_apply_apply]
  have hsplit := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
    1 2 (LeviCivita (I := I) g₀)
    (fun y : M => (connectionDifferenceSection (I := I) g₁ g₀).toSection y) (fun y : M => om y)
    (fun y : M => X y) hτ hw hV
  have hval : (fun y : M =>
        (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
          (connectionDifferenceSection (I := I) g₁ g₀).toSection y) (om y)) =
      (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) := by
    funext y
    rw [connectionDifferenceSection_toSection]
    rfl
  rw [hsplit, hval]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorSectionMDiffAt_connectionDifferencePairing
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) (x : M) :
    TensorSectionMDiffAt (I := I) 2
      (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) x := by
  classical
  have hval : (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) =
      (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
        (connectionDifferenceSection (I := I) g₁ g₀).toSection y) (om y)) := by
    funext y
    rw [connectionDifferenceSection_toSection]
    rfl
  rw [hval]
  unfold TensorSectionMDiffAt
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((connectionDifferenceSection (I := I) g₁ g₀).toSection y)) x :=
    (connectionDifferenceSection (I := I) g₁ g₀).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := Tensor0SModel 1 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun y : M => Tensor0SSpace 1 I y)
    (E₂ := fun y : M => Tensor0SSpace 2 I y)
    (IM := I) (IB := I)
    (b := id)
    (ϕ := fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
      (connectionDifferenceSection (I := I) g₁ g₀).toSection y))
    (v := fun y : M => om y) hτ hw

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma connectionDifferencePairing_covariantDerivative02_eval
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) x (X x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) =
      directionalDeriv (I := I)
          (fun b : M => om b (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            connectionDifference (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
        - om x (fun _ : Fin 1 =>
            connectionDifference (I := I) g₁ g₀ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
  classical
  set V : Π b : M, Tensor0SSpace 2 I b :=
    fun b => connectionDifferencePairing (I := I) g₁ g₀ b (om b) with hVdef
  have hV : TensorSectionMDiffAt (I := I) 2 V x :=
    tensorSectionMDiffAt_connectionDifferencePairing (I := I) g₁ g₀ om x
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (Y b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x := by
    have hY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    unfold TensorSectionMDiffAt
    have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 1 V hV
    exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
      (F₁ := E) (F₂ := Tensor0SModel 1 ℝ E)
      (E₁ := fun b : M => TangentSpace I b)
      (E₂ := fun b : M => Tensor0SSpace 1 I b)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M V y)
      (v := fun y : M => Y y) hCurried hY'
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 V hV Y (X x)
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff Z (X x) (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x))
        (fun i => Fin.elim0 i) =
      directionalDeriv (I := I)
        (fun b : M => om b (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b))) x (X x) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x)]
    rw [directionalDeriv_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    show Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₁ b (Z b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [show Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) 0 b (W₁ b) (Z b))
          (fun i => Fin.elim0 i) =
        Tensor0SSpace.toModel (W₁ b)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
            (fun i => Fin.elim0 i)) from by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
          (T := W₁ b)
          (v0 := tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
          (vs := (fun i => Fin.elim0 i))]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (Y b))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
          (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := V)]
    rw [show Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) 1 b (V b) (Y b))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
            (fun i => Fin.elim0 i)) =
        Tensor0SSpace.toModel (V b)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
              (fun i => Fin.elim0 i))) from by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
          (T := V b)
          (v0 := tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
          (vs := Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Z b))
            (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  have hcorr2 : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
          (fun i => Fin.elim0 i)) =
      om x (fun _ : Fin 1 =>
        connectionDifference (I := I) g₁ g₀ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
    have hW₁x : W₁ x = Tensor0SNabla.curriedSection I M V x (Y x) := rfl
    rw [hW₁x, Tensor0SNabla.curriedSection_apply]
    rw [show Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) 1 x (V x) (Y x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
            (fun i => Fin.elim0 i)) =
        Tensor0SSpace.toModel (V x)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
              (fun i => Fin.elim0 i))) from by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
          (T := V x)
          (v0 := tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          (vs := Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
            (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  have hcorr1 : Tensor0SSpace.toModel (V x)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x))
            (fun i => Fin.elim0 i))) =
      om x (fun _ : Fin 1 =>
        connectionDifference (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
      := by
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) = W₁ from rfl]
  rw [show (![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)] : Fin 1 → E) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x))
        (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel2, hbase, hcorr2, hcorr1]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma connectionDifferencePairing_covariantDerivative01_eval
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    connectionDifferencePairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      directionalDeriv (I := I)
          (fun b : M => om b (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            (LeviCivita (I := I) g₀).toFun
              (fun b => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)) := by
  classical
  have hWYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)⟩ : TotalSpace E (TangentSpace I))) :=
    connectionDifference_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  set WYZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) hWYZ with hWYZdef
  have hom_mdiff : TensorSectionMDiffAt (I := I) 1 (fun y : M => om y) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 (fun y : M => om y) hom_mdiff WYZ (X x) (fun i => Fin.elim0 i)
  have hLHS : connectionDifferencePairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (WYZ x))
          (fun i => Fin.elim0 i)) := by
    rw [connectionDifferencePairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hLHS, hpeel]
  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x))
        (fun i => Fin.elim0 i) =
      directionalDeriv (I := I)
        (fun b : M => om b (fun _ : Fin 1 => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b))) x (X x) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x)]
    rw [directionalDeriv_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    show Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M (fun y : M => om y) b (WYZ b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := fun y : M => om y)]
    rw [show Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) 0 b (om b) (WYZ b))
          (fun i => Fin.elim0 i) =
        Tensor0SSpace.toModel (om b)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (WYZ b))
            (fun i => Fin.elim0 i)) from by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
          (T := om b)
          (v0 := tangentSpaceModelContinuousLinearEquiv (I := I) b (WYZ b))
          (vs := (fun i => Fin.elim0 i))]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  have hcorr : Tensor0SSpace.toModel ((fun y : M => om y) x)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x)))
          (fun i => Fin.elim0 i))
          =
      om x (fun _ : Fin 1 =>
        (LeviCivita (I := I) g₀).toFun
          (fun b => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)) := by
    change Tensor0SSpace.toModel (om x)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x)))
          (fun i => Fin.elim0 i)) = _
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hbase, hcorr]

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceSection_covGrad_eq_covDerivConnectionDifference
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
          (om x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)])) =
      om x (fun _ : Fin 1 => covDerivConnectionDifference (I := I) g₀ g₁ X Z Y x) := by
  classical
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) x
    (om x) (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]))]
  rw [show (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) : Fin 3 → E) 0 =
      tangentSpaceModelContinuousLinearEquiv (I := I) x (X x) from rfl]
  rw [show Matrix.vecTail
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) : Fin 3 → E) =
        Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)] from by
      funext k; simp only [Matrix.vecTail, Function.comp]
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      exact j'.elim0]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))) (om x)
      = _ from connectionDifferenceSection_tensorCovDerivAt_homSplit (I := I) g₁ g₀ om X x]
  rw [show Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) x (X x) -
          connectionDifferencePairing (I := I) g₁ g₀ x
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
              (fun y : M => om y) x (X x)))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) =
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => connectionDifferencePairing (I := I) g₁ g₀ y (om y)) x (X x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)])
        - Tensor0SSpace.toModel
            (connectionDifferencePairing (I := I) g₁ g₀ x
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
                (fun y : M => om y) x (X x)))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
              ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) from by
      rw [Tensor0SSpace.toModel_sub]; rfl]
  rw [connectionDifferencePairing_covariantDerivative02_eval (I := I) g₁ g₀ om X Y Z x]
  rw [show Tensor0SSpace.toModel
        (connectionDifferencePairing (I := I) g₁ g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) =
      connectionDifferencePairing (I := I) g₁ g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) from rfl]
  rw [connectionDifferencePairing_covariantDerivative01_eval (I := I) g₁ g₀ om X Y Z x]
  have hvec : covDerivConnectionDifference (I := I) g₀ g₁ X Z Y x =
      (LeviCivita (I := I) g₀).toFun (fun b => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
        - connectionDifference (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
        - connectionDifference (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) := by
    have hexpand : covDerivConnectionDifference (I := I) g₀ g₁ X Z Y x =
        (LeviCivita (I := I) g₀).toFun (fun b => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
          - connectionDifference (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
          - connectionDifference (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x))
              (Z x) := rfl
    rw [hexpand]; abel
  rw [show (fun _ : Fin 1 => covDerivConnectionDifference (I := I) g₀ g₁ X Z Y x)
      = (fun _ : Fin 1 =>
          (LeviCivita (I := I) g₀).toFun (fun b => connectionDifference (I := I) g₁ g₀ b (Y b) (Z b)) x (X x)
            - connectionDifference (I := I) g₁ g₀ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x))
              (Z x)
            - connectionDifference (I := I) g₁ g₀ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      from by funext k; rw [hvec]]
  rw [tensor0SOne_apply_sub (I := I) x (om x), tensor0SOne_apply_sub (I := I) x (om x)]
  ring

end Curvature
end Geometry
end DifferentialGeometry
