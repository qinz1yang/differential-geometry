import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Group.Constructions

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

section NormCharacterization

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem innerProductSpaceable_iff_nonempty_innerProductSpace :
    InnerProductSpaceable E ↔ Nonempty (InnerProductSpace ℝ E) :=
  ⟨fun _ => nonempty_innerProductSpace ℝ E,
    fun ⟨inst⟩ => inst.toInnerProductSpaceable⟩

@[instance_reducible]
noncomputable def innerProductSpaceOfInnerProductSpaceable (h : InnerProductSpaceable E) :
    InnerProductSpace ℝ E :=
  InnerProductSpace.ofNorm ℝ fun x y : E => h.parallelogram_identity x y

end NormCharacterization

theorem not_innerProductSpaceable_prod : ¬ InnerProductSpaceable (ℝ × ℝ) := by
  intro h
  have hp := h.parallelogram_identity ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  norm_num [Prod.norm_def] at hp

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
variable {D : RealTimeInterval}

private local instance w536ReducedVolumeMeasurableSpaceE : MeasurableSpace E := borel E
private local instance w536ReducedVolumeBorelSpaceE : BorelSpace E := ⟨rfl⟩
private local instance w536ReducedVolumeMeasurableSpaceM : MeasurableSpace M := borel M
private local instance w536ReducedVolumeBorelSpaceM : BorelSpace M := ⟨rfl⟩

noncomputable local instance w536ReducedVolumeInnerProductSpace [h : InnerProductSpaceable E] :
    InnerProductSpace ℝ E :=
  innerProductSpaceOfInnerProductSpaceable h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_anti_of_innerProductSpaceable [h : InnerProductSpaceable E]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau₂) :
    lReducedJacobian S T x Z tau₂ ≤ lReducedJacobian S T x Z tau₁ :=
  lReducedJacobian_anti S hS T x htau₁ h12 hZ

section Connected

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_lint_of_innerProductSpaceable [h : InnerProductSpaceable E]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (tau : ℝ) (htau : 0 < tau) (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) :=
  redVolume_lint S hS T x tau htau hslab

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_anti_of_innerProductSpaceable [h : InnerProductSpaceable E]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Set.Icc (T - tau₂) T ⊆ D.regular) :
    redVolume S T x tau₂ ≤ redVolume S T x tau₁ :=
  redVolume_anti S hS T x htau₁ h12 hslab

end Connected

end DifferentialGeometry.PDE.RicciFlow.Perelman
