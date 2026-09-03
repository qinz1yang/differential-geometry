import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Exponential.DiagonalInverseBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace DiagonalInverseBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def fixedBasePartialDiffeomorph
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
  (B.fixed p).hom

@[simp]
theorem fixedBasePartialDiffeomorph_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) (u : E) :
    B.fixedBasePartialDiffeomorph u =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from u) :=
  rfl

@[simp]
theorem fixedBasePartialDiffeomorph_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    B.fixedBasePartialDiffeomorph.source =
      (fun u : E => (⟨p, u⟩ : TangentBundle I M)) ⁻¹' B.hom.source :=
  rfl

@[simp]
theorem fixedBasePartialDiffeomorph_target
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    B.fixedBasePartialDiffeomorph.target =
      (fun q : M => (p, q)) ⁻¹' B.dom :=
  rfl

@[simp]
theorem fixedBasePartialDiffeomorph_symm_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) (q : M) :
    B.fixedBasePartialDiffeomorph.symm q = ((B.inv (p, q)).snd : E) :=
  rfl

theorem fixedBasePartialDiffeomorph_zero_mem_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    (0 : E) ∈ B.fixedBasePartialDiffeomorph.source := by
  exact B.zero_mem

theorem fixedBasePartialDiffeomorph_center_mem_target
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    p ∈ B.fixedBasePartialDiffeomorph.target := by
  have hmap :=
    B.fixedBasePartialDiffeomorph.map_source B.fixedBasePartialDiffeomorph_zero_mem_source
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  simpa only [fixedBasePartialDiffeomorph_apply, hzero] using hmap

theorem fixedBasePartialDiffeomorph_symm_center
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    B.fixedBasePartialDiffeomorph.symm p = (0 : E) := by
  have hleft :=
    B.fixedBasePartialDiffeomorph.left_inv B.fixedBasePartialDiffeomorph_zero_mem_source
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  change B.fixedBasePartialDiffeomorph.symm.toPartialEquiv p = (0 : E)
  change B.fixedBasePartialDiffeomorph.symm.toPartialEquiv (B.fixedBasePartialDiffeomorph (0 : E)) = (0 : E) at hleft
  rw [show B.fixedBasePartialDiffeomorph (0 : E) = p by simpa only [fixedBasePartialDiffeomorph_apply] using hzero] at hleft
  exact hleft

end DiagonalInverseBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
