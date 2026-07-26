import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option autoImplicit false

/-!
# Fixed-base partial diffeomorphisms from diagonal exponential branches

This file retains the established fixed-partial-diffeomorphism API as a
compatibility projection of `DiagInvBranch.fixed`.  The canonical fixed-first
object is `ExpInvBranch`.
-/

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace DiagInvBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The established fixed-partial-diffeomorphism view of the canonical
fixed-first branch. -/
def fixedPD
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
  (B.fixed p).hom

/-- The fixed-base partial diffeomorphism agrees with the intrinsic
exponential map. -/
@[simp]
theorem fixedPD_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) (u : E) :
    B.fixedPD u =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from u) :=
  rfl

/-- The source of the fixed-base partial diffeomorphism is the corresponding
slice of the diagonal branch source. -/
@[simp]
theorem fixedPD_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.source =
      (fun u : E => (⟨p, u⟩ : TangentBundle I M)) ⁻¹' B.hom.source :=
  rfl

/-- The target of the fixed-base partial diffeomorphism is the corresponding
slice of the diagonal branch target. -/
@[simp]
theorem fixedPD_target
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.target =
      (fun q : M => (p, q)) ⁻¹' B.dom :=
  rfl

/-- The inverse of the fixed-base partial diffeomorphism is the selected
fixed-first coordinate readout. -/
@[simp]
theorem fixedPD_inv_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) (q : M) :
    B.fixedPD.symm q = ((B.inv (p, q)).snd : E) :=
  rfl

/-- The model-space origin belongs to the fixed-base source. -/
theorem fixedPD_zero_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    (0 : E) ∈ B.fixedPD.source := by
  exact B.zero_mem

/-- The branch center belongs to the fixed-base target. -/
theorem fixedPD_center_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    p ∈ B.fixedPD.target := by
  have hmap :=
    B.fixedPD.map_source B.fixedPD_zero_mem
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  simpa only [fixedPD_apply, hzero] using hmap

/-- The inverse fixed-base chart sends its center to the model-space
origin. -/
@[simp]
theorem fixedPD_symm_center
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.symm p = (0 : E) := by
  have hleft :=
    B.fixedPD.left_inv B.fixedPD_zero_mem
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  simpa only [fixedPD_apply, hzero] using hleft

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
