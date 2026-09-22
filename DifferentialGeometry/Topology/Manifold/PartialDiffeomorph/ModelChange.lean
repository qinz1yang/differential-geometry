import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Mathlib.Geometry.Manifold.LocalDiffeomorph
open scoped Manifold ContDiff
namespace PartialDiffeomorph
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
def transContinuousLinearEquiv (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n where
  toPartialEquiv := Phi.toPartialEquiv
  open_source := Phi.open_source
  open_target := Phi.open_target
  contMDiffOn_toFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_toFun
  contMDiffOn_invFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_invFun
@[simp] theorem transContinuousLinearEquiv_source (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).source = Phi.source := rfl
@[simp] theorem transContinuousLinearEquiv_target (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).target = Phi.target := rfl
@[simp] theorem transContinuousLinearEquiv_apply (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') (x : M) :
    (Phi.transContinuousLinearEquiv e f) x = Phi x := rfl
@[simp] theorem transContinuousLinearEquiv_symm (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).symm = Phi.symm.transContinuousLinearEquiv f e := rfl
variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

theorem transContinuousLinearEquiv_trans
    (Phi : PartialDiffeomorph I J M N n) (Psi : PartialDiffeomorph J K N P n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') (g : G ≃L[𝕜] G') :
    (Phi.trans Psi).transContinuousLinearEquiv e g =
      (Phi.transContinuousLinearEquiv e f).trans (Psi.transContinuousLinearEquiv f g) := rfl

def ofTransContinuousLinearEquiv (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F')
    (Phi : PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := Phi.toPartialEquiv
  open_source := Phi.open_source
  open_target := Phi.open_target
  contMDiffOn_toFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_toFun
  contMDiffOn_invFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_invFun
@[simp] theorem transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F')
    (Phi : PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n) :
    (Phi.ofTransContinuousLinearEquiv e f).transContinuousLinearEquiv e f = Phi := rfl
@[simp] theorem ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (Phi : PartialDiffeomorph I J M N n) (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).ofTransContinuousLinearEquiv e f = Phi := rfl

end PartialDiffeomorph
