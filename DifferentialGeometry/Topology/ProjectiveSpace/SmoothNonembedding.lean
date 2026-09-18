import DifferentialGeometry.Topology.Manifold.AmbientNormalOrientation
import DifferentialGeometry.Topology.Manifold.AmbientSectionExtension
import DifferentialGeometry.Topology.Manifold.TransverseFlow
import DifferentialGeometry.Topology.ProjectiveSpace.AntipodalCylinderOrientation
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem not_cooriented_projective_embedding
    (f : SphereAntipodalQuotient → ThreeSpace)
    (C : CoorientedSmoothEmbeddingRealNormalAtlas (𝓡 2) ThreeModel ∞ f)
    (hf : Function.Injective f) : False := by
  obtain ⟨V, hsupp, _, htrans⟩ := C.exists_compactlySupported_transverseField hf
  let v : ∀ a : ThreeSpace, TangentSpace ThreeModel a := V
  have hv : ContMDiff ThreeModel ThreeModel.tangent ∞
      (fun a => (⟨a, v a⟩ : TangentBundle ThreeModel ThreeSpace)) := V.contMDiff
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let F : SphereAntipodalQuotient × ℝ → ThreeSpace :=
    fun p => curveAt v hc (f p.1) p.2
  let q : S × ℝ → ThreeSpace := F ∘ SphereAntipodalQuotient.productProjection
  have hproj : IsLocalDiffeomorph CI CI ∞ SphereAntipodalQuotient.productProjection :=
    isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
      SphereAntipodalQuotient.isLocalDiffeomorph_proj
  have hF (x : SphereAntipodalQuotient) :
      IsLocalDiffeomorphAt CI ThreeModel ∞ F (x, 0) :=
    C.toSmoothEmbeddingRealNormalAtlas.isLocalDiffeomorphAt_flowMap
      (by simp [ThreeSpace]) v hv hsupp x (htrans x)
  have hq (y : S) : IsLocalDiffeomorphAt CI ThreeModel ∞ q (y, 0) :=
    IsLocalDiffeomorphAt.comp (P := ThreeSpace) ThreeModel (hproj (y, 0))
      (hF (SphereAntipodalQuotient.proj y))
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  let os : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel ThreeSpace :=
    DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
      (Orientation.reindex ℝ ThreeSpace (finCongr hdim).symm
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨om, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      ThreeModel os
  let om3 : DifferentialGeometry.ManifoldOrientation ThreeModel ThreeSpace 3 :=
    cast (congrArg
      (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel ThreeSpace n) hdim) om
  let o : TangentOrientationSection ThreeSpace :=
    { orientation := om3.orientation
      locally_constant := om3.locally_constant }
  apply not_antipodal_product_localDiffeomorphAt_zero o q hq
  intro p
  apply congrArg F
  exact (SphereAntipodalQuotient.productProjection_eq_iff p (-p.1, p.2)).mpr
    (Or.inr rfl) |>.symm

theorem SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree
    (f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3)) :
    ¬ IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f := by
  intro hf
  let C := smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement hf.isEmbedding
    (isImmersionOfComplement_real_of_isSmoothEmbedding_finrank_succ hf (by simp))
  obtain ⟨O⟩ := C.toEmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient
    hf.isEmbedding (isCompact_range hf.contMDiff.continuous).isClosed
  exact not_cooriented_projective_embedding f (C.coorientedAtlas O) hf.isEmbedding.injective

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
