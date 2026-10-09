import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingOpenImage
import DifferentialGeometry.Topology.Manifold.OpenPartialHomeomorph.InverseRegularity

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {δ : ℝ} {X : Set W.Carrier}

/-- The actual cusp immersion has invertible derivative because both tangent
spaces have dimension three. No metric-error smallness is needed. -/
theorem CuspEmbedding.isInvertible_mfderiv_at
    (e : CuspEmbedding W g K δ X) (p : CuspHalfSpace) (hp : p ∈ cuspDomain) :
    (mfderiv halfCollarModel W.model e.toFun p).IsInvertible := by
  let A := mfderiv halfCollarModel W.model e.toFun p
  have hdim : Module.finrank ℝ (TangentSpace halfCollarModel p) =
      Module.finrank ℝ (TangentSpace W.model (e.toFun p)) := by
    change Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp
  let L := (A.toLinearMap.linearEquivOfInjective (e.immersion p hp) hdim).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

/-- Package the given finite-order cusp embedding and its actual image as a
partial diffeomorphism, retaining its total forward map and controlled domain. -/
def CuspEmbedding.toPartialDiffeomorph
    (e : CuspEmbedding W g K δ X) :
    PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier (K + 1) := by
  have hinj : InjOn e.toFun cuspDomain := by
    intro p hp q hq hpq
    exact congrArg Subtype.val (e.isEmbedding.injective
      (show (fun z : cuspDomain => e.toFun z) ⟨p, hp⟩ =
        (fun z : cuspDomain => e.toFun z) ⟨q, hq⟩ from hpq))
  have hopen : _root_.Topology.IsOpenEmbedding (cuspDomain.domRestrict e.toFun) :=
    ⟨e.isEmbedding, by simpa only [range_domRestrict] using e.isOpen_image_openness⟩
  have hdomain : IsOpen cuspDomain :=
    isOpen_lt (by fun_prop) continuous_const
  let d := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv e.toFun cuspDomain) e.contMDiffOn.continuousOn
    hopen.isOpenMap hdomain
  exact DifferentialGeometry.Topology.OpenPartialHomeomorph.toPartialDiffeomorphOfIsInvertibleMFDeriv
    (K + 1) (by omega) d e.contMDiffOn (fun p hp => e.isInvertible_mfderiv_at p hp)

@[simp] theorem CuspEmbedding.toPartialDiffeomorph_source
    (e : CuspEmbedding W g K δ X) : e.toPartialDiffeomorph.source = cuspDomain := rfl

@[simp] theorem CuspEmbedding.toPartialDiffeomorph_target
    (e : CuspEmbedding W g K δ X) :
    e.toPartialDiffeomorph.target = e.toFun '' cuspDomain := rfl

@[simp] theorem CuspEmbedding.coe_toPartialDiffeomorph
    (e : CuspEmbedding W g K δ X) :
    (e.toPartialDiffeomorph : CuspHalfSpace → W.Carrier) = e.toFun := rfl

end DifferentialGeometry.Geometry.Collapse
