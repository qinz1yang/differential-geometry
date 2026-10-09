import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Geometry.Metric.Pullback.FinitePatchCurvature
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteInteriorPatch

/-!
# Actual finite inverse patches inside a cusp collar

Positive height and the original boundary-preimage ledger give intrinsic interior points.
The finite inverse patch is selected directly from the original cusp embedding.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Filter GC.Endpoint Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem isOpen_cuspDomain : IsOpen cuspDomain := by
  change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Iio cuspDepth)
  apply isOpen_Iio.preimage
  fun_prop

theorem cusp_isInteriorPoint_of_height_pos {p : CuspHalfSpace} (hp : 0 < p.2.val 0) :
    halfCollarModel.IsInteriorPoint p := by
  change p ∈ halfCollarModel.interior CuspHalfSpace
  rw [ModelWithCorners.interior_prod]
  refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
  change extChartAt (𝓡∂ 1) p.2 p.2 ∈ interior (Set.range (𝓡∂ 1))
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  simpa using hp

theorem CuspEmbedding.exists_finiteInteriorPatch {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) :
    ∃ Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier (K + 1),
      p ∈ Φ.source ∧ Φ.source ⊆ cuspDomain ∧ EqOn e.toFun Φ Φ.source ∧
      Φ.source ⊆ halfCollarModel.interior CuspHalfSpace ∧ Φ.target ⊆ W.interior := by
  have heI : W.model.IsInteriorPoint (e.toFun p) := by
    apply (W.model.isInteriorPoint_iff_not_isBoundaryPoint (e.toFun p)).mpr
    intro hb
    have hez := (CuspEmbedding.boundary_preimage e (p := p) hp).mp hb
    exact hz.ne' hez
  exact DifferentialGeometry.Topology.Manifold.exists_finiteInteriorPatch (n := K + 1) (by omega)
    isOpen_cuspDomain e.contMDiffOn hp (cusp_isInteriorPoint_of_height_pos hz) heI
    (by simp) (e.immersion p hp)

theorem cusp_isInteriorPoint_iff_height_pos {p : CuspHalfSpace} :
    halfCollarModel.IsInteriorPoint p ↔ 0 < p.2.val 0 := by
  refine ⟨fun hp => ?_, cusp_isInteriorPoint_of_height_pos⟩
  change p ∈ halfCollarModel.interior CuspHalfSpace at hp
  rw [ModelWithCorners.interior_prod] at hp
  have hhalf := hp.2
  change extChartAt (𝓡∂ 1) p.2 p.2 ∈ interior (Set.range (𝓡∂ 1)) at hhalf
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hhalf
  simpa using hhalf

theorem CuspEmbedding.isOpen_image_positive_cuspDomain {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) :
    IsOpen (e.toFun '' {p | p ∈ cuspDomain ∧ 0 < p.2.val 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, ⟨hp, hz⟩, rfl⟩
  obtain ⟨Φ, hpΦ, hΦU, heq, hΦI, _hΦT⟩ := e.exists_finiteInteriorPatch hp hz
  have htarget : e.toFun p ∈ Φ.target := by
    rw [heq hpΦ]
    exact Φ.map_source hpΦ
  apply Filter.mem_of_superset (Φ.open_target.mem_nhds htarget)
  intro z hzΦ
  have hsource := Φ.map_target hzΦ
  refine ⟨Φ.symm z, ⟨hΦU hsource,
    cusp_isInteriorPoint_iff_height_pos.mp (hΦI hsource)⟩, ?_⟩
  exact (heq hsource).trans (Φ.right_inv' hzΦ)

theorem CuspEmbedding.exists_finitePullbackPatch {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) :
    ∃ Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier (K + 1),
      p ∈ Φ.source ∧ Φ.source ⊆ cuspDomain ∧ EqOn e.toFun Φ Φ.source ∧
      Φ.source ⊆ halfCollarModel.interior CuspHalfSpace ∧ Φ.target ⊆ W.interior ∧
      ∃ h : Bundle.ContMDiffRiemannianMetric halfCollarModel K
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
            EuclideanSpace ℝ (Fin 1))
          (TangentSpace halfCollarModel :
            (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens CuspHalfSpace) → Type _),
        ∀ x v w, h.inner x v w = g.inner (e.toFun x)
          (mfderiv halfCollarModel W.model e.toFun (x : CuspHalfSpace) v)
          (mfderiv halfCollarModel W.model e.toFun (x : CuspHalfSpace) w) := by
  obtain ⟨Φ, hpΦ, hΦU, heq, hΦI, hΦT⟩ := e.exists_finiteInteriorPatch hp hz
  refine ⟨Φ, hpΦ, hΦU, heq, hΦI, hΦT,
    finitePatchPullbackMetric g Φ (m := K) le_rfl, ?_⟩
  intro x v w
  have heqx : e.toFun =ᶠ[nhds (x : CuspHalfSpace)] Φ :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds x.property) fun y hy => heq hy
  rw [finitePatchPullbackMetric_inner]
  have hdv : mfderiv halfCollarModel W.model e.toFun (x : CuspHalfSpace) v =
      mfderiv halfCollarModel W.model Φ (x : CuspHalfSpace) v :=
    congrArg (fun L : TangentSpace halfCollarModel (x : CuspHalfSpace) →L[ℝ]
      TangentSpace W.model (e.toFun x) => L v)
      (heqx.mfderiv_eq (I := halfCollarModel) (I' := W.model))
  have hdw : mfderiv halfCollarModel W.model e.toFun (x : CuspHalfSpace) w =
      mfderiv halfCollarModel W.model Φ (x : CuspHalfSpace) w :=
    congrArg (fun L : TangentSpace halfCollarModel (x : CuspHalfSpace) →L[ℝ]
      TangentSpace W.model (e.toFun x) => L w)
      (heqx.mfderiv_eq (I := halfCollarModel) (I' := W.model))
  exact (congrArg (fun y : W.Carrier => g.inner y
    (mfderiv halfCollarModel W.model Φ (x : CuspHalfSpace) v)
    (mfderiv halfCollarModel W.model Φ (x : CuspHalfSpace) w))
    heqx.self_of_nhds.symm).trans
    (congrArg₂ (fun a b : TangentSpace W.model (e.toFun x) =>
      g.inner (e.toFun x) a b) hdv.symm hdw.symm)

end DifferentialGeometry.Geometry.Collapse
