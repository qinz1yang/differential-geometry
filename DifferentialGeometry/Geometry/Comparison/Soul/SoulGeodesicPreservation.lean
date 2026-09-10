import DifferentialGeometry.Geometry.Comparison.Soul.InducedSliceConnection
import DifferentialGeometry.Geometry.Comparison.Soul.GeodesicGerms
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveIsometricImmersion

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem embeddedSlice_inclusion_preservesGeodesics
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    DifferentialGeometry.Geometry.PreservesGeodesics
      (inducedSliceMetric g hS) g (Subtype.val : S → M) := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
  let gS := inducedSliceMetric g hS
  change ∀ (γ : ℝ → S) (t : ℝ), IsGeodesicAt gS γ t →
    IsGeodesicAt g (Subtype.val ∘ γ) t
  intro γ t hγ
  obtain ⟨η, hη, hηgeo, heq⟩ := exists_contMDiff_representative_of_isGeodesicAt gS hγ
  have hi : ContMDiff IB I ∞ (Subtype.val : S → M) :=
    embeddedSlice_inclusion_contMDiff hS
  have hηM : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Subtype.val ∘ η) := hi.comp hη
  have hunit : ContMDiff 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro s
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  have hV : ContMDiff 𝓘(ℝ, ℝ) (ModelWithCorners.tangent IB) ∞
      (fun s => (⟨η s, mfderiv 𝓘(ℝ, ℝ) IB η s (1 : ℝ)⟩ : TangentBundle IB S)) := by
    change ContMDiff 𝓘(ℝ, ℝ) (ModelWithCorners.tangent IB) ∞
      (tangentMap 𝓘(ℝ, ℝ) IB η ∘ fun s : ℝ =>
        (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
    exact (hη.contMDiff_tangentMap (m := ∞) (by simp)).comp hunit
  have hpush :
      (fun s => mfderiv IB I (Subtype.val : S → M) (η s)
        (mfderiv 𝓘(ℝ, ℝ) IB η s (1 : ℝ))) =
      (fun s => mfderiv 𝓘(ℝ, ℝ) I (Subtype.val ∘ η) s (1 : ℝ)) := by
    funext s
    exact (mfderiv_comp_apply s (hi.mdifferentiableAt (by simp))
      (hη.mdifferentiableAt (by simp)) (1 : ℝ)).symm
  have hηMgeo : IsGeodesicAt g (Subtype.val ∘ η) t := by
    obtain ⟨U, hU, htU, _hcont, hgeo⟩ :=
      (isGeodesicAt_iff_exists_isGeodesicOn gS η t).mp hηgeo
    apply (isGeodesicAt_iff_exists_isGeodesicOn g (Subtype.val ∘ η) t).mpr
    refine ⟨U, hU, htU, hηM.continuous.continuousOn, ?_⟩
    intro s hs
    have hzero := (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := IB) gS η s hη).mpr (hgeo s hs)
    have hinc := embeddedSlice_inclusion_covDerivAlong g hEnorm hconv hclosed hB
      η hη (fun r => mfderiv 𝓘(ℝ, ℝ) IB η r (1 : ℝ)) hV s
    rw [hzero, map_zero, hpush] at hinc
    exact (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g (Subtype.val ∘ η) s hηM).mp hinc.symm
  apply isGeodesicAt_congr_of_eventuallyEq g hηMgeo
  filter_upwards [heq.symm] with s hs
  exact congrArg Subtype.val hs

end DifferentialGeometry.Geometry.Topology

end
