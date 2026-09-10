import DifferentialGeometry.Geometry.Comparison.Soul.SoulDiffeomorph
import DifferentialGeometry.Geometry.Comparison.Soul.SoulGeodesicCarrier
import DifferentialGeometry.Geometry.Comparison.Soul.PointNormalBundle
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveGeodesicCarrier

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Completeness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem riemannianMetricComplete_of_isMetricNorm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) :
    RiemannianMetricComplete (I := I) g := by
  let m : PseudoEMetricSpace M := inferInstance
  have hmcomplete : @CompleteSpace M m.toUniformSpace := inferInstance
  have hdist (x y : M) :
      riemannianEDistOf (I := I) g x y = @edist M m.toEDist x y :=
    (riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y).trans
      (IsRiemannianManifold.out (I := I) x y).symm
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  refine ⟨?_⟩
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let hEM : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : EMetricSpace M := hEM
  change @CompleteSpace M hEM.toPseudoEMetricSpace.toUniformSpace
  have heq : hEM.toPseudoEMetricSpace = m := by
    apply PseudoEMetricSpace.ext
    ext x y
    change riemannianEDistOf (I := I) g x y = @edist M m.toEDist x y
    exact hdist x y
  rw [heq]
  exact hmcomplete

end Completeness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem maxSliceDim_eq_zero_of_positiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {S : Set M} (hne : S.Nonempty) (hcompact : IsCompact S)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    maxSliceDim I S = 0 := by
  by_contra hzero
  have hpos : 0 < maxSliceDim I S := Nat.pos_of_ne_zero hzero
  apply Poincare.Geometry.no_compact_geodesic_carrier (I := I) g
    (riemannianMetricComplete_of_isMetricNorm g hEnorm) hsec hdim S hne hcompact
  intro x hx
  obtain ⟨γ, hγzero, hγsmooth, hγgeo, hγgerm, hγunit, hγmem⟩ :=
    exists_unit_geodesic_in_soul_of_pos_dim g hEnorm hconv hcompact.isClosed hB hpos hx
  refine ⟨γ, hγzero, 1, zero_lt_one, hγgerm 0, hγsmooth.contMDiffOn, ?_, ?_, ?_⟩
  · intro t _ht
    exact hγgeo t
  · intro t _ht
    exact hγunit t
  · intro t _ht
    exact hγmem t

theorem exists_point_soul_diffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g) (p : M) :
    ∃ (S : Set M) (s : M), S = {s} ∧ S.Nonempty ∧ IsCompact S ∧
      IsTotallyConvex (I := I) g S ∧ relBoundary I S = ∅ ∧ maxSliceDim I S = 0 ∧
      ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ E, e s = 0 := by
  classical
  obtain ⟨S, hconv, hB, hne, hcompact, _hconnected, hcodim, _hgeodesic, hbundle⟩ :=
    exists_soul_normal_diffeomorph g hEnorm hsec.toNonnegative p
  have hzero : maxSliceDim I S = 0 := by
    by_cases hdim : 2 ≤ Module.finrank ℝ E
    · exact maxSliceDim_eq_zero_of_positiveSectionalCurvature g hEnorm hsec hdim
        hne hcompact hconv hB
    · omega
  obtain ⟨s, hsingleton⟩ :=
    eq_singleton_of_maxSliceDim_eq_zero g hEnorm hconv hne hB hzero
  refine ⟨S, s, hsingleton, hne, hcompact, hconv, hB, hzero, ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  obtain ⟨_hembedding, Φ, hΦzero⟩ := hbundle
  obtain ⟨Ψ, hΨzero⟩ :=
    exists_point_normalBundle_diffeomorph g hEnorm hne hconv hB hzero
  let q : S := ⟨s, by rw [hsingleton]; exact mem_singleton s⟩
  refine ⟨Φ.symm.trans Ψ, ?_⟩
  change Ψ (Φ.symm s) = 0
  have hΦq : Φ ⟨q, 0⟩ = s := hΦzero q
  rw [← hΦq, Φ.symm_apply_apply]
  exact hΨzero q

end DifferentialGeometry.Geometry.Topology

end
