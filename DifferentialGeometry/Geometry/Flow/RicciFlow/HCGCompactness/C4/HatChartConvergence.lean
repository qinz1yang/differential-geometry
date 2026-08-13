import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveraging
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBApproxIso
import DifferentialGeometry.Geometry.Exponential.GaussLemma
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem chartSymmUnif
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    UniformContinuousOn
      (fun v : E => (NormalCoordinates.normalChartAt (I := I) g p).symm v) K := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun v : E => ψ.symm v) K := by
    simpa [ψ] using ψ.contMDiffOn_invFun.continuousOn.mono hKtarget
  exact hK.uniformContinuousOn_of_continuous hcont

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartSymmIdConv
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist ((NormalCoordinates.normalChartAt (I := I) g p).symm v)
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (F a b v)) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  obtain ⟨η, hηpos, hηtarget⟩ :=
    hK.exists_cthickening_subset_open ψ.open_target hKtarget
  let K' : Set E := Metric.cthickening η K
  have hK' : IsCompact K' := hK.cthickening
  have hK'target : K' ⊆ ψ.target := by
    simpa only [K'] using hηtarget
  have huc :
      UniformContinuousOn
        (fun v : E => ψ.symm v) K' :=
    chartSymmUnif (I := I) g p hK' hK'target
  rw [Metric.uniformContinuousOn_iff] at huc
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  have hminpos : 0 < min δ η := lt_min hδpos hηpos
  obtain ⟨N, hN⟩ := hclose (min δ η) hminpos
  refine ⟨N, fun a ha b hb v hv => ?_⟩
  have hvK' : v ∈ K' := Metric.self_subset_cthickening K hv
  have hdist : dist (F a b v) v < min δ η := hN a ha b hb v hv
  have hFvK' : F a b v ∈ K' := by
    exact Metric.mem_cthickening_of_dist_le (F a b v) v η K hv
      (le_trans (le_of_lt hdist) (min_le_right δ η))
  simpa [dist_comm] using
    hδ (F a b v) hFvK' v hvK' (lt_of_lt_of_le hdist (min_le_left δ η))

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPtsConv
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S : Set M} {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hSsource : ∀ x : M, x ∈ S →
      x ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hScoord : ∀ x : M, x ∈ S →
      (NormalCoordinates.normalChartAt (I := I) g p) x ∈ K)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ x : M, x ∈ S →
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hdecoded :
      ∀ ε : Real, ε > 0 → ∃ N : Nat,
        ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
          dist (ψ.symm v) (ψ.symm (F a b v)) < ε := by
    simpa [ψ] using
      chartSymmIdConv (I := I) g p hK hKtarget F hclose
  intro ε hε
  obtain ⟨N, hN⟩ := hdecoded ε hε
  refine ⟨N, fun a ha b hb x hx => ?_⟩
  have hxK : ψ x ∈ K := by
    simpa [ψ] using hScoord x hx
  have hxsrc : x ∈ ψ.source := by
    simpa [ψ] using hSsource x hx
  have hdist : dist (ψ.symm (ψ x)) (ψ.symm (F a b (ψ x))) < ε :=
    hN a ha b hb (ψ x) hxK
  have hleft : ψ.symm (ψ x) = x := by
    simpa [ψ] using NormalCoordinates.normalChartAt_left_inv (I := I) g p hxsrc
  rw [hleft] at hdist
  simpa [ψ] using hdist

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPtsSrcK
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S Ksrc : Set M} (hKsrc : IsCompact Ksrc) (hSsub : S ⊆ Ksrc)
    (hsrcK : Ksrc ⊆ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (F : Nat -> Nat -> E -> E)
    (hclose : ∀ δ : Real, δ > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) g p) '' Ksrc ->
          dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ x : M, x ∈ S ->
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun x : M => ψ x) Ksrc := by
    exact ψ.contMDiffOn_toFun.continuousOn.mono hsrcK
  have hK : IsCompact (ψ '' Ksrc) := hKsrc.image_of_continuousOn hcont
  have hKtarget : ψ '' Ksrc ⊆ ψ.target := by
    rintro v ⟨x, hx, rfl⟩
    exact ψ.map_source (hsrcK hx)
  have hSsource : ∀ x : M, x ∈ S -> x ∈ ψ.source := by
    intro x hx
    exact hsrcK (hSsub hx)
  have hScoord : ∀ x : M, x ∈ S -> ψ x ∈ ψ '' Ksrc := by
    intro x hx
    exact ⟨x, hSsub hx, rfl⟩
  simpa [ψ] using
    chartPtsConv (I := I) (g := g) (p := p) (S := S) (K := ψ '' Ksrc)
      hK hKtarget hSsource hScoord F hclose

omit [Module.Finite ℝ E] in
theorem properBallSrcOfRad
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    Metric.closedBall c R ⊆
      (NormalCoordinates.normalChartAt (I := I) Y.metric c).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  intro y hy
  have hed :
      riemannianEDist I c y =
        ENNReal.ofReal (dist c y) := by
    have h := P.realizes c y
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c y ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_le : dist c y ≤ R := by
    have hdist := (Metric.mem_closedBall.mp hy)
    simpa [dist_comm] using hdist
  have hsmall : (riemannianEDist I c y).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c y)]
    exact lt_of_le_of_lt hdist_le hR
  exact memNChartSrcOfDist (I := I) Y.metric c hEnorm hfin hsmall

omit [Module.Finite ℝ E] in
theorem properBallNormal
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c y : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hy : letI : MetricSpace Y.M := P.ms; y ∈ Metric.ball c R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    ∃ v : E,
      v ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric c).target ∧
      (show TangentSpace I c from v) ∈ expDomain (I := I) Y.metric c ∧
      Real.sqrt (Y.metric.inner c v v) = dist c y ∧
      y = expMap (I := I) Y.metric c (show TangentSpace I c from v) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w)
  have hed : riemannianEDist I c y = ENNReal.ofReal (dist c y) := by
    have h := P.realizes c y
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c y ≠ (⊤ : ENNReal) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_lt : dist c y < R := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  have hsmall : (riemannianEDist I c y).toReal <
      expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal dist_nonneg]
    exact hdist_lt.trans hR
  obtain ⟨v, hvtgt, hvdom, hvlen, hyeq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  refine ⟨v, hvtgt, hvdom, ?_, hyeq⟩
  calc
    Real.sqrt (Y.metric.inner c v v) = (riemannianEDist I c y).toReal := hvlen
    _ = dist c y := by rw [hed, ENNReal.toReal_ofReal dist_nonneg]

omit [Module.Finite ℝ E] in
theorem properExpDist
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (c : Y.M) {v : E}
    (hv :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Real.sqrt (Y.metric.inner c v v) < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
      Real.sqrt (Y.metric.inner c v v) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w)
  have hed := edist_exp_eq_radius (I := I) Y.metric c hEnorm hv
  have hdist :
      riemannianEDist I c
          (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
        ENNReal.ofReal
          (dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) := by
    have h := P.realizes c
      (expMap (I := I) Y.metric c (show TangentSpace I c from v))
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hofReal :
      ENNReal.ofReal
          (dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) =
        ENNReal.ofReal (Real.sqrt (Y.metric.inner c v v)) := by
    rw [← hdist]
    exact hed
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp hofReal


end HCGCompactness
end DifferentialGeometry
