import DifferentialGeometry.Analysis.Parabolic.HarmonicMapHeatFlow.Galerkin
import DifferentialGeometry.Geometry.Metric.DeTurck.HarmonicMapTension
import DifferentialGeometry.Analysis.Integration.Measure.Family.ParametricContinuity
import DifferentialGeometry.Geometry.Exponential.Variation.Smoothness
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Bundle Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Geometry.Riemannian.Exponential

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M]
  [SigmaCompactSpace M]

@[reducible] private noncomputable def harmonicMapFlowRiemBundle
    (q : SmoothRiemannianMetric I M) :
    RiemannianBundle (fun x : M => TangentSpace I x) :=
  ⟨q.toRiemannianMetric⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M] [SigmaCompactSpace M] in
private theorem harmonicMapFlowContBundle
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      harmonicMapFlowRiemBundle (I := I) q
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    harmonicMapFlowRiemBundle (I := I) q
  exact ⟨q.inner, q.contMDiff.continuous, fun _ _ _ => rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[reducible] private noncomputable def harmonicMapFlowEMetric
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      harmonicMapFlowRiemBundle (I := I) q
    PseudoEMetricSpace M := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    harmonicMapFlowRiemBundle (I := I) q
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    harmonicMapFlowContBundle (I := I) q
  exact PseudoEMetricSpace.ofRiemannianMetric I M

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [SigmaCompactSpace M]
  [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem harmonicMapFlowEnorm
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      harmonicMapFlowRiemBundle (I := I) q
    ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (q.inner x v v)) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    harmonicMapFlowRiemBundle (I := I) q
  intro x v
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def harmonicMapFlowDiagExp
    (q : SmoothRiemannianMetric I M) : TangentBundle I M → M × M := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    harmonicMapFlowRiemBundle (I := I) q
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    harmonicMapFlowContBundle (I := I) q
  letI : PseudoEMetricSpace M := harmonicMapFlowEMetric (I := I) q
  exact diagExp (I := I) q (harmonicMapFlowEnorm (I := I) q)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowDiagExp_cd_zero
    (q : SmoothRiemannianMetric I M) (x : M) (n : ℕ) :
    ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (harmonicMapFlowDiagExp (I := I) (M := M) q)
      (⟨x, (0 : E)⟩ : TangentBundle I M) := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    harmonicMapFlowRiemBundle (I := I) q
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    harmonicMapFlowContBundle (I := I) q
  let : PseudoEMetricSpace M := harmonicMapFlowEMetric (I := I) q
  change ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
    (diagExp (I := I) q (harmonicMapFlowEnorm (I := I) q))
    (⟨x, (0 : E)⟩ : TangentBundle I M)
  exact diagExp_contMDiffAt_zero (I := I)
    q (harmonicMapFlowEnorm (I := I) q) x n

noncomputable def harmonicMapFlowAdd
    (q : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) : M → M :=
  fun x =>
    (harmonicMapFlowDiagExp (I := I) (M := M) q
      (⟨x, harmonicMapFlowUnknown (I := I) q S x⟩ : TangentBundle I M)).2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M] [SigmaCompactSpace M] in
@[simp] theorem harmonicMapFlowUnknown_zero
    (q : SmoothRiemannianMetric I M) (x : M) :
    harmonicMapFlowUnknown (I := I) q (0 : SmoothCcTensor q 0 1) x = 0 := by
  change harmonicMapFlowUnknownLM (I := I) q x 0 = 0
  exact map_zero _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowAdd_zero
    (q : SmoothRiemannianMetric I M) :
    harmonicMapFlowAdd (I := I) (M := M) q (0 : SmoothCcTensor q 0 1) = id := by
  funext x
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    harmonicMapFlowRiemBundle (I := I) q
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    harmonicMapFlowContBundle (I := I) q
  let : PseudoEMetricSpace M := harmonicMapFlowEMetric (I := I) q
  have hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm
      (I := I) (M := M) q := by
    with_unfolding_all
      exact harmonicMapFlowEnorm (I := I) q
  change (diagExp (I := I) q hEnorm
      (⟨x, harmonicMapFlowUnknown (I := I) q (0 : SmoothCcTensor q 0 1) x⟩ :
        TangentBundle I M)).2 = x
  rw [harmonicMapFlowUnknown_zero, diagExp_snd,
    expMapIntrinsic_zero (I := I) q hEnorm x]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowAdd_zero_md
    (q : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (harmonicMapFlowAdd (I := I) (M := M) q
      (0 : SmoothCcTensor q 0 1)) x v = v := by
  rw [harmonicMapFlowAdd_zero, mfderiv_id]
  rfl

noncomputable def harmonicMapFlowSpecLaunch
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (p : EuclideanSpace ℝ {i // i ∈ S} × M) : TangentBundle I M :=
  TotalSpace.mk' E p.2
    (harmonicMapFlowUnknown (I := I) q
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpecLaunch_zero
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) (x : M) :
    harmonicMapFlowSpecLaunch (I := I) (M := M) q S (0, x) =
      (⟨x, (0 : E)⟩ : TangentBundle I M) := by
  simp only [harmonicMapFlowSpecLaunch, map_zero, harmonicMapFlowUnknown_zero]
  rfl

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecLaunch_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
      (∞ : WithTop ℕ∞)
      (harmonicMapFlowSpecLaunch (I := I) (M := M) q S) := by
  classical
  have hterm : ∀ j : {i // i ∈ S},
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
        (∞ : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          TotalSpace.mk' E p.2
            (p.1 j • harmonicMapFlowUnknown (I := I) q
              (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) := by
    intro j
    have hc : ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ, ℝ)
          (∞ : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M => p.1 j) := by
      have hp : ContDiff ℝ (∞ : WithTop ℕ∞)
          (EuclideanSpace.proj (𝕜 := ℝ) j :
            EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
      exact hp.contMDiff.comp contMDiff_fst
    have hs : ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
          (∞ : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          TotalSpace.mk' E p.2
            (harmonicMapFlowUnknown (I := I) q
              (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) :=
      (harmonicMapFlowUnknownSec (I := I) q
        (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1)).contMDiff.comp
          contMDiff_snd
    simpa only [EuclideanSpace.coe_proj] using hc.smul_bundle hs
  have hsum : ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
        (∞ : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
        TotalSpace.mk' E p.2
          (∑ j : {i // i ∈ S}, p.1 j • harmonicMapFlowUnknown (I := I) q
            (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) := by
    exact ContMDiff.sum_bundle (F := E) contMDiff_snd Finset.univ
      (fun j _ => hterm j)
  refine hsum.congr (fun p => ?_)
  simp only [harmonicMapFlowSpecLaunch, harmonicMapFlowSpecIncl_apply]
  apply congrArg (TotalSpace.mk' E p.2)
  change harmonicMapFlowUnknownLM (I := I) q p.2
      (∑ j : {i // i ∈ S},
        p.1 j • eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, harmonicMapFlowUnknownLM_apply]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecChart
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ∀ x : M,
          ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
            (harmonicMapFlowDiagExp (I := I) (M := M) q)
            (harmonicMapFlowSpecLaunch (I := I) (M := M) q S (u, x)) := by
  classical
  let U : Set (TangentBundle I M) :=
    {z | ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (harmonicMapFlowDiagExp (I := I) (M := M) q) z}
  have hfinite : ((n : ℕ∞) : WithTop ℕ∞) ≠ (∞ : WithTop ℕ∞) := by
    simp
  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (contMDiffAt_iff_contMDiffAt_nhds hfinite).1 hz
  let P : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    (harmonicMapFlowSpecLaunch (I := I) (M := M) q S) ⁻¹' U
  have hP_open : IsOpen P :=
    hU_open.preimage (harmonicMapFlowSpecLaunch_cd (I := I) (M := M) q S).continuous
  have hslice :
      ({(0 : EuclideanSpace ℝ {i // i ∈ S})} ×ˢ (Set.univ : Set M)) ⊆ P := by
    rintro ⟨u, x⟩ ⟨hu, -⟩
    simp only [Set.mem_singleton_iff] at hu
    subst u
    change harmonicMapFlowSpecLaunch (I := I) (M := M) q S (0, x) ∈ U
    rw [harmonicMapFlowSpecLaunch_zero]
    exact harmonicMapFlowDiagExp_cd_zero (I := I) (M := M) q x n
  obtain ⟨A, B, hA_open, _hB_open, hzeroA, hunivB, hAB⟩ :=
    generalized_tube_lemma
      (isCompact_singleton (x := (0 : EuclideanSpace ℝ {i // i ∈ S})))
      (isCompact_univ : IsCompact (Set.univ : Set M)) hP_open hslice
  have hzeroA' : (0 : EuclideanSpace ℝ {i // i ∈ S}) ∈ A := hzeroA rfl
  obtain ⟨R, hR_pos, hR_ball⟩ := Metric.isOpen_iff.mp hA_open 0 hzeroA'
  refine ⟨R, hR_pos, ?_⟩
  intro u hu x
  have hux : (u, x) ∈ A ×ˢ B :=
    ⟨hR_ball hu, hunivB (Set.mem_univ x)⟩
  exact hAB hux

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecAdd_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod I)
        (n : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          harmonicMapFlowDiagExp (I := I) (M := M) q
            (harmonicMapFlowSpecLaunch (I := I) (M := M) q S p))
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hchart⟩ :=
    harmonicMapFlowSpecChart (I := I) (M := M) q S n
  refine ⟨R, hR, ?_⟩
  intro p hp
  have hlaunch :
      ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
        (n : ℕ∞) (harmonicMapFlowSpecLaunch (I := I) (M := M) q S) p :=
    (harmonicMapFlowSpecLaunch_cd (I := I) (M := M) q S).contMDiffAt.of_le
      (by exact_mod_cast le_top)
  exact ((hchart p.1 hp.1 p.2).comp p hlaunch).contMDiffWithinAt

noncomputable def harmonicMapFlowDirDensity
    (q h : SmoothRiemannianMetric I M) (Phi : M → M) (x : M) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i : Fin (Module.finrank ℝ E),
      q.inner (Phi x)
        (mfderiv I I Phi x
          (metricComparisonEndomorphism (I := I) q h x
            (smoothOrthoFrame (I := I) q x i x)))
        (mfderiv I I Phi x (smoothOrthoFrame (I := I) q x i x))

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowDirDensity_zero
    (q h : SmoothRiemannianMetric I M) (x : M) :
    harmonicMapFlowDirDensity (I := I) (M := M) q h
        (harmonicMapFlowAdd (I := I) (M := M) q (0 : SmoothCcTensor q 0 1)) x =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          q.inner x
            (metricComparisonEndomorphism (I := I) q h x
              (smoothOrthoFrame (I := I) q x i x))
            (smoothOrthoFrame (I := I) q x i x) := by
  rw [harmonicMapFlowDirDensity, harmonicMapFlowAdd_zero]
  simp only [id_eq, mfderiv_id]
  rfl

noncomputable def harmonicMapFlowDirEnergy
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, harmonicMapFlowDirDensity (I := I) (M := M) q h
      (harmonicMapFlowAdd (I := I) (M := M) q S) x
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

noncomputable def harmonicMapFlowSpecEnergy
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) : ℝ :=
  harmonicMapFlowDirEnergy (I := I) (M := M) q (g t)
    (harmonicMapFlowSpecIncl (I := I) (M := M) q S u)

noncomputable def harmonicMapFlowSpecResid
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  -fderiv ℝ (harmonicMapFlowSpecEnergy (I := I) (M := M) q g S t) u

noncomputable def harmonicMapFlowSpecPrincipal
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  -(harmonicMapFlowFinForm (I := I) (M := M) q (g t)
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S) u)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpecPrincipal_apply
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u v : EuclideanSpace ℝ {i // i ∈ S}) :
    harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t u v =
      -harmonicMapFlowWeakForm (I := I) (M := M) q (g t)
        (harmonicMapFlowSpecIncl (I := I) (M := M) q S u)
        (harmonicMapFlowSpecIncl (I := I) (M := M) q S v) := by
  simp only [harmonicMapFlowSpecPrincipal, neg_apply, harmonicMapFlowFinForm_apply]

noncomputable def harmonicMapFlowSpecLow
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  harmonicMapFlowSpecResid (I := I) (M := M) q g S t u -
    harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t u

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpec_split
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    harmonicMapFlowSpecResid (I := I) (M := M) q g S t u =
      harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t u +
        harmonicMapFlowSpecLow (I := I) (M := M) q g S t u := by
  simp only [harmonicMapFlowSpecLow]
  abel

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpecPrincipal_zero
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) :
    harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t 0 = 0 := by
  simp only [harmonicMapFlowSpecPrincipal, map_zero, neg_zero]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecPrincipal_nonpos
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      (g t).inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t u u ≤ 0 := by
  rw [harmonicMapFlowSpecPrincipal_apply]
  exact neg_nonpos.mpr (harmonicMapFlowWeak_nonneg (I := I) (M := M)
    q (g t) k htie hδ_half hδ_nn hδ
    (harmonicMapFlowSpecIncl (I := I) (M := M) q S u))

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecPrincipal_lower
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      (g t).inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    (1 - δ / (1 - δ)) *
        harmonicMapFlowWeakForm (I := I) (M := M) q q
          (harmonicMapFlowSpecIncl (I := I) (M := M) q S u)
          (harmonicMapFlowSpecIncl (I := I) (M := M) q S u) ≤
      C.toReal *
        (-harmonicMapFlowSpecPrincipal (I := I) (M := M) q g S t u u) := by
  simpa only [harmonicMapFlowSpecPrincipal_apply, neg_neg] using
    (harmonicMapFlowForm_self_rev (I := I) (M := M) q (g t) C hC0 hCtop hvol
      k htie hδ_half hδ_nn hδ
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S u))

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpecLow_zero
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) :
    harmonicMapFlowSpecLow (I := I) (M := M) q g S t 0 =
      harmonicMapFlowSpecResid (I := I) (M := M) q g S t 0 := by
  simp only [harmonicMapFlowSpecLow, harmonicMapFlowSpecPrincipal_zero, sub_zero]

noncomputable def harmonicMapFlowSpecResidR
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  harmonicMapFlowSpecResid (I := I) (M := M) q g S t (ballRetraction R u)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecResidR_eq
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    {R : ℝ} (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S})
    (hu : ‖u‖ ≤ R) :
    harmonicMapFlowSpecResidR (I := I) (M := M) q g S R t u =
      harmonicMapFlowSpecResid (I := I) (M := M) q g S t u := by
  rw [harmonicMapFlowSpecResidR, ballRetraction_eq_self_of_mem hu]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecRes_data
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    {T R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn
      (Function.uncurry (harmonicMapFlowSpecResid (I := I) (M := M) q g S))
      (Icc (0 : ℝ) T ×ˢ
        Metric.closedBall
          (0 : EuclideanSpace ℝ {i // i ∈ S}) R))
    (hD : ContinuousOn
      (fun p : ℝ × EuclideanSpace ℝ {i // i ∈ S} =>
        fderiv ℝ (harmonicMapFlowSpecResid (I := I) (M := M) q g S p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ
        Metric.closedBall
          (0 : EuclideanSpace ℝ {i // i ∈ S}) R))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ {i // i ∈ S}) R,
        DifferentiableAt ℝ
          (harmonicMapFlowSpecResid (I := I) (M := M) q g S t) u) :
    ∃ A : ℝ, ∃ L : ℝ≥0, 0 ≤ A ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        LipschitzWith L
          (harmonicMapFlowSpecResidR (I := I) (M := M) q g S R t)) ∧
      (∀ u : EuclideanSpace ℝ {i // i ∈ S},
        ContinuousOn
          (fun t => harmonicMapFlowSpecResidR (I := I) (M := M) q g S R t u)
          (Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        ∀ u : EuclideanSpace ℝ {i // i ∈ S},
          ‖harmonicMapFlowSpecResidR (I := I) (M := M) q g S R t u‖ ≤
            A + (L : ℝ) * ‖u‖) := by
  with_unfolding_all
    exact retractResid_data
      (F := harmonicMapFlowSpecResid (I := I) (M := M) q g S) hR hF hD hdiff

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
