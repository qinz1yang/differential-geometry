import DifferentialGeometry.Analysis.Parabolic.HarmonicMapHeatFlow.MapRegularity
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.RankZeroInner
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowSpecPush_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmap : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (3 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)))
    (B : ∀ x : M, TangentSpace I x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M ↦ (TotalSpace.mk' E x (B x) : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
      (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E
          (harmonicMapFlowAdd (I := I) (M := M) q
            (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2)
          (mfderiv I I
            (harmonicMapFlowAdd (I := I) (M := M) q
              (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2 (B p.2)) :
          TangentBundle I M))
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  intro p hp
  let D : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    Metric.ball 0 R ×ˢ (Set.univ : Set M)
  let f : (EuclideanSpace ℝ {i // i ∈ S} × M) → M → M :=
    fun z y ↦ harmonicMapFlowAdd (I := I) (M := M) q
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S z.1) y
  have hpD : p ∈ D := hp
  have hf : ContMDiffWithinAt
      ((𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I).prod I) I (3 : ℕ∞)
      (Function.uncurry f) (D ×ˢ (Set.univ : Set M)) (p, p.2) := by
    have hpre : ContMDiffWithinAt
        ((𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I).prod I)
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (3 : ℕ∞)
        (fun z : (EuclideanSpace ℝ {i // i ∈ S} × M) × M ↦ (z.1.1, z.2))
        (D ×ˢ (Set.univ : Set M)) (p, p.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : MapsTo
        (fun z : (EuclideanSpace ℝ {i // i ∈ S} × M) × M ↦ (z.1.1, z.2))
        (D ×ˢ (Set.univ : Set M)) D := by
      rintro ⟨z, y⟩ ⟨hz, -⟩
      exact ⟨hz.1, Set.mem_univ y⟩
    exact (hmap p hp).comp (p, p.2) hpre hmaps
  have hg : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2) D p :=
    contMDiffWithinAt_snd
  have hu : MapsTo
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2) D
      (Set.univ : Set M) := fun _ _ ↦ Set.mem_univ _
  have hφ := ContMDiffWithinAt.mfderivWithin
    (I := I) (I' := I) (n := (3 : ℕ∞)) (m := (2 : ℕ∞))
    (f := f) (g := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2)
    (t := D) (u := (Set.univ : Set M)) (x₀ := p)
    hf hg hpD hu (by norm_num) uniqueMDiffOn_univ
  have hv0 : ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E z.2 (B z.2) : TangentBundle I M)) :=
    hB.comp contMDiff_snd
  have hv : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod 𝓘(ℝ, E))
      (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E z.2 (B z.2) : TangentBundle I M)) D p :=
    (hv0.of_le
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)).contMDiffAt.contMDiffWithinAt
  have hb₂ : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f z z.2) D p :=
    (hmap.of_le (by norm_num)) p hp
  have hkey := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := I) (F₁ := E) (F₂ := E)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (b₁ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2)
    (b₂ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f z z.2)
    (ϕ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
      mfderiv I I (f z) z.2)
    (v := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ B z.2)
    (m₀ := p) (s := D) (n := (2 : ℕ∞))
    ?_ hv hb₂
  · convert hkey using 2
  · have hrw :
        (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M))
            E (TangentSpace I (M := M))
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2) p)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2) z)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2) p)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2) z)
            (mfderiv I I (f z) z.2)) =
          (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
            inTangentCoordinates I I
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2)
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2)
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦
                mfderivWithin I I (f w) (Set.univ : Set M) w.2) p z) := by
      funext z
      unfold inTangentCoordinates
      congr 1
      exact (congrFun
        (mfderivWithin_univ (I := I) (I' := I) (f := f z)) z.2).symm
    rw [hrw]
    exact hφ

omit [CompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
omit [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
omit [I.Boundaryless] in
private theorem harmonicMapFlowRaisedFrame_cd
    (q h : SmoothRiemannianMetric I M)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M ↦ (TotalSpace.mk' E x
        (metricComparisonEndomorphism (I := I) q h x
          (smoothOrthoFrame (I := I) q x₀ i x)) : TangentBundle I M)) := by
  with_unfolding_all
    exact ContMDiff.clm_bundle_apply
      (b := id)
      (metricComparisonEndomorphismField (I := I) (M := M) q h).contMDiff_toFun
      (smoothOrthoFrame_smooth (I := I) q x₀ i)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowSpecFrozen_cd
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmap : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (3 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)))
    (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ)
      (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (1 / 2 : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            q.inner
              (harmonicMapFlowAdd (I := I) (M := M) q
                (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2)
              (mfderiv I I
                (harmonicMapFlowAdd (I := I) (M := M) q
                  (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2
                (metricComparisonEndomorphism (I := I) q h p.2
                  (smoothOrthoFrame (I := I) q x₀ i p.2)))
              (mfderiv I I
                (harmonicMapFlowAdd (I := I) (M := M) q
                  (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2
                (smoothOrthoFrame (I := I) q x₀ i p.2)))
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  classical
  let D : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    Metric.ball 0 R ×ˢ (Set.univ : Set M)
  let F : EuclideanSpace ℝ {i // i ∈ S} × M → M :=
    fun p ↦ harmonicMapFlowAdd (I := I) (M := M) q
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2
  have hmetric : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M ↦
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (F p) (q.inner (F p))) D := by
    with_unfolding_all
      exact (q.contMDiff.of_le
        (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)).comp_contMDiffOn
        (hmap.of_le (by norm_num))
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {j // j ∈ S}).prod I) 𝓘(ℝ)
        (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {j // j ∈ S} × M ↦
          q.inner (F p)
            (mfderiv I I
              (harmonicMapFlowAdd (I := I) (M := M) q
                (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2
              (metricComparisonEndomorphism (I := I) q h p.2
                (smoothOrthoFrame (I := I) q x₀ i p.2)))
            (mfderiv I I
              (harmonicMapFlowAdd (I := I) (M := M) q
                (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2
              (smoothOrthoFrame (I := I) q x₀ i p.2))) D := by
    intro i
    have hframe : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M ↦ (TotalSpace.mk' E x
          (smoothOrthoFrame (I := I) q x₀ i x) : TangentBundle I M)) :=
      smoothOrthoFrame_smooth (I := I) q x₀ i
    have hraised := harmonicMapFlowRaisedFrame_cd (I := I) (M := M) q h x₀ i
    have hpush := harmonicMapFlowSpecPush_cd (I := I) (M := M) q S R hmap
      (fun x : M ↦ smoothOrthoFrame (I := I) q x₀ i x) hframe
    have hpushRaised := harmonicMapFlowSpecPush_cd (I := I) (M := M) q S R hmap
      (fun x : M ↦ metricComparisonEndomorphism (I := I) q h x
        (smoothOrthoFrame (I := I) q x₀ i x))
      hraised
    have happ := ContMDiffOn.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun y : M ↦ TangentSpace I y)
      (E₂ := fun y : M ↦ TangentSpace I y)
      (E₃ := fun _ : M ↦ ℝ)
      (b := F) hmetric hpushRaised hpush
    intro p hp
    have hat := happ p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hat
    exact hat.2
  intro p hp
  have hc : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ) (2 : ℕ∞)
      (fun _ : EuclideanSpace ℝ {i // i ∈ S} × M ↦ (1 / 2 : ℝ)) D p :=
    contMDiffWithinAt_const
  exact hc.mul (ContMDiffWithinAt.sum (fun i _ ↦ hterm i p hp))

omit [I.Boundaryless] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M] [SigmaCompactSpace M] in
private theorem harmonicMapFlowDens_eq_frozen
    (q h : SmoothRiemannianMetric I M) (Φ : M → M)
    (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    harmonicMapFlowDirDensity (I := I) (M := M) q h Φ y =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          q.inner (Φ y)
            (mfderiv I I Φ y
              (metricComparisonEndomorphism (I := I) q h y
                (smoothOrthoFrame (I := I) q x₀ i y)))
            (mfderiv I I Φ y
              (smoothOrthoFrame (I := I) q x₀ i y)) := by
  classical
  let dΦ : TangentSpace I y →L[ℝ] TangentSpace I (Φ y) := mfderiv I I Φ y
  let A : TangentSpace I y →L[ℝ] TangentSpace I y :=
    metricComparisonEndomorphism (I := I) q h y
  let step₁ : TangentSpace I y →L[ℝ] TangentSpace I (Φ y) →L[ℝ] ℝ :=
    (q.inner (Φ y)).comp (dΦ.comp A)
  let precomp : (TangentSpace I (Φ y) →L[ℝ] ℝ) →L[ℝ]
      (TangentSpace I y →L[ℝ] ℝ) := ContinuousLinearMap.precomp ℝ dΦ
  let Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    precomp.comp step₁
  have hmove := orthonormal_basis_bilin_trace (I := I) (M := M) q y Hb
    (fun i ↦ smoothOrthoFrame (I := I) q y i y)
    (fun i j ↦ smoothOrthoFrame_orthonormal_at_center (I := I) q y i j)
  have hfixed := orthonormal_basis_bilin_trace (I := I) (M := M) q y Hb
    (fun i ↦ smoothOrthoFrame (I := I) q x₀ i y)
    (fun i j ↦ smoothOrthoFrame_orthonormal (I := I) q x₀ hy i j)
  unfold harmonicMapFlowDirDensity
  exact congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z) (by
    simpa only [Hb, precomp, step₁, dΦ, A, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply] using hmove.trans hfixed.symm)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpecDens_cd
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ)
        (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          harmonicMapFlowDirDensity (I := I) (M := M) q h
            (harmonicMapFlowAdd (I := I) (M := M) q
              (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1)) p.2)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hmap⟩ := harmonicMapFlowSpecMap_cd (I := I) (M := M) q S 3
  refine ⟨R, hR, ?_⟩
  intro p hp
  have hmap' : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (3 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpecIncl (I := I) (M := M) q S z.1) z.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
    intro z hz
    have hfun :
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          harmonicMapFlowSpecMap (I := I) (M := M) q S p.2 p.1) =
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          harmonicMapFlowAdd (I := I) (M := M) q
            (harmonicMapFlowSpecIncl (I := I) (M := M) q S p.1) p.2) := by
      funext p
      exact harmonicMapFlowSpecMap_apply (I := I) (M := M) q S p.2 p.1
    rw [← hfun]
    exact hmap z hz
  have hfrozen := harmonicMapFlowSpecFrozen_cd (I := I) (M := M) q h S R hmap' p.2 p hp
  refine hfrozen.congr_of_eventuallyEq_of_mem ?_ hp
  have hnbhd : ∀ᶠ z : EuclideanSpace ℝ {i // i ∈ S} × M in
      𝓝[Metric.ball 0 R ×ˢ (Set.univ : Set M)] p,
      z.2 ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) p.2 := by
    apply Filter.Eventually.filter_mono inf_le_left
    exact continuousAt_snd.eventually
      (smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) p.2)
  filter_upwards [hnbhd] with z hz
  exact harmonicMapFlowDens_eq_frozen (I := I) (M := M) q h
    (harmonicMapFlowAdd (I := I) (M := M) q
      (harmonicMapFlowSpecIncl (I := I) (M := M) q S z.1)) p.2 hz

omit [BoundarylessManifold I M]
  [ConnectedSpace M] in
theorem harmonicMapFlowSpecCoeff_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (v : EuclideanSpace ℝ {i // i ∈ S}) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
        (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          (TotalSpace.mk' E
            (harmonicMapFlowSpecMap (I := I) (M := M) q S p.2 p.1)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
              (harmonicMapFlowSpecMap (I := I) (M := M) q S p.2)
              p.1
              ((tangentSpaceModelContinuousLinearEquiv
                (I := 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}))
                p.1).symm.toContinuousLinearMap v)) :
            TangentBundle I M))
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hmap⟩ :=
    harmonicMapFlowSpecMap_cd (I := I) (M := M) q S 3
  refine ⟨R, hR, ?_⟩
  intro p hp
  let V := EuclideanSpace ℝ {i // i ∈ S}
  let IV : ModelWithCorners ℝ V V := 𝓘(ℝ, V)
  let F : V × M → M := fun z ↦
    harmonicMapFlowSpecMap (I := I) (M := M) q S z.2 z.1
  let f : (V × M) → V → M := fun z =>
    harmonicMapFlowSpecMap (I := I) (M := M) q S z.2
  have hopen : IsOpen (Metric.ball (0 : V) R ×ˢ (Set.univ : Set M)) :=
    Metric.isOpen_ball.prod isOpen_univ
  have hmapAt : ContMDiffAt (𝓘(ℝ, V).prod I) I (3 : ℕ∞) F p := by
    exact (hmap p hp).contMDiffAt (hopen.mem_nhds hp)
  have hf : ContMDiffAt ((𝓘(ℝ, V).prod I).prod 𝓘(ℝ, V)) I (3 : ℕ∞)
      (Function.uncurry f) (p, p.1) := by
    have hpre : ContMDiffAt ((𝓘(ℝ, V).prod I).prod 𝓘(ℝ, V))
        (𝓘(ℝ, V).prod I) (3 : ℕ∞)
        (fun z : (V × M) × V ↦ (z.2, z.1.2)) (p, p.1) :=
      contMDiffAt_snd.prodMk (contMDiffAt_fst.snd)
    with_unfolding_all
      exact hmapAt.comp (p, p.1) hpre
  have hg : ContMDiffAt (𝓘(ℝ, V).prod I) 𝓘(ℝ, V) (2 : ℕ∞)
      (fun z : V × M ↦ z.1) p := contMDiffAt_fst
  have hφ := ContMDiffAt.mfderiv
    (I := IV) (I' := I) (n := (3 : ℕ∞)) (m := (2 : ℕ∞))
    (f := f) (g := fun z : V × M ↦ z.1) hf hg (by norm_num)
  have hv0 : ContMDiff IV (IV.tangent) ∞
      (fun u : V ↦ (TotalSpace.mk' V u v : TangentBundle IV V)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : V ↦ v)).mpr
      contDiff_const
  have hv : ContMDiffAt (𝓘(ℝ, V).prod I)
      (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (2 : ℕ∞)
      (fun z : V × M ↦
        (TotalSpace.mk' V z.1 v : TangentBundle IV V)) p := by
    exact (hv0.of_le
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)).contMDiffAt.comp
      p contMDiffAt_fst
  have hb₂ : ContMDiffAt (𝓘(ℝ, V).prod I) I (2 : ℕ∞) F p :=
    hmapAt.of_le (by norm_num)
  have hkey := ContMDiffAt.clm_apply_of_inCoordinates
    (IB₁ := IV) (IB₂ := I) (F₁ := V) (F₂ := E)
    (E₁ := TangentSpace IV (M := V))
    (E₂ := TangentSpace I (M := M))
    (b₁ := fun z : V × M ↦ z.1) (b₂ := F)
    (ϕ := fun z : V × M ↦ mfderiv IV I (f z) z.1)
    (v := fun _ : V × M ↦ v) (m₀ := p) (n := (2 : ℕ∞))
    ?_ hv hb₂
  · with_unfolding_all
      exact hkey.contMDiffWithinAt
  · have hrw :
        (fun z : V × M ↦
          ContinuousLinearMap.inCoordinates V (TangentSpace IV (M := V))
            E (TangentSpace I (M := M))
            ((fun w : V × M ↦ w.1) p) ((fun w : V × M ↦ w.1) z)
            (F p) (F z) (mfderiv IV I (f z) z.1)) =
          (fun z : V × M ↦
            inTangentCoordinates IV I (fun w : V × M ↦ w.1)
              (fun w : V × M ↦ f w w.1)
              (fun w : V × M ↦ mfderiv IV I (f w) w.1) p z) := by
      with_unfolding_all
        rfl
    rw [hrw]
    exact hφ

noncomputable def harmonicMapFlowStateVar
    (q : SmoothRiemannianMetric I M)
    (S U : SmoothCcTensor q 0 1) (x : M) :
    TangentSpace I (harmonicMapFlowAdd (I := I) (M := M) q S x) :=
  mfderiv 𝓘(ℝ) I
    (fun a : ℝ ↦ harmonicMapFlowAdd (I := I) (M := M) q (S + a • U) x) 0 1

noncomputable def harmonicMapFlowStateMass
    (q h : SmoothRiemannianMetric I M)
    (S U V : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, q.inner (harmonicMapFlowAdd (I := I) (M := M) q S x)
      (harmonicMapFlowStateVar (I := I) (M := M) q S U x)
      (harmonicMapFlowStateVar (I := I) (M := M) q S V x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

private noncomputable def harmonicMapFlowFiberExp
    (q : SmoothRiemannianMetric I M) (x : M) : E → M :=
  fun v : E ↦
    (harmonicMapFlowDiagExp (I := I) (M := M) q
      (⟨x, (show TangentSpace I x from v)⟩ : TangentBundle I M)).2

omit [BoundarylessManifold I M] [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem harmonicMapFlowFiberExp_mfd
    (q : SmoothRiemannianMetric I M) (x : M) :
    mfderiv 𝓘(ℝ, E) I (harmonicMapFlowFiberExp (I := I) (M := M) q x) 0 =
      ContinuousLinearMap.id ℝ E := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨q.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun y : M ↦ TangentSpace I y) :=
    ⟨q.inner, q.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : PseudoEMetricSpace M :=
    PseudoEMetricSpace.ofRiemannianMetric I M
  have hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (q.inner y v v)) := by
    intro y v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  with_unfolding_all
    exact mfderiv_expMapIntrinsic_at_zero (I := I) q hEnorm x

omit [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowFiberExp_md
    (q : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt 𝓘(ℝ, E) I
      (harmonicMapFlowFiberExp (I := I) (M := M) q x) 0 := by
  have : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  by_contra hnot
  have hzero := harmonicMapFlowFiberExp_mfd (I := I) (M := M) q x
  rw [mfderiv_zero_of_not_mdifferentiableAt hnot] at hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv' : (0 : E) = v := by
    with_unfolding_all
      exact DFunLike.congr_fun hzero v
  exact hv hv'.symm

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowStateVar_zero
    (q : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor q 0 1) (x : M) :
    harmonicMapFlowStateVar (I := I) (M := M) q 0 U x =
      harmonicMapFlowUnknown (I := I) q U x := by
  let w : E := harmonicMapFlowUnknown (I := I) q U x
  let line : ℝ → E := fun a : ℝ ↦ a • w
  have hpath :
      (fun a : ℝ ↦ harmonicMapFlowAdd (I := I) (M := M) q
        ((0 : SmoothCcTensor q 0 1) + a • U) x) =
        harmonicMapFlowFiberExp (I := I) (M := M) q x ∘ line := by
    funext a
    simp only [zero_add, Function.comp_apply, line, w, harmonicMapFlowFiberExp,
      harmonicMapFlowAdd, harmonicMapFlowUnknown_smul]
    rfl
  have hline_md : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) line 0 := by
    have hMD : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ line := by
      with_unfolding_all
        exact contMDiff_id.smul contMDiff_const
    exact hMD.contMDiffAt.mdifferentiableAt (by decide)
  have hline : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt line
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      with_unfolding_all
        exact (hasFDerivAt_id (0 : ℝ)).smul_const w
    rw [h.fderiv]
    change (1 : ℝ) • w = w
    exact one_smul ℝ w
  have hline_zero : line 0 = 0 := by
    simp only [line, zero_smul]
  have houter : MDifferentiableAt 𝓘(ℝ, E) I
      (harmonicMapFlowFiberExp (I := I) (M := M) q x) (line 0) := by
    simpa only [line, zero_smul] using
      harmonicMapFlowFiberExp_md (I := I) (M := M) q x
  unfold harmonicMapFlowStateVar
  rw [hpath]
  have hcomp := mfderiv_comp_apply (f := line) (x := (0 : ℝ))
    houter hline_md (1 : ℝ)
  have hgoal :
      mfderiv 𝓘(ℝ, E) I
          (harmonicMapFlowFiberExp (I := I) (M := M) q x) (line 0)
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ)) =
        harmonicMapFlowUnknown (I := I) q U x := by
    rw [hline]
    rw [hline_zero]
    have hmfd := DFunLike.congr_fun
      (harmonicMapFlowFiberExp_mfd (I := I) (M := M) q x) w
    with_unfolding_all
      exact hmfd
  exact hcomp.trans hgoal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowUnitLift
    (q : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor q 0 1) (x : M) :
    Tensor0SSpace.toRS0
        (unitEvalSection (I := I) (M := M) q 1 S x) =
      S.toSection x := by
  apply tensorRSSpace_ext (I := I) (M := M) 0 1 x
  intro c
  have hc : c = (tensor0SSpaceEvalScalar
      (𝕜 := ℝ) (I := I) (M := M) x) c •
      unitZeroSec (I := I) (M := M) x := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    change Tensor0SSpace.toModel c v =
      Tensor0SSpace.toModel
        ((tensor0SSpaceEvalScalar
          (𝕜 := ℝ) (I := I) (M := M) x) c •
          unitZeroSec (I := I) (M := M) x) v
    rw [Tensor0SSpace.toModel_smul,
      smul_apply, unitZeroSec_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply, smul_eq_mul,
      Tensor0SSpace.evalScalar_apply, mul_one]
    exact congrArg (Tensor0SSpace.toModel c)
      (Subsingleton.elim v Fin.elim0)
  change (tensor0SSpaceEvalScalar
      (𝕜 := ℝ) (I := I) (M := M) x) c •
      unitEvalSection (I := I) (M := M) q 1 S x =
    (S.toSection x) c
  rw [unitEvalSection_apply]
  calc
    (tensor0SSpaceEvalScalar
        (𝕜 := ℝ) (I := I) (M := M) x) c •
          (S.toSection x) (unitZeroSec (I := I) (M := M) x) =
        (S.toSection x)
          ((tensor0SSpaceEvalScalar
            (𝕜 := ℝ) (I := I) (M := M) x) c •
            unitZeroSec (I := I) (M := M) x) := by
      rw [map_smul]
    _ = (S.toSection x) c := congrArg (S.toSection x) hc.symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowChartInv
    (q : SmoothRiemannianMetric I M) (x : M) :
    MetricInverseInBasis (I := I) q x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
      (fun i j ↦ (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j) := by
  classical
  have hdet : IsUnit (gramMatrixAt (I := I) (M := M) q x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (gramMatrixAt_isUnit (I := I) (M := M) q x)
  intro i j
  constructor
  · have hij := congrFun (congrFun
      (gramMatrixAt_inv_mul_self (I := I) (M := M) q x) i) j
    with_unfolding_all
      exact hij
  · have hmul : gramMatrixAt (I := I) (M := M) q x *
        (gramMatrixAt (I := I) (M := M) q x)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hdet
    have hij := congrFun (congrFun hmul i) j
    with_unfolding_all
      exact hij

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowCovInner
    (q : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    q.inner x
        (inverseMetricSharpFib (I := I) q x α)
        (inverseMetricSharpFib (I := I) q x β) =
      covariantTensorInnerPointwise (I := I) (M := M) 1 q x
        (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) := by
  classical
  have hsharp : ∀ γ : Tensor0SSpace 1 I x,
      inverseMetricSharpFib (I := I) q x γ =
        cotangentSharp (I := I) q x γ := by
    intro γ
    apply metricFlatLinear_injective (I := I) q x
    ext w
    change q.inner x (inverseMetricSharpFib (I := I) q x γ) w =
      q.inner x (cotangentSharp (I := I) q x γ) w
    rw [inverseMetricSharpFib_inner, cotangentSharp_inner,
      cotangentToDualLinear_apply]
  have hcoord := cotangentInner_eq_coord (I := I) q x
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
    (fun i j ↦ (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j)
    (harmonicMapFlowChartInv (I := I) (M := M) q x) α β
  have htensor :
      covariantTensorInnerPointwise (I := I) (M := M) 1 q x
          (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j *
              cotangentToDual (I := I) α ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) *
                cotangentToDual (I := I) β ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
    rw [tensorInnerPointwise_0s_succ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorInnerPointwise_0s_zero_arity]
    have hα :
        ((Tensor0SSpace.toModel α).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (fun k : Fin 0 ↦ Fin.elim0 k) =
          cotangentToDual (I := I) α ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
      rw [ContinuousMultilinearMap.curryLeft_apply,
        Tensor0SSpace.toModel_apply_model_vector]
      let X : TangentSpace I x :=
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
      have hvec :
          (fun k : Fin 1 =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (@Fin.cons 0 (fun _ : Fin 1 => E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                (fun k : Fin 0 => Fin.elim0 k) k)) =
            fun _ : Fin 1 => X := by
        funext k
        fin_cases k
        rfl
      rw [hvec]
      calc
        α (fun _ : Fin 1 => X) = cotangentToDual (I := I) α X :=
          (cotangentToDual_apply (I := I) α X).symm
        _ = cotangentToDual (I := I) α ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
          with_unfolding_all
            rfl
    have hβ :
        ((Tensor0SSpace.toModel β).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
            (fun k : Fin 0 ↦ Fin.elim0 k) =
          cotangentToDual (I := I) β ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
      rw [ContinuousMultilinearMap.curryLeft_apply,
        Tensor0SSpace.toModel_apply_model_vector]
      let X : TangentSpace I x :=
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
      have hvec :
          (fun k : Fin 1 =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (@Fin.cons 0 (fun _ : Fin 1 => E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
                (fun k : Fin 0 => Fin.elim0 k) k)) =
            fun _ : Fin 1 => X := by
        funext k
        fin_cases k
        rfl
      rw [hvec]
      calc
        β (fun _ : Fin 1 => X) = cotangentToDual (I := I) β X :=
          (cotangentToDual_apply (I := I) β X).symm
        _ = cotangentToDual (I := I) β ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
          with_unfolding_all
            rfl
    rw [hα, hβ]
    ring
  calc
    q.inner x
        (inverseMetricSharpFib (I := I) q x α)
        (inverseMetricSharpFib (I := I) q x β) =
        cotangentInner (I := I) q x α β := by
      rw [hsharp α, hsharp β]
      rfl
    _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j *
              cotangentToDual (I := I) α ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) *
                cotangentToDual (I := I) β ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := hcoord
    _ = covariantTensorInnerPointwise (I := I) (M := M) 1 q x
          (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) := htensor.symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem harmonicMapFlowMassPt
    (q : SmoothRiemannianMetric I M)
    (U V : SmoothCcTensor q 0 1) (x : M) :
    q.inner x (harmonicMapFlowUnknown (I := I) q U x)
        (harmonicMapFlowUnknown (I := I) q V x) =
      tensorInnerPointwise (I := I) (M := M) q 0 1 x
        (U.toFun x) (V.toFun x) := by
  let α : Tensor0SSpace 1 I x :=
    unitEvalSection (I := I) (M := M) q 1 U x
  let β : Tensor0SSpace 1 I x :=
    unitEvalSection (I := I) (M := M) q 1 V x
  have hU : U.toFun x = TensorRSSpace.toModel
      (Tensor0SSpace.toRS0 α) := by
    rw [SmoothCcTensor.toFun_apply,
      harmonicMapFlowUnitLift (I := I) (M := M) q U x]
  have hV : V.toFun x = TensorRSSpace.toModel
      (Tensor0SSpace.toRS0 β) := by
    rw [SmoothCcTensor.toFun_apply,
      harmonicMapFlowUnitLift (I := I) (M := M) q V x]
  unfold harmonicMapFlowUnknown
  change q.inner x
      (inverseMetricSharpFib (I := I) q x α)
      (inverseMetricSharpFib (I := I) q x β) = _
  rw [hU, hV, inner_toRS0]
  exact harmonicMapFlowCovInner (I := I) (M := M) q x α β

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowStateMass_zero_eq
    (q h : SmoothRiemannianMetric I M)
    (U V : SmoothCcTensor q 0 1) :
    harmonicMapFlowStateMass (I := I) (M := M) q h 0 U V =
      harmonicMapFlowMass (I := I) (M := M) q h U V := by
  unfold harmonicMapFlowStateMass harmonicMapFlowMass
  rw [harmonicMapFlowAdd_zero]
  simp only [id_eq, harmonicMapFlowStateVar_zero]
  apply integral_congr_ae
  filter_upwards with x
  exact harmonicMapFlowMassPt (I := I) (M := M) q U V x

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
