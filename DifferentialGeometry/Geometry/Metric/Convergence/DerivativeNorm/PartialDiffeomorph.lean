import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem metricDerivNorm_restrict_open
    (A B gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a (A.restrictOpen U) (B.restrictOpen U)
      (gRef.restrictOpen U) x = metricDerivNorm (I := I) a A B gRef (x : M) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 1 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold I 2 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  have hcov (g : SmoothRiemannianMetric I M) :
      metricCovDeriv (I := I) (g.restrictOpen U) (gRef.restrictOpen U) a x =
        metricCovDeriv (I := I) g gRef a (x : M) := by
    ext slots
    rw [metricCovDeriv_eq_covDerivOfField, metricCovDeriv_eq_covDerivOfField]
    exact covDerivOfField_restrictOpen (I := I) gRef U
      (Tensor0SBundle.metricTensorField (I := I) (g.restrictOpen U))
      (Tensor0SBundle.metricTensorField (I := I) g)
      (by intro y v; rfl) a x slots
  have hdiff : metricDiffCovDerivAt (I := I) a (A.restrictOpen U) (B.restrictOpen U)
      (gRef.restrictOpen U) x = metricDiffCovDerivAt (I := I) a A B gRef (x : M) := by
    unfold metricDiffCovDerivAt
    rw [hcov A, hcov B]
    rfl
  unfold metricDerivNorm
  rw [hdiff]
  exact congrArg Real.sqrt
    (normSq0S_restrictOpen_apply (I := I) gRef U (a + 2) x _)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem metricDerivNorm_eq_of_partialDiffeomorph_inner
    (Phi : PartialDiffeomorph I J M N ∞) {U : TopologicalSpace.Opens M}
    [SigmaCompactSpace U] (hU : (U : Set M) ⊆ Phi.source)
    (gk gInf gRef : SmoothRiemannianMetric J N)
    (Gk GInf GRef : SmoothRiemannianMetric I U)
    (hk : ∀ (y : U) (v w : TangentSpace I y),
      Gk.inner y v w = gk.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hInf : ∀ (y : U) (v w : TangentSpace I y),
      GInf.inner y v w = gInf.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hRef : ∀ (y : U) (v w : TangentSpace I y),
      GRef.inner y v w = gRef.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a Gk GInf GRef x =
      metricDerivNorm (I := J) a gk gInf gRef (Phi (x : M)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let D : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  let _ : IsManifold I 1 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold I 2 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold J 1 V := IsManifold.of_le (I := J) (M := V) (n := ∞) (by decide)
  let _ : IsManifold J 2 V := IsManifold.of_le (I := J) (M := V) (n := ∞) (by decide)
  have hmetric (A : SmoothRiemannianMetric I U) (g : SmoothRiemannianMetric J N)
      (h : ∀ (y : U) (v w : TangentSpace I y),
        A.inner y v w = g.inner (Phi (y : M))
          (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w)) :
      A = Diffeomorph.pullbackMetricCross (g.restrictOpen V) D := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    change A.inner y v w = g.inner (Phi (y : M))
      (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Phi hU) y v)
      (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Phi hU) y w)
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact h y v w
  rw [hmetric Gk gk hk, hmetric GInf gInf hInf, hmetric GRef gRef hRef]
  exact (metricDerivNorm_pullbackCross (I := I) (J := J)
    (gk.restrictOpen V) (gInf.restrictOpen V) (gRef.restrictOpen V) D a x).trans
      (metricDerivNorm_restrict_open (I := J) gk gInf gRef V a (D x))

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
open Set Filter
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [T2Space Q] [IsManifold I ∞ Q]
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]

omit [T2Space N] in
theorem metricDerivNorm_relative_pullback
    (Φ : PartialDiffeomorph I J Q M (∞ : WithTop ℕ∞))
    (Ψ : PartialDiffeomorph I J Q N (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens Q) [SigmaCompactSpace U]
    (hΦ : (U : Set Q) ⊆ Φ.source) (hΨ : (U : Set Q) ⊆ Ψ.source)
    (g : SmoothRiemannianMetric J M) (h : SmoothRiemannianMetric J N)
    (GΦ GΨ : SmoothRiemannianMetric I U)
    (hGΦ : ∀ (z : U) (v w : TangentSpace I z),
      GΦ.inner z v w = g.inner ((Φ : Q → M) z)
        (mfderiv I J (Φ : Q → M) (z : Q) v) (mfderiv I J (Φ : Q → M) (z : Q) w))
    (hGΨ : ∀ (z : U) (v w : TangentSpace I z),
      GΨ.inner z v w = h.inner ((Ψ : Q → N) z)
        (mfderiv I J (Ψ : Q → N) (z : Q) v) (mfderiv I J (Ψ : Q → N) (z : Q) w))
    (A : SmoothRiemannianMetric J M) (a : ℕ) (x : U)
    (hA : ∀ᶠ y in nhds ((Φ : Q → M) x), ∀ v w : TangentSpace J y,
      A.inner y v w = h.inner ((Φ.symm.trans Ψ) y)
        (mfderiv J J (Φ.symm.trans Ψ : M → N) y v)
        (mfderiv J J (Φ.symm.trans Ψ : M → N) y w)) :
    metricDerivNorm (I := J) a A g g ((Φ : Q → M) x) =
      metricDerivNorm (I := I) a GΨ GΦ GΦ x := by
  let W : TopologicalSpace.Opens M :=
    ⟨(Φ : Q → M) '' (U : Set Q), image_opens_isOpen Φ hΦ⟩
  let e : Diffeomorph I J U W (∞ : WithTop ℕ∞) := PartialDiffeomorph.toOpensDiffeo Φ hΦ
  let AΦ : SmoothRiemannianMetric I U := Diffeomorph.pullbackMetricCross (A.restrictOpen W) e
  have hAΦ : ∀ (z : U) (v w : TangentSpace I z),
      AΦ.inner z v w = A.inner ((Φ : Q → M) z)
        (mfderiv I J (Φ : Q → M) (z : Q) v) (mfderiv I J (Φ : Q → M) (z : Q) w) := by
    intro z v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
    rfl
  have hinner : ∀ᶠ z : U in nhds x, ∀ v w : TangentSpace I z,
      AΦ.inner z v w = GΨ.inner z v w := by
    have hc : ContinuousAt (fun z : U => (Φ : Q → M) z) x :=
      ((Φ.contMDiffOn_toFun.continuousOn.mono hΦ).continuousAt
        (U.isOpen.mem_nhds x.2)).comp continuous_subtype_val.continuousAt
    filter_upwards [hc.eventually hA] with z hz v w
    rw [hAΦ z v w, hGΨ z v w]
    have hmap : (Φ.symm.trans Ψ) ((Φ : Q → M) z) = (Ψ : Q → N) z := by
      rw [_root_.PartialDiffeomorph.trans_apply, _root_.PartialDiffeomorph.symm_apply_apply Φ (hΦ z.2)]
    have hΦd : MDifferentiableAt I J (Φ : Q → M) (z : Q) :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hΦ z.2))).mdifferentiableAt (by decide)
    have hmem : ((Φ : Q → M) z) ∈ (Φ.symm.trans Ψ).source := by
      rw [_root_.PartialDiffeomorph.trans_source]
      refine ⟨Φ.map_source (hΦ z.2), ?_⟩
      simpa only [Set.mem_preimage, _root_.PartialDiffeomorph.symm_apply_apply Φ (hΦ z.2)] using hΨ z.2
    have hFd : MDifferentiableAt J J (Φ.symm.trans Ψ : M → N) ((Φ : Q → M) z) :=
      ((Φ.symm.trans Ψ).contMDiffOn_toFun.contMDiffAt
        ((Φ.symm.trans Ψ).open_source.mem_nhds hmem)).mdifferentiableAt (by decide)
    have hcomp : (mfderiv J J (Φ.symm.trans Ψ : M → N) ((Φ : Q → M) z)).comp
          (mfderiv I J (Φ : Q → M) (z : Q)) = mfderiv I J (Ψ : Q → N) (z : Q) := by
      rw [← mfderiv_comp (z : Q) hFd hΦd]
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [Φ.open_source.mem_nhds (hΦ z.2)] with q hq
      rw [Function.comp_apply, _root_.PartialDiffeomorph.trans_apply,
        _root_.PartialDiffeomorph.symm_apply_apply Φ hq]
    rw [hz _ _]
    change h.inner ((Φ.symm.trans Ψ) ((Φ : Q → M) z))
      (((mfderiv J J (Φ.symm.trans Ψ : M → N) ((Φ : Q → M) z)).comp
        (mfderiv I J (Φ : Q → M) (z : Q))) v)
      (((mfderiv J J (Φ.symm.trans Ψ : M → N) ((Φ : Q → M) z)).comp
        (mfderiv I J (Φ : Q → M) (z : Q))) w) = _
    rw [hcomp, hmap]
  have heqnorm : metricDerivNorm (I := I) a AΦ GΦ GΦ x =
      metricDerivNorm (I := I) a GΨ GΦ GΦ x :=
    metricDerivNorm_eq_of_metric_eventuallyEq (I := I) a AΦ GΨ GΦ GΦ x hinner
  have hnorm := metricDerivNorm_eq_of_partialDiffeomorph_inner Φ hΦ A g g AΦ GΦ GΦ hAΦ hGΦ hGΦ a x
  exact hnorm.symm.trans heqnorm

end DifferentialGeometry.CheegerGromovCompactness
