import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelMetricConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private def fixedDomainImage (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) : Opens N :=
  ⟨e '' (U : Set M), e.toHomeomorph.isOpenMap U U.isOpen⟩

private def fixedDomainDiffeomorph (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) :
    U ≃ₘ⟮I, J⟯ fixedDomainImage e U :=
  DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo e.toPartialDiffeomorph
    (Set.subset_univ (U : Set M))

def fixedDomainPullbackMetric (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) (W : Opens N)
    (hU : e '' (U : Set M) ⊆ W) (g : SmoothRiemannianMetric J W) :
    SmoothRiemannianMetric I U :=
  Diffeomorph.pullbackMetricCross
    (g.restrictOpenOfSubset (I := J) (V := fixedDomainImage e U) hU)
    (fixedDomainDiffeomorph e U)

omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace F] [SigmaCompactSpace N] in
theorem fixedDomainPullbackMetric_inner
    (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) (W : Opens N)
    (hU : e '' (U : Set M) ⊆ W) (g : SmoothRiemannianMetric J W)
    (x : U) (v w : TangentSpace I x) :
    (fixedDomainPullbackMetric e U W hU g).inner x v w =
      g.inner ⟨e x, hU ⟨x, x.2, rfl⟩⟩
        (mfderiv I J e (x : M) v) (mfderiv I J e (x : M) w) := by
  have hd (a : TangentSpace I x) :
      mfderiv I J (fixedDomainDiffeomorph e U) x a = mfderiv I J e (x : M) a :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      e.toPartialDiffeomorph (Set.subset_univ (U : Set M)) x a
  have hpull := Diffeomorph.pullbackMetricCross_inner
    (g.restrictOpenOfSubset (I := J) (V := fixedDomainImage e U) hU)
    (fixedDomainDiffeomorph e U) x v w
  have hrestrict := SmoothRiemannianMetric.restrictSubset_inner g hU
    (fixedDomainDiffeomorph e U x)
    (mfderiv I J (fixedDomainDiffeomorph e U) x v)
    (mfderiv I J (fixedDomainDiffeomorph e U) x w)
  exact (hpull.trans hrestrict).trans (congrArg₂
    (fun V Z : F => g.inner ⟨e x, hU ⟨x, x.2, rfl⟩⟩ V Z) (hd v) (hd w))

omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace F] [SigmaCompactSpace N] in
theorem fixedDomainPullbackMetric_restrict
    (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) (W : Opens N)
    (hU : e '' (U : Set M) ⊆ W) (g : SmoothRiemannianMetric J N) :
    fixedDomainPullbackMetric e U W hU (g.restrictOpen (I := J) W) =
      (Diffeomorph.pullbackMetricCross g e).restrictOpen (I := I) U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hleft := (fixedDomainPullbackMetric_inner e U W hU
    (g.restrictOpen (I := J) W) x v w).trans
      (SmoothRiemannianMetric.restrictOpen_inner g W ⟨e x, hU ⟨x, x.2, rfl⟩⟩
        (mfderiv I J e (x : M) v) (mfderiv I J e (x : M) w))
  have hright := (SmoothRiemannianMetric.restrictOpen_inner
    (Diffeomorph.pullbackMetricCross g e) U x v w).trans
      (Diffeomorph.pullbackMetricCross_inner g e (x : M) v w)
  exact hleft.trans hright.symm

theorem metricDerivNorm_fixedDomainPullback
    (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) (W : Opens N)
    (hU : e '' (U : Set M) ⊆ W) (gk gInf gRef : SmoothRiemannianMetric J W)
    (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a (fixedDomainPullbackMetric e U W hU gk)
        (fixedDomainPullbackMetric e U W hU gInf)
        (fixedDomainPullbackMetric e U W hU gRef) x =
      metricDerivNorm (I := J) a gk gInf gRef ⟨e x, hU ⟨x, x.2, rfl⟩⟩ := by
  let V := fixedDomainImage e U
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen J W.isOpen)
  let _ : IsManifold I 1 U := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 U := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I ((∞ : WithTop ℕ∞) + 1) U := by
    simpa using (inferInstance : IsManifold I ∞ U)
  let _ : IsManifold J 1 V := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 2 V := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J ((∞ : WithTop ℕ∞) + 1) V := by
    simpa using (inferInstance : IsManifold J ∞ V)
  change metricDerivNorm (I := I) a
      (Diffeomorph.pullbackMetricCross (gk.restrictOpenOfSubset (I := J) hU)
        (fixedDomainDiffeomorph e U))
      (Diffeomorph.pullbackMetricCross (gInf.restrictOpenOfSubset (I := J) hU)
        (fixedDomainDiffeomorph e U))
      (Diffeomorph.pullbackMetricCross (gRef.restrictOpenOfSubset (I := J) hU)
        (fixedDomainDiffeomorph e U)) x = _
  rw [metricDerivNorm_pullbackCross]
  exact metricDerivNorm_flat (I := J) (U := W) (V := V) hU
    gk gInf gRef a (fixedDomainDiffeomorph e U x)

theorem metricDerivNormSupOn_fixedDomainPullback
    (e : M ≃ₘ⟮I, J⟯ N) (U : Opens M) (W : Opens N)
    (hU : e '' (U : Set M) ⊆ W) (gk gInf gRef : SmoothRiemannianMetric J W)
    (K : Set U) (p : ℕ) :
    metricDerivNormSupOn (I := I) K p (fixedDomainPullbackMetric e U W hU gk)
        (fixedDomainPullbackMetric e U W hU gInf)
        (fixedDomainPullbackMetric e U W hU gRef) =
      metricDerivNormSupOn (I := J)
        ((fun x : U => (⟨e x, hU ⟨x, x.2, rfl⟩⟩ : W)) '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨a, ha, x, hx, hr⟩
    refine ⟨a, ha, ⟨e x, hU ⟨x, x.2, rfl⟩⟩, ⟨x, hx, rfl⟩, ?_⟩
    rw [← metricDerivNorm_fixedDomainPullback e U W hU gk gInf gRef a x]
    exact hr
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, hr⟩
    refine ⟨a, ha, x, hx, ?_⟩
    rw [metricDerivNorm_fixedDomainPullback]
    exact hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
