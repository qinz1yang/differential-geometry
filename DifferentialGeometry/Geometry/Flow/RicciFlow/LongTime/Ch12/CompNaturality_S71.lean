import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompGeometry_S60
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

/-!
# CH12-S71 / G2: naturality of `metricDerivNorm` under the restriction of a partial diffeomorphism

`fixedDomainPullbackMetric` / `metricDerivNorm_fixedDomainPullback` (FixedDomain.lean) are stated for a
global diffeomorphism `e : M ≃ₘ N`.  Here the same statements for a `PartialDiffeomorph Φ` and an open
`U ⊆ Φ.source`, via `toOpensDiffeo Φ hU : U ≃ₘ Φ '' U` (same proof, the diffeomorphism being replaced).
Then the two pull-back identities (E1, E2) of `CompGeometry_S60` for `Φ`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

section Local

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

/-- the image `Φ '' U` as an `Opens`. -/
abbrev partialImage_S71 (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞)) (U : Opens M)
    (hU : (U : Set M) ⊆ Φ.source) : Opens N :=
  ⟨(Φ : M → N) '' (U : Set M), DifferentialGeometry.image_opens_isOpen Φ hU⟩

/-- the pull-back, under `Φ|_U`, of a metric on an open `W ⊇ Φ '' U`: a metric on `↥U`. -/
def localPullbackMetric_S71 (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞)) (U : Opens M)
    (hU : (U : Set M) ⊆ Φ.source) (W : Opens N) (hW : (Φ : M → N) '' (U : Set M) ⊆ W)
    (g : SmoothRiemannianMetric J W) : SmoothRiemannianMetric I U :=
  Diffeomorph.pullbackMetricCross
    (g.restrictOpenOfSubset (I := J) (V := partialImage_S71 Φ U hU) hW)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU)

omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace F] [SigmaCompactSpace N] in
theorem localPullbackMetric_inner_S71
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞)) (U : Opens M)
    (hU : (U : Set M) ⊆ Φ.source) (W : Opens N) (hW : (Φ : M → N) '' (U : Set M) ⊆ W)
    (g : SmoothRiemannianMetric J W) (x : U) (v w : TangentSpace I x) :
    (localPullbackMetric_S71 Φ U hU W hW g).inner x v w =
      g.inner ⟨Φ x, hW ⟨x, x.2, rfl⟩⟩
        (mfderiv I J (Φ : M → N) (x : M) v) (mfderiv I J (Φ : M → N) (x : M) w) := by
  have hd (a : TangentSpace I x) :
      mfderiv I J (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU) x a =
        mfderiv I J (Φ : M → N) (x : M) a :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU x a
  have hpull := Diffeomorph.pullbackMetricCross_inner
    (g.restrictOpenOfSubset (I := J) (V := partialImage_S71 Φ U hU) hW)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU) x v w
  have hrestrict := SmoothRiemannianMetric.restrictSubset_inner g hW
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU x)
    (mfderiv I J (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU) x v)
    (mfderiv I J (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU) x w)
  exact (hpull.trans hrestrict).trans (congrArg₂
    (fun V Z : F => g.inner ⟨Φ x, hW ⟨x, x.2, rfl⟩⟩ V Z) (hd v) (hd w))

/-- **Naturality of `metricDerivNorm` under `Φ|_U : U ≃ₘ Φ '' U`** (local version of
`metricDerivNorm_fixedDomainPullback`). -/
theorem metricDerivNorm_localPullback_S71
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞)) (U : Opens M)
    (hU : (U : Set M) ⊆ Φ.source) (W : Opens N) (hW : (Φ : M → N) '' (U : Set M) ⊆ W)
    (gk gInf gRef : SmoothRiemannianMetric J W) (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a (localPullbackMetric_S71 Φ U hU W hW gk)
        (localPullbackMetric_S71 Φ U hU W hW gInf)
        (localPullbackMetric_S71 Φ U hU W hW gRef) x =
      metricDerivNorm (I := J) a gk gInf gRef ⟨Φ x, hW ⟨x, x.2, rfl⟩⟩ := by
  let V := partialImage_S71 Φ U hU
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
      (Diffeomorph.pullbackMetricCross (gk.restrictOpenOfSubset (I := J) hW)
        (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU))
      (Diffeomorph.pullbackMetricCross (gInf.restrictOpenOfSubset (I := J) hW)
        (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU))
      (Diffeomorph.pullbackMetricCross (gRef.restrictOpenOfSubset (I := J) hW)
        (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU)) x = _
  rw [metricDerivNorm_pullbackCross]
  exact metricDerivNorm_flat (I := J) (U := W) (V := V) hW
    gk gInf gRef a (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU x)

end Local

end GC.LongTime.Ch12
