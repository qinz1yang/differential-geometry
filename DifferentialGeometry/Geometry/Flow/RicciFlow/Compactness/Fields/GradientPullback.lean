import DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open Geometry.Curvature Geometry.Operator
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem normGradSqFun_gSeqExt_of_chi_eq_one
    (Phi : PointedCGHMaps X P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (k : ℕ) (t : ℝ) (x : P.M) (hx : x ∈ Phi.source k) (hchi : bf.chi k x = 1)
    {f : (X.term (phi k)).M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Phi.map k x)) :
    normGradSqFun (gSeqExt Phi R bf hsrc htgt k t) (f ∘ Phi.map k) x =
      normGradSqFun ((X.term (phi k)).S.base.metric t) f (Phi.map k x) := by
  have hPhi := (Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ hx
  apply normGradSqFun_comp_of_pullback_inner
    (gSeqExt Phi R bf hsrc htgt k t) ((X.term (phi k)).S.base.metric t)
    (hPhi.mdifferentiableAt (by simp)) _
    (hPhi.mfderivToContinuousLinearEquiv (by simp)).surjective hf
  intro v w
  have heq := gSeqExt_inner_of_mem Phi R bf hsrc htgt k t x hx v w
  rw [hchi, one_smul, sub_self, zero_smul, add_zero] at heq
  exact heq.trans
    (PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback
      Phi hsrc htgt k t x hx v w)

theorem eventually_normGradSqFun_gSeqExt_eq_on_compact
    (Phi : PointedCGHMaps X P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ t : ℝ, ∀ x ∈ K, ∀ f : (X.term (phi k)).M → ℝ,
      MDifferentiableAt I 𝓘(ℝ, ℝ) f (Phi.map k x) →
      normGradSqFun (gSeqExt Phi R bf hsrc htgt k t) (f ∘ Phi.map k) x =
        normGradSqFun ((X.term (phi k)).S.base.metric t) f (Phi.map k x) := by
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [eventually_ge_atTop N] with k hk
  intro t x hx f hf
  obtain ⟨W, _hW, hgrow, hchi⟩ := bf.chi_one k
  exact normGradSqFun_gSeqExt_of_chi_eq_one Phi R bf hsrc htgt k t x
    (bf.grow_subset k (hN k hk hx)) (hchi x (hgrow (hN k hk hx))) hf

end DifferentialGeometry.CheegerGromovCompactness
