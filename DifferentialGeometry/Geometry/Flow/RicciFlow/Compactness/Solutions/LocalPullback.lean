import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Restriction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]


theorem exists_local_solution_of_partialDiffeomorph
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D)
    (hS : IsSolutionOn S) (Phi : PartialDiffeomorph I I M N ∞)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (hU : (U : Set M) ⊆ Phi.source) :
    ∃ S' : SolutionOn (I := I) (M := U) D, IsSolutionOn S' ∧
      ∀ t (x : U) (v w : TangentSpace I x),
        (S'.base.metric t).inner x v w =
          (S.base.metric t).inner (Phi x)
            (mfderiv I I Phi x v) (mfderiv I I Phi x w) := by
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  let S' := solutionOnPullback (solutionOnRestrictOpen S V) e
  refine ⟨S', isSolutionOn_pullback _ (isSolutionOn_restrictOpen S hS V) e, ?_⟩
  intro t x v w
  change (Diffeomorph.pullbackMetric ((S.base.metric t).restrictOpen V) e).inner x v w = _
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
  exact congrArg₂ (fun v' w' => (S.base.metric t).inner (Phi (x : M)) v' w')
    (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x v)
    (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x w)

theorem exists_local_solution_of_pullback
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D)
    (hS : IsSolutionOn (I := I) S)
    (Phi : PartialDiffeomorph I I M N ∞)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (hU : (U : Set M) ⊆ Phi.source)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hmet : ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
      (g t).inner x v w = (S.family.metric t).inner (Phi x)
        (mfderiv I I (Phi : M → N) x v) (mfderiv I I (Phi : M → N) x w)) :
    ∃ S' : SolutionOn (I := I) (M := U) D,
      IsSolutionOn (I := I) S' ∧
      ∀ t : ℝ, S'.family.metric t = (g t).restrictOpen (I := I) U := by
  obtain ⟨S', hS', hmetric⟩ := exists_local_solution_of_partialDiffeomorph S hS Phi U hU
  refine ⟨S', hS', ?_⟩
  intro t
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  exact (hmetric t x v w).trans (hmet t (x : M) x.property v w).symm


theorem ricCovTower_normSq_eq_of_local_pullback
    (Phi : PartialDiffeomorph I I M N ∞)
    (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x)
        (mfderiv I I (Phi : M → N) x v) (mfderiv I I (Phi : M → N) x w))
    (p : ℕ) (x : U) :
    Tensor0SBundle.normSq0S (I := I) g (x : M) (2 + p)
        (ricCovTower (I := I) g g p (x : M)) =
      Tensor0SBundle.normSq0S (I := I) h (Phi (x : M)) (2 + p)
        (ricCovTower (I := I) h h p (Phi (x : M))) := by
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  have heq : Diffeomorph.pullbackMetric (I := I) (h.restrictOpen (I := I) V) e =
      g.restrictOpen (I := I) U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    exact (congrArg₂ (fun v' w' => h.inner (Phi (y : M)) v' w')
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v)
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y w)).trans
      (hmet (y : M) y.property v w).symm
  rw [← ricCovTower_normSq0S_restrictOpen (I := I) g U p x, ← heq,
    ricCovTower_normSq0S_pullback (I := I) (h.restrictOpen (I := I) V) e p x,
    ricCovTower_normSq0S_restrictOpen (I := I) h V p (e x)]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
