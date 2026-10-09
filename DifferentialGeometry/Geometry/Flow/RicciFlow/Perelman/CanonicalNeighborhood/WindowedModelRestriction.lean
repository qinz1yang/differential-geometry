import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {U : TopologicalSpace.Opens M} [SigmaCompactSpace U]
  {eps kappa t : ℝ} {x : U}

def WindowedModelWitness.ofRestrictOpen
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) :
    WindowedModelWitness eps kappa S x.val t := by
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := I3) U ⟨x⟩
  let F := W.embedding.trans j
  have hsc : (solutionOnRestrictOpen S U).scalar t x = S.scalar t x.val :=
    scalar_restrictOpen S U t x
  have hQ : 0 < S.scalar t x.val := hsc ▸ W.scalar_pos
  have hmetric (v : ℝ) :
      rescaledMetric (solutionOnRestrictOpen S U) t ((solutionOnRestrictOpen S U).scalar t x)
        W.scalar_pos v =
        (rescaledMetric S t (S.scalar t x.val) hQ v).restrictOpen U := by
    simp only [hsc]
    apply SmoothRiemannianMetric.ext_inner
    intro y V Z
    change (S.scalar t x.val) *
      ((S.base.metric (parabolicTime t (S.scalar t x.val) v)).restrictOpen U).inner y V Z = _
    rfl
  have hsource : F.source = W.embedding.source := by
    ext y
    change (y ∈ W.embedding.source ∧ W.embedding y ∈ (Set.univ : Set U)) ↔
      y ∈ W.embedding.source
    simp only [mem_univ, and_true]
  have hball : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith : modelRadius eps ≤ modelRadius eps + 1)).trans
      W.buffered_ball
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hQ
      window_mem := by simpa only [hsc] using W.window_mem
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := F
      buffered_ball := hsource ▸ W.buffered_ball
      base_map := ?_
      comparison :=
        { pullback := W.comparison.pullback
          pullback_eq := ?_
          jet := W.comparison.jet
          jet_zero := W.comparison.jet_zero
          jet_succ := W.comparison.jet_succ
          equivalence := W.comparison.equivalence
          close := W.comparison.close }
      source_capture := ?_ }
  · exact congrArg Subtype.val W.base_map
  · intro v y hy V
    rw [W.comparison.pullback_eq v y hy V, hmetric]
    have hder : mfderiv I3 I3 (F : W.model.M → M) y =
        (mfderiv I3 I3 (Subtype.val : U → M) (W.embedding y)).comp
          (mfderiv I3 I3 W.embedding y) :=
      mfderiv_comp y (hasMFDerivAt_subtype_val U (W.embedding y)).mdifferentiableAt
        (W.embedding.mdifferentiableAt (by decide) (hball hy))
    rw [hder]
    simp only [DifferentialGeometry.mfderiv_subtype_val,
      SmoothRiemannianMetric.restrictOpen_inner]
    rfl
  · intro y hy
    rw [DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed _
      U hU x (modelRadius eps - 1)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z ∈ riemannianBallOf
        (rescaledMetric (solutionOnRestrictOpen S U) t ((solutionOnRestrictOpen S U).scalar t x)
          W.scalar_pos 0) x (modelRadius eps - 1) := by
      rw [hmetric]
      exact hz
    obtain ⟨w, hw, hweq⟩ := W.source_capture hz'
    exact ⟨w, hsource.symm ▸ hw, congrArg Subtype.val hweq⟩

@[simp] theorem WindowedModelWitness.ofRestrictOpen_model
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) :
    (W.ofRestrictOpen hU).model = W.model := rfl

@[simp] theorem WindowedModelWitness.ofRestrictOpen_embedding_apply
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) (y : W.model.M) :
    (W.ofRestrictOpen hU).embedding y = (W.embedding y).val := rfl

theorem WindowedModelWitness.ofRestrictOpen_embedding
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) :
    (W.ofRestrictOpen hU).embedding = W.embedding.trans
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
        (I := I3) U ⟨x⟩) := rfl

theorem WindowedModelWitness.ofRestrictOpen_source
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) :
    (W.ofRestrictOpen hU).embedding.source = W.embedding.source := by
  ext y
  change (y ∈ W.embedding.source ∧ W.embedding y ∈ (Set.univ : Set U)) ↔
    y ∈ W.embedding.source
  simp only [mem_univ, and_true]

theorem WindowedModelWitness.ofRestrictOpen_target
    (hU : IsClosed (U : Set M))
    (W : WindowedModelWitness eps kappa (solutionOnRestrictOpen S U) x t) :
    (W.ofRestrictOpen hU).embedding.target = Subtype.val '' W.embedding.target := by
  rw [← (W.ofRestrictOpen hU).embedding.toPartialEquiv.image_source_eq_target,
    (W.ofRestrictOpen_source hU)]
  change (Subtype.val ∘ W.embedding) '' W.embedding.source = Subtype.val '' W.embedding.target
  calc
    _ = Subtype.val '' (W.embedding '' W.embedding.source) :=
      (Set.image_image Subtype.val W.embedding W.embedding.source).symm
    _ = Subtype.val '' W.embedding.target :=
      congrArg (Set.image Subtype.val) W.embedding.toPartialEquiv.image_source_eq_target



theorem OrientedWitness.ofRestrictOpen
    (hU : IsClosed (U : Set M)) (o : TangentOrientationSection M)
    (h : OrientedWitness (solutionOnRestrictOpen S U) (o.restrictOpen U) eps kappa x t) :
    OrientedWitness S o eps kappa x.val t := by
  obtain ⟨W, oN, hO⟩ := h
  refine ⟨W.ofRestrictOpen hU, oN, ?_⟩
  intro y hy
  change W.model.M at y
  have hsrc : y ∈ W.embedding.source := by
    rwa [W.ofRestrictOpen_source hU] at hy
  obtain ⟨hf, hpres⟩ := hO y hsrc
  have hder : mfderiv I3 I3 (W.ofRestrictOpen hU).embedding y =
      mfderiv I3 I3 W.embedding y := by
    have hfun : ((W.ofRestrictOpen hU).embedding : W.model.M → M) =
        fun z => (W.embedding z).val := funext (W.ofRestrictOpen_embedding_apply hU)
    rw [hfun]
    exact DifferentialGeometry.mfderiv_subtypeVal_comp (I := I3) (J := I3)
      (U := U) W.embedding y
  refine ⟨hder.symm ▸ hf, ?_⟩
  unfold PreservesTangentOrientationAt at hpres ⊢
  simp only [hder, W.ofRestrictOpen_embedding_apply hU,
    TangentOrientationSection.restrictOpen_orientation, TangentSpace] at hpres ⊢
  convert! hpres using 1

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
