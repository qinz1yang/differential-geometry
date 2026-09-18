import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialErrorTower
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless]

private theorem comparison_jet_contDiffOn_of_ancient
    (L : PointedFlowData.{v, uE, uH} J ancientTimeInterval)
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {Phi : L.M → P.M} {U : Set L.M} {A alpha : ℝ} {order : ℕ}
    (hA : 0 < A)
    (C : MetricComparisonOn L.S.base.metric P.S.base.metric Phi U (Icc (-A) 0) order alpha)
    (q : ℕ) (y : L.M) (hy : y ∈ U) (v : Fin 2 → TangentSpace J y) :
    ContDiffOn ℝ ∞ (fun s => C.jet q s y v) (Icc (-A) 0) := by
  let w : Fin 2 → TangentSpace I3 (Phi y) := fun j => mfderiv J I3 Phi y (v j)
  have htarget := (tensor0SEvalCLM (I := I3) (x := Phi y) w).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time P.S P.isSolution
      (show -A - 1 < -A by linarith) (neg_neg_of_pos hA)
      (fun _ hs => hs.2) (fun _ hs => hs.2) (Phi y))
  have hsource := (tensor0SEvalCLM (I := J) (x := y) v).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time L.S L.isSolution
      (show -A - 1 < -A by linarith) (neg_neg_of_pos hA)
      (fun _ hs => hs.2) (fun _ hs => hs.2) y)
  have hzero : ContDiffOn ℝ ∞ (fun s => C.jet 0 s y v) (Icc (-A) 0) := by
    apply (htarget.sub hsource).congr
    intro s _hs
    rw [C.jet_zero s y v, C.pullback_eq s y hy v]
    rfl
  intro s hs
  exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
    (f := fun b r => C.jet b r y v) (uniqueDiffOn_Icc (neg_neg_of_pos hA)) hs
    (hzero s hs) (fun b r hr => C.jet_succ b r hr y hy v) q

theorem WindowedModelWitness.exists_composed_comparison
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (L : PointedFlowData.{v, uE, uH} J ancientTimeInterval)
    (Phi : PartialDiffeomorph J I3 L.M W.model.M ∞)
    (U : TopologicalSpace.Opens L.M) (hU : (U : Set L.M) ⊆ Phi.source)
    (himage : MapsTo Phi U (riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)))
    {A alpha : ℝ} (hA : 0 < A) (hdepth : A < modelDepth delta)
    {order : ℕ} (horder : order ≤ modelOrder delta)
    (halpha : 0 < alpha) (hsmall : alpha ≤ backgroundJetSmallness E order)
    (C : MetricComparisonOn L.S.base.metric W.model.S.base.metric Phi U
      (Icc (-A) 0) order alpha)
    {K : Set L.M} (hK : IsCompact K) (hKU : K ⊆ U) :
    Nonempty (MetricComparisonOn L.S.base.metric
      (rescaledMetric S t (S.scalar t x) W.scalar_pos)
      (fun y => W.embedding (Phi y)) K (Icc (-A) 0) order
      (alpha + backgroundJetConstant E order * ((order : ℝ) + 1) * delta)) := by
  have htimes : Icc (-A) 0 ⊆ Icc (-modelDepth delta) 0 :=
    Icc_subset_Icc (neg_le_neg hdepth.le) le_rfl
  have hderiv (b : ℕ) {s : ℝ} (hs : s ∈ Icc (-A) 0) (y : W.model.M)
      (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
      HasDerivWithinAt (fun r => W.comparison.jet b r y v)
        (W.comparison.jet (b + 1) s y v) (Icc (-A) 0) s :=
    (W.hasDerivWithinAt_comparison_jet hS hreg b
      ⟨lt_of_lt_of_le (neg_lt_neg hdepth) hs.1, hs.2⟩ y hy v).mono htimes
  let c : MetricComparisonOn W.model.S.base.metric
      (rescaledMetric S t (S.scalar t x) W.scalar_pos) W.embedding
      (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
      (Icc (-A) 0) (modelOrder delta) delta := {
    pullback := W.comparison.pullback
    pullback_eq := W.comparison.pullback_eq
    jet := W.comparison.jet
    jet_zero := W.comparison.jet_zero
    jet_succ := fun b s hs y hy v =>
      ((hderiv b hs y hy v).derivWithin (uniqueDiffOn_Icc (neg_neg_of_pos hA) s hs)).symm
    equivalence := fun s hs => W.comparison.equivalence s (htimes hs)
    close := fun a b hab s hs => W.comparison.close a b hab s (htimes hs) }
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := J) hK U.isOpen hKU
  obtain ⟨V, hVopen, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hone
  let V' : TopologicalSpace.Opens L.M := ⟨V ∩ U, hVopen.inter U.isOpen⟩
  have hV'U : (V' : Set L.M) ⊆ U := inter_subset_right
  have hKV' : K ⊆ V' := subset_inter hKV hKU
  have hone' : EqOn chi (fun _ => 1) V' := fun y hy => hVone hy.1
  obtain ⟨T⟩ := TransportedErrorTower.nonempty_of_partial_pullback c L.S.base.metric Phi U V'
    hU hV'U himage chi hchi hsupp hone' (C.mono hV'U le_rfl le_rfl)
    horder W.eps_pos.le halpha hsmall (by
      intro b s hs z hz v
      obtain ⟨y, hy, rfl⟩ := hz
      exact (hderiv b hs (Phi y) (himage hy) v).differentiableWithinAt)
  have hball : riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball
  exact ⟨((C.mono hV'U le_rfl le_rfl).trans c T
    (fun _ hy => himage (hV'U hy))
    (fun _ hy => Phi.mdifferentiableAt (by simp) (hU (hV'U hy)))
    (fun _ hy => W.embedding.mdifferentiableAt (by simp) (hball (himage (hV'U hy))))
    (fun b s hs _hu y hy v => by
      exact (comparison_jet_contDiffOn_of_ancient L W.model hA C b y (hV'U hy) v s hs).differentiableWithinAt (by simp))).mono hKV' le_rfl le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
