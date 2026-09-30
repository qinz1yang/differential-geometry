import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelCoveringBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelClassification

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [SigmaCompactSpace M] in
private theorem WindowedModelWitness.round_component_of_round_model
    {delta kappa epsR eps : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (R : RoundComponent W.model.S epsR W.model.basepoint 0 univ)
    (order : ℕ) (horderR : order ≤ ⌈epsR⁻¹⌉₊)
    (hepsR : 0 < epsR) (hepsR1 : epsR < 1)
    (hsmall : epsR ≤ backgroundJetSmallness ThreeSpace order)
    (horder : order ≤ modelOrder delta)
    (herror : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * delta ≤ eps - epsR)
    (horder' : ⌈eps⁻¹⌉₊ ≤ order) (hepshalf : eps ≤ 1 / 2)
    (hbuffer : 2 * (Real.pi / Real.sqrt (1 / 6)) + 1 ≤ modelRadius delta) :
    Nonempty (RoundComponent S eps x t (connectedComponent x)) := by
  let _ : TopologicalSpace R.Z := R.topology
  let _ : ChartedSpace ThreeSpace R.Z := R.charted
  let _ : IsManifold I3 ∞ R.Z := R.smooth
  let _ : T2Space R.Z := R.t2
  let _ : CompactSpace R.Z := R.compact
  let _ : ConnectedSpace R.Z := R.connected
  let Phi : R.Z ≃ₘ⟮I3, I3⟯ W.model.M := {
    toFun := R.map
    invFun := R.map.symm
    left_inv := fun z => R.map.left_inv' (by rw [R.source_eq]; trivial)
    right_inv := fun y => R.map.right_inv' (by rw [R.target_eq]; trivial)
    contMDiff_toFun := by
      change ContMDiff I3 I3 ∞ (R.map : R.Z → W.model.M)
      exact contMDiffOn_univ.mp (R.source_eq ▸ R.map.contMDiffOn_toFun)
    contMDiff_invFun := by
      change ContMDiff I3 I3 ∞ (R.map.symm : W.model.M → R.Z)
      apply contMDiffOn_univ.mp
      have hh := R.map.contMDiffOn_invFun
      rw [R.target_eq] at hh
      exact hh }
  let _ : CompactSpace W.model.M := Phi.surjective.compactSpace Phi.continuous
  let _ : ConnectedSpace W.model.M := Phi.surjective.connectedSpace Phi.continuous
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hball : (univ : Set W.model.M) ⊆
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta) := by
    intro y _
    obtain ⟨z, rfl⟩ := Phi.surjective y
    have hd := metricDistance_le_of_roundComponent_edistDiameter
      roundComponent_edist_diameter_bound R hepsR.le hepsR1 z
    rw [R.center_eq, hbase, Real.sqrt_one, div_one] at hd
    have hsqrt : Real.sqrt (1 + epsR) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith
    have hDia : 0 ≤ Real.pi / Real.sqrt (1 / 6) := by positivity
    have hdist : metricDistance (W.model.S.base.metric 0) W.model.basepoint (Phi z) ≤
        modelRadius delta := by
      exact (hd.trans (mul_le_mul_of_nonneg_right hsqrt hDia)).trans (by linarith)
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint (Phi z) ≤ _
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top
      (W.model.S.base.metric 0) W.model.basepoint (Phi z))]
    exact ENNReal.ofReal_le_ofReal hdist
  have hsrc : (univ : Set W.model.M) ⊆ W.embedding.source :=
    hball.trans ((riemannianClosedBallOf_mono (W.model.S.base.metric 0)
      W.model.basepoint (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have hcont : Continuous (W.embedding : W.model.M → M) :=
    continuousOn_univ.mp (W.embedding.contMDiffOn_toFun.continuousOn.mono hsrc)
  have himage : W.embedding '' (univ : Set W.model.M) = connectedComponent x := by
    have hclosed := (isCompact_univ.image hcont).isClosed
    have hopen := W.embedding.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_univ hsrc
    have hconn := isConnected_univ.image W.embedding hcont.continuousOn
    have hx : x ∈ W.embedding '' (univ : Set W.model.M) := ⟨_, mem_univ _, W.base_map⟩
    exact subset_antisymm (hconn.subset_connectedComponent hx)
      ((show IsClopen (W.embedding '' (univ : Set W.model.M)) from ⟨hclosed, hopen⟩).connectedComponent_subset hx)
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hm : scaleMetric (W.model.S.scalar 0 W.model.basepoint) R.Q_pos
      (W.model.S.base.metric 0) = W.model.S.base.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [scaleMetric_inner, hbase, one_mul]
  have cmp : MetricComparisonOn
      (fun _ => scaleMetric (W.model.S.scalar 0 W.model.basepoint) R.Q_pos (W.model.S.base.metric 0))
      (fun _ => scaleMetric (S.scalar t x) W.scalar_pos (S.base.metric t))
      W.embedding (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
        (modelRadius delta)) {0} (modelOrder delta) delta := by
    simpa only [hm, rescaledMetric, parabolicTime_zero] using
      W.comparison.freezeTime ht0 W.eps_pos.le ({0} : Set ℝ)
  obtain ⟨R'⟩ := roundComponent_transport_of_comparison R W.scalar_pos W.embedding cmp
    order eps horderR hepsR hsmall horder W.eps_pos.le herror horder' hepshalf W.base_map
    (by simpa only [R.target_eq] using hsrc) (by simpa only [R.target_eq] using hball)
    Phi (fun _ => rfl)
  exact ⟨himage ▸ R'⟩

theorem exists_windowedModelWitness_round_component_of_model_round_component {eps : ℝ}
    (heps : 0 < eps) (hepshalf : eps ≤ 1 / 2) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
        {delta kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
        RoundComponent W.model.S eta W.model.basepoint 0 univ →
        Nonempty (RoundComponent S eps x t (connectedComponent x)) := by
  let order := ⌈eps⁻¹⌉₊
  let epsR := min (eps / 2) (backgroundJetSmallness ThreeSpace order)
  let B := 2 * (Real.pi / Real.sqrt (1 / 6)) + 1
  let K := backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1)
  have hR : 0 < epsR := lt_min (by positivity) (backgroundJetSmallness_pos ThreeSpace order)
  have hReps : epsR ≤ eps / 2 := min_le_left _ _
  have hRsmall : epsR ≤ backgroundJetSmallness ThreeSpace order := min_le_right _ _
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := mul_pos (backgroundJetConstant_pos ThreeSpace order) (by positivity)
  have hgap : 0 < eps - epsR := by linarith
  refine ⟨epsR, hR, (by linarith), min eps (min ((eps - epsR) / K) (B⁻¹ ^ 2)),
    lt_min heps (lt_min (div_pos hgap hK) (sq_pos_of_pos (inv_pos.mpr hB))), ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta R
  have hdeps : delta ≤ eps := hdelta.trans (min_le_left _ _)
  have hdrest := hdelta.trans (min_le_right _ _)
  have hderror : delta ≤ (eps - epsR) / K := hdrest.trans (min_le_left _ _)
  have hdradius : delta ≤ B⁻¹ ^ 2 := hdrest.trans (min_le_right _ _)
  apply W.round_component_of_round_model R order
  · exact Nat.ceil_mono (inv_anti₀ hR (by linarith))
  · exact hR
  · linarith
  · exact hRsmall
  · exact (Nat.le_add_right order 1).trans (modelOrder_anti W.eps_pos hdeps)
  · simpa only [K, mul_comm] using (le_div_iff₀ hK).mp hderror
  · exact le_rfl
  · exact hepshalf
  · calc
      B = modelRadius (B⁻¹ ^ 2) := by rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hB.le), inv_inv]
      _ ≤ modelRadius delta := modelRadius_anti W.eps_pos hdradius

theorem exists_windowedModelWitness_round_component {eps : ℝ}
    (heps : 0 < eps) (hepshalf : eps ≤ 1 / 2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
        {delta kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
        KappaSolutions.IsShrinkingSphericalSpaceFormFlow (I := I3) W.model →
        Nonempty (RoundComponent S eps x t (connectedComponent x)) := by
  obtain ⟨eta, heta, _, delta0, hdelta0, htransfer⟩ :=
    exists_windowedModelWitness_round_component_of_model_round_component.{u} heps hepshalf
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta hround
  obtain ⟨R⟩ := roundComponent_of_shrinkingSphericalSpaceFormFlow W.model hround le_rfl
    W.model.basepoint heta
  exact htransfer W hdelta R

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
