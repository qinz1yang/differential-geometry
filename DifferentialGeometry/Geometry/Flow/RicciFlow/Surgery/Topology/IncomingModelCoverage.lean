import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComponentModelTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalPullbackReduction

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

attribute [local instance] PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem OrientedWitness.ofComponentTimeShift
    {P : OrientedThreeStage} {a s : ℝ} {G : P.IncomingSlab a s}
    {c : ConnectedComponents P.Carrier} {eps kappa t : ℝ} {x : P.componentOpen c}
    (h : OrientedWitness (G.componentTimeShift c) (P.componentOrientation c) eps kappa x t) :
    OrientedWitness G.flow P.orientation eps kappa x.val (t + a) := by
  obtain ⟨W, oN, hO⟩ := h
  refine ⟨W.ofComponentTimeShift, oN, ?_⟩
  intro y hy
  change W.model.M at y
  have hsrc : y ∈ W.embedding.source := by
    rwa [W.ofComponentTimeShift_source] at hy
  obtain ⟨hf, hpres⟩ := hO y hsrc
  have hder : mfderiv I3 I3 W.ofComponentTimeShift.embedding y =
      mfderiv I3 I3 W.embedding y := by
    have hfun : (W.ofComponentTimeShift.embedding : W.model.M → P.Carrier) =
        fun z => (W.embedding z).val := funext (W.ofComponentTimeShift_embedding_apply)
    rw [hfun]
    exact DifferentialGeometry.mfderiv_subtypeVal_comp (I := I3) (J := I3)
      (U := P.componentOpen c) W.embedding y
  refine ⟨hder.symm ▸ hf, ?_⟩
  unfold PreservesTangentOrientationAt at hpres ⊢
  simp only [hder, W.ofComponentTimeShift_embedding_apply,
    OrientedThreeStage.componentOrientation, TangentSpace] at hpres ⊢
  convert! hpres using 1

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_component_high_curvature_models (c : ConnectedComponents P.Carrier) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q : ℝ, 0 < Q ∧ ∀ (x : P.componentOpen c) (t : ℝ), t ∈ Ico a s →
        Q ≤ G.flow.scalar t x.val →
        OrientedWitness (G.componentTimeShift c) (P.componentOrientation c)
          eps kappa x (t - a) := by
  let _ : CompactSpace (P.componentOpen c) := P.component_compact c
  let _ : ConnectedSpace (P.componentOpen c) := P.component_connected c
  obtain ⟨kappa, hkappa, hmodels⟩ := closed_flow_models (sub_pos.mpr G.lt)
    (G.componentTimeShift c) (G.isSolutionOn_componentTimeShift c) (P.componentOrientation c)
  refine ⟨kappa, hkappa, ?_⟩
  intro eps heps heps1
  obtain ⟨Q, hQ, hmodel⟩ := hmodels eps heps heps1
  refine ⟨Q, hQ, ?_⟩
  intro x t ht hscalar
  apply hmodel x (t - a) (by constructor <;> linarith [ht.1, ht.2])
  simpa only [G.componentTimeShift_scalar, sub_add_cancel] using hscalar

theorem exists_all_point_high_curvature_model_coverage :
    ∃ kappa : ConnectedComponents P.Carrier → ℝ, (∀ c, 0 < kappa c) ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ Q : ℝ, 0 < Q ∧
        ∀ (x : P.Carrier) (t : ℝ), t ∈ Ico a s → Q ≤ G.flow.scalar t x →
          OrientedWitness G.flow P.orientation eps (kappa (ConnectedComponents.mk x)) x t := by
  classical
  let _ : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  let _ : Fintype (ConnectedComponents P.Carrier) := Fintype.ofFinite _
  choose kappa hkappa hmodels using G.exists_component_high_curvature_models
  refine ⟨kappa, hkappa, ?_⟩
  intro eps heps heps1
  choose Q hQ hmodel using (fun c => hmodels c eps heps heps1)
  let Qmax : ℝ := 1 + ∑ c : ConnectedComponents P.Carrier, Q c
  have hQmax : 0 < Qmax := by
    have hn : 0 ≤ ∑ c : ConnectedComponents P.Carrier, Q c :=
      Finset.sum_nonneg (fun c _ => (hQ c).le)
    dsimp [Qmax]
    linarith
  refine ⟨Qmax, hQmax, ?_⟩
  intro x t ht hscalar
  let c := ConnectedComponents.mk x
  let xc : P.componentOpen c := ⟨x, rfl⟩
  have hQle : Q c ≤ Qmax := by
    have hsingle := Finset.single_le_sum (fun j _ => (hQ j).le) (Finset.mem_univ c)
    dsimp [Qmax]
    linarith
  have W := hmodel c xc t ht (hQle.trans hscalar)
  have hW : OrientedWitness G.flow P.orientation eps (kappa c) x ((t - a) + a) :=
    W.ofComponentTimeShift
  simpa only [sub_add_cancel] using hW

theorem exists_uniform_high_curvature_models :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q : ℝ, 0 < Q ∧ ∀ (x : P.Carrier) (t : ℝ), t ∈ Ico a s →
        Q ≤ G.flow.scalar t x → OrientedWitness G.flow P.orientation eps kappa x t := by
  classical
  let _ : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  let _ : Fintype (ConnectedComponents P.Carrier) := Fintype.ofFinite _
  obtain ⟨kappa, hkappa, hmodels⟩ := G.exists_all_point_high_curvature_model_coverage
  let μ := ∏ c : ConnectedComponents P.Carrier, min (kappa c) 1
  have hμ : 0 < μ := Finset.prod_pos (fun c _ => lt_min (hkappa c) zero_lt_one)
  have hμle : ∀ c, μ ≤ kappa c := by
    intro c
    have hb : ∏ j ∈ (Finset.univ : Finset (ConnectedComponents P.Carrier)).erase c,
        min (kappa j) 1 ≤ 1 := Finset.prod_le_one₀
          (fun j _ => (lt_min (hkappa j) zero_lt_one).le) (fun j _ => min_le_right _ _)
    have heq : μ = min (kappa c) 1 *
        ∏ j ∈ (Finset.univ : Finset (ConnectedComponents P.Carrier)).erase c,
          min (kappa j) 1 := by
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ c)).symm
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hb ((lt_min (hkappa c) zero_lt_one).le)).trans
      (by simpa only [mul_one] using min_le_left (kappa c) 1)
  refine ⟨μ, hμ, ?_⟩
  intro eps heps heps1
  obtain ⟨Q, hQ, hm⟩ := hmodels eps heps heps1
  refine ⟨Q, hQ, fun x t ht hx => ?_⟩
  exact (hm x t ht hx).mono_kappa hμ (hμle _)

theorem exists_uniform_canonical_constants_with_cap_neck_charts
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ Q : ℝ, 0 < Q ∧
        ∀ (x : P.Carrier) (t : ℝ), t ∈ Ico a s → Q ≤ G.flow.scalar t x →
          ∃ K : CanonicalWitness G.flow eps C C x t, K.capTubeHasNeckChart eps := by
  obtain ⟨C, delta, hC, hd, hd1, htransfer⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{u} heps hsmall 1
  refine ⟨C, hC, ?_⟩
  intro P a s G
  obtain ⟨kappa, _, hm⟩ := G.exists_uniform_high_curvature_models
  obtain ⟨Q, hQ, hmodel⟩ := hm delta hd hd1
  refine ⟨Q, hQ, ?_⟩
  intro x t ht hR
  have hw := hmodel x t ht hR
  have hreg : Ioo (t - (delta * G.flow.scalar t x)⁻¹) t ⊆
      (RealTimeInterval.closedOpen a s G.lt).regular := by
    obtain ⟨W, _⟩ := hw
    simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
      interior_mono W.window_mem
  obtain ⟨B, hB⟩ := htransfer kappa P.Carrier _ G.flow G.equation delta
    P.orientation x t le_rfl hreg hw
  exact ⟨B.canonicalWitnessMono B.tolerance_lt.le hsmall,
    hB.mono_eps B.tolerance_lt.le hsmall⟩


theorem exists_all_point_canonical_neighborhoods_with_cap_neck_charts :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 Q : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < Q ∧
        ∀ (x : P.Carrier) (t : ℝ), t ∈ Ico a s → Q ≤ G.flow.scalar t x →
          ∃ K : CanonicalWitness G.flow eps C1 C2 x t, K.capTubeHasNeckChart eps := by
  refine ⟨1 / 44, by norm_num, ?_⟩
  intro eps heps hsmall
  obtain ⟨C, hC, hcanonical⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps
      (hsmall.trans_lt (by norm_num))
  obtain ⟨Q, hQ, hK⟩ := hcanonical P a s G
  exact ⟨C, C, Q, hC, hC, hQ, hK⟩

theorem exists_all_point_canonical_neighborhoods :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 Q : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < Q ∧
        ∀ (x : P.Carrier) (t : ℝ), t ∈ Ico a s → Q ≤ G.flow.scalar t x →
          Nonempty (CanonicalWitness G.flow eps C1 C2 x t) := by
  obtain ⟨epsCan, hepsCan, hmain⟩ := G.exists_all_point_canonical_neighborhoods_with_cap_neck_charts
  refine ⟨epsCan, hepsCan, ?_⟩
  intro eps heps hsmall
  obtain ⟨C1, C2, Q, hC1, hC2, hQ, hK⟩ := hmain eps heps hsmall
  exact ⟨C1, C2, Q, hC1, hC2, hQ, fun x t ht hR => ⟨(hK x t ht hR).choose⟩⟩

section

attribute [local instance] OrientedThreeStage.component_compact

theorem exists_component_canonical_neighborhoods_with_cap_neck_charts
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C Q : ℝ, 1 ≤ C ∧ 0 < Q ∧
      ∀ (c : ConnectedComponents P.Carrier) (x : P.componentOpen c) (t : ℝ),
        t ∈ Ico a s → Q ≤ G.flow.scalar t x.val →
          ∃ K : CanonicalWitness (G.componentTimeShift c) eps C C x (t - a),
            K.capTubeHasNeckChart eps := by
  classical
  obtain ⟨C, delta, hC, hd, hd1, htransfer⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{u} heps hsmall 1
  choose kappa hkappa hmodels using G.exists_component_high_curvature_models
  choose Q hQ hmodel using fun c => hmodels c delta hd hd1
  let _ : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  let _ : Fintype (ConnectedComponents P.Carrier) := Fintype.ofFinite _
  let Qmax : ℝ := 1 + ∑ c : ConnectedComponents P.Carrier, Q c
  have hQmax : 0 < Qmax := by
    have hn : 0 ≤ ∑ c : ConnectedComponents P.Carrier, Q c :=
      Finset.sum_nonneg (fun c _ => (hQ c).le)
    dsimp [Qmax]
    linarith
  refine ⟨C, Qmax, hC, hQmax, ?_⟩
  intro c x t ht hscalar
  let _ : CompactSpace (P.componentOpen c) := P.component_compact c
  have hQle : Q c ≤ Qmax := by
    have hsingle := Finset.single_le_sum (fun j _ => (hQ j).le) (Finset.mem_univ c)
    dsimp [Qmax]
    linarith
  have hw := hmodel c x t ht (hQle.trans hscalar)
  have hreg : Ioo (t - a - (delta * (G.componentTimeShift c).scalar (t - a) x)⁻¹)
      (t - a) ⊆ (RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)).regular := by
    obtain ⟨W, _⟩ := hw
    simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
      interior_mono W.window_mem
  obtain ⟨B, hB⟩ := htransfer (kappa c) (P.componentOpen c) _
    (G.componentTimeShift c) (G.isSolutionOn_componentTimeShift c) delta
    (P.componentOrientation c) x (t - a) le_rfl hreg hw
  exact ⟨B.canonicalWitnessMono B.tolerance_lt.le hsmall,
    hB.mono_eps B.tolerance_lt.le hsmall⟩

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
