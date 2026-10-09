import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] {D : RealTimeInterval}

theorem sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
    {S : SolutionOn (I := I) (M := M) D} {W : Set ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hanc : PhiAlmostNonnegative (I := I) (M := M) S W Phi)
    (hdim : Module.finrank ℝ E = 3) {t : ℝ} (ht : t ∈ W) (x : M) :
    Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤
      4 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * max (S.scalar t x) 1 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hmax := le_max_left (S.scalar t x) 1
  have hm1 := le_max_right (S.scalar t x) 1
  have hP : 0 < max (S.scalar t x) 1 / 4 := by linarith
  have hub : S.scalar t x ≤ 4 * (max (S.scalar t x) 1 / 4) := by linarith
  have h := sqrt_rmNormSq_le_of_scalar_le (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 3)
    (fun t y basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le S t y basis horth ha)
    hPhi hanc hdim ht x hP hub
  have h4 : 4 * (max (S.scalar t x) 1 / 4) = max (S.scalar t x) 1 := by ring
  rw [h4] at h
  have hquot : Phi (max (S.scalar t x) 1) / max (S.scalar t x) 1 ≤ Phi 1 / 1 :=
    hPhi.quotientAntitoneOn (mem_Ioi.2 one_pos) (mem_Ioi.2 (by linarith)) hm1
  rw [div_one, div_le_iff₀ (by linarith)] at hquot
  have hphi0 := hPhi.pos 0
  have hkey : max (S.scalar t x) 1 / 4 + Phi (max (S.scalar t x) 1) + Phi 0 ≤
      (1 + Phi 1 + Phi 0) * max (S.scalar t x) 1 := by
    nlinarith
  calc Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x)
      ≤ 2 * (2 * Real.sqrt 3) *
          (max (S.scalar t x) 1 / 4 + Phi (max (S.scalar t x) 1) + Phi 0) := h
    _ ≤ 2 * (2 * Real.sqrt 3) * ((1 + Phi 1 + Phi 0) * max (S.scalar t x) 1) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * max (S.scalar t x) 1 := by ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_forall_Icc_scalar_le {b : ℝ} (hb : b < s) :
    ∃ K : ℝ, ∀ t ∈ Icc a b, ∀ x : P.Carrier, G.flow.scalar t x ≤ K := by
  have hsub : Icc a b ×ˢ (univ : Set P.Carrier) ⊆
      (RealTimeInterval.closedOpen a s G.lt).carrier ×ˢ univ :=
    prod_mono (fun _ hz => ⟨hz.1, hz.2.trans_lt hb⟩) subset_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image
    (G.equation.scalarCont.mono hsub)
  exact ⟨K, fun t ht x => hK ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩⟩

theorem exists_forall_Icc_riemannNorm_le {b : ℝ} (hb : b < s) :
    ∃ K : ℝ, ∀ t ∈ Icc a b, ∀ x : P.Carrier, G.riemannNorm t x ≤ K := by
  have hc : ContinuousOn (fun q : ℝ × P.Carrier => G.riemannNorm q.1 q.2)
      (Ico a s ×ˢ univ) :=
    (P.tensorFamily_normSq_continuousOn G.equation.smoothMetric.metricTensor_cont
      G.equation.rm04Cont).sqrt
  have hsub : Icc a b ×ˢ (univ : Set P.Carrier) ⊆ Ico a s ×ˢ univ :=
    prod_mono (fun _ hz => ⟨hz.1, hz.2.trans_lt hb⟩) subset_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image (hc.mono hsub)
  exact ⟨K, fun t ht x => hK ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩⟩

theorem exists_noncanonical_point_with_canonical_above_double {ε C1 C2 q T η : ℝ}
    (hq : 0 ≤ q) (hT : a ≤ T)
    (hbad : ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t < T + η ∧ t < s ∧ q < G.flow.scalar t x ∧
      ¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) :
    ∃ (x' : P.Carrier) (t' : ℝ), T ≤ t' ∧ t' < T + η ∧ t' < s ∧ q < G.flow.scalar t' x' ∧
      (¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x' t', W.capTubeHasNeckChart ε) ∧
      ∀ (y : P.Carrier) (t : ℝ), T ≤ t → t ≤ t' →
        2 * G.flow.scalar t' x' ≤ G.flow.scalar t y →
          ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε := by
  obtain ⟨x₀, t₀, hT₀, hη₀, hs₀, hq₀, hbad₀⟩ := hbad
  obtain ⟨K, hK⟩ := G.exists_forall_Icc_scalar_le hs₀
  set B : Set ℝ := {r | ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t ≤ t₀ ∧ q < G.flow.scalar t x ∧
      (¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) ∧
      G.flow.scalar t x = r} with hB
  have hmem : G.flow.scalar t₀ x₀ ∈ B := by
    rw [hB]
    exact ⟨x₀, t₀, hT₀, le_rfl, hq₀, hbad₀, rfl⟩
  have hbdd : BddAbove B := by
    refine ⟨K, fun r hr => ?_⟩
    rw [hB] at hr
    obtain ⟨x, t, hTt, htt₀, -, -, rfl⟩ := hr
    exact hK t ⟨hT.trans hTt, htt₀⟩ x
  have hle : G.flow.scalar t₀ x₀ ≤ sSup B := le_csSup hbdd hmem
  have hhalf : sSup B / 2 < sSup B := by linarith
  obtain ⟨r, hrB, hr⟩ := exists_lt_of_lt_csSup ⟨_, hmem⟩ hhalf
  rw [hB] at hrB
  obtain ⟨x', t', hTt', ht't₀, hq', hbad', rfl⟩ := hrB
  refine ⟨x', t', hTt', ht't₀.trans_lt hη₀, ht't₀.trans_lt hs₀, hq', hbad', ?_⟩
  intro y t hTt htt' hdouble
  by_contra hnc
  have hyB : G.flow.scalar t y ∈ B := by
    rw [hB]
    exact ⟨y, t, hTt, htt'.trans ht't₀, by linarith, hnc, rfl⟩
  have hyle := le_csSup hbdd hyB
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
