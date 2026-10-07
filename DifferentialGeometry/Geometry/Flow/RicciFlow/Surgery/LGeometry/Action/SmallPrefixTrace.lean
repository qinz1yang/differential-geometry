import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergenceQuadraticWeight

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Topology BigOperators Interval

theorem regularizedStageStart_eq_max_zero
    (H : ObservedHistory) (T : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (j : Fin (H.eventCount + 1)) :
    H.regularizedStageStart T a j = max a (H.regularizedStageStart T 0 j) := by
  have hmono : Monotone Real.sqrt := fun _ _ h => Real.sqrt_le_sqrt h
  simp only [regularizedStageStart, ← max_sub_sub_left, sub_sub_cancel, hmono.map_max,
    Real.sqrt_sq ha, zero_pow two_ne_zero, Real.sqrt_zero]
  rw [← max_assoc, max_eq_left ha]


theorem sum_stage_action_eq_of_collapsed_suffix
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hcut : cut ≤ last) (T u v : ℝ)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T u j.val = H.regularizedStageEnd T v j.val) :
    (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) =
      ∑ j : H.StageInterval first cut,
        H.stageRegularizedAction j.val T
          (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  classical
  let A : H.StageInterval first last → ℝ := fun j =>
    H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  let e : {j : H.StageInterval first last // j.val ≤ cut} ≃ H.StageInterval first cut :=
    { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
      invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans hcut⟩, j.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum := Fintype.sum_equiv e (fun j => A j.val)
    (fun j => A ⟨j.val, j.property.1, j.property.2.trans hcut⟩) (fun _ => rfl)
  have hzero : (∑ j : {j : H.StageInterval first last // ¬j.val ≤ cut}, A j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    dsimp only [A]
    rw [hcollapsed j.val (lt_of_not_ge j.property)]
    exact intervalIntegral.integral_same
  change (∑ j, A j) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last => j.val ≤ cut) A,
    hsum, hzero, add_zero]


/-- The actual weighted positive-prefix action tends to the action of the
original full family. Collapsed stages contribute zero and are retained in the
limiting original action. -/
theorem tendsto_regularizedWeightedStageAction_of_collapsed_suffix
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hcut : cut ≤ last) (T v : ℝ)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpos : ∀ j : H.StageInterval first cut,
      H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T 0 j.val = H.regularizedStageEnd T v j.val)
    (hInt : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    Tendsto (fun a : ℝ => ∑ j : H.StageInterval first cut,
      ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
        (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian j.val T
          (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩) r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) := by
  classical
  let gammaCut : (j : H.StageInterval first cut) → ℝ → (H.stage j.val).Carrier :=
    fun j => gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    intervalIntegral.tendsto_integral_one_sub_sq_div_sq_mul
      (Real.sqrt_nonneg _) (hpos j)
      (hInt ⟨j.val, j.property.1, j.property.2.trans hcut⟩))
  have hpref : Tendsto (fun a : ℝ => ∑ j : H.StageInterval first cut,
      ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
        (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian j.val T (gammaCut j) r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ j : H.StageInterval first cut, H.stageRegularizedAction j.val T (gammaCut j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) := by
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    simp only [H.regularizedStageStart_eq_max_zero T ha.le]
    rfl
  have hfull := H.sum_stage_action_eq_of_collapsed_suffix first last cut hcut T 0 v
    gamma hcollapsed
  change (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
    (∑ j : H.StageInterval first cut, H.stageRegularizedAction j.val T (gammaCut j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) at hfull
  rw [← hfull] at hpref
  exact hpref

/-- The finite-prefix trace energy converges with the final scalar and speed
terms fixed. No zero-velocity or free-endpoint minimum is used. -/
theorem tendsto_regularizedStage_trace_energy
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hcut : cut ≤ last) (T : ℝ) {v : ℝ} (hv : 0 < v)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpos : ∀ j : H.StageInterval first cut,
      H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T 0 j.val = H.regularizedStageEnd T v j.val)
    (hInt : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (R speedSq : ℝ) :
    let W : ℝ → ℝ := fun a => ∑ j : H.StageInterval first cut,
      ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
        (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian j.val T
          (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩) r
    let L := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)
    Tendsto (fun a : ℝ => 3 / (v - a) - v * R - W a / (2 * (v - a) ^ 2) +
      speedSq / (4 * v)) (𝓝[>] (0 : ℝ))
      (𝓝 (3 / v - v * R - L / (2 * v ^ 2) + speedSq / (4 * v))) := by
  intro W L
  have hW : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    H.tendsto_regularizedWeightedStageAction_of_collapsed_suffix first last cut hcut
      T v gamma hpos hcollapsed hInt
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun a : ℝ => v - a) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hid
  have hdenSq : (2 : ℝ) * v ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hv.ne')
  exact (((tendsto_const_nhds.div hden hv.ne').sub tendsto_const_nhds).sub
    (hW.div ((hden.pow 2).const_mul 2) hdenSq)).add tendsto_const_nhds

/-- Choose a genuine positive cutoff below an already chosen reserve so that
the actual-history trace energy is within the prescribed error. The original
full action, actual endpoint metric, scalar and original endpoint velocity are
fixed throughout the selection. Identifying a receiving smooth representative's
velocity with this original velocity is a separate geometric germ calculation. -/
theorem exists_small_prefix_trace_energy_lt
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hfirst : first ≤ cut) (hcut : cut ≤ last) (T : ℝ) {v : ℝ} (hv : 0 < v)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpos : ∀ j : H.StageInterval first cut,
      H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T 0 j.val = H.regularizedStageEnd T v j.val)
    (hInt : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    let jf : H.StageInterval first last := ⟨first, le_rfl, hfirst.trans hcut⟩
    let q := gamma jf v
    let g := H.stageMetric first (T - v ^ 2)
    let R := metricScalarAt g q
    let V : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v
    let W : ℝ → ℝ := fun a => ∑ j : H.StageInterval first cut,
      ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
        (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian j.val T
          (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩) r
    let L := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)
    ∀ {rho epsilon : ℝ}, 0 < rho → 0 < epsilon →
      ∃ a : ℝ, 0 < a ∧ a < rho ∧ a < v ∧
        3 / (v - a) - v * R - W a / (2 * (v - a) ^ 2) + g.inner q V V / (4 * v) <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + epsilon := by
  intro jf q g R V W L rho epsilon hrho hepsilon
  let E : ℝ → ℝ := fun a => 3 / (v - a) - v * R - W a / (2 * (v - a) ^ 2) +
    g.inner q V V / (4 * v)
  let E0 : ℝ := 3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v)
  have hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 E0) :=
    H.tendsto_regularizedStage_trace_energy first last cut hcut T hv gamma
      hpos hcollapsed hInt R (g.inner q V V)
  have hlt : ∀ᶠ a in 𝓝[>] (0 : ℝ), E a < E0 + epsilon :=
    hE.eventually (gt_mem_nhds (lt_add_of_pos_right E0 hepsilon))
  have hnear : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < a ∧ a < rho ∧ a < v ∧ E a < E0 + epsilon := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hrho).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds, hlt] with a ha har hav hbound
    exact ⟨ha, har, hav, hbound⟩
  exact hnear.exists

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
