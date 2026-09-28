import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Geodesic.Seam
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {H : ObservedHistory.{u}}

private theorem mem_regularizedStage_Icc {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j)) :
    r ∈ Icc (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 ≤ r := ha.trans hr.1
  have ha2 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha hr.1 2
  have hb2 : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
  constructor
  · apply (Real.sqrt_le_left hr0).2
    have := le_min (show T - r ^ 2 ≤ T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.le_sqrt hr0 ?_).2
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      linarith
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      nlinarith

private theorem mem_regularizedStage_Ioo {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Ioo a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)) :
    r ∈ Ioo (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 < r := ha.trans_lt hr.1
  have ha2 : a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have hb2 : r ^ 2 < b ^ 2 := pow_lt_pow_left₀ hr.2 hr0.le two_ne_zero
  constructor
  · apply (Real.sqrt_lt' hr0).2
    have := lt_min (show T - r ^ 2 < T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.lt_sqrt hr0.le).2
    have := max_lt (show T - b ^ 2 < T - r ^ 2 by linarith) ht.1
    linarith

private theorem ne_stageEndTime {t : ℝ} (ht : t < H.horizon) (hB : t ∉ range H.time)
    (j : Fin (H.eventCount + 1)) : t ≠ H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => rw [stageEndTime_last]; exact ht.ne
  | cast i => rw [stageEndTime_castSucc]; exact fun h => hB ⟨i.succ, h.symm⟩

namespace LWindow

variable {lo hi lo₁ hi₁ lo₂ hi₂ : Fin (H.eventCount + 1)} {T : ℝ}

private theorem mem_range_of_mem_Icc (W : H.LWindow lo hi T) {r : ℝ} (hr : r ∈ Ioo W.a W.b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j)) :
    lo ≤ j ∧ j ≤ hi := by
  have ha := W.nonneg
  have h1 : W.a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have h2 : r ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hr.2 (ha.trans hr.1.le) two_ne_zero
  constructor
  · by_contra h
    have := (stageEndTime_le_time_of_lt (not_le.1 h)).trans (H.time_le_of_mem_stageDomain W.lower)
    linarith [ht.2]
  · by_contra h
    have := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
      (stageEndTime_le_time_of_lt (not_le.1 h))
    linarith [ht.1]

private theorem f_eq_of_f_eq (W₁ : H.LWindow lo₁ hi₁ T) (W₂ : H.LWindow lo₂ hi₂ T)
    {y₁ : W₁.X} {y₂ : W₂.X} {k : Fin (H.eventCount + 1)} (hk₁ : lo₁ ≤ k ∧ k ≤ hi₁)
    (hk₂ : lo₂ ≤ k ∧ k ≤ hi₂) (h : W₁.f ⟨k, hk₁⟩ y₁ = W₂.f ⟨k, hk₂⟩ y₂)
    (j : Fin (H.eventCount + 1)) (hj₁ : lo₁ ≤ j ∧ j ≤ hi₁) (hj₂ : lo₂ ≤ j ∧ j ≤ hi₂) :
    W₁.f ⟨j, hj₁⟩ y₁ = W₂.f ⟨j, hj₂⟩ y₂ := by
  rcases le_total k j with hkj | hjk
  · induction j using Fin.induction with
    | zero =>
      obtain rfl : k = 0 := le_antisymm hkj (Fin.zero_le k)
      exact h
    | succ i ih =>
      rcases eq_or_lt_of_le hkj with rfl | hlt
      · exact h
      have hki : k ≤ i.castSucc := Fin.le_castSucc_iff.2 hlt
      have hc₁ : lo₁ ≤ i.castSucc ∧ i.castSucc ≤ hi₁ :=
        ⟨hk₁.1.trans hki, i.castSucc_lt_succ.le.trans hj₁.2⟩
      have hc₂ : lo₂ ≤ i.castSucc ∧ i.castSucc ≤ hi₂ :=
        ⟨hk₂.1.trans hki, i.castSucc_lt_succ.le.trans hj₂.2⟩
      have e := ih hc₁ hc₂ hki
      have h₁ : (H.event i).RegularCrossing (W₁.f ⟨i.castSucc, hc₁⟩ y₁) (W₁.f ⟨i.succ, hj₁⟩ y₁) :=
        W₁.crossing i hc₁.1 hj₁.2 y₁
      have h₂ : (H.event i).RegularCrossing (W₂.f ⟨i.castSucc, hc₂⟩ y₂) (W₂.f ⟨i.succ, hj₂⟩ y₂) :=
        W₂.crossing i hc₂.1 hj₂.2 y₂
      rw [e] at h₁
      exact (H.event i).regularCrossing_right_unique h₁ h₂
  · induction j using Fin.reverseInduction with
    | last =>
      obtain rfl : k = Fin.last _ := le_antisymm (Fin.le_last k) hjk
      exact h
    | cast i ih =>
      rcases eq_or_lt_of_le hjk with heq | hlt
      · subst heq
        exact h
      have hik : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 hlt
      have hc₁ : lo₁ ≤ i.succ ∧ i.succ ≤ hi₁ :=
        ⟨hj₁.1.trans i.castSucc_lt_succ.le, hik.trans hk₁.2⟩
      have hc₂ : lo₂ ≤ i.succ ∧ i.succ ≤ hi₂ :=
        ⟨hj₂.1.trans i.castSucc_lt_succ.le, hik.trans hk₂.2⟩
      have e := ih hc₁ hc₂ hik
      have h₁ : (H.event i).RegularCrossing (W₁.f ⟨i.castSucc, hj₁⟩ y₁) (W₁.f ⟨i.succ, hc₁⟩ y₁) :=
        W₁.crossing i hj₁.1 hc₁.2 y₁
      have h₂ : (H.event i).RegularCrossing (W₂.f ⟨i.castSucc, hj₂⟩ y₂) (W₂.f ⟨i.succ, hc₂⟩ y₂) :=
        W₂.crossing i hj₂.1 hc₂.2 y₂
      rw [e] at h₁
      exact (H.event i).regularCrossing_left_unique h₁ h₂

section Transfer

variable (W₁ : H.LWindow lo₁ hi₁ T) (W₂ : H.LWindow lo₂ hi₂ T) {k : Fin (H.eventCount + 1)}
  (hk₁ : lo₁ ≤ k ∧ k ≤ hi₁) (hk₂ : lo₂ ≤ k ∧ k ≤ hi₂)

private def transferSet : TopologicalSpace.Opens W₂.X :=
  ⟨W₂.f ⟨k, hk₂⟩ ⁻¹' range (W₁.f ⟨k, hk₁⟩),
    (W₁.localDiffeomorph _).isOpen_range.preimage (W₂.localDiffeomorph _).contMDiff.continuous⟩

private def transferMap : transferSet W₁ W₂ hk₁ hk₂ → W₁.X :=
  fun y => Classical.choose y.property

private theorem f_transferMap (y : transferSet W₁ W₂ hk₁ hk₂) :
    W₁.f ⟨k, hk₁⟩ (transferMap W₁ W₂ hk₁ hk₂ y) = W₂.f ⟨k, hk₂⟩ y :=
  Classical.choose_spec y.property

private theorem f_transferMap_of_mem (y : transferSet W₁ W₂ hk₁ hk₂)
    (j : Fin (H.eventCount + 1)) (hj₁ : lo₁ ≤ j ∧ j ≤ hi₁) (hj₂ : lo₂ ≤ j ∧ j ≤ hi₂) :
    W₁.f ⟨j, hj₁⟩ (transferMap W₁ W₂ hk₁ hk₂ y) = W₂.f ⟨j, hj₂⟩ y :=
  f_eq_of_f_eq W₁ W₂ hk₁ hk₂ (f_transferMap W₁ W₂ hk₁ hk₂ y) j hj₁ hj₂

private theorem isLocalDiffeomorph_transferMap :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (transferMap W₁ W₂ hk₁ hk₂) := by
  intro y
  have hx := W₁.localDiffeomorph ⟨k, hk₁⟩ (transferMap W₁ W₂ hk₁ hk₂ y)
  have h1 := (isLocalDiffeomorph_subtype_val (transferSet W₁ W₂ hk₁ hk₂) y).comp ThreeModel _
    (W₂.localDiffeomorph ⟨k, hk₂⟩ y.val)
  have h2 : IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ hx.localInverse
      ((W₂.f ⟨k, hk₂⟩ ∘ Subtype.val) y) := by
    have := hx.localInverse_isLocalDiffeomorphAt
    rwa [f_transferMap] at this
  refine DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_eventuallyEq ?_
    (h1.comp ThreeModel _ h2)
  have hmem : W₂.f ⟨k, hk₂⟩ y.val ∈ hx.localInverse.source := by
    rw [← f_transferMap W₁ W₂ hk₁ hk₂ y]
    exact hx.localInverse_mem_source
  have hsrc : ∀ᶠ y' : transferSet W₁ W₂ hk₁ hk₂ in 𝓝 y,
      W₂.f ⟨k, hk₂⟩ y'.val ∈ hx.localInverse.source :=
    ((W₂.localDiffeomorph _).contMDiff.continuous.comp
      continuous_subtype_val).continuousAt.preimage_mem_nhds
        (hx.localInverse_open_source.mem_nhds hmem)
  filter_upwards [hsrc] with y' hy'
  apply W₁.injective ⟨k, hk₁⟩
  simp only [Function.comp_apply]
  rw [f_transferMap, hx.localInverse_right_inv hy']

private theorem inner_transferMap {t : ℝ} {j : Fin (H.eventCount + 1)}
    (hj₁ : lo₁ ≤ j ∧ j ≤ hi₁) (hj₂ : lo₂ ≤ j ∧ j ≤ hi₂)
    (h₁ : W₁.S.base.metric t =
      localPullMetric (H.stageMetric j t) (W₁.f ⟨j, hj₁⟩) (W₁.localDiffeomorph _))
    (h₂ : W₂.S.base.metric t =
      localPullMetric (H.stageMetric j t) (W₂.f ⟨j, hj₂⟩) (W₂.localDiffeomorph _))
    (y : transferSet W₁ W₂ hk₁ hk₂) (v w : TangentSpace ThreeModel y) :
    (W₂.S.base.metric t).inner y.val v w =
      (W₁.S.base.metric t).inner (transferMap W₁ W₂ hk₁ hk₂ y)
        (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y v)
        (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y w) := by
  set g := transferMap W₁ W₂ hk₁ hk₂
  have hfun : W₁.f ⟨j, hj₁⟩ ∘ g = W₂.f ⟨j, hj₂⟩ ∘ Subtype.val :=
    funext fun y => f_transferMap_of_mem W₁ W₂ hk₁ hk₂ y j hj₁ hj₂
  have hd (u : TangentSpace ThreeModel y) :
      mfderiv ThreeModel ThreeModel (W₁.f ⟨j, hj₁⟩) (g y)
        (mfderiv ThreeModel ThreeModel g y u) =
      mfderiv ThreeModel ThreeModel (W₂.f ⟨j, hj₂⟩) y.val u := by
    have e1 := mfderiv_comp y ((W₁.localDiffeomorph ⟨j, hj₁⟩ (g y)).mdifferentiableAt (by simp))
      ((isLocalDiffeomorph_transferMap W₁ W₂ hk₁ hk₂ y).mdifferentiableAt (by simp))
    have e2 := mfderiv_comp y ((W₂.localDiffeomorph ⟨j, hj₂⟩ y.val).mdifferentiableAt (by simp))
      ((isLocalDiffeomorph_subtype_val (transferSet W₁ W₂ hk₁ hk₂) y).mdifferentiableAt
        (by simp))
    have e3 : mfderiv ThreeModel ThreeModel (W₁.f ⟨j, hj₁⟩ ∘ g) y u =
        mfderiv ThreeModel ThreeModel (W₂.f ⟨j, hj₂⟩ ∘ Subtype.val) y u := by
      rw [hfun]
    rw [e1, e2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val_apply] at e3
    exact e3
  have hp : W₁.f ⟨j, hj₁⟩ (g y) = W₂.f ⟨j, hj₂⟩ y.val :=
    f_transferMap_of_mem W₁ W₂ hk₁ hk₂ y j hj₁ hj₂
  have key : ∀ (p q : (H.stage j).Carrier) (a b a' b' : ThreeSpace), p = q → a = a' → b = b' →
      (H.stageMetric j t).inner p a b = (H.stageMetric j t).inner q a' b' := by
    rintro p q a b a' b' rfl rfl rfl
    rfl
  calc (W₂.S.base.metric t).inner y.val v w
      = (H.stageMetric j t).inner (W₂.f ⟨j, hj₂⟩ y.val)
          (mfderiv ThreeModel ThreeModel (W₂.f ⟨j, hj₂⟩) y.val v)
          (mfderiv ThreeModel ThreeModel (W₂.f ⟨j, hj₂⟩) y.val w) := by
        rw [h₂]
        exact localPullMetric_inner _ _ _ _ _ _
    _ = (H.stageMetric j t).inner (W₁.f ⟨j, hj₁⟩ (g y))
          (mfderiv ThreeModel ThreeModel (W₁.f ⟨j, hj₁⟩) (g y)
            (mfderiv ThreeModel ThreeModel g y v))
          (mfderiv ThreeModel ThreeModel (W₁.f ⟨j, hj₁⟩) (g y)
            (mfderiv ThreeModel ThreeModel g y w)) :=
        key _ _ _ _ _ _ hp.symm (hd v).symm (hd w).symm
    _ = _ := by
        rw [h₁]
        exact (localPullMetric_inner _ _ _ _ _ _).symm

private def TransferIsometricAt (t : ℝ) : Prop :=
  ∀ (y : transferSet W₁ W₂ hk₁ hk₂) (v w : TangentSpace ThreeModel y),
    (W₂.S.base.metric t).inner y.val v w =
      (W₁.S.base.metric t).inner (transferMap W₁ W₂ hk₁ hk₂ y)
        (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y v)
        (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y w)

private theorem transferIsometricAt_of_not_mem {t : ℝ}
    (ht₁ : t ∈ Ioo (T - W₁.b ^ 2) (T - W₁.a ^ 2)) (ht₂ : t ∈ Ioo (T - W₂.b ^ 2) (T - W₂.a ^ 2))
    (hB : t ∉ range H.time) : TransferIsometricAt W₁ W₂ hk₁ hk₂ t := by
  intro y v w
  have hpos : 0 ≤ T - t := by nlinarith [ht₁.2, sq_nonneg W₁.a]
  set r := Real.sqrt (T - t) with hr
  have hr2 : T - r ^ 2 = t := by rw [hr, Real.sq_sqrt hpos]; ring
  have hmem : ∀ {lo hi : Fin (H.eventCount + 1)} (W : H.LWindow lo hi T),
      t ∈ Ioo (T - W.b ^ 2) (T - W.a ^ 2) → r ∈ Ioo W.a W.b := by
    intro lo hi W ht
    have hb : 0 < W.b := W.nonneg.trans_lt W.lt
    refine ⟨(Real.lt_sqrt W.nonneg).2 (by linarith [ht.2]), (Real.sqrt_lt' hb).2 ?_⟩
    linarith [ht.1]
  have hr₁ := hmem W₁ ht₁
  have hr₂ := hmem W₂ ht₂
  obtain ⟨j, hj⟩ := W₁.exists_mem_piece (Ioo_subset_Icc_self hr₁)
  have hjt := W₁.mem_Icc_of_mem_piece j hj
  rw [hr2] at hjt
  have hhor : t < H.horizon := ht₁.2.trans_le
    ((H.le_stageEndTime_of_mem_stageDomain W₁.upper).trans (H.stageEndTime_le_horizon hi₁))
  have hjs : t ∈ Ioo (H.time j.val) (H.stageEndTime j.val) :=
    ⟨lt_of_le_of_ne hjt.1 fun h => hB ⟨j.val, h⟩,
      lt_of_le_of_ne hjt.2 (ne_stageEndTime hhor hB j.val)⟩
  rw [← hr2] at hjs hjt
  have hj₂ := mem_range_of_mem_Icc W₂ hr₂ hjt
  have hm₁ := W₁.metric j r (mem_regularizedStage_Ioo W₁.nonneg hr₁ hjs)
  have hm₂ := W₂.metric ⟨j.val, hj₂⟩ r (mem_regularizedStage_Ioo W₂.nonneg hr₂ hjs)
  rw [hr2] at hm₁ hm₂
  exact inner_transferMap W₁ W₂ hk₁ hk₂ j.property hj₂ hm₁ hm₂ y v w

private theorem transferIsometricAt_of_lt {t : ℝ} (ht₁ : t ∈ W₁.D.regular)
    (ht₂ : t ∈ W₂.D.regular) (hb₁ : T - W₁.b ^ 2 < t) (hb₂ : T - W₂.b ^ 2 < t)
    (ha₁ : t ≤ T - W₁.a ^ 2) (ha₂ : t ≤ T - W₂.a ^ 2) : TransferIsometricAt W₁ W₂ hk₁ hk₂ t := by
  intro y v w
  have c₂ : ContinuousAt (fun t => (W₂.S.base.metric t).inner y.val v w) t :=
    (W₂.solution.smoothMetric.coeff_cont y.val v w).continuousAt (W₂.D.regular_mem_nhds ht₂)
  have c₁ : ContinuousAt (fun t => (W₁.S.base.metric t).inner (transferMap W₁ W₂ hk₁ hk₂ y)
      (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y v)
      (mfderiv ThreeModel ThreeModel (transferMap W₁ W₂ hk₁ hk₂) y w)) t :=
    (W₁.solution.smoothMetric.coeff_cont _ _ _).continuousAt (W₁.D.regular_mem_nhds ht₁)
  have hB : ((range H.time) \ {t})ᶜ ∈ 𝓝 t :=
    (finite_range _).sdiff.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
  have hev : ∀ᶠ t' in 𝓝[<] t, TransferIsometricAt W₁ W₂ hk₁ hk₂ t' := by
    filter_upwards [Ioo_mem_nhdsLT (show max (T - W₁.b ^ 2) (T - W₂.b ^ 2) < t from max_lt hb₁ hb₂),
      nhdsWithin_le_nhds hB, self_mem_nhdsWithin] with t' ht' hB' hlt
    have h := max_lt_iff.1 ht'.1
    exact transferIsometricAt_of_not_mem W₁ W₂ hk₁ hk₂ ⟨h.1, hlt.trans_le ha₁⟩
      ⟨h.2, hlt.trans_le ha₂⟩ fun h => hB' ⟨h, ne_of_lt hlt⟩
  exact tendsto_nhds_unique ((c₂.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (hev.mono fun t ht => ht y v w)) (c₁.tendsto.mono_left nhdsWithin_le_nhds)

private theorem exists_isLRegularizedGeodesicOn_transfer {K : Set ℝ} (hK : IsOpen K) {s₀ : ℝ}
    (hs₀ : s₀ ∈ K) (γ : ℝ → W₂.X) (hγ : IsLRegularizedGeodesicOn W₂.S T γ K)
    (hU : ∀ r ∈ K, γ r ∈ transferSet W₁ W₂ hk₁ hk₂)
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ W₁.D.regular)
    (hmet : ∀ r ∈ K, TransferIsometricAt W₁ W₂ hk₁ hk₂ (T - r ^ 2)) :
    ∃ δ : ℝ → W₁.X, IsLRegularizedGeodesicOn W₁.S T δ K ∧
      ∀ r ∈ K, ∀ (j : Fin (H.eventCount + 1)) (hj₁ : lo₁ ≤ j ∧ j ≤ hi₁)
        (hj₂ : lo₂ ≤ j ∧ j ≤ hi₂), W₁.f ⟨j, hj₁⟩ (δ r) = W₂.f ⟨j, hj₂⟩ (γ r) := by
  classical
  set U := transferSet W₁ W₂ hk₁ hk₂
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  let γU : ℝ → U := fun r => if h : γ r ∈ U then ⟨γ r, h⟩ else ⟨γ s₀, hU s₀ hs₀⟩
  have hγU : ∀ r ∈ K, (γU r).val = γ r := fun r hr => by simp only [γU, dite_eq_left (hU r hr)]
  have hSU := CheegerGromovCompactness.isSolutionOn_restrictOpen W₂.S W₂.solution U
  have hcont : ContinuousOn γU K := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (show ContinuousOn γ K from fun r hr =>
      (hγ r hr).2.1.continuousAt.continuousWithinAt).congr fun r hr => hγU r hr
  have hgeoU : IsLRegularizedGeodesicOn (CheegerGromovCompactness.solutionOnRestrictOpen W₂.S U)
      T γU K := by
    refine (isLRegularizedGeodesicOn_comp_iff_of_localPullMetric
      (isLocalDiffeomorph_subtype_val U) hK hcont
      (fun s _ => (localPullMetric_subtype_val _ U).symm) (fun _ _ => Iff.rfl)).1 ?_
    exact hγ.congr_of_eventuallyEq fun r hr =>
      Filter.eventually_of_mem (hK.mem_nhds hr) fun r' hr' => hγU r' hr'
  have hg := isLocalDiffeomorph_transferMap W₁ W₂ hk₁ hk₂
  have hδ := hgeoU.comp_of_localPullMetric hg
    (fun s hs => SmoothRiemannianMetric.ext_inner fun y v w => by
      rw [localPullMetric_inner]
      exact hmet s hs y v w)
    (fun s hs _ => hreg s hs)
    (fun s hs => Filter.eventually_of_mem (hK.mem_nhds hs) fun r hr => (hgeoU r hr).2.1)
  refine ⟨transferMap W₁ W₂ hk₁ hk₂ ∘ γU, hδ, fun r hr j hj₁ hj₂ => ?_⟩
  rw [Function.comp_apply, f_transferMap_of_mem W₁ W₂ hk₁ hk₂ _ j hj₁ hj₂, hγU r hr]

end Transfer

private theorem exists_eq_of_eq_left {W₁ : H.LWindow lo₁ hi₁ T} {W₂ : H.LWindow lo₂ hi₂ T}
    {γ₁ : ℝ → W₁.X} {γ₂ : ℝ → W₂.X}
    (hγ₁ : IsLRegularizedGeodesicOn W₁.S T γ₁ (Ioo W₁.a W₁.b))
    (hγ₂ : IsLRegularizedGeodesicOn W₂.S T γ₂ (Ioo W₂.a W₂.b)) {s : ℝ}
    (hs₁ : s ∈ Ioo W₁.a W₁.b) (hs₂ : s ∈ Ioo W₂.a W₂.b) {k : Fin (H.eventCount + 1)}
    (hk₁ : lo₁ ≤ k ∧ k ≤ hi₁) (hk₂ : lo₂ ≤ k ∧ k ≤ hi₂) {ε : ℝ} (hε : 0 < ε)
    (hleft : ∀ r ∈ Ioo (s - ε) s, W₁.f ⟨k, hk₁⟩ (γ₁ r) = W₂.f ⟨k, hk₂⟩ (γ₂ r)) :
    ∃ η > 0, ∀ r ∈ Ioo (s - η) (s + η), ∀ (j : Fin (H.eventCount + 1))
      (hj₁ : lo₁ ≤ j ∧ j ≤ hi₁) (hj₂ : lo₂ ≤ j ∧ j ≤ hi₂),
      W₁.f ⟨j, hj₁⟩ (γ₁ r) = W₂.f ⟨j, hj₂⟩ (γ₂ r) := by
  have c₁ : ContinuousAt (fun r => W₁.f ⟨k, hk₁⟩ (γ₁ r)) s :=
    (W₁.localDiffeomorph _).contMDiff.continuous.continuousAt.comp (hγ₁ s hs₁).2.1.continuousAt
  have c₂ : ContinuousAt (fun r => W₂.f ⟨k, hk₂⟩ (γ₂ r)) s :=
    (W₂.localDiffeomorph _).contMDiff.continuous.continuousAt.comp (hγ₂ s hs₂).2.1.continuousAt
  have hs : W₁.f ⟨k, hk₁⟩ (γ₁ s) = W₂.f ⟨k, hk₂⟩ (γ₂ s) :=
    tendsto_nhds_unique ((c₁.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (Filter.eventually_of_mem (Ioo_mem_nhdsLT (by linarith)) hleft))
      (c₂.tendsto.mono_left nhdsWithin_le_nhds)
  have hU : γ₂ s ∈ transferSet W₁ W₂ hk₁ hk₂ := ⟨γ₁ s, hs⟩
  have hev : ∀ᶠ r in 𝓝 s, γ₂ r ∈ transferSet W₁ W₂ hk₁ hk₂ ∧ r ∈ Ioo W₁.a W₁.b ∧
      r ∈ Ioo W₂.a W₂.b :=
    by
      filter_upwards [(hγ₂ s hs₂).2.1.continuousAt.preimage_mem_nhds
        ((transferSet W₁ W₂ hk₁ hk₂).isOpen.mem_nhds hU), Ioo_mem_nhds hs₁.1 hs₁.2,
        Ioo_mem_nhds hs₂.1 hs₂.2] with r h1 h2 h3
      exact ⟨h1, h2, h3⟩
  obtain ⟨η₀, hη₀, hη₀s⟩ := Metric.eventually_nhds_iff.1 hev
  set η := min η₀ ε with hη
  have hηpos : 0 < η := lt_min hη₀ hε
  have hK : ∀ r ∈ Ioo (s - η) (s + η), γ₂ r ∈ transferSet W₁ W₂ hk₁ hk₂ ∧
      r ∈ Ioo W₁.a W₁.b ∧ r ∈ Ioo W₂.a W₂.b := fun r hr => hη₀s (by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hr.1, hr.2, min_le_left η₀ ε])
  have hmet : ∀ r ∈ Ioo (s - η) (s + η), TransferIsometricAt W₁ W₂ hk₁ hk₂ (T - r ^ 2) := by
    intro r hr
    obtain ⟨-, hr₁, hr₂⟩ := hK r hr
    have hb₁ : r ^ 2 < W₁.b ^ 2 := pow_lt_pow_left₀ hr₁.2 (W₁.nonneg.trans hr₁.1.le) two_ne_zero
    have hb₂ : r ^ 2 < W₂.b ^ 2 := pow_lt_pow_left₀ hr₂.2 (W₂.nonneg.trans hr₂.1.le) two_ne_zero
    have ha₁ : W₁.a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ W₁.nonneg hr₁.1.le 2
    have ha₂ : W₂.a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ W₂.nonneg hr₂.1.le 2
    exact transferIsometricAt_of_lt W₁ W₂ hk₁ hk₂ (W₁.regular r (Ioo_subset_Icc_self hr₁))
      (W₂.regular r (Ioo_subset_Icc_self hr₂)) (by linarith) (by linarith) (by linarith)
      (by linarith)
  obtain ⟨δ, hδ, hδf⟩ := exists_isLRegularizedGeodesicOn_transfer W₁ W₂ hk₁ hk₂ isOpen_Ioo
    (show s ∈ Ioo (s - η) (s + η) by constructor <;> linarith) γ₂
    (fun r hr => hγ₂ r (hK r hr).2.2) (fun r hr => (hK r hr).1)
    (fun r hr => W₁.regular r (Ioo_subset_Icc_self (hK r hr).2.1)) hmet
  have hloc : ∀ r ∈ Ioo (s - η) s, δ r = γ₁ r := by
    intro r hr
    have hrK : r ∈ Ioo (s - η) (s + η) := ⟨hr.1, by linarith [hr.2]⟩
    apply W₁.injective ⟨k, hk₁⟩
    rw [hδf r hrK k hk₁ hk₂, ← hleft r ⟨by linarith [hr.1, min_le_right η₀ ε], hr.2⟩]
  have hr₀ : s - η / 2 ∈ Ioo (s - η) s := ⟨by linarith, by linarith⟩
  have hevq : δ =ᶠ[𝓝 (s - η / 2)] γ₁ :=
    Filter.eventually_of_mem (Ioo_mem_nhds hr₀.1 hr₀.2) hloc
  have hvel : lVelocity (I := ThreeModel) δ (s - η / 2) =
      lVelocity (I := ThreeModel) γ₁ (s - η / 2) := by
    unfold lVelocity
    exact congrArg (fun L => L (1 : ℝ)) (hevq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  have hr₀K : s - η / 2 ∈ Ioo (s - η) (s + η) := ⟨hr₀.1, by linarith [hr₀.2]⟩
  have heq := lRegularizedSolution_eqOn W₁.S W₁.solution T isOpen_Ioo isPreconnected_Ioo hr₀K
    isOpen_Ioo isPreconnected_Ioo hr₀K hδ (fun r hr => hγ₁ r (hK r hr).2.1)
    (hloc _ hr₀) hvel
  refine ⟨η, hηpos, fun r hr j hj₁ hj₂ => ?_⟩
  rw [← heq ⟨hr, hr⟩, hδf r hr j hj₁ hj₂]

private theorem exists_eq_of_initialVector {m : Fin (H.eventCount + 1)}
    {W₁ : H.LWindow lo₁ m T} {W₂ : H.LWindow lo₂ m T} (ha₁ : W₁.a = 0) (ha₂ : W₂.a = 0)
    {x₁ : W₁.X} {x₂ : W₂.X}
    {Z₁ : TangentSpace ThreeModel x₁} {Z₂ : TangentSpace ThreeModel x₂}
    (hb₂ : W₂.b ∈ lRegularizedDomain W₂.S T x₂ Z₂)
    (hx : W₁.f ⟨m, W₁.le, le_rfl⟩ x₁ = W₂.f ⟨m, W₂.le, le_rfl⟩ x₂)
    (hZ : mfderiv ThreeModel ThreeModel (W₁.f ⟨m, W₁.le, le_rfl⟩) x₁ Z₁ =
      mfderiv ThreeModel ThreeModel (W₂.f ⟨m, W₂.le, le_rfl⟩) x₂ Z₂) :
    ∃ η > 0, ∀ r ∈ Ico 0 η, ∀ (j : Fin (H.eventCount + 1)) (hj₁ : lo₁ ≤ j ∧ j ≤ m)
      (hj₂ : lo₂ ≤ j ∧ j ≤ m), W₁.f ⟨j, hj₁⟩ (lRegularizedCurve W₁.S T x₁ Z₁ r) =
        W₂.f ⟨j, hj₂⟩ (lRegularizedCurve W₂.S T x₂ Z₂ r) := by
  have hk₁ : lo₁ ≤ m ∧ m ≤ m := ⟨W₁.le, le_rfl⟩
  have hk₂ : lo₂ ≤ m ∧ m ≤ m := ⟨W₂.le, le_rfl⟩
  obtain ⟨α₂, J₂, hJo, hJc, h0J, -, hcurve₂⟩ := hb₂
  have hc₂ := lRegularizedCurve_eqOn W₂.S W₂.solution T hJo hJc h0J hcurve₂
  have hgeo₂ : IsLRegularizedGeodesicOn W₂.S T (lRegularizedCurve W₂.S T x₂ Z₂) J₂ :=
    hcurve₂.2.2.congr_of_eventuallyEq fun r hr =>
      Filter.eventually_of_mem (hJo.mem_nhds hr) fun r' hr' => hc₂ hr'
  have hU : lRegularizedCurve W₂.S T x₂ Z₂ 0 ∈ transferSet W₁ W₂ hk₁ hk₂ := by
    rw [lRegularizedCurve_zero]
    exact ⟨x₁, hx⟩
  have hb₁ : 0 < W₁.b := ha₁ ▸ W₁.lt
  have hb₂' : 0 < W₂.b := ha₂ ▸ W₂.lt
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), lRegularizedCurve W₂.S T x₂ Z₂ r ∈ transferSet W₁ W₂ hk₁ hk₂ ∧
      r ∈ J₂ ∧ r ∈ Ioo (-W₁.b) W₁.b ∧ r ∈ Ioo (-W₂.b) W₂.b :=
    by
      filter_upwards [(hgeo₂ 0 h0J).2.1.continuousAt.preimage_mem_nhds
        ((transferSet W₁ W₂ hk₁ hk₂).isOpen.mem_nhds hU), hJo.mem_nhds h0J,
        Ioo_mem_nhds (show -W₁.b < 0 by linarith) hb₁,
        Ioo_mem_nhds (show -W₂.b < 0 by linarith) hb₂'] with r h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
  obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1 hev
  have hK : ∀ r ∈ Ioo (-η) η, lRegularizedCurve W₂.S T x₂ Z₂ r ∈ transferSet W₁ W₂ hk₁ hk₂ ∧
      r ∈ J₂ ∧ r ∈ Ioo (-W₁.b) W₁.b ∧ r ∈ Ioo (-W₂.b) W₂.b := fun r hr => hηs (by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact hr)
  have hsq : ∀ {b r : ℝ}, r ∈ Ioo (-b) b → |r| ∈ Icc 0 b ∧ T - |r| ^ 2 = T - r ^ 2 :=
    fun hr => ⟨⟨abs_nonneg _, (abs_lt.2 hr).le⟩, by rw [sq_abs]⟩
  have hreg₁ : ∀ r ∈ Ioo (-η) η, T - r ^ 2 ∈ W₁.D.regular := fun r hr => by
    obtain ⟨h1, h2⟩ := hsq (hK r hr).2.2.1
    rw [← h2]
    exact W₁.regular _ (ha₁ ▸ h1)
  have hreg₂ : ∀ r ∈ Ioo (-η) η, T - r ^ 2 ∈ W₂.D.regular := fun r hr => by
    obtain ⟨h1, h2⟩ := hsq (hK r hr).2.2.2
    rw [← h2]
    exact W₂.regular _ (ha₂ ▸ h1)
  have hmet : ∀ r ∈ Ioo (-η) η, TransferIsometricAt W₁ W₂ hk₁ hk₂ (T - r ^ 2) := by
    intro r hr
    have hr₁ : r ^ 2 < W₁.b ^ 2 := by
      rw [← sq_abs]
      exact pow_lt_pow_left₀ (abs_lt.2 (hK r hr).2.2.1) (abs_nonneg r) two_ne_zero
    have hr₂ : r ^ 2 < W₂.b ^ 2 := by
      rw [← sq_abs]
      exact pow_lt_pow_left₀ (abs_lt.2 (hK r hr).2.2.2) (abs_nonneg r) two_ne_zero
    have hr0 := sq_nonneg r
    exact transferIsometricAt_of_lt W₁ W₂ hk₁ hk₂ (hreg₁ r hr) (hreg₂ r hr) (by linarith)
      (by linarith) (by rw [ha₁]; linarith) (by rw [ha₂]; linarith)
  have h0 : (0 : ℝ) ∈ Ioo (-η) η := ⟨by linarith, hη⟩
  obtain ⟨δ, hδ, hδf⟩ := exists_isLRegularizedGeodesicOn_transfer W₁ W₂ hk₁ hk₂ isOpen_Ioo h0
    (lRegularizedCurve W₂.S T x₂ Z₂) (fun r hr => hgeo₂ r (hK r hr).2.1)
    (fun r hr => (hK r hr).1) hreg₁ hmet
  have hδ0 : δ 0 = x₁ := by
    apply W₁.injective ⟨m, hk₁⟩
    rw [hδf 0 h0 m hk₁ hk₂, lRegularizedCurve_zero]
    exact hx.symm
  have hT₂ : T ∈ W₂.D.regular := by simpa using hreg₂ 0 h0
  have hcomp : (W₁.f ⟨m, hk₁⟩ ∘ δ) =ᶠ[𝓝 (0 : ℝ)]
      (W₂.f ⟨m, hk₂⟩ ∘ lRegularizedCurve W₂.S T x₂ Z₂) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) fun r hr => hδf r hr m hk₁ hk₂
  have hv1 := lVelocity_comp_of_isLocalDiffeomorph (W₁.localDiffeomorph ⟨m, hk₁⟩) (hδ 0 h0).2.1
  have hv2 := lVelocity_comp_of_isLocalDiffeomorph (W₂.localDiffeomorph ⟨m, hk₂⟩)
    (hgeo₂ 0 h0J).2.1
  have hv12 : lVelocity (I := ThreeModel) (W₁.f ⟨m, hk₁⟩ ∘ δ) 0 =
      lVelocity (I := ThreeModel) (W₂.f ⟨m, hk₂⟩ ∘ lRegularizedCurve W₂.S T x₂ Z₂) 0 := by
    unfold lVelocity
    exact congrArg (fun L => L (1 : ℝ)) (hcomp.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  have hvel : lVelocity (I := ThreeModel) δ 0 = 2 • Z₁ := by
    have hinj : Function.Injective (mfderiv ThreeModel ThreeModel (W₁.f ⟨m, hk₁⟩) (δ 0)) := by
      rw [← (W₁.localDiffeomorph ⟨m, hk₁⟩).mfderivToContinuousLinearEquiv_coe (by simp)]
      exact ((W₁.localDiffeomorph ⟨m, hk₁⟩).mfderivToContinuousLinearEquiv (by simp) _).injective
    apply hinj
    rw [← hv1, hv12, hv2, lRegularizedCurve_velocity_zero W₂.S W₂.solution T x₂ Z₂ hT₂,
      lRegularizedCurve_zero, hδ0, map_smul, map_nsmul, ← hZ, two_smul]
    exact two_smul ℝ _
  have hcurve : IsLRegularizedCurveOn W₁.S T δ (Ioo (-η) η) x₁ Z₁ := ⟨hδ0, hvel, hδ⟩
  have hc₁ := lRegularizedCurve_eqOn W₁.S W₁.solution T isOpen_Ioo isPreconnected_Ioo h0 hcurve
  refine ⟨η, hη, fun r hr j hj₁ hj₂ => ?_⟩
  have hrK : r ∈ Ioo (-η) η := ⟨by linarith [hr.1], hr.2⟩
  rw [hc₁ hrK, hδf r hrK j hj₁ hj₂]

end LWindow

private theorem lt_stageEndTime_of_mem_stageDomain {k : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain k) (hth : t < H.horizon) : t < H.stageEndTime k := by
  cases k using Fin.lastCases with
  | last => rwa [stageEndTime_last]
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    rw [stageEndTime_castSucc]
    exact ht.2

variable (H) in
def IsHistoryLGeodesicOn {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) : Prop :=
  T - v ^ 2 ∈ H.stageDomain first ∧
    (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))) ∧
    (∀ s ∈ Ioo 0 v, ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
      (W : H.LWindow lo hi T), s ∈ Ioo W.a W.b ∧ W.b ≤ v ∧ ∃ γ : ℝ → W.X,
        IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
        ∀ j : H.StageInterval lo hi,
          EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
            (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
    ContinuousWithinAt (α ⟨first, le_rfl, hle⟩) (Iio v) v

variable (H) in
def HasHistoryLInitialVector {first last : Fin (H.eventCount + 1)} (T : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (p : (H.stage last).Carrier) (Z : TangentSpace ThreeModel p) : Prop :=
  ∃ (lo : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (W : H.LWindow lo last T) (x : W.X)
    (Zx : TangentSpace ThreeModel x), W.a = 0 ∧ W.f ⟨last, W.le, le_rfl⟩ x = p ∧
    mfderiv ThreeModel ThreeModel (W.f ⟨last, W.le, le_rfl⟩) x Zx = Z ∧
    W.b ∈ lRegularizedDomain W.S T x Zx ∧
    ∀ j : H.StageInterval lo last,
      EqOn (W.f j ∘ lRegularizedCurve W.S T x Zx) (α ⟨j.val, hlo.trans j.property.1, j.property.2⟩)
        (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T W.b j.val))

section Uniqueness

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {α β : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
  {p : (H.stage last).Carrier} {Z : TangentSpace ThreeModel p}

private theorem agree_base (hv : 0 < v) (hT : T ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hα₀ : H.HasHistoryLInitialVector T α p Z)
    (hβ₀ : H.HasHistoryLInitialVector T β p Z) :
    ∃ η > 0, ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        r < η → α j r = β j r := by
  obtain ⟨lo₁, hlo₁, W₁, x₁, Z₁, ha₁, hx₁, hZ₁, -, heq₁⟩ := hα₀
  obtain ⟨lo₂, hlo₂, W₂, x₂, Z₂, ha₂, hx₂, hZ₂, hb₂, heq₂⟩ := hβ₀
  obtain ⟨η, hη, hηeq⟩ := LWindow.exists_eq_of_initialVector ha₁ ha₂ hb₂ (hx₁.trans hx₂.symm)
    (hZ₁.trans hZ₂.symm)
  have hb₁ : 0 < W₁.b := ha₁ ▸ W₁.lt
  have hb₂' : 0 < W₂.b := ha₂ ▸ W₂.lt
  refine ⟨min η (min W₁.b W₂.b), lt_min hη (lt_min hb₁ hb₂'), fun j r hr hrη => ?_⟩
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr.1
  have hr₁ : r < W₁.b := hrη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr₂ : r < W₂.b := hrη.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    rw [sq, mul_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hT, H.le_stageEndTime_of_mem_stageDomain hT⟩
  have hjt := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower j hr
  have hlo : ∀ {lo : Fin (H.eventCount + 1)} (W : H.LWindow lo last T), r < W.b → lo ≤ j.val := by
    intro lo W hrW
    by_contra h
    have := (stageEndTime_le_time_of_lt (not_le.1 h)).trans (H.time_le_of_mem_stageDomain W.lower)
    have : r ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hrW hr0 two_ne_zero
    linarith [hjt.2]
  have e₁ := heq₁ ⟨j.val, hlo W₁ hr₁, j.property.2⟩
    (mem_regularizedStage_Icc le_rfl ⟨hr0, hr₁.le⟩ hjt)
  have e₂ := heq₂ ⟨j.val, hlo W₂ hr₂, j.property.2⟩
    (mem_regularizedStage_Icc le_rfl ⟨hr0, hr₂.le⟩ hjt)
  simp only [Function.comp_apply] at e₁ e₂
  exact e₁.symm.trans ((hηeq r ⟨hr0, hrη.trans_le (min_le_left _ _)⟩ j.val ⟨hlo W₁ hr₁,
    j.property.2⟩ ⟨hlo W₂ hr₂, j.property.2⟩).trans e₂)

private theorem agree_step (hv : 0 < v) (hα : H.IsHistoryLGeodesicOn hle T v α)
    (hβ : H.IsHistoryLGeodesicOn hle T v β) (hT : T ∈ H.stageDomain last) {s : ℝ}
    (hs : s ∈ Ioo 0 v)
    (hagree : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        r < s → α j r = β j r) :
    ∃ η > 0, ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        r < s + η → α j r = β j r := by
  obtain ⟨lo₁, hi₁, hlo₁, hhi₁, W₁, hs₁, -, γ₁, hγ₁, heq₁⟩ := hα.2.2.1 s hs
  obtain ⟨lo₂, hi₂, hlo₂, hhi₂, W₂, hs₂, -, γ₂, hγ₂, heq₂⟩ := hβ.2.2.1 s hs
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    rw [sq, mul_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hT, H.le_stageEndTime_of_mem_stageDomain hT⟩
  have hTh : T ≤ H.horizon :=
    (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon _)
  have hs2 : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero
  have hs0 : 0 < s ^ 2 := pow_pos hs.1 2
  have hlow := H.time_le_of_mem_stageDomain hα.1
  have ht0 : 0 ≤ T - s ^ 2 := (H.time_nonneg first).trans (by linarith)
  have hth : T - s ^ 2 < H.horizon := by linarith
  set k := H.activeStage ⟨T - s ^ 2, ht0, hth.le⟩ with hk
  have hkd : T - s ^ 2 ∈ H.stageDomain k := H.activeStage_mem _
  have hkt : H.time k ≤ T - s ^ 2 := H.time_le_of_mem_stageDomain hkd
  have hke : T - s ^ 2 < H.stageEndTime k := lt_stageEndTime_of_mem_stageDomain hkd hth
  have hk₁ := LWindow.mem_range_of_mem_Icc W₁ hs₁ ⟨hkt, hke.le⟩
  have hk₂ := LWindow.mem_range_of_mem_Icc W₂ hs₂ ⟨hkt, hke.le⟩
  have hev : ∀ᶠ r in 𝓝 s, T - r ^ 2 < H.stageEndTime k ∧ 0 < r ∧ r < v ∧
      r ∈ Ioo W₁.a W₁.b ∧ r ∈ Ioo W₂.a W₂.b := by
    have hc : ContinuousAt (fun r : ℝ => T - r ^ 2) s := by fun_prop
    filter_upwards [hc.eventually_lt continuousAt_const hke, lt_mem_nhds hs.1,
      gt_mem_nhds hs.2, Ioo_mem_nhds hs₁.1 hs₁.2, Ioo_mem_nhds hs₂.1 hs₂.2]
      with r h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : ∀ r, s - ε < r → r < s + ε → T - r ^ 2 < H.stageEndTime k ∧ 0 < r ∧ r < v ∧
      r ∈ Ioo W₁.a W₁.b ∧ r ∈ Ioo W₂.a W₂.b := fun r h1 h2 => hεs (by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith)
  have hpiece : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) := fun j r hr =>
    H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hα.1 j hr
  have hleft : ∀ r ∈ Ioo (s - ε) s, W₁.f ⟨k, hk₁⟩ (γ₁ r) = W₂.f ⟨k, hk₂⟩ (γ₂ r) := by
    intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hball r hr.1 (by linarith [hr.2])
    have hr2 : r ^ 2 < s ^ 2 := pow_lt_pow_left₀ hr.2 h2.le two_ne_zero
    have ht : T - r ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) := ⟨by linarith, h1.le⟩
    have hkf : first ≤ k ∧ k ≤ last := ⟨hlo₁.trans hk₁.1, hk₁.2.trans hhi₁⟩
    have e := hagree ⟨k, hkf⟩ r (mem_regularizedStage_Icc le_rfl ⟨h2.le, h3.le⟩ ht) hr.2
    have e₁ := heq₁ ⟨k, hk₁⟩ (mem_regularizedStage_Icc W₁.nonneg (Ioo_subset_Icc_self h4) ht)
    have e₂ := heq₂ ⟨k, hk₂⟩ (mem_regularizedStage_Icc W₂.nonneg (Ioo_subset_Icc_self h5) ht)
    exact e₁.trans (e.trans e₂.symm)
  obtain ⟨η, hη, hηeq⟩ := LWindow.exists_eq_of_eq_left hγ₁ hγ₂ hs₁ hs₂ hk₁ hk₂ hε hleft
  refine ⟨min η ε, lt_min hη hε, fun j r hr hrs => ?_⟩
  rcases lt_or_ge r s with hlt | hge
  · exact hagree j r hr hlt
  have hrε : r < s + ε := hrs.trans_le (by linarith [min_le_right η ε])
  have hrη : r < s + η := hrs.trans_le (by linarith [min_le_left η ε])
  obtain ⟨-, -, -, h4, h5⟩ := hball r (by linarith) hrε
  have ht := hpiece j r hr
  have hj₁ := LWindow.mem_range_of_mem_Icc W₁ h4 ht
  have hj₂ := LWindow.mem_range_of_mem_Icc W₂ h5 ht
  have e₁ := heq₁ ⟨j.val, hj₁⟩ (mem_regularizedStage_Icc W₁.nonneg (Ioo_subset_Icc_self h4) ht)
  have e₂ := heq₂ ⟨j.val, hj₂⟩ (mem_regularizedStage_Icc W₂.nonneg (Ioo_subset_Icc_self h5) ht)
  exact e₁.symm.trans ((hηeq r ⟨by linarith, hrη⟩ j.val hj₁ hj₂).trans e₂)

theorem IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector (hv : 0 < v)
    (hα : H.IsHistoryLGeodesicOn hle T v α) (hβ : H.IsHistoryLGeodesicOn hle T v β)
    (hα₀ : H.HasHistoryLInitialVector T α p Z) (hβ₀ : H.HasHistoryLInitialVector T β p Z)
    (j : H.StageInterval first last) :
    EqOn (α j) (β j)
      (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) := by
  have hT : T ∈ H.stageDomain last := by
    obtain ⟨lo, hlo, W, x, Zx, ha, -⟩ := hα₀
    simpa [ha] using W.upper
  let A : ℝ → Prop := fun s => ∀ (j : H.StageInterval first last) (r : ℝ),
    r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
      r < s → α j r = β j r
  have hmono : ∀ {s s'}, s ≤ s' → A s' → A s := fun hss h j r hr hrs =>
    h j r hr (hrs.trans_le hss)
  set S : Set ℝ := {s | s ∈ Icc 0 v ∧ A s}
  have h0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hv.le⟩, fun j r hr hr0 =>
    absurd ((Real.sqrt_nonneg _).trans hr.1) (not_le.2 hr0)⟩
  have hbdd : BddAbove S := ⟨v, fun s hs => hs.1.2⟩
  obtain ⟨η₀, hη₀, hA₀⟩ := agree_base hv hT hα.1 hα₀ hβ₀
  have hc0 : 0 < sSup S := (lt_min hη₀ hv).trans_le
    (le_csSup hbdd ⟨⟨(lt_min hη₀ hv).le, min_le_right _ _⟩, hmono (min_le_left _ _) hA₀⟩)
  have hAc : A (sSup S) := fun j r hr hrc => by
    obtain ⟨s, hsS, hrs⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ hrc
    exact hsS.2 j r hr hrs
  have hcv : sSup S ≤ v := csSup_le ⟨0, h0⟩ fun s hs => hs.1.2
  have hcv' : sSup S = v := by
    by_contra hne
    have hlt : sSup S < v := lt_of_le_of_ne hcv hne
    obtain ⟨η, hη, hAη⟩ := agree_step hv hα hβ hT ⟨hc0, hlt⟩ hAc
    have hmem : min (sSup S + η) v ∈ S := ⟨⟨hc0.le.trans (le_min (by linarith) hcv),
      min_le_right _ _⟩, hmono (min_le_left _ _) hAη⟩
    have := le_csSup hbdd hmem
    have : sSup S < min (sSup S + η) v := lt_min (by linarith) hlt
    linarith
  rw [hcv'] at hAc
  intro r hr
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    rw [sq, mul_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hT, H.le_stageEndTime_of_mem_stageDomain hT⟩
  have hrv : r ≤ v := hr.2.trans (H.regularizedStage_bounds le_rfl hv.le hupper hα.1 j).2.2
  rcases lt_or_eq_of_le hrv with hlt | heqv
  · exact hAc j r hr hlt
  subst heqv
  have hTh : T ≤ H.horizon :=
    (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon _)
  have hv2 : 0 < r ^ 2 := pow_pos hv 2
  have hfe : T - r ^ 2 < H.stageEndTime first :=
    lt_stageEndTime_of_mem_stageDomain hα.1 (by linarith)
  have hjt := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hα.1 j hr
  obtain ⟨jv, hj1, hj2⟩ := j
  obtain rfl : jv = first := by
    by_contra hne
    have hlt : first < jv := lt_of_le_of_ne hj1 (Ne.symm hne)
    have := stageEndTime_le_time_of_lt hlt
    change T - r ^ 2 ∈ Icc (H.time jv) (H.stageEndTime jv) at hjt
    linarith [hjt.1]
  have hev : ∀ᶠ r' in 𝓝[<] r, α ⟨jv, hj1, hj2⟩ r' = β ⟨jv, hj1, hj2⟩ r' := by
    have hc : ContinuousAt (fun r' : ℝ => T - r' ^ 2) r := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const hfe),
      nhdsWithin_le_nhds (lt_mem_nhds hv), self_mem_nhdsWithin] with r' h1 h2 h3
    have hlow := H.time_le_of_mem_stageDomain hα.1
    have h3' : r' ^ 2 < r ^ 2 := pow_lt_pow_left₀ h3 h2.le two_ne_zero
    exact hAc ⟨jv, hj1, hj2⟩ r' (mem_regularizedStage_Icc le_rfl ⟨h2.le, h3.le⟩
      ⟨by linarith, h1.le⟩) h3
  exact tendsto_nhds_unique_of_eventuallyEq hα.2.2.2 hβ.2.2.2 hev

end Uniqueness

variable (H) in
def historyLExpDomain {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
    (p : (H.stage last).Carrier) : Set (TangentSpace ThreeModel p) :=
  {Z | ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
    H.IsHistoryLGeodesicOn hle T v α ∧ H.HasHistoryLInitialVector T α p Z}

variable (H) in
def historyLExp {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
    (p : (H.stage last).Carrier) (Z : H.historyLExpDomain hle T v p) : (H.stage first).Carrier :=
  Classical.choose Z.property ⟨first, le_rfl, hle⟩ v

theorem historyLExp_eq {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
    (hv : 0 < v) {p : (H.stage last).Carrier} (Z : H.historyLExpDomain hle T v p)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hα : H.IsHistoryLGeodesicOn hle T v α) (hZ : H.HasHistoryLInitialVector T α p Z) :
    H.historyLExp hle T v p Z = α ⟨first, le_rfl, hle⟩ v := by
  have h := Classical.choose_spec Z.property
  have hv' : v ∈ Icc (H.regularizedStageStart T 0 first) (H.regularizedStageEnd T v first) :=
    mem_regularizedStage_Icc le_rfl ⟨hv.le, le_rfl⟩
      ⟨H.time_le_of_mem_stageDomain hα.1, H.le_stageEndTime_of_mem_stageDomain hα.1⟩
  exact IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hv h.1 hα h.2 hZ
    ⟨first, le_rfl, hle⟩ hv'

section Regular

variable {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {T B v : ℝ}
  {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

private theorem bounds_of_regularizedCost_eq
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤) :
    T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧ T - v ^ 2 ∈ H.stageDomain first := by
  have hne : (H.regularizedActionValues first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
      (α ⟨first, le_rfl, hle⟩ v)).Nonempty := by
    by_contra h
    exact hfin (hmin.trans (H.regularizedCost_eq_top_of_no_competitor first last hle T B 0 v _ _
      (not_nonempty_iff_eq_empty.1 h)))
  obtain ⟨A, -, -, hupper, hlower, -⟩ := hne
  exact ⟨hupper, hlower⟩

private theorem node_of_regularCrossing
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    ∃ z : (H.event i).old,
      z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
        (Real.sqrt (T - H.time i.succ)) ∧
      (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (T - H.time i.succ)) := by
  obtain ⟨z, -, h1, h2⟩ := hcross i hf hl
  exact ⟨z, h1, h2⟩

variable
  (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
    -B ≤ metricScalarAt (H.stageMetric j t) x)
  (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
    (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
  (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
    (H.event i).RegularCrossing
      (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
      (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
  (hmin : H.regularizedExtendedAction first last T B 0 v α =
    H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
      (α ⟨first, le_rfl, hle⟩ v))
  (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤)
include hfloor hα hcross hmin hfin

theorem isHistoryLGeodesicOn_of_regularizedCost_eq (hv : 0 < v) :
    H.IsHistoryLGeodesicOn hle T v α := by
  have hnode := node_of_regularCrossing hcross
  obtain ⟨hupper, hlower⟩ := bounds_of_regularizedCost_eq hle hmin hfin
  have hT : T ≤ H.stageEndTime last := by simpa using hupper.2
  have hlowt := H.time_le_of_mem_stageDomain hlower
  refine ⟨hlower, hcross, fun s hs => ?_, ?_⟩
  · have hs2 : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero
    have hs0 : 0 < s ^ 2 := pow_pos hs.1 2
    have hth : T - s ^ 2 < H.horizon := by linarith [H.stageEndTime_le_horizon last]
    have ht0 : 0 ≤ T - s ^ 2 := (H.time_nonneg first).trans (by linarith)
    obtain ⟨k, hkd⟩ : ∃ k, T - s ^ 2 ∈ H.stageDomain k :=
      ⟨_, H.activeStage_mem ⟨T - s ^ 2, ht0, hth.le⟩⟩
    have hkt := H.time_le_of_mem_stageDomain hkd
    have hke := lt_stageEndTime_of_mem_stageDomain hkd hth
    have hfk : first ≤ k := by
      by_contra h
      have := stageEndTime_le_time_of_lt (not_le.1 h)
      linarith
    have hkl : k ≤ last := by
      by_contra h
      have := stageEndTime_le_time_of_lt (not_le.1 h)
      linarith
    rcases eq_or_lt_of_le hkt with heq | hlt
    · have hfk' : first < k := H.time_strictMono.lt_iff_lt.1 (by linarith)
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt ((Fin.zero_le first).trans_lt hfk'))
      have hf : first ≤ i.castSucc := Fin.le_castSucc_iff.2 hfk'
      have hsq : Real.sqrt (T - H.time i.succ) = s := by
        rw [heq, sub_sub_cancel, Real.sqrt_sq hs.1.le]
      obtain ⟨W, -, ha, hb, hbv, γ, -, -, hW, hgeo⟩ :=
        LWindow.exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq hle le_rfl hv.le
          hupper hlower hfloor α hα hcross hmin hfin i hf hkl (by rw [hsq]; exact hs.1)
      rw [hsq] at ha hb
      exact ⟨i.castSucc, i.succ, hf, hkl, W, ⟨ha, hb⟩, hbv, γ, hgeo, hW⟩
    · have hc : ContinuousAt (fun r : ℝ => T - r ^ 2) s := by fun_prop
      have hev : ∀ᶠ r in 𝓝 s, H.time k < T - r ^ 2 ∧ T - r ^ 2 < H.stageEndTime k ∧ 0 < r ∧
          r < v := by
        filter_upwards [continuousAt_const.eventually_lt hc hlt,
          hc.eventually_lt continuousAt_const hke, lt_mem_nhds hs.1, gt_mem_nhds hs.2]
          with r h1 h2 h3 h4
        exact ⟨h1, h2, h3, h4⟩
      obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hev
      have ha := hεs (show dist (s - ε / 2) s < ε by
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
      have hb := hεs (show dist (s + ε / 2) s < ε by
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
      obtain ⟨W, hWa, hWb, -, γ, -, heq, hgeo⟩ :=
        LWindow.exists_stage_isLRegularizedGeodesicOn_of_regularizedCost_eq hle le_rfl hupper
          hlower hfloor α hα hnode hmin hfin ⟨k, hfk, hkl⟩ ha.2.2.1.le (by linarith) hb.2.2.2.le
          hb.1 ha.2.1
      refine ⟨k, k, hfk, hkl, W, by rw [hWa, hWb]; constructor <;> linarith,
        hWb ▸ hb.2.2.2.le, γ, hWa ▸ hWb ▸ hgeo, fun j r hr => ?_⟩
      obtain ⟨jv, h1, h2⟩ := j
      obtain rfl := le_antisymm h2 h1
      have hsub := W.piece_subset ⟨jv, h1, h2⟩ hr
      rw [hWa, hWb] at hsub
      exact heq hsub
  · have hend := H.regularizedStageEnd_eq_of_mem_stageDomain hv.le hlower
    have hfe : T - v ^ 2 < H.stageEndTime first :=
      lt_stageEndTime_of_mem_stageDomain hlower (by
        linarith [H.stageEndTime_le_horizon last, pow_pos hv 2])
    have hstart : H.regularizedStageStart T 0 first < v := by
      apply (Real.sqrt_lt' hv).2
      rcases min_cases (T - 0 ^ 2) (H.stageEndTime first) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · norm_num
        exact pow_pos hv 2
      · linarith
    have hc := (hα ⟨first, le_rfl, hle⟩).1
    rw [uIcc_of_le (hstart.le.trans hend.ge), hend] at hc
    exact (hc v (right_mem_Icc.2 hstart.le)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT hstart) Ioo_subset_Icc_self)

theorem exists_hasHistoryLInitialVector_of_regularizedCost_eq (hv : 0 < v)
    (hT : T ∈ Ioo (H.time last) (H.stageEndTime last)) :
    ∃ Z : TangentSpace ThreeModel (α ⟨last, hle, le_rfl⟩ 0),
      H.HasHistoryLInitialVector T α (α ⟨last, hle, le_rfl⟩ 0) Z := by
  have hnode := node_of_regularCrossing hcross
  obtain ⟨-, hlower⟩ := bounds_of_regularizedCost_eq hle hmin hfin
  have hd : 0 < (T - H.time last) / 2 := by linarith [hT.1]
  set b := min v (Real.sqrt ((T - H.time last) / 2)) with hbdef
  have hb : 0 < b := lt_min hv (Real.sqrt_pos.2 hd)
  have hb2 : b ^ 2 ≤ (T - H.time last) / 2 := by
    calc b ^ 2 ≤ Real.sqrt ((T - H.time last) / 2) ^ 2 :=
          pow_le_pow_left₀ hb.le (min_le_right _ _) 2
      _ = (T - H.time last) / 2 := Real.sq_sqrt hd.le
  obtain ⟨W, hWa, hWb, -, γ, -, heq, -, hZ⟩ :=
    LWindow.exists_stage_initialVector_of_regularizedCost_eq hle hlower hfloor α hα hnode hmin hfin
      hb (min_le_left _ _) (by linarith) hT.2
  obtain ⟨Zx, ⟨hdom, hZeq⟩, -⟩ := hZ
  refine ⟨mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) (γ 0) Zx, last, hle, W, γ 0,
    Zx, hWa, heq ⟨le_rfl, hb.le⟩, rfl, hWb ▸ hdom, fun j r hr => ?_⟩
  obtain ⟨jv, h1, h2⟩ := j
  obtain rfl := le_antisymm h2 h1
  have hsub := W.piece_subset ⟨jv, h1, h2⟩ (hWa ▸ hr)
  rw [hWa, hWb] at hsub
  simp only [Function.comp_apply]
  rw [hZeq hsub]
  exact heq hsub

theorem exists_historyLExp_eq_of_regularizedCost_eq (hv : 0 < v)
    (hT : T ∈ Ioo (H.time last) (H.stageEndTime last)) :
    ∃ Z : H.historyLExpDomain hle T v (α ⟨last, hle, le_rfl⟩ 0),
      H.historyLExp hle T v _ Z = α ⟨first, le_rfl, hle⟩ v := by
  have hgeo := isHistoryLGeodesicOn_of_regularizedCost_eq hle hfloor hα hcross hmin hfin hv
  obtain ⟨Z, hZ⟩ :=
    exists_hasHistoryLInitialVector_of_regularizedCost_eq hle hfloor hα hcross hmin hfin hv hT
  exact ⟨⟨Z, α, hgeo, hZ⟩, historyLExp_eq hv _ hgeo hZ⟩

end Regular

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
