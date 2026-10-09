import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OrientationDegree
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAncestry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Descendants
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure ObservationTower (P : OrientedThreeStage.{u}) (g : P.Metric) where
  history : ℕ → ObservedHistory.{u}
  horizon_eq : ∀ n : ℕ, (history n).horizon = (n : ℝ)
  initial : ∀ n : ℕ, InitialIdentification P g (history n)
  successor : ∀ n : ℕ, ObservedHistory.SamePresentation
    ((history (n + 1)).restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by rw [horizon_eq]; exact_mod_cast Nat.le_succ n⟩)
      (history n)
  initial_successor : ∀ n : ℕ,
    HEq ((initial (n + 1)).restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by rw [horizon_eq]; exact_mod_cast Nat.le_succ n⟩).map
      (initial n).map

namespace ObservationTower
open ObservedHistory
variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)


def atIndex (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) : ObservedHistory.{u} :=
  (T.history n).restrict ⟨b, hb, by rw [T.horizon_eq]; exact hbn⟩


def initialAtIndex (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    InitialIdentification P g (T.atIndex n b hb hbn) :=
  (T.initial n).restrict ⟨b, hb, by rw [T.horizon_eq]; exact hbn⟩

@[simp] theorem atIndex_horizon (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    (T.atIndex n b hb hbn).horizon = b := rfl

@[simp] theorem initialAtIndex_map (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    (T.initialAtIndex n b hb hbn).map = (T.initial n).map := rfl

def observe (b : ℝ) (hb : 0 ≤ b) : ObservedHistory.{u} :=
  T.atIndex (Nat.ceil b) b hb (Nat.le_ceil b)


def observeInitial (b : ℝ) (hb : 0 ≤ b) : InitialIdentification P g (T.observe b hb) :=
  T.initialAtIndex (Nat.ceil b) b hb (Nat.le_ceil b)

@[simp] theorem observe_horizon (b : ℝ) (hb : 0 ≤ b) : (T.observe b hb).horizon = b := rfl


theorem integer_restrict (n m : ℕ) (hnm : n ≤ m) :
    (T.atIndex m n (Nat.cast_nonneg n) (by exact_mod_cast hnm)).SamePresentation
      (T.history n) := by
  induction m, hnm using Nat.le_induction with
  | base =>
    unfold atIndex
    have ht : (⟨(n : ℝ), Nat.cast_nonneg n,
        by rw [T.horizon_eq]⟩ : Icc (0 : ℝ) (T.history n).horizon) =
        ⟨(T.history n).horizon, (T.history n).horizon_nonneg, le_rfl⟩ :=
      Subtype.ext (T.horizon_eq n).symm
    rw [ht]
    exact restrict_self (T.history n)
  | succ m hnm ih =>
    let a : Icc (0 : ℝ) (T.history (m + 1)).horizon :=
      ⟨(m : ℝ), Nat.cast_nonneg m, by rw [T.horizon_eq]; exact_mod_cast Nat.le_succ m⟩
    let t : Icc (0 : ℝ) ((T.history (m + 1)).restrict a).horizon :=
      ⟨(n : ℝ), Nat.cast_nonneg n, by change (n : ℝ) ≤ (m : ℝ); exact_mod_cast hnm⟩
    have hn := restrict_restrict (T.history (m + 1)) a t
    have hc := SamePresentation.restrict
      ((T.history (m + 1)).restrict a) (T.successor m) t
    exact hn.symm.trans (hc.trans ih)

theorem initial_heq (n m : ℕ) (hnm : n ≤ m) : HEq (T.initial m).map (T.initial n).map := by
  induction m, hnm using Nat.le_induction with
  | base => exact HEq.rfl
  | succ m hnm ih => exact (T.initial_successor m).trans ih


theorem atIndex_compat (n m : ℕ) (hnm : n ≤ m)
    (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    (T.atIndex m b hb (hbn.trans (by exact_mod_cast hnm))).SamePresentation
      (T.atIndex n b hb hbn) := by
  let a : Icc (0 : ℝ) (T.history m).horizon :=
    ⟨(n : ℝ), Nat.cast_nonneg n, by rw [T.horizon_eq]; exact_mod_cast hnm⟩
  let t : Icc (0 : ℝ) ((T.history m).restrict a).horizon := ⟨b, hb, hbn⟩
  have hn := restrict_restrict (T.history m) a t
  have hc := SamePresentation.restrict
    ((T.history m).restrict a) (T.integer_restrict n m hnm) t
  exact hn.symm.trans hc


theorem atIndex_independent (n m : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hbn : b ≤ (n : ℝ)) (hbm : b ≤ (m : ℝ)) :
    (T.atIndex n b hb hbn).SamePresentation (T.atIndex m b hb hbm) := by
  have hn := T.atIndex_compat n (max n m) (le_max_left n m) b hb hbn
  have hm := T.atIndex_compat m (max n m) (le_max_right n m) b hb hbm
  exact hn.symm.trans hm

theorem observe_eq_atIndex (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    (T.observe b hb).SamePresentation (T.atIndex n b hb hbn) :=
  T.atIndex_independent (Nat.ceil b) n b hb (Nat.le_ceil b) hbn


theorem initialAtIndex_heq (n m : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hbn : b ≤ (n : ℝ)) (hbm : b ≤ (m : ℝ)) :
    HEq (T.initialAtIndex n b hb hbn).map (T.initialAtIndex m b hb hbm).map :=
  (T.initial_heq n (max n m) (le_max_left n m)).symm.trans
    (T.initial_heq m (max n m) (le_max_right n m))


theorem observe_restrict (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ((T.observe b hb).restrict ⟨a, ha, hab⟩).SamePresentation (T.observe a ha) := by
  let n := Nat.ceil b
  let t : Icc (0 : ℝ) (T.history n).horizon :=
    ⟨b, hb, by rw [T.horizon_eq]; exact Nat.le_ceil b⟩
  have hn := restrict_restrict (T.history n) t ⟨a, ha, hab⟩
  have he := T.observe_eq_atIndex n a ha (hab.trans (Nat.le_ceil b))
  exact hn.trans he.symm


theorem observeInitial_restrict_heq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    HEq ((T.observeInitial b hb).restrict ⟨a, ha, hab⟩).map (T.observeInitial a ha).map :=
  T.initial_heq (Nat.ceil a) (Nat.ceil b) (Nat.ceil_mono hab)

private theorem eventTimes_subset_of_same {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) : H.eventTimes ⊆ K.eventTimes := by
  rintro t ⟨i, rfl⟩
  have he := R.time_eq i.succ
  change H.time i.succ = K.time (Fin.cast R.count_eq i).succ at he
  exact ⟨Fin.cast R.count_eq i, he.symm⟩

private theorem eventTimes_eq_of_same {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) : H.eventTimes = K.eventTimes :=
  Subset.antisymm (eventTimes_subset_of_same R) (eventTimes_subset_of_same R.symm)


theorem atIndex_eventTimes (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℝ)) :
    (T.atIndex n b hb hbn).eventTimes = (T.history n).eventTimes ∩ Ioc 0 b :=
  (T.history n).restrict_eventTimes _


theorem eventTimes_mono (n m : ℕ) (hnm : n ≤ m) :
    (T.history n).eventTimes ⊆ (T.history m).eventTimes := by
  have he := eventTimes_eq_of_same (T.integer_restrict n m hnm)
  rw [T.atIndex_eventTimes] at he
  rw [← he]
  exact inter_subset_left


def eventTimes : Set ℝ := ⋃ n : ℕ, (T.history n).eventTimes

theorem eventTimes_inter (b : ℝ) (hb : 0 ≤ b) :
    T.eventTimes ∩ Ioc 0 b = (T.observe b hb).eventTimes := by
  apply Subset.antisymm
  · rintro t ⟨ht, htb⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp ht
    let m := max k (Nat.ceil b)
    have hkm : k ≤ m := le_max_left _ _
    have hbm : b ≤ (m : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast le_max_right k (Nat.ceil b))
    have hm : t ∈ (T.atIndex m b hb hbm).eventTimes := by
      rw [T.atIndex_eventTimes]
      exact ⟨T.eventTimes_mono k m hkm hk, htb⟩
    rw [eventTimes_eq_of_same (T.observe_eq_atIndex m b hb hbm)]
    exact hm
  · intro t ht
    change t ∈ (T.atIndex (Nat.ceil b) b hb (Nat.le_ceil b)).eventTimes at ht
    rw [T.atIndex_eventTimes] at ht
    exact ⟨mem_iUnion.mpr ⟨Nat.ceil b, ht.1⟩, ht.2⟩

theorem eventTimes_finite (b : ℝ) (hb : 0 ≤ b) : (T.eventTimes ∩ Ioc 0 b).Finite := by
  rw [T.eventTimes_inter b hb]
  exact Set.finite_range _

theorem observe_unique (b : ℝ) (hb : 0 ≤ b) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H)
    (hH : ∀ n : ℕ, ∀ hn : b ≤ (n : ℝ),
      H.SamePresentation (T.atIndex n b hb hn))
    (hA : ∀ n : ℕ, ∀ hn : b ≤ (n : ℝ),
      HEq A.map (T.initialAtIndex n b hb hn).map) :
    H.SamePresentation (T.observe b hb) ∧ HEq A.map (T.observeInitial b hb).map :=
  ⟨hH (Nat.ceil b) (Nat.le_ceil b), hA (Nat.ceil b) (Nat.le_ceil b)⟩


theorem eventTimes_pos {s : ℝ} (hs : s ∈ T.eventTimes) : 0 < s := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hs
  obtain ⟨i, rfl⟩ := hn
  rw [← (T.history n).time_zero]
  apply (T.history n).time_strictMono
  change 0 < i.val + 1
  omega

theorem eventTimes_finite_Icc (a b : ℝ) : (T.eventTimes ∩ Icc a b).Finite := by
  apply (T.eventTimes_finite (max 0 b) (le_max_left 0 b)).subset
  rintro s ⟨hs, hsb⟩
  exact ⟨hs, T.eventTimes_pos hs, hsb.2.trans (le_max_right 0 b)⟩


theorem observe_slice_stage (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (t : Icc (0 : ℝ) a) :
    (T.observe a ha).stageAt t =
      (T.observe b hb).stageAt ⟨t.1, t.2.1, t.2.2.trans hab⟩ := by
  let H := T.observe b hb
  let u : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
  let R := T.observe_restrict a b ha hb hab
  have hi := SamePresentation.activeStage (H.restrict u) R t
  have hs := R.stage_eq ((H.restrict u).activeStage t)
  rw [hi] at hs
  exact hs.symm.trans (H.restrict_stageAt u t)

theorem observe_slice_metric (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (t : Icc (0 : ℝ) a) :
    HEq ((T.observe a ha).stageMetric ((T.observe a ha).activeStage t) t.1)
      ((T.observe b hb).stageMetric
        ((T.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2.trans hab⟩) t.1) := by
  let H := T.observe b hb
  let u : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
  let R := T.observe_restrict a b ha hb hab
  have hi := SamePresentation.activeStage (H.restrict u) R t
  have hm := R.metric_heq ((H.restrict u).activeStage t) t.1 ((H.restrict u).activeStage_mem t)
  have hm' := hi ▸ hm
  exact hm'.symm.trans (H.restrict_sliceMetric u t)

theorem empty_absorbing (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    [IsEmpty ((T.observe a ha).stage (Fin.last (T.observe a ha).eventCount)).Carrier] :
    IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier := by
  let H := T.observe b hb
  let ta : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
  have he := T.observe_slice_stage a b ha hb hab ⟨a, ha, le_rfl⟩
  have hlastA : (T.observe a ha).activeStage ⟨a, ha, le_rfl⟩ =
      Fin.last (T.observe a ha).eventCount :=
    (T.observe a ha).activeStage_at_horizon
  change (T.observe a ha).stage ((T.observe a ha).activeStage ⟨a, ha, le_rfl⟩) =
    H.stage (H.activeStage ta) at he
  rw [hlastA] at he
  let : IsEmpty (H.stage (H.activeStage ta)).Carrier := he ▸ inferInstance
  have hlast := H.empty_stage_is_last (H.activeStage ta)
  rw [← hlast]
  infer_instance

theorem empty_no_later_events (a : ℝ) (ha : 0 ≤ a)
    [IsEmpty ((T.observe a ha).stage (Fin.last (T.observe a ha).eventCount)).Carrier] :
    ∀ s ∈ T.eventTimes, s ≤ a := by
  intro s hs
  let b := max a s
  have hb : 0 ≤ b := ha.trans (le_max_left a s)
  have hab : a ≤ b := le_max_left a s
  let H := T.observe b hb
  let ta : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
  have hsb : s ∈ H.eventTimes := by
    rw [← T.eventTimes_inter b hb]
    exact ⟨hs, T.eventTimes_pos hs, le_max_right a s⟩
  have he := T.observe_slice_stage a b ha hb hab ⟨a, ha, le_rfl⟩
  change (T.observe a ha).stage ((T.observe a ha).activeStage ⟨a, ha, le_rfl⟩) =
    H.stage (H.activeStage ta) at he
  have hlastA : (T.observe a ha).activeStage ⟨a, ha, le_rfl⟩ =
      Fin.last (T.observe a ha).eventCount :=
    (T.observe a ha).activeStage_at_horizon
  rw [hlastA] at he
  let : IsEmpty (H.stage (H.activeStage ta)).Carrier := he ▸ inferInstance
  have hlast := H.empty_stage_is_last (H.activeStage ta)
  obtain ⟨j, hj⟩ := hsb
  have htime := H.time_strictMono.monotone (Fin.le_last j.succ)
  rw [← hlast] at htime
  exact hj ▸ htime.trans (H.activeStage_time_le ta)
end ObservationTower
namespace InitialIdentification
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

def sourceComponent (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) : ConnectedComponents P.Carrier :=
  A.map.toHomeomorph.symm.continuous.connectedComponentsMap c

private theorem initial_component_map_mem (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier)
    (x : (P.component (A.sourceComponent c)).Carrier) :
    ConnectedComponents.mk (A.map x.1) = c := by
  have hinv : ∀ d : ConnectedComponents (H.stage 0).Carrier,
      A.map.continuous.connectedComponentsMap
        (A.map.symm.continuous.connectedComponentsMap d) = d := by
    intro d
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
    simp only [Continuous.connectedComponentsMap_mk, Diffeomorph.apply_symm_apply]
  have hx := congrArg A.map.continuous.connectedComponentsMap x.property
  change ConnectedComponents.mk (A.map x.1) =
    A.map.continuous.connectedComponentsMap
      (A.map.symm.continuous.connectedComponentsMap c) at hx
  exact hx.trans (hinv c)

private theorem initial_component_inv_mem (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) (y : ((H.stage 0).component c).Carrier) :
    ConnectedComponents.mk (A.map.symm y.1) = A.sourceComponent c := by
  have hy := congrArg A.map.symm.continuous.connectedComponentsMap y.property
  exact hy


def actualComponentDiffeomorph (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    (P.component (A.sourceComponent c)).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯
      ((H.stage 0).component c).Carrier where
  toFun x := ⟨A.map x.1, initial_component_map_mem A c x⟩
  invFun y := ⟨A.map.symm y.1, initial_component_inv_mem A c y⟩
  left_inv x := Subtype.ext (A.map.symm_apply_apply x.1)
  right_inv y := Subtype.ext (A.map.apply_symm_apply y.1)
  contMDiff_toFun := by
    intro x
    exact codRestr_contMDiffAt (V := (H.stage 0).componentOpen c)
      (initial_component_map_mem A c)
      (A.map.contMDiff.comp contMDiff_subtype_val).contMDiffAt
  contMDiff_invFun := by
    intro y
    exact codRestr_contMDiffAt (V := P.componentOpen (A.sourceComponent c))
      (initial_component_inv_mem A c)
      (A.map.symm.contMDiff.comp contMDiff_subtype_val).contMDiffAt

theorem actualComponentDiffeomorph_coe (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier)
    (x : (P.component (A.sourceComponent c)).Carrier) :
    (A.actualComponentDiffeomorph c x).1 = A.map x.1 := rfl


theorem actualComponentDiffeomorph_mfderiv (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier)
    (x : (P.component (A.sourceComponent c)).Carrier) :
    mfderiv ThreeModel ThreeModel (A.actualComponentDiffeomorph c) x =
      mfderiv ThreeModel ThreeModel A.map x.1 := by
  let U := P.componentOpen (A.sourceComponent c)
  let V := (H.stage 0).componentOpen c
  let : ChartedSpace ThreeSpace U := (P.component (A.sourceComponent c)).charts
  let : ChartedSpace ThreeSpace V := ((H.stage 0).component c).charts
  let e := A.actualComponentDiffeomorph c
  have he : MDifferentiableAt ThreeModel ThreeModel (e : U → V) x :=
    e.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  have hv : MDifferentiableAt ThreeModel ThreeModel (Subtype.val : V → (H.stage 0).Carrier)
      (e x) := (contMDiff_subtype_val (I := ThreeModel) (n := ∞)).contMDiffAt.mdifferentiableAt (by decide)
  have hu : MDifferentiableAt ThreeModel ThreeModel (Subtype.val : U → P.Carrier) x :=
    (contMDiff_subtype_val (I := ThreeModel) (n := ∞)).contMDiffAt.mdifferentiableAt (by decide)
  have hA : MDifferentiableAt ThreeModel ThreeModel A.map x.1 :=
    A.map.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  ext v
  have hl := DFunLike.congr_fun (mfderiv_comp x hv he) v
  have hr := DFunLike.congr_fun (mfderiv_comp x hA hu) v
  have hvv := mfderiv_subtype_val_apply (I := ThreeModel) (M := (H.stage 0).Carrier)
    V (e x) (mfderiv ThreeModel ThreeModel (e : U → V) x v)
  have huv := mfderiv_subtype_val_apply (I := ThreeModel) (M := P.Carrier) U x v
  exact hvv.symm.trans (hl.symm.trans (hr.trans
    (congrArg (fun w : ThreeSpace => mfderiv ThreeModel ThreeModel A.map x.1 w) huv)))
theorem actualComponentDiffeomorph_metric (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier)
    (x : (P.component (A.sourceComponent c)).Carrier) (v w : TangentSpace ThreeModel x) :
    ((H.stage 0).componentMetric (H.initialMetric 0) c).inner
      (A.actualComponentDiffeomorph c x)
      (mfderiv ThreeModel ThreeModel (A.actualComponentDiffeomorph c) x v)
      (mfderiv ThreeModel ThreeModel (A.actualComponentDiffeomorph c) x w) =
      (P.componentMetric g (A.sourceComponent c)).inner x v w := by
  have hv := DFunLike.congr_fun (A.actualComponentDiffeomorph_mfderiv c x) v
  have hw := DFunLike.congr_fun (A.actualComponentDiffeomorph_mfderiv c x) w
  change (H.initialMetric 0).inner (A.map x.1) _ _ = g.inner x.1 v w
  rw [hv, hw]
  exact A.metric_eq x.1 v w

theorem actualComponentDiffeomorph_positive (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    PreservesTangentOrientation (P.component (A.sourceComponent c)).orientation
      ((H.stage 0).component c).orientation (A.actualComponentDiffeomorph c) := by
  refine ⟨(A.actualComponentDiffeomorph c).contMDiff, ?_⟩
  intro x
  obtain ⟨hbij, hpos⟩ := A.positive.2 x.1
  have hd := A.actualComponentDiffeomorph_mfderiv c x
  have hbij' : Function.Bijective
      (mfderiv ThreeModel ThreeModel (A.actualComponentDiffeomorph c) x) := by
    rw [hd]
    exact hbij
  refine ⟨hbij', ?_⟩
  unfold PreservesTangentOrientationAt at hpos ⊢
  have he : LinearEquiv.ofBijective
      (mfderiv ThreeModel ThreeModel (A.actualComponentDiffeomorph c) x).toLinearMap hbij' =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel A.map x.1).toLinearMap hbij := by
    ext v
    exact DFunLike.congr_fun hd v
  change Orientation.map (Fin 3) _ (P.orientation.orientation x.1) =
    (H.stage 0).orientation.orientation (A.map x.1)
  rw [he]
  exact hpos

theorem component_diffeomorph (A : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    let P₀ := P.component (A.sourceComponent c)
    let Q₀ := (H.stage 0).component c
    letI : ConnectedSpace P₀.Carrier := P.component_connected (A.sourceComponent c)
    letI : ConnectedSpace Q₀.Carrier := (H.stage 0).component_connected c
    ∃ e : P₀.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q₀.Carrier,
      (∀ x : P₀.Carrier, (e x).1 = A.map x.1) ∧
      PreservesTangentOrientation P₀.orientation Q₀.orientation e ∧
      (∀ (x : P₀.Carrier) (v w : TangentSpace ThreeModel x),
        ((H.stage 0).componentMetric (H.initialMetric 0) c).inner (e x)
          (mfderiv ThreeModel ThreeModel e x v) (mfderiv ThreeModel ThreeModel e x w) =
        (P.componentMetric g (A.sourceComponent c)).inner x v w) ∧
      orientedDegree P₀.orientation Q₀.orientation ⟨e, e.continuous⟩ = 1 := by
  let P₀ := P.component (A.sourceComponent c)
  let Q₀ := (H.stage 0).component c
  let : ConnectedSpace P₀.Carrier := P.component_connected (A.sourceComponent c)
  let : ConnectedSpace Q₀.Carrier := (H.stage 0).component_connected c
  refine ⟨A.actualComponentDiffeomorph c, A.actualComponentDiffeomorph_coe c,
    A.actualComponentDiffeomorph_positive c, A.actualComponentDiffeomorph_metric c, ?_⟩
  exact orientedDegree_diffeomorph P₀.orientation Q₀.orientation
    (A.actualComponentDiffeomorph c) (A.actualComponentDiffeomorph_positive c)

theorem components_simplyConnected (A : InitialIdentification P g H)
    (hP : ∀ c : ConnectedComponents P.Carrier, SimplyConnectedSpace (P.component c).Carrier)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    SimplyConnectedSpace ((H.stage 0).component c).Carrier := by
  let : SimplyConnectedSpace (P.component (A.sourceComponent c)).Carrier := hP _
  exact (A.actualComponentDiffeomorph c).symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem component_classes (A : InitialIdentification P g H)
    (hP : ∀ c : ConnectedComponents P.Carrier, SimplyConnectedSpace (P.component c).Carrier)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    let P₀ := P.component (A.sourceComponent c)
    let Q₀ := (H.stage 0).component c
    letI : ConnectedSpace P₀.Carrier := P.component_connected (A.sourceComponent c)
    letI : ConnectedSpace Q₀.Carrier := (H.stage 0).component_connected c
    letI : SimplyConnectedSpace P₀.Carrier := hP (A.sourceComponent c)
    letI : SimplyConnectedSpace Q₀.Carrier := A.components_simplyConnected hP c
    ∃ e : P₀.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q₀.Carrier,
      (∀ x : P₀.Carrier, (e x).1 = A.map x.1) ∧
      (∀ p : P₀.Carrier, basedHomotopyMap ⟨e, e.continuous⟩ p
        (positiveHomotopyClass P₀.orientation p) = positiveHomotopyClass Q₀.orientation (e p)) ∧
      FreeHomotopyClass.map (contractibleLoopPostcompose ⟨e, e.continuous⟩)
        (positiveFreeContractibleClass P₀.orientation) = positiveFreeContractibleClass Q₀.orientation := by
  let P₀ := P.component (A.sourceComponent c)
  let Q₀ := (H.stage 0).component c
  let : ConnectedSpace P₀.Carrier := P.component_connected (A.sourceComponent c)
  let : ConnectedSpace Q₀.Carrier := (H.stage 0).component_connected c
  let : SimplyConnectedSpace P₀.Carrier := hP (A.sourceComponent c)
  let : SimplyConnectedSpace Q₀.Carrier := A.components_simplyConnected hP c
  obtain ⟨e, he, _, _, hd⟩ := A.component_diffeomorph c
  refine ⟨e, he, ?_, positiveFreeContractibleClass_natural P₀.orientation Q₀.orientation
    ⟨e, e.continuous⟩ hd⟩
  intro p
  have hd' : orientedDegree P₀.orientation Q₀.orientation ⟨e, e.continuous⟩ = 1 := hd
  have htransport :=
    rfs_degree_class_transport P₀.orientation Q₀.orientation ⟨e, e.continuous⟩ p
  rw [hd', zpow_one] at htransport
  exact htransport

end InitialIdentification

namespace ObservationTower
open ObservedHistory
variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)

theorem observe_simplyConnected
    (hP : ∀ c : ConnectedComponents P.Carrier, SimplyConnectedSpace (P.component c).Carrier)
    (b : ℝ) (hb : 0 ≤ b) (j : Fin ((T.observe b hb).eventCount + 1))
    (c : ConnectedComponents ((T.observe b hb).stage j).Carrier) :
    SimplyConnectedSpace (((T.observe b hb).stage j).component c).Carrier :=
  rfs_simply_connected_history (T.observe b hb)
    ((T.observeInitial b hb).components_simplyConnected hP) j c

theorem observe_unique_ancestry (b : ℝ) (hb : 0 ≤ b)
    (terminal : ConnectedComponents ((T.observe b hb).stage
      (Fin.last (T.observe b hb).eventCount)).Carrier) :
    Nonempty (Unique (FiniteAncestorChain (T.observe b hb) terminal)) :=
  exists_unique_finiteAncestorChain (T.observe b hb) terminal

theorem observe_finite_ancestry
    (hP : ∀ c : ConnectedComponents P.Carrier, SimplyConnectedSpace (P.component c).Carrier)
    (b : ℝ) (hb : 0 ≤ b) (parameters : CutoffParameters)
    (cutoff : ∀ j : Fin (T.observe b hb).eventCount,
      GeometricCutoffRecord (T.observe b hb) j parameters)
    (terminal : ConnectedComponents ((T.observe b hb).stage
      (Fin.last (T.observe b hb).eventCount)).Carrier) :
    let H := T.observe b hb
    let h0 := (T.observeInitial b hb).components_simplyConnected hP
    let chain := finiteAncestorChain H terminal
    let hSC := rfs_simply_connected_history H h0
    (∀ j : Fin (H.eventCount + 1),
      let P := (H.stage j).component (chain.component j)
      letI : ConnectedSpace P.Carrier := (H.stage j).component_connected (chain.component j)
      letI : SimplyConnectedSpace P.Carrier := hSC j (chain.component j)
      ∀ q : P.Carrier,
        Function.Injective (fun z : ℤ => positiveHomotopyClass P.orientation q ^ z) ∧
        positiveFreeContractibleClass P.orientation ≠ FreeHomotopyClass.mk
          (ContinuousMap.const (Sphere 2)
            (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop P.Carrier))) ∧
    (∀ j : Fin H.eventCount,
      let G := cutoff j
      let child := chain.component j.succ
      let P := G.Parent child
      let Q := G.Child child
      letI : ConnectedSpace P.Carrier := (H.stage j.castSucc).component_connected
        ((H.event j).transition.childParent child)
      letI : ConnectedSpace Q.Carrier := (H.stage j.succ).component_connected child
      letI : SimplyConnectedSpace P.Carrier := hSC j.castSucc ((H.event j).transition.childParent child)
      letI : SimplyConnectedSpace Q.Carrier := hSC j.succ child
      ∃ K : G.ComparisonSupport child,
        (∀ p : P.Carrier, basedHomotopyMap K.canonicalWholeParentMap p
          (positiveHomotopyClass P.orientation p) =
            positiveHomotopyClass Q.orientation (K.canonicalWholeParentMap p)) ∧
        FreeHomotopyClass.map (contractibleLoopPostcompose K.canonicalWholeParentMap)
          (positiveFreeContractibleClass P.orientation) = positiveFreeContractibleClass Q.orientation) := by
  exact rfs_finite_ancestry (T.observe b hb) parameters cutoff
    ((T.observeInitial b hb).components_simplyConnected hP) terminal

theorem observe_initial_classes
    (hP : ∀ c : ConnectedComponents P.Carrier, SimplyConnectedSpace (P.component c).Carrier)
    (b : ℝ) (hb : 0 ≤ b)
    (terminal : ConnectedComponents ((T.observe b hb).stage
      (Fin.last (T.observe b hb).eventCount)).Carrier) :
    let H := T.observe b hb
    let A := T.observeInitial b hb
    let c := (finiteAncestorChain H terminal).component 0
    let P₀ := P.component (A.sourceComponent c)
    let Q₀ := (H.stage 0).component c
    letI : ConnectedSpace P₀.Carrier := P.component_connected (A.sourceComponent c)
    letI : ConnectedSpace Q₀.Carrier := (H.stage 0).component_connected c
    letI : SimplyConnectedSpace P₀.Carrier := hP (A.sourceComponent c)
    letI : SimplyConnectedSpace Q₀.Carrier := A.components_simplyConnected hP c
    ∃ e : P₀.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q₀.Carrier,
      (∀ x : P₀.Carrier, (e x).1 = A.map x.1) ∧
      (∀ p : P₀.Carrier, basedHomotopyMap ⟨e, e.continuous⟩ p
        (positiveHomotopyClass P₀.orientation p) = positiveHomotopyClass Q₀.orientation (e p)) ∧
      FreeHomotopyClass.map (contractibleLoopPostcompose ⟨e, e.continuous⟩)
        (positiveFreeContractibleClass P₀.orientation) = positiveFreeContractibleClass Q₀.orientation := by
  exact (T.observeInitial b hb).component_classes hP
    ((finiteAncestorChain (T.observe b hb) terminal).component 0)

private theorem stage_component_transport_surjective {P Q : OrientedThreeStage.{u}}
    (h : P = Q) : Function.Surjective
      (fun c : ConnectedComponents P.Carrier => (h ▸ c : ConnectedComponents Q.Carrier)) := by
  cases h
  exact Function.surjective_id

theorem observe_ancestry_restrict (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (terminal : ConnectedComponents ((T.observe b hb).stage
      (Fin.last (T.observe b hb).eventCount)).Carrier) :
    let H := T.observe b hb
    let S := T.observe a ha
    let t : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
    let R := (T.observe_restrict a b ha hb hab).symm
    let oldIndex : Fin (S.eventCount + 1) → Fin (H.eventCount + 1) := fun j =>
      Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage t).isLt) 1)
        (Fin.cast (congrArg (· + 1) R.count_eq) j)
    ∃ earlier : ConnectedComponents (S.stage (Fin.last S.eventCount)).Carrier,
      R.componentToOther (Fin.last S.eventCount) earlier =
        (finiteAncestorChain H terminal).component (oldIndex (Fin.last S.eventCount)) ∧
      ∀ j : Fin (S.eventCount + 1), R.componentToOther j
        ((finiteAncestorChain S earlier).component j) =
        (finiteAncestorChain H terminal).component (oldIndex j) := by
  let H := T.observe b hb
  let S := T.observe a ha
  let t : Icc (0 : ℝ) H.horizon := ⟨a, ha, hab⟩
  let R := (T.observe_restrict a b ha hb hab).symm
  let oldIndex : Fin (S.eventCount + 1) → Fin (H.eventCount + 1) := fun j =>
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage t).isLt) 1)
      (Fin.cast (congrArg (· + 1) R.count_eq) j)
  let terminalK := (finiteAncestorChain H terminal).component (H.activeStage t)
  have hf := H.finite_ancestry_restrict t terminal
  obtain ⟨earlier, hearlier⟩ := stage_component_transport_surjective
    (R.stage_eq (Fin.last S.eventCount))
    ((finiteAncestorChain H terminal).component (oldIndex (Fin.last S.eventCount)))
  refine ⟨earlier, hearlier, ?_⟩
  have hterminal : R.componentToOther (Fin.last S.eventCount) earlier =
      (finiteAncestorChain (H.restrict t) terminalK).component
        (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last S.eventCount)) :=
    hearlier.trans (hf _).symm
  intro j
  exact (R.finite_ancestry earlier terminalK hterminal j).trans (hf _)
end ObservationTower
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
