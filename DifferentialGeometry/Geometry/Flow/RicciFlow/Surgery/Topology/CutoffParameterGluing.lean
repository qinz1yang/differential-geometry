import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace CutoffParameters

def diagonal (p : ℕ → CutoffParameters) : CutoffParameters :=
  { p 0 with
    delta := fun t => (p (Nat.ceil t)).delta t
    neckRadius := fun t => (p (Nat.ceil t)).neckRadius t
    protectedRadius := fun t => (p (Nat.ceil t)).protectedRadius t
    delta_pos := fun t ht => (p (Nat.ceil t)).delta_pos t ht
    delta_lt_one := fun t ht => (p (Nat.ceil t)).delta_lt_one t ht
    neckRadius_pos := fun t ht => (p (Nat.ceil t)).neckRadius_pos t ht
    protectedRadius_pos := fun t ht => (p (Nat.ceil t)).protectedRadius_pos t ht }

theorem diagonal_eq_on_prefix (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t ∧
      (p m).neckRadius t = (p n).neckRadius t ∧
      (p m).protectedRadius t = (p n).protectedRadius t)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (n : ℝ)) :
    (diagonal p).delta t = (p n).delta t ∧
    (diagonal p).neckRadius t = (p n).neckRadius t ∧
    (diagonal p).protectedRadius t = (p n).protectedRadius t :=
  hcompat (Nat.ceil t) n (Nat.ceil_le.mpr ht.2) t ⟨ht.1, Nat.le_ceil t⟩

theorem diagonal_eval_of_nonpos (p : ℕ → CutoffParameters) {t : ℝ} (ht : t ≤ 0) :
    (diagonal p).delta t = (p 0).delta t ∧
    (diagonal p).neckRadius t = (p 0).neckRadius t ∧
    (diagonal p).protectedRadius t = (p 0).protectedRadius t := by
  have hceil : Nat.ceil t = 0 := Nat.ceil_eq_zero.mpr ht
  simp only [diagonal, hceil, and_self]

theorem diagonal_delta_eq (p : ℕ → CutoffParameters) {δ : ℝ → ℝ}
    (hdelta : ∀ n, (p n).delta = δ) : (diagonal p).delta = δ := by
  funext t
  exact congrFun (hdelta (Nat.ceil t)) t

theorem diagonal_neckRadius_antitone (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).neckRadius t = (p n).neckRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ))) :
    AntitoneOn (diagonal p).neckRadius (Ici 0) := by
  intro s hs t ht hst
  change (p (Nat.ceil t)).neckRadius t ≤ (p (Nat.ceil s)).neckRadius s
  rw [hcompat (Nat.ceil s) (Nat.ceil t) (Nat.ceil_mono hst) s ⟨hs, Nat.le_ceil s⟩]
  exact hanti (Nat.ceil t) ⟨hs, hst.trans (Nat.le_ceil t)⟩ ⟨ht, Nat.le_ceil t⟩ hst

def spliceAfter (p q : CutoffParameters) (T : ℝ) : CutoffParameters :=
  { p with
    delta := fun t => if t ≤ T then p.delta t else q.delta t
    neckRadius := fun t => if t ≤ T then p.neckRadius t else q.neckRadius t
    protectedRadius := fun t => if t ≤ T then p.protectedRadius t else q.protectedRadius t
    delta_pos := fun t ht => by split <;> [exact p.delta_pos t ht; exact q.delta_pos t ht]
    delta_lt_one := fun t ht => by
      split <;> [exact p.delta_lt_one t ht; exact q.delta_lt_one t ht]
    neckRadius_pos := fun t ht => by
      split <;> [exact p.neckRadius_pos t ht; exact q.neckRadius_pos t ht]
    protectedRadius_pos := fun t ht => by
      split <;> [exact p.protectedRadius_pos t ht; exact q.protectedRadius_pos t ht] }

theorem spliceAfter_eval_of_le (p q : CutoffParameters) {T t : ℝ} (ht : t ≤ T) :
    (p.spliceAfter q T).delta t = p.delta t ∧
      (p.spliceAfter q T).neckRadius t = p.neckRadius t ∧
      (p.spliceAfter q T).protectedRadius t = p.protectedRadius t := by
  simp only [spliceAfter, ite_eq_left ht, and_self]

theorem spliceAfter_eval_of_lt (p q : CutoffParameters) {T t : ℝ} (ht : T < t) :
    (p.spliceAfter q T).delta t = q.delta t ∧
      (p.spliceAfter q T).neckRadius t = q.neckRadius t ∧
      (p.spliceAfter q T).protectedRadius t = q.protectedRadius t := by
  simp only [spliceAfter, ite_eq_right (not_le.mpr ht), and_self]

theorem spliceAfter_neckRadius_antitone (p q : CutoffParameters) (T : ℝ)
    (hp : AntitoneOn p.neckRadius (Icc 0 T))
    (hq : AntitoneOn q.neckRadius (Ici T))
    (hjoin : q.neckRadius T ≤ p.neckRadius T) :
    AntitoneOn (p.spliceAfter q T).neckRadius (Ici 0) := by
  intro s hs t ht hst
  change (if t ≤ T then p.neckRadius t else q.neckRadius t) ≤
    if s ≤ T then p.neckRadius s else q.neckRadius s
  by_cases hsT : s ≤ T
  · by_cases htT : t ≤ T
    · rw [ite_eq_left htT, ite_eq_left hsT]
      exact hp ⟨hs, hsT⟩ ⟨ht, htT⟩ hst
    · rw [ite_eq_right htT, ite_eq_left hsT]
      have hTt : T ≤ t := (lt_of_not_ge htT).le
      exact (hq (show T ∈ Ici T from le_refl T) hTt hTt).trans
        (hjoin.trans (hp ⟨hs, hsT⟩ ⟨hs.trans hsT, le_rfl⟩ hsT))
  · have hTt : T < t := (lt_of_not_ge hsT).trans_le hst
    rw [ite_eq_right (not_le.mpr hTt), ite_eq_right hsT]
    exact hq (lt_of_not_ge hsT).le hTt.le hst

end CutoffParameters

namespace GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {p : ℕ → CutoffParameters} {n : ℕ}

def diagonalParameters (R : GeometricCutoffRecord H i (p n))
    (hstatic : (p n).fixed = (p 0).fixed ∧
      (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧
      (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧
      (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (ht : H.time i.succ ≤ (n : ℝ)) :
    GeometricCutoffRecord H i (CutoffParameters.diagonal p) :=
  let htime := CutoffParameters.diagonal_eq_on_prefix p hcompat n
    ⟨by
      rw [← H.time_zero]
      exact H.time_strictMono.monotone (Fin.zero_le i.succ), ht⟩
  R.congrParameters htime.1.symm htime.2.1.symm htime.2.2.symm
    hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2

theorem diagonalParameters_preserves (R : GeometricCutoffRecord H i (p n))
    (hstatic : (p n).fixed = (p 0).fixed ∧
      (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧
      (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧
      (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (ht : H.time i.succ ≤ (n : ℝ)) :
    (R.diagonalParameters hstatic hcompat ht).nominalRadius = R.nominalRadius ∧
      (R.diagonalParameters hstatic hcompat ht).delta = R.delta ∧
      (R.diagonalParameters hstatic hcompat ht).order = R.order ∧
      HEq (R.diagonalParameters hstatic hcompat ht).neck R.neck ∧
      HEq (R.diagonalParameters hstatic hcompat ht).static R.static := by
  have hnonneg : 0 ≤ H.time i.succ := by
    rw [← H.time_zero]
    exact H.time_strictMono.monotone (Fin.zero_le i.succ)
  let htime := CutoffParameters.diagonal_eq_on_prefix p hcompat n ⟨hnonneg, ht⟩
  exact ⟨R.congrParameters_nominalRadius (q := CutoffParameters.diagonal p)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_delta (q := CutoffParameters.diagonal p)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_order (q := CutoffParameters.diagonal p)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_neck_heq (q := CutoffParameters.diagonal p)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_static_heq (q := CutoffParameters.diagonal p)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2⟩

def spliceAfterParametersOfLE {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    {T : ℝ} (ht : H.time i.succ ≤ T) :
    GeometricCutoffRecord H i (p.spliceAfter q T) :=
  let htime := p.spliceAfter_eval_of_le q ht
  R.congrParameters htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl

theorem spliceAfterParametersOfLE_preserves {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {T : ℝ} (ht : H.time i.succ ≤ T) :
    (R.spliceAfterParametersOfLE (q := q) ht).nominalRadius = R.nominalRadius ∧
      (R.spliceAfterParametersOfLE (q := q) ht).delta = R.delta ∧
      (R.spliceAfterParametersOfLE (q := q) ht).order = R.order ∧
      HEq (R.spliceAfterParametersOfLE (q := q) ht).neck R.neck ∧
      HEq (R.spliceAfterParametersOfLE (q := q) ht).static R.static := by
  let htime := p.spliceAfter_eval_of_le q ht
  exact ⟨R.congrParameters_nominalRadius (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl,
    R.congrParameters_delta (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl,
    R.congrParameters_order (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl,
    R.congrParameters_neck_heq (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl,
    R.congrParameters_static_heq (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm rfl rfl rfl rfl rfl⟩

def spliceAfterParametersOfLT {p q : CutoffParameters} (R : GeometricCutoffRecord H i q)
    (hstatic : q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
      q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
      q.recenterConstant = p.recenterConstant)
    {T : ℝ} (ht : T < H.time i.succ) :
    GeometricCutoffRecord H i (p.spliceAfter q T) :=
  let htime := p.spliceAfter_eval_of_lt q ht
  R.congrParameters htime.1.symm htime.2.1.symm htime.2.2.symm
    hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2

theorem spliceAfterParametersOfLT_preserves {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i q)
    (hstatic : q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
      q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
      q.recenterConstant = p.recenterConstant)
    {T : ℝ} (ht : T < H.time i.succ) :
    (R.spliceAfterParametersOfLT hstatic ht).nominalRadius = R.nominalRadius ∧
      (R.spliceAfterParametersOfLT hstatic ht).delta = R.delta ∧
      (R.spliceAfterParametersOfLT hstatic ht).order = R.order ∧
      HEq (R.spliceAfterParametersOfLT hstatic ht).neck R.neck ∧
      HEq (R.spliceAfterParametersOfLT hstatic ht).static R.static := by
  let htime := p.spliceAfter_eval_of_lt q ht
  exact ⟨R.congrParameters_nominalRadius (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_delta (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_order (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_neck_heq (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2,
    R.congrParameters_static_heq (q := p.spliceAfter q T)
      htime.1.symm htime.2.1.symm htime.2.2.symm
      hstatic.1 hstatic.2.1 hstatic.2.2.1 hstatic.2.2.2.1 hstatic.2.2.2.2⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
