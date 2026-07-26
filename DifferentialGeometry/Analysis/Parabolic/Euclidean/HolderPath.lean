import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Finite-chart parabolic Holder gauges

This file defines the small amount of function-space bookkeeping needed by
the low-regularity Euclidean parametrix.  The gauge records

* uniform spatial derivatives through order two;
* a spatial exponent-`1/2` seminorm of the second derivative;
* a temporal exponent-`1/4` seminorm of the second derivative.

The values lie in `ℝ≥0∞`, so the definitions are total even for an arbitrary
function.  Finiteness, together with `IsParC2Half`, is the actual regularity
condition.  `eFinParC2Half` sums over a finite family of chart/component
indices; no global atlas structure is built into this analytic layer.
-/

noncomputable section

open Set
open scoped ENNReal NNReal BigOperators Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section SupGauge

variable {X F : Type*} [NormedAddCommGroup F]

/-- Extended uniform norm of a function. -/
def eSupNorm (f : X → F) : ℝ≥0∞ :=
  ⨆ x : X, ENNReal.ofReal ‖f x‖

theorem norm_le_eSup (f : X → F) (x : X) :
    ENNReal.ofReal ‖f x‖ ≤ eSupNorm f :=
  le_iSup (fun y : X => ENNReal.ofReal ‖f y‖) x

theorem eSupNorm_le {f : X → F} {C : ℝ≥0∞} :
    eSupNorm f ≤ C ↔ ∀ x : X, ENNReal.ofReal ‖f x‖ ≤ C := by
  simp only [eSupNorm, iSup_le_iff]

end SupGauge

section SpatialGauge

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extended `C^{2,1/2}` gauge on a Euclidean function. -/
def eC2Half (u : V → F) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range 3, eSupNorm (iteratedFDeriv ℝ j u)) +
    eHolderNorm (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 u)

theorem jet_le_eC2Half (u : V → F) {j : ℕ} (hj : j < 3) (x : V) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ j u x‖ ≤ eC2Half u := by
  have hterm : eSupNorm (iteratedFDeriv ℝ j u) ≤
      ∑ q ∈ Finset.range 3, eSupNorm (iteratedFDeriv ℝ q u) :=
    Finset.single_le_sum
      (fun q _ => zero_le (eSupNorm (iteratedFDeriv ℝ q u)))
      (Finset.mem_range.mpr hj)
  exact (norm_le_eSup (iteratedFDeriv ℝ j u) x).trans
    (hterm.trans (by simp only [eC2Half]; exact le_add_right le_rfl))

theorem spaceHolder_le (u : V → F) :
    eHolderNorm (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 u) ≤ eC2Half u := by
  simp only [eC2Half]
  exact le_add_left le_rfl

end SpatialGauge

section PathGauge

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extended parabolic `C^{2,1/2}` path gauge on `[0, τ]`.  The time exponent
of the second spatial derivative is `1/4`, as required by parabolic scaling. -/
def eParC2Half (τ : ℝ) (u : ℝ → V → F) : ℝ≥0∞ :=
  (⨆ t : Set.Icc (0 : ℝ) τ, eC2Half (u t.1)) +
    ⨆ x : V, eHolderNorm (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x)

/-- The non-gauge regularity conditions for a parabolic `C^{2,1/2}` path.
They rule out the default value of `fderiv` at non-differentiability points
and retain time continuity of all lower spatial jets. -/
def IsParC2Half (τ : ℝ) (u : ℝ → V → F) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ 2 (u t)) ∧
    ∀ j : ℕ, j ≤ 2 → ∀ x : V,
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ j (u t) x)
        (Set.Icc (0 : ℝ) τ)

theorem slice_le_ePar (τ : ℝ) (u : ℝ → V → F)
    (t : Set.Icc (0 : ℝ) τ) :
    eC2Half (u t.1) ≤ eParC2Half τ u := by
  have hsup : eC2Half (u t.1) ≤
      ⨆ s : Set.Icc (0 : ℝ) τ, eC2Half (u s.1) :=
    le_iSup (fun s : Set.Icc (0 : ℝ) τ => eC2Half (u s.1)) t
  exact hsup.trans (by simp only [eParC2Half]; exact le_add_right le_rfl)

theorem timeHolder_le (τ : ℝ) (u : ℝ → V → F) (x : V) :
    eHolderNorm (1 / 4 : ℝ≥0)
        (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x) ≤
      eParC2Half τ u := by
  have hsup : eHolderNorm (1 / 4 : ℝ≥0)
        (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x) ≤
      ⨆ y : V, eHolderNorm (1 / 4 : ℝ≥0)
        (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) y) :=
    le_iSup (fun y : V => eHolderNorm (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) y)) x
  exact hsup.trans (by simp only [eParC2Half]; exact le_add_left le_rfl)

theorem parJet_norm_le {τ : ℝ} {u : ℝ → V → F} {C : ℝ≥0}
    (hu : eParC2Half τ u ≤ C) (t : Set.Icc (0 : ℝ) τ)
    {j : ℕ} (hj : j ≤ 2) (x : V) :
    ‖iteratedFDeriv ℝ j (u t.1) x‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (jet_le_eC2Half (u t.1) (by omega) x).trans
    ((slice_le_ePar τ u t).trans hu)

theorem space_holderWith {τ : ℝ} {u : ℝ → V → F} {C : ℝ≥0}
    (hu : eParC2Half τ u ≤ C) (t : Set.Icc (0 : ℝ) τ) :
    HolderWith C (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 (u t.1)) := by
  have he : eHolderNorm (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 (u t.1)) ≤
      (C : ℝ≥0∞) :=
    (spaceHolder_le (u t.1)).trans ((slice_le_ePar τ u t).trans hu)
  have hmem : MemHolder (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 (u t.1)) :=
    eHolderNorm_lt_top.mp (lt_of_le_of_lt he ENNReal.coe_lt_top)
  exact hmem.holderWith.mono (by
    rw [← ENNReal.coe_le_coe]
    exact coe_nnHolderNorm_le_eHolderNorm.trans he)

theorem time_holderWith {τ : ℝ} {u : ℝ → V → F} {C : ℝ≥0}
    (hu : eParC2Half τ u ≤ C) (x : V) :
    HolderWith C (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x) := by
  have he : eHolderNorm (1 / 4 : ℝ≥0)
        (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x) ≤
      (C : ℝ≥0∞) :=
    (timeHolder_le τ u x).trans hu
  have hmem : MemHolder (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u t.1) x) :=
    eHolderNorm_lt_top.mp (lt_of_le_of_lt he ENNReal.coe_lt_top)
  exact hmem.holderWith.mono (by
    rw [← ENNReal.coe_le_coe]
    exact coe_nnHolderNorm_le_eHolderNorm.trans he)

end PathGauge

section FiniteGauge

variable {ι V F : Type*} [DecidableEq ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Sum of parabolic Holder gauges over a finite chart/component index set. -/
def eFinParC2Half (A : Finset ι) (τ : ℝ) (u : ι → ℝ → V → F) : ℝ≥0∞ :=
  ∑ a ∈ A, eParC2Half τ (u a)

/-- A finite family lies in the parabolic Holder ball when every entry has
the genuine differentiability/time-continuity properties and the finite gauge
is bounded by `C`. -/
def InHolderBall (A : Finset ι) (τ : ℝ) (C : ℝ≥0∞)
    (u : ι → ℝ → V → F) : Prop :=
  (∀ a ∈ A, IsParC2Half τ (u a)) ∧ eFinParC2Half A τ u ≤ C

omit [DecidableEq ι] in
theorem entry_le_eFin (A : Finset ι) (τ : ℝ) (u : ι → ℝ → V → F)
    {a : ι} (ha : a ∈ A) :
    eParC2Half τ (u a) ≤ eFinParC2Half A τ u := by
  unfold eFinParC2Half
  exact Finset.single_le_sum (fun b _ => zero_le (eParC2Half τ (u b))) ha

omit [DecidableEq ι] in
theorem fin_space_holder {A : Finset ι} {τ : ℝ} {u : ι → ℝ → V → F}
    {C : ℝ≥0} (hu : eFinParC2Half A τ u ≤ C) {a : ι} (ha : a ∈ A)
    (t : Set.Icc (0 : ℝ) τ) :
    HolderWith C (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 (u a t.1)) :=
  space_holderWith ((entry_le_eFin A τ u ha).trans hu) t

omit [DecidableEq ι] in
theorem fin_time_holder {A : Finset ι} {τ : ℝ} {u : ι → ℝ → V → F}
    {C : ℝ≥0} (hu : eFinParC2Half A τ u ≤ C) {a : ι} (ha : a ∈ A)
    (x : V) :
    HolderWith C (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => iteratedFDeriv ℝ 2 (u a t.1) x) :=
  time_holderWith ((entry_le_eFin A τ u ha).trans hu) x

end FiniteGauge

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
