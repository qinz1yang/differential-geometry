import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordFamily

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutoffParameters

/-- Change the static model estimate without changing any time-dependent cutoff scale. -/
def withModelWindow (p : CutoffParameters) (D : ℝ) (m : ℕ) (ε : ℝ)
    (hD : 0 < D) (hε : 0 < ε) : CutoffParameters := {
  p with
  modelRadius := D
  modelRadius_pos := hD
  modelOrder := m
  modelAccuracy := ε
  modelAccuracy_pos := hε }

variable (p : CutoffParameters) (D : ℝ) (m : ℕ) (ε : ℝ) (hD : 0 < D) (hε : 0 < ε)

@[simp] theorem withModelWindow_delta :
    (p.withModelWindow D m ε hD hε).delta = p.delta := rfl

@[simp] theorem withModelWindow_neckRadius :
    (p.withModelWindow D m ε hD hε).neckRadius = p.neckRadius := rfl

@[simp] theorem withModelWindow_protectedRadius :
    (p.withModelWindow D m ε hD hε).protectedRadius = p.protectedRadius := rfl

@[simp] theorem withModelWindow_fixed :
    (p.withModelWindow D m ε hD hε).fixed = p.fixed := rfl

@[simp] theorem withModelWindow_modelRadius :
    (p.withModelWindow D m ε hD hε).modelRadius = D := rfl

@[simp] theorem withModelWindow_modelOrder :
    (p.withModelWindow D m ε hD hε).modelOrder = m := rfl

@[simp] theorem withModelWindow_modelAccuracy :
    (p.withModelWindow D m ε hD hε).modelAccuracy = ε := rfl

@[simp] theorem withModelWindow_recenterConstant :
    (p.withModelWindow D m ε hD hε).recenterConstant = p.recenterConstant := rfl

end CutoffParameters

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
  {D ε : ℝ} {m : ℕ}

/-- Give the selected record a coarser static model view, retaining its necks and backward data. -/
def restrictModelWindow (R : GeometricCutoffRecord H i p)
    (hR : ∀ b, (R.static b).hasCanonicalWindow)
    (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
    (hε : p.modelAccuracy ≤ ε) :
    GeometricCutoffRecord H i
      (p.withModelWindow D m ε hD (p.modelAccuracy_pos.trans_le hε)) := {
  R with
  order_lower := fun α =>
    (max_le_max (Nat.add_le_add_right hm 6)
      (le_refl (2 * ⌊(R.delta α)⁻¹⌋₊ + 4))).trans (R.order_lower α)
  static := fun b => (R.static b).restrictCanonicalWindow (hR b) hD hDp hm hε }

variable (R : GeometricCutoffRecord H i p)
  (hR : ∀ b, (R.static b).hasCanonicalWindow)
  (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
  (hε : p.modelAccuracy ≤ ε)

@[simp] theorem restrictModelWindow_nominalRadius :
    (R.restrictModelWindow hR hD hDp hm hε).nominalRadius = R.nominalRadius := rfl

@[simp] theorem restrictModelWindow_delta :
    (R.restrictModelWindow hR hD hDp hm hε).delta = R.delta := rfl

@[simp] theorem restrictModelWindow_order :
    (R.restrictModelWindow hR hD hDp hm hε).order = R.order := rfl

@[simp] theorem restrictModelWindow_neck :
    (R.restrictModelWindow hR hD hDp hm hε).neck = R.neck := rfl

@[simp] theorem restrictModelWindow_backward :
    (R.restrictModelWindow hR hD hDp hm hε).backward = R.backward := rfl

@[simp] theorem restrictModelWindow_static (b : (H.event i).RetainedBoundaryIndex) :
    (R.restrictModelWindow hR hD hDp hm hε).static b =
      (R.static b).restrictCanonicalWindow (hR b) hD hDp hm hε := rfl

@[simp] theorem restrictModelWindow_static_neck (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).neck = (R.static b).neck := rfl

@[simp] theorem restrictModelWindow_static_Output (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.Output =
      (R.static b).witness.Output := rfl

@[simp] theorem restrictModelWindow_static_metric (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.metric =
      (R.static b).witness.metric := rfl

@[simp] theorem restrictModelWindow_static_inclusion (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).inclusion =
      (R.static b).inclusion := rfl

@[simp] theorem restrictModelWindow_static_cap (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.cap =
      (R.static b).witness.cap := rfl

@[simp] theorem restrictModelWindow_static_retained (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.retained =
      (R.static b).witness.retained := rfl

@[simp] theorem restrictModelWindow_static_collapse (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.collapse =
      (R.static b).witness.collapse := rfl

@[simp] theorem restrictModelWindow_static_window
    (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow D) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).window x =
      (R.static b).window
        ⟨x.val, x.property.trans_le (add_le_add hDp (le_refl 1))⟩ := rfl

@[simp] theorem restrictModelWindow_static_windowMetric
    (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.windowMetric =
      (R.static b).witness.windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add hDp (le_refl 1)) :
          standardCapWindow D ≤ standardCapWindow p.modelRadius) := rfl

/-- The same selected caps retain canonical coverage in a window containing the cap core. -/
theorem hasCanonicalWindow_restrictModelWindow
    (hcap : StandardCap.transitionEnd < D + 1) (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).hasCanonicalWindow :=
  (R.static b).hasCanonicalWindow_restrictCanonicalWindow (hR b) hD hDp hm hε hcap

end GeometricCutoffRecord

namespace RetainedCoreHistory

/-- Restrict the selected family's static model while retaining its eventwise cutoff bounds. -/
theorem IsCanonicalCutoffRecordFamily.restrictModelWindow
    {H : RetainedCoreHistory.{u}} {p₀ p : CutoffParameters} {δbound ρbound : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records)
    {D ε : ℝ} {m : ℕ} (hD : 0 < D) (hDp : D ≤ p.modelRadius)
    (hm : m ≤ p.modelOrder) (hε : p.modelAccuracy ≤ ε)
    (hcap : StandardCap.transitionEnd < D + 1) :
    H.IsCanonicalCutoffRecordFamily
      (p₀.withModelWindow D m ε hD (p.modelAccuracy_pos.trans_le hε)) δbound ρbound
      (fun i => (records i).restrictModelWindow (hrec.2.2.2.2.2.1 i) hD hDp hm hε) := by
  refine ⟨hrec.1, rfl, rfl, rfl, hrec.2.2.2.2.1, ?_,
    hrec.2.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2⟩
  intro i b
  exact (records i).hasCanonicalWindow_restrictModelWindow
    (hrec.2.2.2.2.2.1 i) hD hDp hm hε hcap b

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
