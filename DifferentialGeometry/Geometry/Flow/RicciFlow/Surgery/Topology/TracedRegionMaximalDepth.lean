import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Topology.Sequences.NestedSubsequence

set_option autoImplicit false

noncomputable section

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

def DepthExtendable (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (σ : ℕ → ℕ) (T : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop,
    (H (σ i)).isTracedRegion (t (σ i)) (y (σ i)) (A / Real.sqrt (R (σ i))) (T / R (σ i))
      (K * R (σ i))

variable {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
  {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {σ σ' ψ : ℕ → ℕ} {T T' : ℝ}

theorem DepthExtendable.mono_depth (h : DepthExtendable H t y R σ T) (hR : ∀ n, 0 < R n)
    (hT' : 0 < T') (hle : T' ≤ T) : DepthExtendable H t y R σ T' := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  refine ⟨K, hK, hev.mono fun i hi => hi.mono_depth (div_pos hT' (hR (σ i))) ?_⟩
  exact div_le_div_of_nonneg_right hle (hR (σ i)).le

theorem DepthExtendable.comp (h : DepthExtendable H t y R σ T) (hψ : StrictMono ψ) :
    DepthExtendable H t y R (σ ∘ ψ) T := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  exact ⟨K, hK, hψ.tendsto_atTop.eventually hev⟩

theorem DepthExtendable.congr (h : DepthExtendable H t y R σ T)
    (hσ : ∀ᶠ i in atTop, σ i = σ' i) : DepthExtendable H t y R σ' T := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  refine ⟨K, hK, ?_⟩
  have key : ∀ m m' : ℕ, m = m' →
      (H m).isTracedRegion (t m) (y m) (A / Real.sqrt (R m)) (T / R m) (K * R m) →
      (H m').isTracedRegion (t m') (y m') (A / Real.sqrt (R m')) (T / R m') (K * R m') := by
    rintro m _ rfl hm
    exact hm
  filter_upwards [hev, hσ] with i hi he
  exact key _ _ he hi

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
