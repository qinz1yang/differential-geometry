import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Doubling_O16
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation

/-!
# CH12-O16 G2b-(b1), final slab: backward scalar doubling on a closed slab

Same as `incoming_scalar_backward_doubling_O16` for a `ClosedSlab` (interior time derivative from
`differentiableAt_scalar_time`), and its `P2_O2` (second clause) specialisation to the final slab of
`F.tower.history n`.
-/

set_option autoImplicit false

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.PDE.RicciFlow
open scoped NNReal

namespace GC.LongTime.Ch12

universe u

/-- Backward doubling at a fixed point of a closed slab flow, interior window. -/
theorem closed_scalar_backward_doubling_O16 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.ClosedSlab a s) (y : P.Carrier) {θ : ℝ → ℝ} {C : ℝ≥0}
    (hP2 : ∀ t ∈ Ioo a s, θ t < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {c b M : ℝ} (hM : 0 < M) (hcb : Icc c b ⊆ Ioo a s) (hθ : ∀ t ∈ Icc c b, θ t ≤ M)
    (hb : G.flow.scalar b y ≤ M) (hwin : b - c ≤ (12 * ((C : ℝ) + 1) * M)⁻¹) :
    ∀ t ∈ Icc c b, G.flow.scalar t y ≤ 2 * M := by
  have hder : ∀ t ∈ Icc c b, DifferentiableAt ℝ (fun v => G.flow.scalar v y) t := by
    intro t ht
    exact DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.differentiableAt_scalar_time
      G.equation (hcb ht) y
  have hC1 : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  refine backward_doubling_O16 hC1 hM ?_ ?_ ?_ hb hwin
  · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hder t (Ioc_subset_Icc_self ht)).differentiableWithinAt
  · intro t ht hMt
    have ht' : t ∈ Icc c b := Ioc_subset_Icc_self ht
    have h1 := hP2 t (hcb ht') (lt_of_le_of_lt (hθ t ht') hMt)
    have h2 : (C : ℝ) * G.flow.scalar t y ^ 2 ≤ ((C : ℝ) + 1) * G.flow.scalar t y ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    exact h1.trans h2

section Profile

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **(b1), final slab**: backward doubling at a fixed point of the final slab of
`F.tower.history n`, from the second clause of `P2_O2`. -/
theorem final_scalar_backward_doubling_O16 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime) (n : ℕ)
    (h : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
      (F.tower.history n).horizon)
    (y : ((F.tower.history n).stage (Fin.last (F.tower.history n).eventCount)).Carrier)
    {c b M : ℝ} (hM : 0 < M)
    (hcb : Icc c b ⊆ Ioo ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))
      (F.tower.history n).horizon)
    (hneck : ∀ t ∈ Icc c b, (Hp.parameters.neckRadius t ^ 2)⁻¹ ≤ M)
    (hb : ((F.tower.history n).finalSlab h).flow.scalar b y ≤ M)
    (hwin : b - c ≤ (12 * ((Ctime : ℝ) + 1) * M)⁻¹) :
    ∀ t ∈ Icc c b, ((F.tower.history n).finalSlab h).flow.scalar t y ≤ 2 * M :=
  closed_scalar_backward_doubling_O16 ((F.tower.history n).finalSlab h) y
    (θ := fun t => (Hp.parameters.neckRadius t ^ 2)⁻¹) (fun t ht hlt => hP2.2 n h y t ht hlt)
    hM hcb hneck hb hwin

end Profile

end GC.LongTime.Ch12
