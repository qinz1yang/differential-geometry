import DifferentialGeometry.Topology.MetricSpace.ProductEnds
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

open Set Metric

namespace IsometryEquiv

theorem isBounded_factor_of_unbounded_components
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [PreconnectedSpace Y]
    (e : X ≃ᵢ WithLp 2 (ℝ × Y))
    {K : Set X} (hK : Bornology.IsBounded K) {a b : X}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    Bornology.IsBounded (univ : Set Y) := by
  classical
  by_contra hY
  let h : X ≃ₜ ℝ × Y := e.toHomeomorph.trans (WithLp.homeomorphProd 2 ℝ Y)
  have hlip : LipschitzWith 1 h := by
    change LipschitzWith 1 (WithLp.ofLp ∘ e)
    simpa using (WithLp.prod_lipschitzWith_ofLp 2 ℝ Y).comp e.isometry.lipschitzWith
  have hanti : AntilipschitzWith ((2 : NNReal) ^ (1 / (2 : ENNReal)).toReal) h := by
    change AntilipschitzWith _ (WithLp.ofLp ∘ e)
    simpa using (WithLp.prod_antilipschitzWith_ofLp 2 ℝ Y).comp e.isometry.antilipschitzWith
  have himage (x : X) (hx : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
      h '' connectedComponentIn Kᶜ x = connectedComponentIn (h '' K)ᶜ (h x) := by
    have hxK : x ∈ Kᶜ := by
      by_contra hxK
      have hh : connectedComponentIn Kᶜ x = ∅ := connectedComponentIn_eq_empty hxK
      exact hx (hh ▸ Bornology.isBounded_empty)
    rw [h.image_connectedComponentIn hxK]
    congr 1
    exact h.toEquiv.image_compl K
  have hunbounded (x : X) (hx : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
      ¬ Bornology.IsBounded (connectedComponentIn (h '' K)ᶜ (h x)) := by
    rw [← himage x hx]
    intro hbnd
    exact hx ((hanti.isBounded_preimage hbnd).subset (subset_preimage_image h _))
  have heq := connectedComponentIn_compl_prod_eq_of_unbounded hY (hlip.isBounded_image hK)
    (hunbounded a ha) (hunbounded b hb)
  rw [← himage a ha, ← himage b hb] at heq
  exact hab (h.injective.image_injective heq)

end IsometryEquiv
