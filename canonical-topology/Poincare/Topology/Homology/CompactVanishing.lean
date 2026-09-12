import Poincare.Topology.Homology.EuclideanLocalVanishing
import Poincare.Topology.Homology.LocalStarConvex
import Poincare.Topology.Homology.RelativeVanishing

noncomputable section

open CategoryTheory Module Set

universe u

namespace Poincare.Topology

private theorem integralRelativeHomology_empty_complement_subsingleton
    {X : Type u} [TopologicalSpace X] (n : ℕ) :
    Subsingleton (integralRelativeHomology n (∅ : Set X)ᶜ) := by
  simpa only [compl_empty] using integralRelativeHomology_univ_subsingleton (X := X) n

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem integralRelativeHomology_subsingleton_of_bounded_starConvex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E} {c : E}
    (hs : StarConvex ℝ c K) (hb : Bornology.IsBounded K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact integralRelativeHomology_empty_complement_subsingleton n
  · let := integralLocalHomology_subsingleton_of_finrank_lt n hn c
    let e := (integralBoundedStarConvexLocalHomologyIso n (hs.mem hK) hs hb).toLinearEquiv
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

theorem integralRelativeHomology_subsingleton_of_bounded_convex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E}
    (hK : Convex ℝ K) (hb : Bornology.IsBounded K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact integralRelativeHomology_empty_complement_subsingleton n
  · exact integralRelativeHomology_subsingleton_of_bounded_starConvex n hn (hK.starConvex hc) hb

theorem integralRelativeHomology_subsingleton_of_compact_convex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E}
    (hK : Convex ℝ K) (hc : IsCompact K) :
    Subsingleton (integralRelativeHomology n Kᶜ) :=
  integralRelativeHomology_subsingleton_of_bounded_convex n hn hK hc.isBounded

end Poincare.Topology

end
