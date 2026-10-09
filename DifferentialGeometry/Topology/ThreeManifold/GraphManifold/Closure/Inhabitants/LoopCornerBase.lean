import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBundle

/-!
The true compact cornered base adds the actual two corner fills to the rounded orbit annulus.
Both genuine charts have the exact positive quadrant, with the same rounding off unit rectangles.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def loopCornerFill : Set (ℝ × ℝ) :=
  (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ∩ {v | standardRimRounding v ≤ 0}

theorem loopCornerFill_compact : IsCompact loopCornerFill :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le contDiff_standardRimRounding.continuous continuous_const)

theorem loopCornerFill_source : loopCornerFill ⊆ rimBox 2 := by
  intro v hv
  change |v.1| < 2 ∧ |v.2| < 2
  rw [abs_of_nonneg hv.1.1.1, abs_of_nonneg hv.1.2.1]
  exact ⟨by linarith [hv.1.1.2], by linarith [hv.1.2.2]⟩

def loopCircleCornerBase : Set loopCircleBase :=
  {z | loopCircleBaseRounding z ≤ 0} ∪ ⋃ b : Bool, loopBaseCorner b '' loopCornerFill

theorem loopCircleCornerBase_compact : IsCompact loopCircleCornerBase := by
  refine loopCircleBaseRounding_compact.union (isCompact_iUnion fun b => ?_)
  apply loopCornerFill_compact.image_of_continuousOn
  apply (loopBaseCorner b).contMDiffOn_toFun.continuousOn.mono
  rw [loopBaseCorner_source]
  exact loopCornerFill_source

private theorem baseCorners_pairwise : Pairwise fun b b' : Bool =>
    Disjoint (loopBaseCorner b).target (loopBaseCorner b').target := by
  intro b b' h
  cases b <;> cases b'
  · exact False.elim (h rfl)
  · exact loopBaseCorner_disjoint
  · exact loopBaseCorner_disjoint.symm
  · exact False.elim (h rfl)

theorem loopCircleCornerBase_chart (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopBaseCorner b v ∈ loopCircleCornerBase ↔ 0 ≤ v.1 ∧ 0 ≤ v.2 := by
  constructor
  · intro hz
    rcases hz with hr | hf
    · have hs : 0 ≤ standardRimRounding v := by
        change loopCircleBaseRounding (loopBaseCorner b v) ≤ 0 at hr
        rw [loopCircleBaseRounding_corner b v hv] at hr
        linarith
      exact nonneg_of_standardRimRounding_nonneg v hs
    · obtain ⟨b', hb'⟩ := mem_iUnion.mp hf
      obtain ⟨w, hw, he⟩ := hb'
      have hws : w ∈ (loopBaseCorner b').source := by
        rw [loopBaseCorner_source]
        exact loopCornerFill_source hw
      have hvs : v ∈ (loopBaseCorner b).source := by
        rw [loopBaseCorner_source]
        exact hv
      have hbb : b' = b := by
        by_contra hn
        have hd := baseCorners_pairwise hn
        exact Set.disjoint_left.mp hd ((loopBaseCorner b').map_source hws)
          (he.symm ▸ (loopBaseCorner b).map_source hvs)
      subst b'
      have hew : w = v := (loopBaseCorner b).injOn hws hvs he
      subst w
      exact ⟨hw.1.1.1, hw.1.2.1⟩
  · rintro ⟨hx, hy⟩
    by_cases hs : 0 ≤ standardRimRounding v
    · left
      change loopCircleBaseRounding (loopBaseCorner b v) ≤ 0
      rw [loopCircleBaseRounding_corner b v hv]
      linarith
    · have hh := band_of_standardRimRounding_neg v hx hy (not_le.mp hs)
      right
      refine mem_iUnion.mpr ⟨b, ⟨v, ?_, rfl⟩⟩
      exact ⟨⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩, (not_le.mp hs).le⟩

theorem loopCircleCornerBase_rounding_agree :
    {z : loopCircleBase | loopCircleBaseRounding z ≤ 0} \
      (⋃ b : Bool, loopBaseCorner b '' rimBox 1) =
    loopCircleCornerBase \ (⋃ b : Bool, loopBaseCorner b '' rimBox 1) := by
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨Or.inl hz, hn⟩
  · rintro ⟨hz, hn⟩
    rcases hz with hr | hf
    · exact ⟨hr, hn⟩
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hf
      obtain ⟨v, hv, rfl⟩ := hb
      have hnot : v ∉ rimBox 1 := by
        intro hmem
        exact hn (mem_iUnion.mpr ⟨b, mem_image_of_mem (loopBaseCorner b) hmem⟩)
      have hpos := (standardRimRounding_nonneg_iff hnot).mpr ⟨hv.1.1.1, hv.1.2.1⟩
      have he : standardRimRounding v = 0 := le_antisymm hv.2 hpos
      refine ⟨?_, hn⟩
      change loopCircleBaseRounding (loopBaseCorner b v) ≤ 0
      rw [loopCircleBaseRounding_corner b v (loopCornerFill_source hv), he]
      norm_num

theorem loopCircleCornerBase_centres (b : Bool) :
    loopBaseCorner b (0, 0) ∈ loopCircleCornerBase := by
  apply (loopCircleCornerBase_chart b (by constructor <;> norm_num)).mpr
  exact ⟨le_rfl, le_rfl⟩

end GC.GraphManifold.Assembly
