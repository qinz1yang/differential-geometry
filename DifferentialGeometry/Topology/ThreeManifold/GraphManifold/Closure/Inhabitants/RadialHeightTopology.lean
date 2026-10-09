import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleRegion

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_TopologyX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_TopologyX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem negativeSeamTime_open : IsOpenMap (fun q : radialNegativeSeam => q.val.2) :=
  isOpenMap_snd.comp radialNegativeSeam.isOpen.isOpenMap_subtype_val

theorem height_no_interior_le (t : ℝ) (hlo : -1 < t) (hhi : t < 0)
    (p : carrier.Carrier) (hp : height p = t) :
    p ∉ interior {r : carrier.Carrier | height r ≤ t} := by
  intro hint
  obtain ⟨q, hq⟩ := exists_negativeSeam_at p (hp.symm ▸ hlo) (hp.symm ▸ hhi)
  have hqt : q.val.2 = t :=
    (height_negativeSeam q).symm.trans ((congrArg height hq).trans hp)
  let U : Set radialNegativeSeam := negativeSeamToCarrier ⁻¹'
    interior {r : carrier.Carrier | height r ≤ t}
  have hU : IsOpen U := isOpen_interior.preimage negativeSeamToCarrier_smooth.continuous
  have hqU : q ∈ U := by
    change negativeSeamToCarrier q ∈ interior {r : carrier.Carrier | height r ≤ t}
    rw [hq]
    exact hint
  have him : (fun q : radialNegativeSeam => q.val.2) '' U ⊆ Iic t := by
    rintro s ⟨r, hr, rfl⟩
    have hm := interior_subset hr
    change height (negativeSeamToCarrier r) ≤ t at hm
    rw [height_negativeSeam] at hm
    exact hm
  have ht : q.val.2 ∈ interior (Iic t) :=
    interior_maximal him (negativeSeamTime_open U hU) (mem_image_of_mem _ hqU)
  rw [interior_Iic, hqt] at ht
  exact lt_irrefl t ht

theorem height_no_interior_ge (t : ℝ) (hlo : -1 < t) (hhi : t < 0)
    (p : carrier.Carrier) (hp : height p = t) :
    p ∉ interior {r : carrier.Carrier | t ≤ height r} := by
  intro hint
  obtain ⟨q, hq⟩ := exists_negativeSeam_at p (hp.symm ▸ hlo) (hp.symm ▸ hhi)
  have hqt : q.val.2 = t :=
    (height_negativeSeam q).symm.trans ((congrArg height hq).trans hp)
  let U : Set radialNegativeSeam := negativeSeamToCarrier ⁻¹'
    interior {r : carrier.Carrier | t ≤ height r}
  have hU : IsOpen U := isOpen_interior.preimage negativeSeamToCarrier_smooth.continuous
  have hqU : q ∈ U := by
    change negativeSeamToCarrier q ∈ interior {r : carrier.Carrier | t ≤ height r}
    rw [hq]
    exact hint
  have him : (fun q : radialNegativeSeam => q.val.2) '' U ⊆ Ici t := by
    rintro s ⟨r, hr, rfl⟩
    have hm := interior_subset hr
    change t ≤ height (negativeSeamToCarrier r) at hm
    rw [height_negativeSeam] at hm
    exact hm
  have ht : q.val.2 ∈ interior (Ici t) :=
    interior_maximal him (negativeSeamTime_open U hU) (mem_image_of_mem _ hqU)
  rw [interior_Ici, hqt] at ht
  exact lt_irrefl t ht

theorem height_interior_le (t : ℝ) (hlo : -1 < t) (hhi : t < 0) :
    interior {p : carrier.Carrier | height p ≤ t} = {p | height p < t} := by
  ext p
  constructor
  · intro hp
    have hm := interior_subset hp
    change height p ≤ t at hm
    change height p < t
    by_contra! hn
    exact height_no_interior_le t hlo hhi p (le_antisymm hm hn) hp
  · intro hp
    have hs : {r : carrier.Carrier | height r < t} ⊆ {r | height r ≤ t} :=
      fun r hr => (show height r < t from hr).le
    exact interior_maximal hs (isOpen_lt height_continuous continuous_const) hp

theorem height_interior_ge (t : ℝ) (hlo : -1 < t) (hhi : t < 0) :
    interior {p : carrier.Carrier | t ≤ height p} = {p | t < height p} := by
  ext p
  constructor
  · intro hp
    have hm := interior_subset hp
    change t ≤ height p at hm
    change t < height p
    by_contra! hn
    exact height_no_interior_ge t hlo hhi p (le_antisymm hn hm) hp
  · intro hp
    have hs : {r : carrier.Carrier | t < height r} ⊆ {r | t ≤ height r} :=
      fun r hr => (show t < height r from hr).le
    exact interior_maximal hs (isOpen_lt continuous_const height_continuous) hp

theorem height_interior_band (a b : ℝ) (ha : -1 < a) (ha0 : a < 0)
    (hb : -1 < b) (hb0 : b < 0) :
    interior {p : carrier.Carrier | a ≤ height p ∧ height p ≤ b} =
      {p | a < height p ∧ height p < b} := by
  change interior ({p : carrier.Carrier | a ≤ height p} ∩ {p | height p ≤ b}) = _
  rw [interior_inter, height_interior_ge a ha ha0, height_interior_le b hb hb0]
  rfl

end GC.GraphManifold.Assembly.FC39P0.X135Radial
