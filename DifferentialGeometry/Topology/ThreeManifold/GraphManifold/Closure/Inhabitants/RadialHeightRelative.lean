import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialHeightTopology

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_RelativeX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_RelativeX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def negativeSeamBelow (u : ℝ) : TopologicalSpace.Opens radialNegativeSeam :=
  ⟨{q | q.val.2 < u}, isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const⟩

def negativeSeamSublevel (u : ℝ) (q : negativeSeamBelow u) :
    {p : carrier.Carrier | height p ≤ u} :=
  ⟨negativeSeamToCarrier q.val, by
    change height (negativeSeamToCarrier q.val) ≤ u
    rw [height_negativeSeam]
    exact q.property.le⟩

theorem negativeSeamSublevel_continuous (u : ℝ) : Continuous (negativeSeamSublevel u) :=
  (negativeSeamToCarrier_smooth.continuous.comp continuous_subtype_val).subtype_mk _

theorem negativeSeamBelowTime_open (u : ℝ) :
    IsOpenMap (fun q : negativeSeamBelow u => q.val.val.2) :=
  negativeSeamTime_open.comp (negativeSeamBelow u).isOpen.isOpenMap_subtype_val

theorem height_sublevel_no_interior_ge (u s : ℝ) (hlo : -1 < s) (hhi : s < 0)
    (hsu : s < u) (p : {p : carrier.Carrier | height p ≤ u}) (hp : height p.val = s) :
    p ∉ interior {r : {p : carrier.Carrier | height p ≤ u} | s ≤ height r.val} := by
  intro hint
  obtain ⟨q, hq⟩ := exists_negativeSeam_at p.val (hp.symm ▸ hlo) (hp.symm ▸ hhi)
  have hqt : q.val.2 = s :=
    (height_negativeSeam q).symm.trans ((congrArg height hq).trans hp)
  let r : negativeSeamBelow u := ⟨q, by change q.val.2 < u; rw [hqt]; exact hsu⟩
  have hr : negativeSeamSublevel u r = p := Subtype.ext hq
  let U : Set (negativeSeamBelow u) := (negativeSeamSublevel u) ⁻¹'
    interior {r : {p : carrier.Carrier | height p ≤ u} | s ≤ height r.val}
  have hU : IsOpen U := isOpen_interior.preimage (negativeSeamSublevel_continuous u)
  have hrU : r ∈ U := by
    change negativeSeamSublevel u r ∈
      interior {r : {p : carrier.Carrier | height p ≤ u} | s ≤ height r.val}
    rw [hr]
    exact hint
  have him : (fun q : negativeSeamBelow u => q.val.val.2) '' U ⊆ Ici s := by
    rintro t ⟨v, hv, rfl⟩
    have hm := interior_subset hv
    change s ≤ height (negativeSeamToCarrier v.val) at hm
    rw [height_negativeSeam] at hm
    exact hm
  have hs : q.val.2 ∈ interior (Ici s) :=
    interior_maximal him (negativeSeamBelowTime_open u U hU) (mem_image_of_mem _ hrU)
  rw [interior_Ici, hqt] at hs
  exact lt_irrefl s hs

theorem height_sublevel_interior_ge (u s : ℝ) (hlo : -1 < s) (hhi : s < 0)
    (hsu : s < u) :
    interior {p : {p : carrier.Carrier | height p ≤ u} | s ≤ height p.val} =
      {p | s < height p.val} := by
  ext p
  constructor
  · intro hp
    have hm := interior_subset hp
    change s ≤ height p.val at hm
    change s < height p.val
    by_contra! hn
    exact height_sublevel_no_interior_ge u s hlo hhi hsu p (le_antisymm hn hm) hp
  · intro hp
    have he : {r : {p : carrier.Carrier | height p ≤ u} | s < height r.val} ⊆
        {r | s ≤ height r.val} := fun r hr => (show s < height r.val from hr).le
    exact interior_maximal he
      (isOpen_lt continuous_const (height_continuous.comp continuous_subtype_val)) hp

theorem height_relInt_band (u s : ℝ) (hlo : -1 < s) (hhi : s < 0) (hsu : s < u) :
    relInt {p : carrier.Carrier | height p ≤ u} {p | s ≤ height p ∧ height p ≤ u} =
      {p | s < height p ∧ height p ≤ u} := by
  have hp : (Subtype.val : {p : carrier.Carrier | height p ≤ u} → carrier.Carrier) ⁻¹'
      {p | s ≤ height p ∧ height p ≤ u} =
      {p : {p : carrier.Carrier | height p ≤ u} | s ≤ height p.val} := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, p.property⟩⟩
  unfold relInt
  rw [hp, height_sublevel_interior_ge u s hlo hhi hsu]
  ext p
  exact ⟨fun ⟨q, hq, hqp⟩ => hqp ▸ ⟨hq, q.property⟩,
    fun ⟨hs, hu⟩ => ⟨⟨p, hu⟩, hs, rfl⟩⟩

theorem height_sublevel_no_interior_le (u s : ℝ) (hlo : -1 < s) (hhi : s < 0)
    (hsu : s < u) (p : {p : carrier.Carrier | height p ≤ u}) (hp : height p.val = s) :
    p ∉ interior {r : {p : carrier.Carrier | height p ≤ u} | height r.val ≤ s} := by
  intro hint
  obtain ⟨q, hq⟩ := exists_negativeSeam_at p.val (hp.symm ▸ hlo) (hp.symm ▸ hhi)
  have hqt : q.val.2 = s :=
    (height_negativeSeam q).symm.trans ((congrArg height hq).trans hp)
  let r : negativeSeamBelow u := ⟨q, by change q.val.2 < u; rw [hqt]; exact hsu⟩
  have hr : negativeSeamSublevel u r = p := Subtype.ext hq
  let U : Set (negativeSeamBelow u) := (negativeSeamSublevel u) ⁻¹'
    interior {r : {p : carrier.Carrier | height p ≤ u} | height r.val ≤ s}
  have hU : IsOpen U := isOpen_interior.preimage (negativeSeamSublevel_continuous u)
  have hrU : r ∈ U := by
    change negativeSeamSublevel u r ∈
      interior {r : {p : carrier.Carrier | height p ≤ u} | height r.val ≤ s}
    rw [hr]
    exact hint
  have him : (fun q : negativeSeamBelow u => q.val.val.2) '' U ⊆ Iic s := by
    rintro t ⟨v, hv, rfl⟩
    have hm := interior_subset hv
    change height (negativeSeamToCarrier v.val) ≤ s at hm
    rw [height_negativeSeam] at hm
    exact hm
  have hs : q.val.2 ∈ interior (Iic s) :=
    interior_maximal him (negativeSeamBelowTime_open u U hU) (mem_image_of_mem _ hrU)
  rw [interior_Iic, hqt] at hs
  exact lt_irrefl s hs

theorem height_sublevel_interior_le (u s : ℝ) (hlo : -1 < s) (hhi : s < 0)
    (hsu : s < u) :
    interior {p : {p : carrier.Carrier | height p ≤ u} | height p.val ≤ s} =
      {p | height p.val < s} := by
  ext p
  constructor
  · intro hp
    have hm := interior_subset hp
    change height p.val ≤ s at hm
    change height p.val < s
    by_contra! hn
    exact height_sublevel_no_interior_le u s hlo hhi hsu p (le_antisymm hm hn) hp
  · intro hp
    have he : {r : {p : carrier.Carrier | height p ≤ u} | height r.val < s} ⊆
        {r | height r.val ≤ s} := fun r hr => (show height r.val < s from hr).le
    exact interior_maximal he
      (isOpen_lt (height_continuous.comp continuous_subtype_val) continuous_const) hp

theorem height_relInt_le (u s : ℝ) (hlo : -1 < s) (hhi : s < 0) (hsu : s < u) :
    relInt {p : carrier.Carrier | height p ≤ u} {p | height p ≤ s} =
      {p | height p < s ∧ height p ≤ u} := by
  unfold relInt
  change Subtype.val '' interior {p : {p : carrier.Carrier | height p ≤ u} |
    height p.val ≤ s} = _
  rw [height_sublevel_interior_le u s hlo hhi hsu]
  ext p
  exact ⟨fun ⟨q, hq, hqp⟩ => hqp ▸ ⟨hq, q.property⟩,
    fun ⟨hs, hu⟩ => ⟨⟨p, hu⟩, hs, rfl⟩⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial

