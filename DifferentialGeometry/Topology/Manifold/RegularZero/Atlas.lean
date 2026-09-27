import DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Manifold.RegularZero
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {g : A → B} {S : Set A} {n : ℕ∞ω}

private def coordinates (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :=
  (exists_coordinates_finrank hn hs hg x.property.1 (hr x x.property.1 x.property.2)).choose

private theorem coordinates_spec (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x.val ∈ (coordinates hn hs hg hr x).source ∧
      (coordinates hn hs hg hr x).source ⊆ S ∧
      (∀ y, (coordinates hn hs hg hr x y).1 = g y) ∧
      (coordinates hn hs hg hr x x.val).2 = 0 :=
  (exists_coordinates_finrank hn hs hg x.property.1 (hr x x.property.1 x.property.2)).choose_spec


def chart (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0}
      (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) :=
  fiberChart g (coordinates hn hs hg hr x)
    (coordinates_spec hn hs hg hr x).2.2.1 (coordinates_spec hn hs hg hr x).2.1 x


theorem mem_chart_source (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x ∈ (chart hn hs hg hr x).source := (coordinates_spec hn hs hg hr x).1


theorem chart_center (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    chart hn hs hg hr x x = 0 := (coordinates_spec hn hs hg hr x).2.2.2


theorem contDiffOn_chart_symm (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ n (fun z => ((chart hn hs hg hr x).symm z).val)
      (chart hn hs hg hr x).target := by
  apply contDiffOn_fiberChart_symm


theorem contDiffOn_chart_transition (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x))
    (x y : {z : A // z ∈ S ∧ g z = 0}) :
    ContDiffOn ℝ n ((chart hn hs hg hr y) ∘ (chart hn hs hg hr x).symm)
      ((chart hn hs hg hr x).target ∩
        (chart hn hs hg hr x).symm ⁻¹' (chart hn hs hg hr y).source) :=
  by apply contDiffOn_fiberChart_transition


@[reducible]
def chartedSpace (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    ChartedSpace (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)
      {y : A // y ∈ S ∧ g y = 0} where
  atlas := range (chart hn hs hg hr)
  chartAt := chart hn hs hg hr
  mem_chart_source := mem_chart_source hn hs hg hr
  chart_mem_atlas x := ⟨x,rfl⟩


theorem isManifold (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    let _ := chartedSpace hn hs hg hr
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) n
      {y : A // y ∈ S ∧ g y = 0} := by
  let _ := chartedSpace hn hs hg hr
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa using contDiffOn_chart_transition hn hs hg hr x y


theorem contMDiff_inclusion (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    let _ := chartedSpace hn hs hg hr
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) n
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) := by
  let _ := chartedSpace hn hs hg hr
  let _ := isManifold hn hs hg hr
  change ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) n
    (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A)
  intro x
  let C := Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ
  let c := chart hn hs hg hr x
  have hx : x ∈ c.source := mem_chart_source hn hs hg hr x
  have hc : ContDiffAt ℝ n (fun z => (c.symm z).val) (c x) :=
    (contDiffOn_chart_symm hn hs hg hr x).contDiffAt
      (c.open_target.mem_nhds (c.map_source hx))
  have hh := hc.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓘(ℝ, C)) (n := n) (x := x))
  apply hh.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds C x] with y hy
  change y.val = (c.symm (c y)).val
  exact (congrArg Subtype.val (c.left_inv hy)).symm

end DifferentialGeometry.Manifold.RegularZero
