import DifferentialGeometry.Topology.Morse.RegularZeroCoordinates
import DifferentialGeometry.Topology.Manifold.RegularZero.Atlas

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Morse
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {g : A → B} {S : Set A}


def regularZeroChart (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0}
      (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) :=
  DifferentialGeometry.Manifold.RegularZero.chart one_ne_zero hs hg hr x


theorem mem_regularZeroChart_source (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x ∈ (regularZeroChart hs hg hr x).source :=
  DifferentialGeometry.Manifold.RegularZero.mem_chart_source one_ne_zero hs hg hr x


theorem regularZeroChart_center (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    regularZeroChart hs hg hr x x = 0 :=
  DifferentialGeometry.Manifold.RegularZero.chart_center one_ne_zero hs hg hr x


theorem contDiffOn_regularZeroChart_symm (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ 1 (fun z => ((regularZeroChart hs hg hr x).symm z).val)
      (regularZeroChart hs hg hr x).target :=
  DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm one_ne_zero hs hg hr x


theorem contDiffOn_regularZeroChart_transition (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x))
    (x y : {z : A // z ∈ S ∧ g z = 0}) :
    ContDiffOn ℝ 1 ((regularZeroChart hs hg hr y) ∘ (regularZeroChart hs hg hr x).symm)
      ((regularZeroChart hs hg hr x).target ∩
        (regularZeroChart hs hg hr x).symm ⁻¹' (regularZeroChart hs hg hr y).source) :=
  DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition one_ne_zero hs hg hr x y


@[reducible]
def regularZeroChartedSpace (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    ChartedSpace (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)
      {y : A // y ∈ S ∧ g y = 0} :=
  DifferentialGeometry.Manifold.RegularZero.chartedSpace one_ne_zero hs hg hr


theorem regularZeroIsManifold (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    let _ := regularZeroChartedSpace hs hg hr
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 1
      {y : A // y ∈ S ∧ g y = 0} :=
  DifferentialGeometry.Manifold.RegularZero.isManifold one_ne_zero hs hg hr


theorem contMDiff_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) :
    let _ := regularZeroChartedSpace hs hg hr
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) 1
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) :=
  DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion one_ne_zero hs hg hr

end DifferentialGeometry.Morse
