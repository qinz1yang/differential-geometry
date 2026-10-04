import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Charted spaces lifted along sheets of a local homeomorphism (lane CMS3-FLOW, BASE-2, G3)

Generic topology for the unit-normal double cover of a codimension-one slice (BASE-2, design
`docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §3 "BASE", review §10).

Data: a continuous `p : X → Y` into a charted space `Y`, and at every `w : X` an open `V w ∋ p w` with a
continuous local section `sec w : Y → X` on `V w` (`p ∘ sec w = id` on `V w`, `sec w (p w) = w`) whose
sheet `{z | p z ∈ V w ∧ sec w (p z) = z}` is open. Then

* `sheetPartialHomeomorph`: the sheet is an open partial homeomorphism `X → Y` (inverse `sec w`);
* `sheetChartedSpace`: `X` is charted over the model of `Y`, with chart at `w` the sheet of `w` followed by
  the chart of `Y` at `p w`;
* `contMDiffAt_sheet_of_comp_sec` / `contMDiffAt_sheet_of_comp_proj`: a map out of (into) `X` is `C^m` at
  a point as soon as its composite with the local section (with `p`) is;
* `isLocalDiffeomorph_sheet_proj`: `p` is a local diffeomorphism of every order.
No groupoid condition is needed for these statements.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {X : Type*} [TopologicalSpace X]
  {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  {HY : Type*} [TopologicalSpace HY] {IY : ModelWithCorners ℝ EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]

/-- One sheet of `p`, as an open partial homeomorphism `X → Y`. -/
def sheetPartialHomeomorph (p : X → Y) (hp : Continuous p) (V : Set Y) (hV : IsOpen V)
    (sec : Y → X) (hsec : ContinuousOn sec V) (hpsec : ∀ y ∈ V, p (sec y) = y)
    (hopen : IsOpen {z | p z ∈ V ∧ sec (p z) = z}) : OpenPartialHomeomorph X Y where
  toFun := p
  invFun := sec
  source := {z | p z ∈ V ∧ sec (p z) = z}
  target := V
  map_source' := fun _ hz => hz.1
  map_target' := fun y hy => ⟨by rw [hpsec y hy]; exact hy, by rw [hpsec y hy]⟩
  left_inv' := fun _ hz => hz.2
  right_inv' := fun y hy => hpsec y hy
  open_source := hopen
  open_target := hV
  continuousOn_toFun := hp.continuousOn
  continuousOn_invFun := hsec

variable (HY) in
/-- The charted space on `X` lifted along the sheets of `p`. -/
@[instance_reducible]
def sheetChartedSpace (p : X → Y) (hp : Continuous p) (V : X → Set Y) (hV : ∀ w, IsOpen (V w))
    (hpV : ∀ w, p w ∈ V w) (sec : X → Y → X) (hsec : ∀ w, ContinuousOn (sec w) (V w))
    (hpsec : ∀ w, ∀ y ∈ V w, p (sec w y) = y) (hself : ∀ w, sec w (p w) = w)
    (hopen : ∀ w, IsOpen {z | p z ∈ V w ∧ sec w (p z) = z}) : ChartedSpace HY X where
  atlas := range fun w =>
    (sheetPartialHomeomorph p hp (V w) (hV w) (sec w) (hsec w) (hpsec w) (hopen w)).trans
      (chartAt HY (p w))
  chartAt w :=
    (sheetPartialHomeomorph p hp (V w) (hV w) (sec w) (hsec w) (hpsec w) (hopen w)).trans
      (chartAt HY (p w))
  mem_chart_source w := ⟨⟨hpV w, hself w⟩, mem_chart_source HY (p w)⟩
  chart_mem_atlas w := ⟨w, rfl⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- **Maps out of the lifted space.** `f` is `C^m` at `w` when `f ∘ sec w` is `C^m` at `p w`. -/
theorem contMDiffAt_sheet_of_comp_sec (p : X → Y) (hp : Continuous p) (V : X → Set Y)
    (hV : ∀ w, IsOpen (V w)) (hpV : ∀ w, p w ∈ V w) (sec : X → Y → X)
    (hsec : ∀ w, ContinuousOn (sec w) (V w)) (hpsec : ∀ w, ∀ y ∈ V w, p (sec w y) = y)
    (hself : ∀ w, sec w (p w) = w) (hopen : ∀ w, IsOpen {z | p z ∈ V w ∧ sec w (p z) = z})
    {m : WithTop ℕ∞} {f : X → N} {w : X} (hf : ContMDiffAt IY J m (fun y => f (sec w y)) (p w)) :
    let _ := sheetChartedSpace HY p hp V hV hpV sec hsec hpsec hself hopen
    ContMDiffAt IY J m f w := by
  let _ := sheetChartedSpace HY p hp V hV hpV sec hsec hpsec hself hopen
  have hcont : ContinuousAt f w := by
    have h1 : ContinuousAt (fun z => f (sec w (p z))) w :=
      ContinuousAt.comp (g := fun y => f (sec w y)) (f := p) hf.continuousAt hp.continuousAt
    refine h1.congr ?_
    filter_upwards [(hopen w).mem_nhds (show w ∈ {z | p z ∈ V w ∧ sec w (p z) = z} from
      ⟨hpV w, hself w⟩)] with z hz
    rw [hz.2]
  rw [contMDiffAt_iff] at hf ⊢
  refine ⟨hcont, ?_⟩
  have h2 := hf.2
  rw [hself w] at h2
  exact h2

/-- **Maps into the lifted space.** `g` is `C^m` at `z₀` when it is continuous there and `p ∘ g` is
`C^m` at `z₀`. -/
theorem contMDiffAt_sheet_of_comp_proj (p : X → Y) (hp : Continuous p) (V : X → Set Y)
    (hV : ∀ w, IsOpen (V w)) (hpV : ∀ w, p w ∈ V w) (sec : X → Y → X)
    (hsec : ∀ w, ContinuousOn (sec w) (V w)) (hpsec : ∀ w, ∀ y ∈ V w, p (sec w y) = y)
    (hself : ∀ w, sec w (p w) = w) (hopen : ∀ w, IsOpen {z | p z ∈ V w ∧ sec w (p z) = z})
    {m : WithTop ℕ∞} {gz : N → X} {z₀ : N} (hc : ContinuousAt gz z₀)
    (hg : ContMDiffAt J IY m (fun z => p (gz z)) z₀) :
    let _ := sheetChartedSpace HY p hp V hV hpV sec hsec hpsec hself hopen
    ContMDiffAt J IY m gz z₀ := by
  let _ := sheetChartedSpace HY p hp V hV hpV sec hsec hpsec hself hopen
  rw [contMDiffAt_iff] at hg ⊢
  exact ⟨hc, hg.2⟩

/-- **`p` is a local diffeomorphism of every order** for the lifted structure. -/
theorem isLocalDiffeomorph_sheet_proj (p : X → Y) (hp : Continuous p) (V : X → Set Y)
    (hV : ∀ w, IsOpen (V w)) (hpV : ∀ w, p w ∈ V w) (sec : X → Y → X)
    (hsec : ∀ w, ContinuousOn (sec w) (V w)) (hpsec : ∀ w, ∀ y ∈ V w, p (sec w y) = y)
    (hself : ∀ w, sec w (p w) = w) (hopen : ∀ w, IsOpen {z | p z ∈ V w ∧ sec w (p z) = z})
    (m : WithTop ℕ∞) :
    let _ := sheetChartedSpace HY p hp V hV hpV sec hsec hpsec hself hopen
    IsLocalDiffeomorph IY IY m p := by
  intro _ w
  set e := sheetPartialHomeomorph p hp (V w) (hV w) (sec w) (hsec w) (hpsec w) (hopen w) with he
  have hpsm : ∀ z : X, ContMDiffAt IY IY m p z := by
    intro z
    refine contMDiffAt_sheet_of_comp_sec p hp V hV hpV sec hsec hpsec hself hopen ?_
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [(hV z).mem_nhds (hpV z)] with y hy
    exact hpsec z y hy
  have hsecsm : ContMDiffOn IY IY m (sec w) (V w) := by
    intro y hy
    refine (contMDiffAt_sheet_of_comp_proj p hp V hV hpV sec hsec hpsec hself hopen
      ((hsec w).continuousAt ((hV w).mem_nhds hy)) ?_).contMDiffWithinAt
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [(hV w).mem_nhds hy] with y' hy'
    exact hpsec w y' hy'
  exact ⟨{ toPartialEquiv := e.toPartialEquiv
           open_source := e.open_source
           open_target := e.open_target
           contMDiffOn_toFun := fun z _ => (hpsm z).contMDiffWithinAt
           contMDiffOn_invFun := hsecsm }, ⟨hpV w, hself w⟩, fun _ _ => rfl⟩

end DifferentialGeometry.Geometry.FiniteSoul
