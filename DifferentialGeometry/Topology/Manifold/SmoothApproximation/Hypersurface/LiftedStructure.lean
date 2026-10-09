import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The smooth structure lifted along a `C^n` local diffeomorphism (W-SUB, O1)

One-sided case of the smooth replacement of a compact `C^k` hypersurface (blueprint LFR47, design
risk R7, external review of the finite soul §8: "extend the normal-orientation double cover to a
double cover of the tube and lift the smooth structure"). Let `X` be a space with a charted space
over `HX` (here the product `S̃ × ℝ` of the unit-normal double cover with the line), `W ⊆ X` open,
and `F : X → M` a `C^n` local diffeomorphism on `W` into a smooth manifold `M` (here the normal
exponential map `(v, h) ↦ exp (h v)`). Then `W` carries the smooth structure pulled back from `M`:

* `liftedBranch`, `liftedChart`: a chosen `C^n` local inverse branch of `F` at each point of `W`,
  restricted into `W`, and the induced open partial homeomorphism `W → M`;
* `liftedChartedSpace`: the charted space over `H` (charts of `M` composed with the branches,
  `ChartedSpace.comp`), and `lifted_isManifold`: it is a smooth manifold (the transitions of the
  branches are restrictions of the identity of `M`);
* `contMDiffAt_lifted_of_comp` (maps into `W` are smooth iff their composite with `F` is),
  `contMDiffAt_lifted_iff` (maps out of `W` are tested on the branch inverses), and their
  consequences `contMDiff_lifted_proj` (`F` is smooth on `W`) and `liftedChartDiffeomorph` (each
  branch is a smooth partial diffeomorphism `W → M`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {J : ModelWithCorners ℝ EX HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {n : WithTop ℕ∞} {F : X → M} {W : Opens X}

/-- The chosen `C^n` local inverse branch of `F` at a point of `W`, restricted into `W`. -/
def liftedBranch (hF : IsLocalDiffeomorphOn J I n F W) (p : W) : PartialDiffeomorph J I X M n :=
  let Ψ := Classical.choose (hF p)
  { toPartialEquiv := (Ψ.toOpenPartialHomeomorph.restrOpen W W.isOpen).toPartialEquiv
    open_source := (Ψ.toOpenPartialHomeomorph.restrOpen W W.isOpen).open_source
    open_target := (Ψ.toOpenPartialHomeomorph.restrOpen W W.isOpen).open_target
    contMDiffOn_toFun := Ψ.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := Ψ.contMDiffOn_invFun.mono inter_subset_left }

theorem liftedBranch_mem_source (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    (p : X) ∈ (liftedBranch hF p).source :=
  ⟨(Classical.choose_spec (hF p)).1, p.2⟩

theorem liftedBranch_source_subset (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    (liftedBranch hF p).source ⊆ W :=
  fun _ hx => hx.2

theorem liftedBranch_eqOn (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    EqOn F (liftedBranch hF p) (liftedBranch hF p).source :=
  fun _ hx => (Classical.choose_spec (hF p)).2 hx.1

/-- The branch at `p` as an open partial homeomorphism from `W` to `M`. -/
def liftedChart (hF : IsLocalDiffeomorphOn J I n F W) (p : W) : OpenPartialHomeomorph W M :=
  (liftedBranch hF p).toOpenPartialHomeomorph.subtypeRestr ⟨p⟩

theorem mem_liftedChart_source (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    p ∈ (liftedChart hF p).source := by
  rw [liftedChart, OpenPartialHomeomorph.subtypeRestr_source]
  exact liftedBranch_mem_source hF p

theorem liftedChart_apply (hF : IsLocalDiffeomorphOn J I n F W) (p : W) {q : W}
    (hq : q ∈ (liftedChart hF p).source) : liftedChart hF p q = F q := by
  rw [liftedChart, OpenPartialHomeomorph.subtypeRestr_source] at hq
  exact (liftedBranch_eqOn hF p hq).symm

theorem liftedChart_symm_val (hF : IsLocalDiffeomorphOn J I n F W) (p : W) {z : M}
    (hz : z ∈ (liftedChart hF p).target) :
    (((liftedChart hF p).symm z : W) : X) = (liftedBranch hF p).symm z :=
  (liftedBranch hF p).toOpenPartialHomeomorph.subtypeRestr_symm_apply ⟨p⟩ hz

theorem liftedChart_target_subset (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    (liftedChart hF p).target ⊆ (liftedBranch hF p).target :=
  (liftedBranch hF p).toOpenPartialHomeomorph.subtypeRestr_target_subset ⟨p⟩

/-- The charted space of `W` over `M` given by the branches. -/
@[reducible] def liftedChartedSpaceM (hF : IsLocalDiffeomorphOn J I n F W) : ChartedSpace M W where
  atlas := range (liftedChart hF)
  chartAt := liftedChart hF
  mem_chart_source := mem_liftedChart_source hF
  chart_mem_atlas p := ⟨p, rfl⟩

theorem lifted_hasGroupoid_idRestr (hF : IsLocalDiffeomorphOn J I n F W) :
    let _ := liftedChartedSpaceM hF
    HasGroupoid W (@idRestrGroupoid M _) := by
  let _ := liftedChartedSpaceM hF
  refine ⟨?_⟩
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  refine ⟨((liftedChart hF p).symm ≫ₕ liftedChart hF q).source,
    ((liftedChart hF p).symm ≫ₕ liftedChart hF q).open_source, ?_⟩
  refine ⟨by simp only [OpenPartialHomeomorph.ofSet_source], fun z hz => ?_⟩
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    mem_inter_iff, mem_preimage] at hz
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply, OpenPartialHomeomorph.ofSet_apply]
  rw [liftedChart_apply hF q hz.2, ← liftedChart_apply hF p ((liftedChart hF p).map_target hz.1),
    (liftedChart hF p).right_inv hz.1]
  rfl

/-- **The lifted charted space** of `W` over the model `H` of `M`. -/
@[reducible] def liftedChartedSpace (hF : IsLocalDiffeomorphOn J I n F W) : ChartedSpace H W :=
  let _ := liftedChartedSpaceM hF
  ChartedSpace.comp H M W

theorem liftedChartedSpace_chartAt (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    (liftedChartedSpace hF).chartAt p = liftedChart hF p ≫ₕ chartAt H (F p) := by
  change liftedChart hF p ≫ₕ chartAt H (liftedChart hF p p) = _
  rw [liftedChart_apply hF p (mem_liftedChart_source hF p)]

/-- **The lifted structure is smooth.** -/
theorem lifted_isManifold [IsManifold I ∞ M] (hF : IsLocalDiffeomorphOn J I n F W) :
    let _ := liftedChartedSpace hF
    IsManifold I ∞ W := by
  let _ := liftedChartedSpaceM hF
  let _ : ChartedSpace H W := liftedChartedSpace hF
  have := lifted_hasGroupoid_idRestr hF
  have : HasGroupoid W (contDiffGroupoid ∞ I) :=
    StructureGroupoid.HasGroupoid.comp (G₂ := @idRestrGroupoid M _) (by
      intro f hf
      have hsmooth {a : OpenPartialHomeomorph M M}
          (ha : a ∈ @idRestrGroupoid M _) : ContMDiffOn I I ∞ a a.source := by
        rcases ha with ⟨s, hs, ha⟩
        refine contMDiffOn_id.congr ?_
        intro x hx
        have hx' := OpenPartialHomeomorph.EqOnSource.eqOn ha hx
        simpa using hx'
      rw [isLocalStructomorphOn_contDiffGroupoid_iff]
      exact ⟨hsmooth hf, by
        simpa only [mfld_simps] using hsmooth ((@idRestrGroupoid M _).symm hf)⟩)
  exact IsManifold.mk' I ∞ W

theorem liftedChartedSpace_extChartAt_symm (hF : IsLocalDiffeomorphOn J I n F W) (p : W) (z : E) :
    let _ := liftedChartedSpace hF
    (extChartAt I p).symm z = (liftedChart hF p).symm ((extChartAt I (F p)).symm z) := by
  intro _
  change (liftedChart hF p).symm ((chartAt H (liftedChart hF p p)).symm (I.symm z)) =
    (liftedChart hF p).symm ((chartAt H (F p)).symm (I.symm z))
  rw [liftedChart_apply hF p (mem_liftedChart_source hF p)]

theorem liftedChartedSpace_extChartAt_self (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    let _ := liftedChartedSpace hF
    extChartAt I p p = extChartAt I (F p) (F p) := by
  intro _
  change I (chartAt H (liftedChart hF p p) (liftedChart hF p p)) = I (chartAt H (F p) (F p))
  rw [liftedChart_apply hF p (mem_liftedChart_source hF p)]

theorem liftedChartedSpace_extChartAt_apply (hF : IsLocalDiffeomorphOn J I n F W) (p : W) {q : W}
    (hq : q ∈ (liftedChart hF p).source) :
    let _ := liftedChartedSpace hF
    extChartAt I p q = extChartAt I (F p) (F q) := by
  intro _
  change I (chartAt H (liftedChart hF p p) (liftedChart hF p q)) = I (chartAt H (F p) (F q))
  rw [liftedChart_apply hF p (mem_liftedChart_source hF p), liftedChart_apply hF p hq]

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  {HY : Type*} [TopologicalSpace HY] {K : ModelWithCorners ℝ EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]

/-- **Maps into the lifted manifold**: continuous at `y` with `C^m` composite with `F`. -/
theorem contMDiffAt_lifted_of_comp (hF : IsLocalDiffeomorphOn J I n F W) {m : WithTop ℕ∞}
    {G : Y → W} {y : Y} (hGc : ContinuousAt G y) (hG : ContMDiffAt K I m (fun z => F (G z)) y) :
    let _ := liftedChartedSpace hF
    ContMDiffAt K I m G y := by
  intro _
  rw [contMDiffAt_iff_target]
  refine ⟨hGc, ?_⟩
  apply (contMDiffAt_iff_target.mp hG).2.congr_of_eventuallyEq
  filter_upwards [hGc.preimage_mem_nhds ((liftedChart hF (G y)).open_source.mem_nhds
    (mem_liftedChart_source hF (G y)))] with z hz
  exact liftedChartedSpace_extChartAt_apply hF (G y) hz

/-- **Maps out of the lifted manifold** are tested on the branch inverses. -/
theorem contMDiffAt_lifted_iff (hF : IsLocalDiffeomorphOn J I n F W) {m : WithTop ℕ∞}
    {G : W → Y} (p : W) :
    let _ := liftedChartedSpace hF
    ContMDiffAt I K m G p ↔ ContMDiffAt I K m (fun z => G ((liftedChart hF p).symm z)) (F p) := by
  intro _
  rw [contMDiffAt_iff_source, contMDiffAt_iff_source, liftedChartedSpace_extChartAt_self hF p]
  have hfun : (G ∘ (extChartAt I p).symm) =
      (fun z => G ((liftedChart hF p).symm z)) ∘ (extChartAt I (F p)).symm := by
    funext z
    exact congrArg G (liftedChartedSpace_extChartAt_symm hF p z)
  rw [hfun]

/-- `F` is smooth on the lifted manifold. -/
theorem contMDiff_lifted_proj (hF : IsLocalDiffeomorphOn J I n F W) :
    let _ := liftedChartedSpace hF
    ContMDiff I I ∞ (fun w : W => F w) := by
  intro _ p
  refine (contMDiffAt_lifted_iff (G := fun w : W => F w) hF p).mpr ?_
  apply contMDiffAt_id.congr_of_eventuallyEq
  have htgt : F p ∈ (liftedChart hF p).target := by
    rw [← liftedChart_apply hF p (mem_liftedChart_source hF p)]
    exact (liftedChart hF p).map_source (mem_liftedChart_source hF p)
  filter_upwards [(liftedChart hF p).open_target.mem_nhds htgt] with z hz
  rw [← liftedChart_apply hF p ((liftedChart hF p).map_target hz), (liftedChart hF p).right_inv hz]
  rfl

/-- Each branch is a smooth partial diffeomorphism from the lifted manifold onto an open set of `M`. -/
def liftedChartDiffeomorph (hF : IsLocalDiffeomorphOn J I n F W) (p : W) :
    let _ := liftedChartedSpace hF
    PartialDiffeomorph I I W M ∞ :=
  let _ := liftedChartedSpace hF
  { toPartialEquiv := (liftedChart hF p).toPartialEquiv
    open_source := (liftedChart hF p).open_source
    open_target := (liftedChart hF p).open_target
    contMDiffOn_toFun := (contMDiff_lifted_proj hF).contMDiffOn.congr fun _ hq =>
      liftedChart_apply hF p hq
    contMDiffOn_invFun := by
      intro z hz
      refine (contMDiffAt_lifted_of_comp hF
        ((liftedChart hF p).continuousOn_symm.continuousAt
          ((liftedChart hF p).open_target.mem_nhds hz)) ?_).contMDiffWithinAt
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [(liftedChart hF p).open_target.mem_nhds hz] with w hw
      rw [← liftedChart_apply hF p ((liftedChart hF p).map_target hw),
        (liftedChart hF p).right_inv hw]
      rfl }

theorem liftedChartDiffeomorph_apply (hF : IsLocalDiffeomorphOn J I n F W) (p : W) (q : W) :
    liftedChartDiffeomorph hF p q = liftedChart hF p q := rfl

/-- The local diffeomorphism `F` is `C^n` at every point of `W`. -/
theorem contMDiffAt_of_isLocalDiffeomorphOn (hF : IsLocalDiffeomorphOn J I n F W) {x : X}
    (hx : x ∈ W) : ContMDiffAt J I n F x := by
  let p : W := ⟨x, hx⟩
  have hsrc := liftedBranch_mem_source hF p
  exact (((liftedBranch hF p).contMDiffOn_toFun.contMDiffAt
    ((liftedBranch hF p).open_source.mem_nhds hsrc))).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem ((liftedBranch hF p).open_source.mem_nhds hsrc)
      (liftedBranch_eqOn hF p))

/-- The inclusion of the lifted manifold into `X` is `C^n`. -/
theorem contMDiff_lifted_val (hF : IsLocalDiffeomorphOn J I n F W) :
    let _ := liftedChartedSpace hF
    ContMDiff I J n (Subtype.val : W → X) := by
  intro _ p
  refine (contMDiffAt_lifted_iff (G := (Subtype.val : W → X)) hF p).mpr ?_
  have htgt : F p ∈ (liftedChart hF p).target := by
    rw [← liftedChart_apply hF p (mem_liftedChart_source hF p)]
    exact (liftedChart hF p).map_source (mem_liftedChart_source hF p)
  have hB := (liftedBranch hF p).contMDiffOn_invFun.contMDiffAt
    ((liftedBranch hF p).open_target.mem_nhds (liftedChart_target_subset hF p htgt))
  refine hB.congr_of_eventuallyEq ?_
  filter_upwards [(liftedChart hF p).open_target.mem_nhds htgt] with z hz
  exact liftedChart_symm_val hF p hz

open Classical in
/-- The inclusion `X ⊇ W → W` (a junk value `p₀` off `W`). -/
def liftedIncl (p₀ : W) (x : X) : W := if h : x ∈ W then ⟨x, h⟩ else p₀

theorem liftedIncl_val (p₀ : W) {x : X} (hx : x ∈ W) : (liftedIncl p₀ x : X) = x := by
  simp [liftedIncl, hx]

theorem liftedIncl_subtype (p₀ : W) (w : W) : liftedIncl p₀ w = w :=
  Subtype.ext (liftedIncl_val p₀ w.2)

/-- **The identity tube** `X ⊇ W → W` (with the lifted structure) is a `C^n` partial
diffeomorphism. -/
def liftedTube (hF : IsLocalDiffeomorphOn J I n F W) (p₀ : W) :
    let _ := liftedChartedSpace hF
    PartialDiffeomorph J I X W n :=
  let _ := liftedChartedSpace hF
  { toFun := liftedIncl p₀
    invFun := Subtype.val
    source := W
    target := univ
    map_source' := fun _ _ => mem_univ _
    map_target' := fun w _ => w.2
    left_inv' := fun x hx => liftedIncl_val p₀ hx
    right_inv' := fun w _ => liftedIncl_subtype p₀ w
    open_source := W.isOpen
    open_target := isOpen_univ
    contMDiffOn_toFun := by
      intro x hx
      have hxW : x ∈ W := hx
      have hval : (Subtype.val ∘ liftedIncl p₀) =ᶠ[𝓝 x] id := by
        filter_upwards [W.isOpen.mem_nhds hxW] with y hy
        exact liftedIncl_val p₀ hy
      have hcont : ContinuousAt (liftedIncl p₀) x := by
        rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
        exact continuousAt_id.congr hval.symm
      refine (contMDiffAt_lifted_of_comp hF hcont ?_).contMDiffWithinAt
      refine (contMDiffAt_of_isLocalDiffeomorphOn hF hxW).congr_of_eventuallyEq ?_
      filter_upwards [hval] with y hy
      exact congrArg F hy
    contMDiffOn_invFun := (contMDiff_lifted_val hF).contMDiffOn }

theorem liftedTube_apply (hF : IsLocalDiffeomorphOn J I n F W) (p₀ : W) {x : X} (hx : x ∈ W) :
    ((liftedTube hF p₀ x : W) : X) = x :=
  liftedIncl_val p₀ hx

theorem liftedTube_source (hF : IsLocalDiffeomorphOn J I n F W) (p₀ : W) :
    (liftedTube hF p₀).source = W := rfl

/-- **Deck transformations are smooth**: a continuous self-map of `W` commuting with `F` is smooth
for the lifted structure. -/
theorem contMDiff_lifted_deck (hF : IsLocalDiffeomorphOn J I n F W) {τ : W → W}
    (hτ : Continuous τ) (hFτ : ∀ w, F (τ w) = F w) :
    let _ := liftedChartedSpace hF
    ContMDiff I I ∞ τ := by
  intro _ w
  refine contMDiffAt_lifted_of_comp hF hτ.continuousAt ?_
  have h := contMDiff_lifted_proj hF w
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => hFτ v)

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
