import DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem preferredChartTangentEquiv_open (U : Opens M) (p x : U)
    (hx : x ∈ (chartAt H p).source) :
    preferredChartTangentEquiv I p x hx =
      preferredChartTangentEquiv I p.val x.val hx.2 := by
  apply ContinuousLinearEquiv.ext
  funext v
  have h := mfderiv_comp (f := (Subtype.val : U → M)) (g := (extChartAt I p.val : M → E))
    x (mdifferentiableAt_extChartAt (I := I) hx.2)
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at h
  exact congrArg (fun A : E →L[ℝ] E => A v) h

def restrictSmoothOrientation (U : Opens M) (o : SmoothOrientation I M) :
    SmoothOrientation I U := by
  refine ⟨fun x => o.val x.val, ?_⟩
  intro p
  let a : (chartAt H p).source → (chartAt H p.val).source :=
    fun x => ⟨x.val.val, x.property.2⟩
  have ha : Continuous a :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have h := (o.property p.val).comp_continuous ha
  have he : (fun x : (chartAt H p).source =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv
        (o.val x.val.val)) =
      (fun x : (chartAt H p).source =>
        Orientation.map _ (preferredChartTangentEquiv I p.val (a x).val (a x).property).toLinearEquiv
          (o.val (a x).val)) := by
    funext x
    rw [preferredChartTangentEquiv_open]
  rw [he]
  exact h

theorem restrictSmoothOrientation_apply (U : Opens M) (o : SmoothOrientation I M) (x : U) :
    (restrictSmoothOrientation I U o).val x = o.val x.val := rfl

def smoothOrientationOfOpenRestrictions
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∃ U : Opens M, p ∈ U ∧
      ∃ oU : SmoothOrientation I U, ∀ x : U, oU.val x = o x.val) :
    SmoothOrientation I M := by
  apply smoothOrientationOfLocalRepresentations I o
  intro p
  obtain ⟨U, hp, oU, hU⟩ := ho p
  let pU : U := ⟨p, hp⟩
  let V : Opens M := U ⊓ ⟨(chartAt H p).source, (chartAt H p).open_source⟩
  let a : V → (chartAt H pU).source :=
    fun y => ⟨⟨y.val, y.property.1⟩, ⟨trivial, y.property.2⟩⟩
  have ha : Continuous a := (continuous_subtype_val.subtype_mk _).subtype_mk _
  have h := (oU.property pU).comp_continuous ha
  have he : (fun y : V =>
      Orientation.map _ (preferredChartTangentEquiv I pU (a y).val (a y).property).toLinearEquiv
        (oU.val (a y).val)) =
      (fun y : V => Orientation.map _
        (preferredChartTangentEquiv I p y.val y.property.2).toLinearEquiv (o y.val)) := by
    funext y
    rw [preferredChartTangentEquiv_open, hU]
  have h' : IsLocallyConstant (fun y : V =>
      Orientation.map _ (preferredChartTangentEquiv I pU (a y).val (a y).property).toLinearEquiv
        (oU.val (a y).val)) := h
  rw [he] at h'
  exact ⟨V, fun _ hy => hy.2, ⟨hp, mem_chart_source H p⟩, h'⟩

theorem smoothOrientationOfOpenRestrictions_apply
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∃ U : Opens M, p ∈ U ∧
      ∃ oU : SmoothOrientation I U, ∀ x : U, oU.val x = o x.val) (p : M) :
    (smoothOrientationOfOpenRestrictions I o ho).val p = o p := rfl

variable {ι : Type*} (U : ι → Opens M) (o : ∀ i, SmoothOrientation I (U i))
variable (hcover : ∀ p : M, ∃ i, p ∈ U i)
variable (heq : ∀ (i j : ι) (p : M) (hi : p ∈ U i) (hj : p ∈ U j),
  (o i).val ⟨p, hi⟩ = (o j).val ⟨p, hj⟩)

def glueSmoothOrientations : SmoothOrientation I M := by
  let O : M → Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
    fun p => (o (hcover p).choose).val ⟨p, (hcover p).choose_spec⟩
  apply smoothOrientationOfOpenRestrictions I O
  intro p
  let i := (hcover p).choose
  exact ⟨U i, (hcover p).choose_spec, o i,
    fun x => heq i (hcover x.val).choose x.val x.property (hcover x.val).choose_spec⟩

theorem glueSmoothOrientations_apply (i : ι) (p : U i) :
    (glueSmoothOrientations I U o hcover heq).val p.val = (o i).val p := by
  change (o (hcover p.val).choose).val ⟨p.val, (hcover p.val).choose_spec⟩ = (o i).val p
  exact heq (hcover p.val).choose i p.val (hcover p.val).choose_spec p.property
end DifferentialGeometry.Topology.Manifold
