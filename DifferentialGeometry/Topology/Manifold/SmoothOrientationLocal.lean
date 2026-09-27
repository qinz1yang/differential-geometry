import DifferentialGeometry.Topology.Manifold.OrientationChartTransition

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold

theorem isLocallyConstant_of_open_neighborhoods {X Y : Type*} [TopologicalSpace X]
    (f : X → Y)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsLocallyConstant (fun y : U => f y.val)) :
    IsLocallyConstant f := by
  intro s
  apply isOpen_iff_mem_nhds.2
  intro x hx
  obtain ⟨U, hxU, hU⟩ := h x
  let V : Set U := (fun y : U => f y.val) ⁻¹' s
  have hV : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V (hU s)
  have hxV : x ∈ (Subtype.val '' V : Set X) := ⟨⟨x, hxU⟩, hx, rfl⟩
  apply mem_of_superset (hV.mem_nhds hxV)
  rintro y ⟨z, hz, rfl⟩
  exact hz

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def smoothOrientationOfLocalRepresentations
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∃ U : Opens M, ∃ hU : (U : Set M) ⊆ (chartAt H p).source,
      p ∈ U ∧ IsLocallyConstant (fun y : U =>
        Orientation.map _ (preferredChartTangentEquiv I p y.val (hU y.property)).toLinearEquiv
          (o y.val))) : SmoothOrientation I M := by
  refine ⟨o, ?_⟩
  intro q
  apply isLocallyConstant_of_open_neighborhoods
  intro x
  obtain ⟨U, hU, hxU, hoU⟩ := ho x.val
  let V : Opens (chartAt H q).source :=
    ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  have hxV : x ∈ V := hxU
  let a : V → U := fun y => ⟨y.val.val, y.property⟩
  let b : V → ↥((chartAt H x.val).source ∩ (chartAt H q).source) :=
    fun y => ⟨y.val.val, hU y.property, y.val.property⟩
  have ha : Continuous a := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hb : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hrep : IsLocallyConstant (fun y : V =>
      Orientation.map _ (preferredChartTangentEquiv I x.val (a y).val
        (hU (a y).property)).toLinearEquiv (o (a y).val)) := hoU.comp_continuous ha
  have he : Continuous (fun y : V =>
      (preferredChartTransitionEquiv I x.val q (b y) : E →L[ℝ] E)) :=
    (continuous_preferredChartTransition I x.val q).comp hb
  have hnew := orientation_map_locallyConstant_field
    (fun y : V => preferredChartTransitionEquiv I x.val q (b y)) he _ hrep
  refine ⟨V, hxV, ?_⟩
  have heq : (fun y : V =>
      Orientation.map _ (preferredChartTransitionEquiv I x.val q (b y)).toLinearEquiv
        (Orientation.map _ (preferredChartTangentEquiv I x.val (a y).val
          (hU (a y).property)).toLinearEquiv (o (a y).val))) =
      (fun y : V => Orientation.map _
        (preferredChartTangentEquiv I q y.val.val y.val.property).toLinearEquiv
          (o y.val.val)) := by
    funext y
    exact preferredChartTransition_orientation I x.val q (b y) (o y.val.val)
  rw [heq] at hnew
  exact hnew

theorem smoothOrientationOfLocalRepresentations_apply
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∃ U : Opens M, ∃ hU : (U : Set M) ⊆ (chartAt H p).source,
      p ∈ U ∧ IsLocallyConstant (fun y : U =>
        Orientation.map _ (preferredChartTangentEquiv I p y.val (hU y.property)).toLinearEquiv
          (o y.val))) (p : M) :
    (smoothOrientationOfLocalRepresentations I o ho).val p = o p := rfl

def smoothOrientationOfPointwiseChartConstancy
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∀ᶠ y in 𝓝 p, ∀ hy : y ∈ (chartAt H p).source,
      Orientation.map _ (preferredChartTangentEquiv I p y hy).toLinearEquiv (o y) = o p) :
    SmoothOrientation I M := by
  apply smoothOrientationOfLocalRepresentations I o
  intro p
  have hn := inter_mem ((chartAt H p).open_source.mem_nhds (mem_chart_source H p)) (ho p)
  obtain ⟨V, hV, hVopen, hpV⟩ := mem_nhds_iff.mp hn
  let U : Opens M := ⟨V, hVopen⟩
  have hU : (U : Set M) ⊆ (chartAt H p).source := fun y hy => (hV hy).1
  refine ⟨U, hU, hpV, ?_⟩
  have he : (fun y : U => Orientation.map _
      (preferredChartTangentEquiv I p y.val (hU y.property)).toLinearEquiv (o y.val)) =
      Function.const U (o p) := by
    funext y
    exact (hV y.property).2 (hU y.property)
  rw [he]
  exact IsLocallyConstant.const (o p)

theorem smoothOrientationOfPointwiseChartConstancy_apply
    (o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (ho : ∀ p : M, ∀ᶠ y in 𝓝 p, ∀ hy : y ∈ (chartAt H p).source,
      Orientation.map _ (preferredChartTangentEquiv I p y hy).toLinearEquiv (o y) = o p)
    (p : M) : (smoothOrientationOfPointwiseChartConstancy I o ho).val p = o p := rfl
end DifferentialGeometry.Topology.Manifold
