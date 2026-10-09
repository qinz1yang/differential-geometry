import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.Manifold.ImmersionRange
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Construction.Immersion
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget

set_option autoImplicit false
noncomputable section

open Set Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

private theorem mem_interior_old_of_regularCrossing
    {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    p ∈ interior (Subtype.val '' E.old) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  obtain ⟨z, hz, hp, _⟩ := h
  let f := fun y : E.old => (y.val.val : P.Carrier)
  have hopen : IsOpen (f '' (𝓡∂ 3).interior E.old) :=
    DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion
      E.old_induced.isImmersion rfl
  have hsub : f '' (𝓡∂ 3).interior E.old ⊆ Subtype.val '' E.old := by
    rintro y ⟨w, _, rfl⟩
    exact ⟨w.val, w.property, rfl⟩
  exact interior_maximal hsub hopen ⟨z, hz, hp⟩

theorem RegularCrossing.exists_survivor_partialDiffeomorph
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier}
    (h : E.RegularCrossing p.val q) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = {x | x.val ∈ interior (Subtype.val '' E.old)} ∧
      p ∈ F.source ∧ F p = q ∧ q ∈ F.target ∧
      (∀ x ∈ F.source, E.RegularCrossing x.val (F x)) ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w := by
  let W : Opens E.incoming.terminalRegularOpen :=
    ⟨{x | x.val ∈ interior (Subtype.val '' E.old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  have hp : p ∈ W := E.mem_interior_old_of_regularCrossing h
  obtain ⟨F, hsource, hcross, _, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W ⟨p, hp⟩ (fun _ hx => hx)
  have hpF : p ∈ F.source := by rw [hsource]; exact hp
  have heq : F p = q := E.regularCrossing_right_unique (hcross p hp) h
  refine ⟨F, hsource, hpF, heq, heq ▸ F.map_source hpF, ?_, ?_⟩
  · intro x hx
    exact hcross x (by change x ∈ (W : Set E.incoming.terminalRegularOpen); rwa [← hsource])
  · intro x hx
    exact hmetric x (by change x ∈ (W : Set E.incoming.terminalRegularOpen); rwa [← hsource])

theorem metric_inner_eq_of_eventually_regularCrossing
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {XH : Type*} [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH}
    {X : Type*} [TopologicalSpace X] [ChartedSpace XH X]
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    {x : X} (hφ : MDifferentiableAt I ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    ∀ v w : TangentSpace I x,
      E.outputMetric.inner (ψ x)
        (mfderiv I ThreeModel ψ x v) (mfderiv I ThreeModel ψ x w) =
      E.terminal.metric.inner (φ x)
        (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, _, hx, _, _, hFcross, hmetric⟩ :=
    (hcross.self_of_nhds).exists_survivor_partialDiffeomorph E
  have hstay : ∀ᶠ y in 𝓝 x, φ y ∈ F.source :=
    hφ.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hx)
  have heq : ψ =ᶠ[𝓝 x] (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    filter_upwards [hcross, hstay] with y hy hys
    exact E.regularCrossing_right_unique hy (hFcross (φ y) hys)
  intro v w
  rw [heq.mfderiv_eq (I := I) (I' := ThreeModel), heq.self_of_nhds, mfderiv_comp x
    (F.mdifferentiableAt (by simp) hx) hφ]
  exact hmetric (φ x) hx _ _

variable {V XH : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace XH X]

theorem exists_survivor_partialDiffeomorph_of_regularCrossing_chart
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x))
    (x₀ : X) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = range φ ∧ ψ = (F : _ → _) ∘ φ ∧
      ∀ p ∈ F.source, ∀ v w : TangentSpace ThreeModel p,
        E.outputMetric.inner (F p) (mfderiv ThreeModel ThreeModel (F : _ → _) p v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) p w) =
          E.terminal.metric.inner p v w := by
  let W : Opens E.incoming.terminalRegularOpen :=
    ⟨range φ, Manifold.isOpen_range_of_isSmoothEmbedding hdim hφ⟩
  have hW : ∀ p ∈ W, p.val ∈ interior (Subtype.val '' E.old) := by
    rintro p ⟨y, rfl⟩
    exact E.mem_interior_old_of_regularCrossing (hcross y)
  obtain ⟨F, hsource, hcrossF, _, hmetric⟩ := E.exists_survivor_partialDiffeomorph
    W ⟨φ x₀, mem_range_self x₀⟩ hW
  have heq : ψ = (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    funext y
    exact E.regularCrossing_right_unique (hcross y) (hcrossF (φ y) (mem_range_self y))
  refine ⟨F, hsource, heq, ?_⟩
  intro p hp
  exact hmetric p (by
    change p ∈ (W : Set E.incoming.terminalRegularOpen)
    rwa [← hsource])

theorem isSmoothEmbedding_of_regularCrossing_chart
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x)) :
    IsSmoothEmbedding I ThreeModel ∞ ψ := by
  by_cases hX : Nonempty X
  · obtain ⟨F, hsource, heq, _⟩ :=
      E.exists_survivor_partialDiffeomorph_of_regularCrossing_chart φ ψ hφ hdim hcross hX.some
    rw [heq]
    exact DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F hφ
      (by rw [hsource])
  · let _ : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨⟨PUnit, inferInstance, inferInstance, fun x => isEmptyElim x⟩,
      ⟨⟨by ext s; simp⟩, fun x => isEmptyElim x⟩⟩

theorem regularCrossing_chart_metric_inner
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x))
    (x : X) (v w : TangentSpace I x) :
    E.outputMetric.inner (ψ x) (mfderiv I ThreeModel ψ x v)
        (mfderiv I ThreeModel ψ x w) =
      E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
        (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, hsource, heq, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph_of_regularCrossing_chart φ ψ hφ hdim hcross x
  have hmd : MDifferentiableAt ThreeModel ThreeModel
      (F : E.incoming.terminalRegularOpen → Q.Carrier) (φ x) :=
    F.mdifferentiableAt (by simp) (by rw [hsource]; exact mem_range_self x)
  have hd := mfderiv_comp x hmd (hφ.contMDiff.mdifferentiableAt (by simp))
  rw [heq, hd]
  exact hmetric (φ x) (by rw [hsource]; exact mem_range_self x)
    (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w)

theorem immersionInducedMetric_eq_of_regularCrossing_chart [IsManifold I ∞ X] [T2Space X]
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x)) :
    immersionInducedMetric E.terminal.metric hφ.isImmersion =
      immersionInducedMetric E.outputMetric
        (E.isSmoothEmbedding_of_regularCrossing_chart φ ψ hφ hdim hcross).isImmersion := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [immersionInducedMetric_inner]
  exact (E.regularCrossing_chart_metric_inner φ ψ hφ hdim hcross x v w).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem RegularCrossing.mem_terminalRegularRegion
    {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    p ∈ E.incoming.terminalRegularRegion := by
  obtain ⟨z, _, hp, _⟩ := h
  have heq : (E.oldTerminal z).val = p := (E.oldTerminal_eq z).trans hp
  exact heq ▸ (E.oldTerminal z).property

variable {V XH : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace XH X]

theorem exists_terminal_chart_of_regularCrossing
    (f : X → P.Carrier) (ψ : X → Q.Carrier)
    (hf : IsSmoothEmbedding I ThreeModel ∞ f)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (f x) (ψ x)) :
    ∃ φ : X → E.incoming.terminalRegularOpen,
      (∀ x, (φ x).val = f x) ∧ IsSmoothEmbedding I ThreeModel ∞ φ ∧
      IsSmoothEmbedding I ThreeModel ∞ ψ ∧
      ∀ (x : X) (v w : TangentSpace I x),
        E.outputMetric.inner (ψ x) (mfderiv I ThreeModel ψ x v)
          (mfderiv I ThreeModel ψ x w) =
        E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
          (mfderiv I ThreeModel φ x w) := by
  let φ : X → E.incoming.terminalRegularOpen := fun x =>
    ⟨f x, (hcross x).mem_terminalRegularRegion E⟩
  have hφ : IsSmoothEmbedding I ThreeModel ∞ φ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
      E.incoming.terminalRegularOpen φ hf
  exact ⟨φ, fun _ => rfl, hφ,
    E.isSmoothEmbedding_of_regularCrossing_chart φ ψ hφ hdim hcross,
    E.regularCrossing_chart_metric_inner φ ψ hφ hdim hcross⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
