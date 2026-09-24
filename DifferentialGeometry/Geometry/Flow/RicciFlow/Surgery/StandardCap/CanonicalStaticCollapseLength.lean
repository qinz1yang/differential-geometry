import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionQuotient
import DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private def centralToOpen (δ : ℝ) (q : neckCentralDomain δ) : openCylinder δ⁻¹ :=
  ⟨q.1.1, q.2⟩

private theorem centralToOpen_continuousOn (δ : ℝ)
    {a b : ℝ} (γ : ℝ → neckCentralDomain δ)
    (hγ : ContinuousOn γ (Icc a b)) :
    ContinuousOn (centralToOpen δ ∘ γ) (Icc a b) := by
  intro t ht
  change Tendsto (centralToOpen δ ∘ γ) (𝓝[Icc a b] t)
    (𝓝 (centralToOpen δ (γ t)))
  rw [tendsto_subtype_rng]
  have hneck : ContinuousOn (fun s => ((γ s).1 : neckBuffer δ)) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hγ
  have hpair : ContinuousOn (fun s => (((γ s).1 : neckBuffer δ) : NeckCylinder)) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hneck
  exact hpair t ht

private def centralPath {d : normalizedDatum g x₀ δ k}
    (γ : ℝ → neckCentralDomain δ) : ℝ → d.oriented.controlledImage :=
  fun t => ⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
    d.oriented.controlledMap_mem_controlledImage _⟩

private theorem centralPath_continuousOn {d : normalizedDatum g x₀ δ k}
    {a b : ℝ} (γ : ℝ → neckCentralDomain δ)
    (hγ : ContinuousOn γ (Icc a b)) :
    ContinuousOn (centralPath (d := d) γ) (Icc a b) := by
  have hraw : ContinuousOn (d.oriented.controlledMap ∘ centralToOpen δ ∘ γ)
      (Icc a b) :=
    (d.oriented.controlledMap_smooth.continuous).comp_continuousOn
      (centralToOpen_continuousOn δ γ hγ)
  intro t ht
  change Tendsto (centralPath (d := d) γ) (𝓝[Icc a b] t)
    (𝓝 (centralPath γ t))
  rw [tendsto_subtype_rng]
  exact hraw t ht

private theorem centralPath_val_eq {d : normalizedDatum g x₀ δ k}
    (γ : ℝ → neckCentralDomain δ) :
    (Subtype.val ∘ centralPath (d := d) γ) =
      (fun t => d.oriented.map (γ t).1) := by
  funext t
  change d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩) = d.oriented.map (γ t).1
  rw [d.oriented.controlledMap_apply]
  rfl

theorem CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck
    {d : normalizedDatum g x₀ δ k}
    {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (γ : ℝ → neckCentralDomain δ) (a b : ℝ)
    (hγ : ContinuousOn γ (Icc a b)) :
    DifferentialGeometry.Geometry.riemannianCurveVariation w.data.outMetric
        (w.data.collapse ∘ (fun t =>
          (⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
            d.oriented.controlledMap_mem_controlledImage _⟩ : d.oriented.controlledImage))) a b ≤
      DifferentialGeometry.Geometry.riemannianCurveVariation g
        (fun t => d.oriented.map (γ t).1) a b := by
  let : RegularSpace M := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  have hp := w.properties.collapse_length (centralPath (d := d) γ) a b
    (centralPath_continuousOn (d := d) γ hγ)
  rw [DifferentialGeometry.Geometry.riemannianCurveVariation_restrictOpen g
    d.oriented.controlledImage (centralPath (d := d) γ) a b
    (centralPath_continuousOn (d := d) γ hγ)] at hp
  rw [centralPath_val_eq (d := d) γ] at hp
  have hpath : centralPath (d := d) γ = (fun t =>
      (⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
        d.oriented.controlledMap_mem_controlledImage _⟩ : d.oriented.controlledImage)) := by
    rfl
  rw [hpath] at hp
  exact hp

end DifferentialGeometry.PDE.RicciFlow.StandardCap
