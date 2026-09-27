import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev NeckE3 := EuclideanSpace ℝ (Fin 3)
private abbrev NeckIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ NeckE3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiff_neckAmbientMap (U : Opens M) {g : SmoothRiemannianMetric I U}
    {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k) :
    ContMDiff NeckIC I ∞ (neckAmbientMap U d) :=
  (contMDiff_subtype_val (I := I) (U := U)).comp d.smooth

theorem neckAmbientMap_mfderiv (U : Opens M) {g : SmoothRiemannianMetric I U}
    {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k) (x : bufferedCylinder δ) :
    mfderiv NeckIC I (neckAmbientMap U d) x = mfderiv NeckIC I d.map x := by
  change mfderiv NeckIC I ((Subtype.val : U → M) ∘ d.map) x = _
  rw [mfderiv_comp x
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiable (by decide) (d.map x))
    (d.smooth.mdifferentiable (by decide) x), mfderiv_subtype_val]
  rfl

theorem normalizedNeckFamily_isManifold {ι : Type*} [Finite ι] {precision : ι → ℝ}
    {L : ℝ} (hL : 0 < L) (U : Opens M) (g : SmoothRiemannianMetric I U)
    (x₀ : ι → U) (order : ι → ℕ) (d : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
    (hdisj : Pairwise (fun i j => Disjoint (range (neckAmbientMap U (d i))) (range (neckAmbientMap U (d j))))) :
    let f := fun i => neckAmbientMap U (d i)
    let hf := fun i => isOpenEmbedding_neckAmbientMap U (d i)
    let hδ := fun i => (d i).precision_pos
    let Q := FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj
    let : ChartedSpace NeckE3 Q := finiteCapChartedSpace I Fact.out hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ Q := by
  dsimp only
  apply finiteCapQuotient_isManifold_of_immersion Fact.out hL (fun i => (d i).precision_pos)
    (fun i => neckAmbientMap U (d i)) (fun i => isOpenEmbedding_neckAmbientMap U (d i)) hdisj
    (fun i => contMDiff_neckAmbientMap U (d i))
  intro i x
  rw [neckAmbientMap_mfderiv]
  exact (d i).immersion x
end DifferentialGeometry.Topology.ThreeManifold.Surgery
