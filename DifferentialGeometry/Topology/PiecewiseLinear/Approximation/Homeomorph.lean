import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.Homeomorph.SmallPerturbation
open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

theorem exists_isPLHomeomorphInto_image_eq_dist_lt_of_approximation
    {n : ℕ} {M₁ : Type u} {M₂ : Type v} [TopologicalSpace M₁]
    [SecondCountableTopology M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (happrox : ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
      ∃ f : M₁ → M₂, IsPLHomeomorphInto n f U ∧
        ∀ x ∈ U, dist (f x) (h x) < ψ x)
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f U ∧ f '' U = h '' U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  obtain ⟨ε, hεcont, hεpos, hεle, himage⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_continuousOn_pos_image_eq_of_isOpen
      (E := EuclideanSpace ℝ (Fin n)) hU hh φ hφ hpos
  obtain ⟨f, hf, hclose⟩ := happrox ε hεcont hεpos
  exact ⟨f, hf, himage f hf.continuousOn hf.injOn hclose,
    fun x hx => (hclose x hx).trans_le (hεle x hx)⟩

theorem exists_isPLHomeomorphInto_image_eq_dist_lt_of_isOpen_three
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ f '' U = h '' U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  exact exists_isPLHomeomorphInto_image_eq_dist_lt_of_approximation (n := 3) hU hh
    (fun ψ hψ hψpos => exists_isPLHomeomorphInto_dist_lt_of_isOpen_three hU hh ψ hψ hψpos)
    φ hφ hpos

theorem exists_homeomorph_isPL_dist_lt_three
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (h : M₁ ≃ₜ M₂) (φ : M₁ → ℝ) (hφ : Continuous φ) (hpos : ∀ x, 0 < φ x) :
    ∃ f : M₁ ≃ₜ M₂, IsPL 3 3 f ∧ ∀ x, dist (f x) (h x) < φ x := by
  have hh : Topology.IsEmbedding (univ.domRestrict (h : M₁ → M₂)) :=
    h.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  obtain ⟨f, hf, himage, hclose⟩ := exists_isPLHomeomorphInto_image_eq_dist_lt_of_isOpen_three isOpen_univ hh φ
    hφ.continuousOn (fun x _ => hpos x)
  have hcont : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hinj : Function.Injective f := Set.injOn_univ.mp hf.injOn
  have hsurj : Function.Surjective f := by
    apply range_eq_univ.mp
    rw [← image_univ, himage, image_univ, h.surjective.range_eq]
  let g : M₁ ≃ₜ M₂ := (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont
    (isOpenMap_of_continuous_injective (E := EuclideanSpace ℝ (Fin 3)) hcont hinj)
  refine ⟨g, ?_, fun x => hclose x (mem_univ x)⟩
  change IsPL 3 3 f
  exact StructureGroupoid.liftPropOn_univ.mp hf.isPLOn

end DifferentialGeometry.Topology.PiecewiseLinear
