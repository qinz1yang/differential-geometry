import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OpenEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.Homeomorph.SmallPerturbation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private def compactExhaustionOfPieceTower {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}
    (T : LocallyFinitePieceTower n X U) (hU : IsOpen U) : CompactExhaustion U where
  toFun i := Subtype.val ⁻¹' T.N i
  isCompact' i := Topology.IsInducing.subtypeVal.isCompact_preimage' (T.isCompact i)
    (by simpa only [Subtype.range_coe] using T.subset i)
  subset_interior_succ' i := fun x hx =>
    preimage_interior_subset_interior_preimage continuous_subtype_val (T.subset_interior hU i hx)
  iUnion_eq' := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    have hx : (x : X) ∈ ⋃ i, T.N i := by
      rw [T.iUnion_eq]
      exact x.property
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, hi⟩

theorem exists_continuousOn_pos_image_eq_of_isOpen
    {m : ℕ} {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂]
    [HasGroupoid M₁ (plGroupoid (m + 1))]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ ε : M₁ → ℝ, ContinuousOn ε U ∧ (∀ x ∈ U, 0 < ε x) ∧
      (∀ x ∈ U, ε x ≤ φ x) ∧
      ∀ f : M₁ → M₂, ContinuousOn f U → InjOn f U → IsOpenMap (U.domRestrict f) →
        (∀ x ∈ U, dist (f x) (h x) < ε x) → f '' U = h '' U := by
  classical
  by_cases hne : U.Nonempty
  · let : Nonempty M₁ := ⟨hne.choose⟩
    obtain ⟨T, -⟩ := exists_locallyFinitePieceTower_of_isOpen (m := m) hU
    have hhcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
    have hhinj : InjOn h U := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hh.injective (show (U.domRestrict h) ⟨x, hx⟩ =
        (U.domRestrict h) ⟨y, hy⟩ from hxy))
    have himage : IsOpen (h '' U) :=
      isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin (m + 1))) hU hhcont hhinj
    let : LocallyPathConnectedSpace M₂ :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂
    exact exists_continuousOn_pos_image_eq_of_dist_lt hh himage
      (compactExhaustionOfPieceTower T hU) φ hφ hpos
  · have hUempty : U = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨φ, hφ, hpos, fun _ _ => le_rfl, ?_⟩
    intro f _ _ _ _
    simp only [hUempty, Set.image_empty]

theorem exists_isPLHomeomorphInto_image_eq_dist_lt_of_approximation
    {m : ℕ} {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂]
    [HasGroupoid M₁ (plGroupoid (m + 1))]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (happrox : ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
      ∃ f : M₁ → M₂, IsPLHomeomorphInto (m + 1) f U ∧
        ∀ x ∈ U, dist (f x) (h x) < ψ x)
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto (m + 1) f U ∧ f '' U = h '' U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  obtain ⟨ε, hεcont, hεpos, hεle, himage⟩ :=
    exists_continuousOn_pos_image_eq_of_isOpen (m := m) hU hh φ hφ hpos
  obtain ⟨f, hf, hclose⟩ := happrox ε hεcont hεpos
  exact ⟨f, hf, himage f hf.continuousOn hf.injOn (hf.isOpenMap_domRestrict hU) hclose,
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
  exact exists_isPLHomeomorphInto_image_eq_dist_lt_of_approximation (m := 2) hU hh
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
