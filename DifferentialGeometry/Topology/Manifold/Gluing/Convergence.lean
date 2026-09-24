import DifferentialGeometry.Topology.Manifold.Gluing.EventualAgreement
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Locality
import DifferentialGeometry.Topology.Maps.OpenCoordinateAgreement

section

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {ι Q E G H : Type*}
  [TopologicalSpace Q] [LocallyCompactSpace Q] [RegularSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  [ChartedSpace E Q] {J : ModelWithCorners ℝ G H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem exists_contMDiffOn_mapCInfConvergenceOnCompacts_of_open_coordinate_cover
    (U : TopologicalSpace.Opens E) (inc : ι → U → Q)
    (hinj : ∀ i, Function.Injective (inc i))
    (hinc : ∀ i, IsLocalDiffeomorph (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (inc i))
    (V : TopologicalSpace.Opens Q) (hV : IsCompact (closure (V : Set Q)))
    (hcover : ∀ q ∈ closure (V : Set Q), ∃ i z, inc i z = q)
    (W : ι × U → Set E) (hW : ∀ a, IsOpen (W a))
    (hcenter : ∀ a : ι × U, (a.2 : E) ∈ W a)
    (f : (ι × U) → ∀ k, E → M k) (b : ∀ k, M k)
    (c : ι → ∀ k, M k → E) (T : ι → ∀ k, Set (M k))
    (hsmooth : ∀ a, ∀ᶠ k in atTop,
      ContMDiffOn (modelWithCornersSelf ℝ E) J ∞ (f a k) (W a))
    (hconv : ∀ a, MapCInfConvergenceOnCompacts (W a)
      (fun k z => c a.1 k (f a k z)) id)
    (hmem : ∀ a (K : Set E), IsCompact K → K ⊆ W a →
      ∀ᶠ k in atTop, MapsTo (f a k) K (T a.1 k))
    (hcompat : ∀ a a' (L : Set Q), IsCompact L →
      L ⊆ (inc a.1 '' (Subtype.val ⁻¹' W a)) ∩
        (inc a'.1 '' (Subtype.val ⁻¹' W a')) →
      ∀ᶠ k in atTop, EqOn
        (Function.extend (inc a.1) (fun z : U => f a k z) (fun _ => b k))
        (Function.extend (inc a'.1) (fun z : U => f a' k z) (fun _ => b k)) L)
    (a₀ : ι × U) (ha₀ : inc a₀.1 a₀.2 ∈ V)
    (hanchor : ∀ᶠ k in atTop, f a₀ k a₀.2 = b k) :
    ∃ F : ∀ k, Q → M k,
      (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) J ∞ (F k) V) ∧
      (∀ᶠ k in atTop, F k (inc a₀.1 a₀.2) = b k) ∧
      (∀ i, MapCInfConvergenceOnCompacts (Subtype.val '' ((inc i) ⁻¹' (V : Set Q)))
        (fun k z => @dite E (z ∈ U) (Classical.propDecidable _)
          (fun hz => c i k (F k (inc i ⟨z, hz⟩))) (fun _ => 0)) id) ∧
      (∀ i (K : Set E), IsCompact K →
        K ⊆ Subtype.val '' ((inc i) ⁻¹' (V : Set Q)) →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ K → F k (inc i ⟨z, hz⟩) ∈ T i k) ∧
      ∀ k q, q ∉ V → F k q = b k := by
  obtain ⟨F, hFsmooth, hFagree, hFout⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_eventually_eqOn_of_open_coordinate_cover
      U inc hinj hinc V hV hcover W hW hcenter f b hsmooth hcompat
  refine ⟨F, hFsmooth, ?_, ?_, ?_, hFout⟩
  · have hsingle : {inc a₀.1 a₀.2} ⊆
        (V : Set Q) ∩ (inc a₀.1 '' (Subtype.val ⁻¹' W a₀)) := by
      exact singleton_subset_iff.mpr ⟨ha₀, a₀.2, hcenter a₀, rfl⟩
    filter_upwards [hFagree a₀ _ isCompact_singleton hsingle, hanchor] with k hk ha
    exact (hk (mem_singleton _)).trans ((hinj a₀.1).extend_apply _ _ a₀.2 |>.trans ha)
  · intro i
    exact MapCInfConvergenceOnCompacts.of_compact_agreement_in_open_coordinates
      U (inc i) (hinj i) (hinc i).contMDiff.continuous V V.isOpen
      (fun a => W (i, a)) (fun a => hW (i, a)) (fun a => hcenter (i, a))
      (fun a => f (i, a)) b (c i) F id (fun a => hconv (i, a))
      (fun a => hFagree (i, a))
  · intro i K hK hKD
    exact DifferentialGeometry.Topology.eventually_mem_of_compact_agreement_in_open_coordinates
      U (inc i) (hinj i) (hinc i).contMDiff.continuous V V.isOpen
      (fun a => W (i, a)) (fun a => hW (i, a)) (fun a => hcenter (i, a))
      (fun a => f (i, a)) b F (T i) (fun a => hmem (i, a))
      (fun a => hFagree (i, a)) K hK hKD

end DifferentialGeometry.CheegerGromovCompactness

end

end
