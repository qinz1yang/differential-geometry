import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckEssentiality
import DifferentialGeometry.Topology.Manifold.PositiveCylinderSupported
import DifferentialGeometry.Topology.SphereSeparation.PositiveProductBand

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology.SphereSeparation

universe u

open DifferentialGeometry.Topology.Manifold
  (exists_supported_diffeomorph_matching_positive_cylinder_sphere)

theorem exists_horn_neck_supported_sphere_matching_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌈ε⁻¹⌉₊ ≤ k →
          ∀ Θ : neckCentralOpen δ → positiveHornDomain,
            IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ →
            (∀ z, P.horn c e (Θ z).val =
              N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) →
            ∀ {ρ a b : ℝ}, 0 < a → ρ < a → a < b →
              (∀ z, b < (Θ z).val.2) →
              ∃ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel,NeckCylinderModel⟯ NeckCylinder)
                (η : Diffeomorph (𝓡 2) (𝓡 2) (Sphere 2) (Sphere 2) ∞),
                (∀ q : Sphere 2, F (η q,a) =
                  (Θ ⟨(q,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                    inv_pos.mpr N.delta_pos⟩).val) ∧
                ∃ K : Set NeckCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
                  EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hseparate⟩ := exists_horn_neck_end_separation_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε c e δ k N hδ hk Θ hΘ hmap ρ a b ha hρa hab hdepth
  obtain ⟨p,R,hR,hfrontl,hfrontr,hcll,hclr,hK,hcompact,hlo,hhi,hband⟩ :=
    hseparate P hε c e N hδ hk Θ hΘ hmap
  let s : Sphere 2 → neckCentralOpen δ := fun q =>
    ⟨(q,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
  have hs : IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞ s := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    have hid : IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : Sphere 2 => (q,(0 : ℝ))) := IsSmoothEmbedding.id
    exact hid.of_comp (J := NeckCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hσ : IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞ (Θ ∘ s) := hΘ.comp hs (by simp)
  have hleft : range (Θ ∘ s) ⊆ closure p.left := by rw [hcll]; exact subset_union_right
  have hright : range (Θ ∘ s) ⊆ closure p.right := by rw [hclr]; exact subset_union_right
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  have hlow : ∀ q : positiveHornDomain, q.val.2 < b → q ∈ p.left := by
    have h := p.lower_band_subset_left_of_separator_above (Real.exp_pos (-R)) hlo
      (r := b) (by rintro z ⟨q,rfl⟩; exact hdepth (s q))
    exact fun q hq => h q hq.le
  obtain ⟨F,η,hF,K,hKc,hKρ,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_matching_positive_cylinder_sphere
      (Θ ∘ s) hσ p hleft hright hK ha hρa hab hlow (fun q => hdepth (s q))
  exact ⟨F,η,hF,K,hKc,hKρ,hfix,hfixi⟩



theorem exists_deep_horn_neck_supported_sphere_matching_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (_ : c ∈ P.component)
          (e : P.hornIndex c) {ρ a b : ℝ}, 0 < a → ρ < a → a < b →
          ∃ Q : ℝ, 0 < Q ∧ ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
            δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ TerminalCorePresentation.hornHalfRange P c e →
              Q < N.scale →
            ∃ (Θ : neckCentralOpen δ → positiveHornDomain)
              (F : NeckCylinder ≃ₘ⟮NeckCylinderModel,NeckCylinderModel⟯ NeckCylinder)
              (η : Diffeomorph (𝓡 2) (𝓡 2) (Sphere 2) (Sphere 2) ∞),
              IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
              (∀ z, P.horn c e (Θ z).val =
                N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) ∧
              (∀ z, b < (Θ z).val.2) ∧
              (∀ q : Sphere 2, F (η q,a) =
                (Θ ⟨(q,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                  inv_pos.mpr N.delta_pos⟩).val) ∧
              ∃ K : Set NeckCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
                EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hseparate⟩ := exists_deep_horn_neck_end_separation_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε c hc e ρ a b ha hρa hab
  obtain ⟨Q,hQ,hcoords⟩ := hseparate P hε c hc e b
  refine ⟨Q,hQ,?_⟩
  intro δ k N hδ hk hcenter hscale
  obtain ⟨Θ,hΘ,hmap,hdepth,p,R,hR,hfrontl,hfrontr,hcll,hclr,hK,hcompact,hlo,hhi,hband⟩ :=
    hcoords N hδ hk hcenter hscale
  let s : Sphere 2 → neckCentralOpen δ := fun q =>
    ⟨(q,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
  have hs : IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞ s := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    have hid : IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : Sphere 2 => (q,(0 : ℝ))) := IsSmoothEmbedding.id
    exact hid.of_comp (J := NeckCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hσ : IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞ (Θ ∘ s) := hΘ.comp hs (by simp)
  have hleft : range (Θ ∘ s) ⊆ closure p.left := by rw [hcll]; exact subset_union_right
  have hright : range (Θ ∘ s) ⊆ closure p.right := by rw [hclr]; exact subset_union_right
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  have hlow : ∀ q : positiveHornDomain, q.val.2 < b → q ∈ p.left := by
    have h := p.lower_band_subset_left_of_separator_above (Real.exp_pos (-R)) hlo
      (r := b) (by rintro z ⟨q,rfl⟩; exact hdepth (s q))
    exact fun q hq => h q hq.le
  obtain ⟨F,η,hF,K,hKc,hKρ,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_matching_positive_cylinder_sphere
      (Θ ∘ s) hσ p hleft hright hK ha hρa hab hlow (fun q => hdepth (s q))
  exact ⟨Θ,F,η,hΘ,hmap,hdepth,hF,K,hKc,hKρ,hfix,hfixi⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
