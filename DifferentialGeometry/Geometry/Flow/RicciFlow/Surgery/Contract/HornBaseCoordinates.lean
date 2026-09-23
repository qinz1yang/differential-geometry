import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents
import DifferentialGeometry.Topology.Connected.CoverBySides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

set_option autoImplicit false
noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem subset_positive_horn_of_isPreconnected_of_scalar_gt
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set D.slab.terminalRegularOpen} (hS : IsPreconnected S)
    (hmeet : (S ∩ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))).Nonempty)
    (hscalar : ∀ x ∈ S, Λ * (P.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x) :
    S ⊆ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
  have hdisj : Disjoint S (frontier (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))) := by
    rw [P.frontier_positive_horn_eq_base]
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, rfl⟩
    exact (not_lt_of_ge (P.horn_base_scalar c e y)) (hscalar _ hx)
  have h :=
    DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      hS hmeet hdisj
  simpa only [(P.isOpen_positive_horn c e).interior_eq] using h

theorem neckCentralDomain_subset_positive_horn_of_scale_gt
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (hcenter : N.center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ) * N.scale) :
    N.chart '' neckCentralDomain δ ⊆ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
  apply P.subset_positive_horn_of_isPreconnected_of_scalar_gt c e
    ((isPreconnected_neckCentralDomain δ).image _ N.chart.continuous.continuousOn)
  · let z : neckBuffer δ := ⟨(N.sphereMark, 0), by
      change -δ⁻¹ - 1 < 0 ∧ 0 < δ⁻¹ + 1
      constructor <;> linarith [inv_pos.mpr N.delta_pos]⟩
    have hz : z ∈ neckCentralDomain δ := by
      change -δ⁻¹ < 0 ∧ 0 < δ⁻¹
      constructor <;> linarith [inv_pos.mpr N.delta_pos]
    exact ⟨N.center, ⟨z, hz, N.marked⟩, hcenter⟩
  · rintro x ⟨q, hq, rfl⟩
    have hr := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδ q ⟨hq.1.le, hq.2.le⟩)).1
    have hlower : (1 - 4323 * δ) * N.scale ≤
        metricScalarAt D.terminal.metric (N.chart q) :=
      (le_div_iff₀ N.scale_pos).mp (by linarith)
    exact hscale.trans_le hlower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

theorem exists_neck_coordinates_in_horn_of_base_scalar_bound
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (hcenter : N.center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ) * N.scale) :
    ∃ Θ : neckCentralOpen δ → positiveHornDomain,
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
      ∀ q : neckCentralOpen δ,
        P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) := by
  have hsub := P.neckCentralDomain_subset_positive_horn_of_scale_gt c e N hk hδ hcenter hscale
  let F : neckCentralOpen δ → (P.positiveHornMap_local c e).image := fun q =>
    ⟨N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q), by
      have hq : Opens.inclusion (neckCentralOpen_le_buffer δ) q ∈ neckCentralDomain δ :=
        q.property.2
      obtain ⟨z,hz,heq⟩ := hsub (mem_image_of_mem N.chart hq)
      exact ⟨⟨z,hz⟩,heq⟩⟩
  let Θ := (P.positiveHornDiffeomorph c e).symm ∘ F
  have hinc : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (Opens.inclusion (neckCentralOpen_le_buffer δ)) := by
    apply isSmoothEmbedding_intoOpen NeckCylinderModel NeckCylinderModel (neckBuffer δ)
    exact IsSmoothEmbedding.of_opens (I := NeckCylinderModel) (neckCentralOpen δ)
  have hcomp : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      ((N.chart : neckBuffer δ → D.slab.terminalRegularOpen) ∘
        Opens.inclusion (neckCentralOpen_le_buffer δ)) :=
    IsSmoothEmbedding.comp N.chart_smooth hinc (by simp)
  have hF : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ F :=
    isSmoothEmbedding_intoOpen NeckCylinderModel ThreeModel _ F hcomp
  have hΘ : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ :=
    IsSmoothEmbedding.comp
      (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding
        (P.positiveHornDiffeomorph c e).symm) hF (by simp)
  refine ⟨Θ,hΘ,?_⟩
  intro q
  exact diffeomorphOntoImage_symm_apply (P.positiveHornMap c e) (P.positiveHornMap_local c e)
    (P.horn_interior_embedding c e).isEmbedding.injective (F q)

private theorem exists_pos_height_lower_on_neck_compact
    {δ : ℝ} (Θ : neckCentralOpen δ → positiveHornDomain)
    (hΘ : Continuous Θ) {R : ℝ} (hR : 0 ≤ R) (hfit : R < δ⁻¹) :
    ∃ m : ℝ, 0 < m ∧ ∀ q : neckCentralOpen δ, |q.val.2| ≤ R → m ≤ (Θ q).val.2 := by
  let S : Set NeckCylinder := univ ×ˢ Icc (-R) R
  have hS : IsCompact S := isCompact_univ.prod isCompact_Icc
  have hsub : S ⊆ neckCentralOpen δ := by
    intro q hq
    exact ⟨mem_univ _,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  let K : Set (neckCentralOpen δ) := Subtype.val ⁻¹' S
  have hK : IsCompact K := _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hS
    (fun q hq => ⟨⟨q,hsub hq⟩,rfl⟩)
  have hne : K.Nonempty := by
    refine ⟨⟨(Geometry.Neck.spherePoint,0),mem_univ _,?_,?_⟩,?_,?_⟩
    · linarith
    · linarith
    · exact mem_univ _
    · exact ⟨by linarith, hR⟩
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne
    ((continuous_subtype_val.comp hΘ).snd.continuousOn)
  refine ⟨(Θ p).val.2,(Θ p).property.2,?_⟩
  intro q hq
  exact hmin ⟨mem_univ _,(abs_le.mp hq).1,(abs_le.mp hq).2⟩

theorem exists_neck_coordinates_with_positive_height_of_base_scalar_bound
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ β : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hβ : δ ≤ β) (hβ1 : β < 1)
    (hfit : β⁻¹ < δ⁻¹)
    (hcenter : N.center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ) * N.scale) :
    ∃ Θ : neckCentralOpen β → positiveHornDomain,
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
      (∀ q : neckCentralOpen β,
        P.horn c e (Θ q).val =
          (N.monoDelta hβ hβ1).chart (Opens.inclusion (neckCentralOpen_le_buffer β) q)) ∧
      ∃ m : ℝ, 0 < m ∧ ∀ q : neckCentralOpen β, m ≤ (Θ q).val.2 := by
  obtain ⟨Θ,hΘ,hmap⟩ :=
    P.exists_neck_coordinates_in_horn_of_base_scalar_bound c e N hk hδ hcenter hscale
  have hβpos : 0 < β := N.delta_pos.trans_le hβ
  have hsub : neckCentralOpen β ≤ neckCentralOpen δ := by
    intro q hq
    exact ⟨mem_univ _,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  let inc := Opens.inclusion hsub
  have hinc : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ inc :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSmoothEmbedding_opens_inclusion hsub
  obtain ⟨m,hm,hheight⟩ := exists_pos_height_lower_on_neck_compact Θ hΘ.contMDiff.continuous
    (inv_nonneg.mpr hβpos.le) hfit
  refine ⟨Θ ∘ inc,hΘ.comp hinc (by simp),?_,m,hm,?_⟩
  · intro q
    exact hmap (inc q)
  · intro q
    exact hheight (inc q) (abs_le.mpr ⟨q.property.2.1.le,q.property.2.2.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end
