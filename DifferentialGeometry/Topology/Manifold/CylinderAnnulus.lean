import DifferentialGeometry.Topology.Manifold.SphereAnnulusBoundaryMatching
import DifferentialGeometry.Topology.Manifold.CylinderCollar.Coordinates
import DifferentialGeometry.Topology.Manifold.NestedBallShell
import DifferentialGeometry.Topology.SphereSeparation.TwoSphereDomain
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.Embedding.CompactFrontier
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_smooth_cylinder_annulus_parametrization
    {K : Set SphereCylinder} (hK : IsCompact K)
    (hregular : closure (interior K) = K) (hconn : IsPreconnected (interior K))
    (e₀ e₁ : S2 → SphereCylinder)
    (he₀ : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ e₁)
    (hfront : frontier K = range e₀ ∪ range e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = univ ∧ e.target = K ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm K ∧
      (∀ p : S2, e (p,0) = e₀ p) ∧ ∀ p : S2, e (η p,1) = e₁ p := by
  let v : S2 := Classical.arbitrary S2
  let C := cylinderExponentialChart v
  have hCs : C.source = univ := cylinderExponentialChart_source v
  have hCinj : Injective C := C.toPartialEquiv.injective_of_source_eq_univ hCs
  have hClocal : IsLocalDiffeomorph SphereCylinderModel (𝓡 3) ∞ C :=
    fun q => C.isLocalDiffeomorphAt _ _ _ (hCs ▸ mem_univ q)
  have hC : IsSmoothEmbedding SphereCylinderModel (𝓡 3) ∞ C :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective
      hClocal hCinj
  have hCo : _root_.Topology.IsOpenEmbedding C :=
    hClocal.isLocalHomeomorph.isOpenEmbedding_of_injective hCinj
  let L := C '' K
  have hLc : IsCompact L := hK.image hCo.continuous
  have hi : interior L = C '' interior K :=
    (DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding hCo K).symm
  have hLregular : closure (interior L) = L := by
    apply Subset.antisymm
    · exact hLc.isClosed.closure_interior_subset
    · rw [hi]
      calc
        L = C '' closure (interior K) := by rw [hregular]
        _ ⊆ closure (C '' interior K) := image_closure_subset_closure_image hCo.continuous
  have hLconn : IsPreconnected (interior L) := by
    rw [hi]
    exact hconn.image C hCo.continuous.continuousOn
  have hLe₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (C ∘ e₀) :=
    IsSmoothEmbedding.comp hC he₀ (by simp)
  have hLe₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (C ∘ e₁) :=
    IsSmoothEmbedding.comp hC he₁ (by simp)
  have hLf : frontier L = range (C ∘ e₀) ∪ range (C ∘ e₁) := by
    rw [show L = C '' K from rfl,
      ← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact hCo hK,
      hfront,image_union,← range_comp,← range_comp]
  have hLd : Disjoint (range (C ∘ e₀)) (range (C ∘ e₁)) := by
    rw [range_comp,range_comp]
    exact (disjoint_image_iff hCinj).mpr hdisj
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      ThreeManifold.smooth_schoenflies_three
  obtain ⟨outer,inner,hnest,hrange⟩ :=
    SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries
      hSch hLc hLregular hLconn (C ∘ e₀) (C ∘ e₁) hLe₀ hLe₁ hLf hLd
  obtain ⟨e,hes,het,he,hei⟩ := exists_smooth_nestedBallShell_parametrization (n := 2)
    outer.toPartialDiffeomorph inner.toPartialDiffeomorph zero_lt_one
    (subset_univ _) (subset_univ _) hnest v
  have het' : e.target = L := het.trans hrange.symm
  have heC : e.target ⊆ C.target := by
    rw [het']
    rintro x ⟨q,_,rfl⟩
    exact C.map_source (hCs ▸ mem_univ q)
  obtain ⟨Ψ,η,hΨ₀,hΨ₁⟩ := exists_parametrized_sphere_annulus_of_smooth_partial_equiv
    e hes he hei (C ∘ e₀) (C ∘ e₁) hLe₀ hLe₁ (by rw [het']; exact hLf)
  let em := Ψ.toEquiv.transPartialEquiv e
  have hems : em.source = univ := by
    change Ψ ⁻¹' e.source = univ
    rw [hes,preimage_univ]
  have hemt : em.target = e.target := rfl
  have hem : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ em := he.comp Ψ.contMDiff
  have hemi : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡∂ 1)) ∞ em.symm em.target :=
    Ψ.symm.contMDiff.comp_contMDiffOn hei
  let d := em.trans C.symm.toPartialEquiv
  have hds : d.source = univ := by
    ext p
    constructor
    · exact fun _ => mem_univ _
    · intro _
      have hp : p ∈ em.source := hems ▸ mem_univ p
      exact ⟨hp,heC (em.map_source hp)⟩
  have hdt : d.target = K := by
    ext q
    constructor
    · rintro ⟨hq,hqe⟩
      change C q ∈ e.target at hqe
      rw [het'] at hqe
      obtain ⟨x,hx,hxq⟩ := hqe
      exact hCinj hxq ▸ hx
    · intro hq
      refine ⟨show q ∈ C.source from hCs ▸ mem_univ q,?_⟩
      change C q ∈ e.target
      rw [het']
      exact mem_image_of_mem C hq
  refine ⟨d,η,hds,hdt,?_,?_,?_,?_⟩
  · apply contMDiffOn_univ.mp
    exact C.contMDiffOn_invFun.comp hem.contMDiffOn
      (fun p _ => heC (em.map_source (hems ▸ mem_univ p)))
  · exact hemi.comp (hC.contMDiff.contMDiffOn)
      (fun q hq => het'.symm ▸ mem_image_of_mem C hq)
  · intro p
    change C.symm (e (Ψ (p,0))) = e₀ p
    rw [hΨ₀]
    exact C.left_inv (hCs ▸ mem_univ _)
  · intro p
    change C.symm (e (Ψ (η p,1))) = e₁ p
    rw [hΨ₁]
    exact C.left_inv (hCs ▸ mem_univ _)

end DifferentialGeometry.Topology.Manifold
