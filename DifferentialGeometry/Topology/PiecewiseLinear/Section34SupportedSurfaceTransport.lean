import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.supported_image_preserving_carrier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S K N : Geometry.SimplicialComplex ℝ E)
    [Finite S.faces] [Finite K.faces] [Finite N.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hKS : K.space ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {Φ : E → E} (hΦ : IsPLHomeomorphOn Φ univ univ)
    (hfix : EqOn Φ id (interior S.space)ᶜ) (hNspace : N.space = Φ '' K.space) :
    IsCombinatorialManifold 2 N ∧ IsConnected N.space ∧ IsCompact N.space ∧
      N.space ⊆ interior S.space ∧ CarriesFundamentalGroupOnto N.space S.space ∧
      Φ '' S.space = S.space ∧ Φ '' interior S.space = interior S.space := by
  let H : E ≃ₜ E :=
    { toFun := Φ
      invFun := Function.invFunOn Φ univ
      left_inv := fun x => hΦ.bijOn.invOn_invFunOn.1 (mem_univ x)
      right_inv := fun x => hΦ.bijOn.invOn_invFunOn.2 (mem_univ x)
      continuous_toFun := continuousOn_univ.mp hΦ.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hΦ.isPiecewiseAffineOn_invFunOn.continuousOn }
  have hHS : Φ '' S.space = S.space :=
    image_eq_of_homeomorph_eqOn_compl_of_subset H hfix interior_subset
  have hHint : Φ '' interior S.space = interior S.space :=
    (H.image_interior S.space).trans (congrArg interior hHS)
  have hKN : IsPLHomeomorphOn Φ K.space N.space := by
    rw [hNspace]
    exact hΦ.restrict (isPolyhedron_space K) (subset_univ K.space)
  have hNconn : IsConnected N.space := by
    rw [hNspace]
    exact hconn.image H H.continuous.continuousOn
  have hNint : N.space ⊆ interior S.space := by
    rw [hNspace, ← hHint]
    exact image_mono hKS
  have hNgen := hgen.image_of_compact (isPolyhedron_space S).isCompact
    H.continuous.continuousOn H.injective.injOn
  change CarriesFundamentalGroupOnto (Φ '' K.space) (Φ '' S.space) at hNgen
  rw [hHS, ← hNspace] at hNgen
  exact ⟨hK.of_isPLHomeomorphOn hKN, hNconn, (isPolyhedron_space N).isCompact,
    hNint, hNgen, hHS, hHint⟩

theorem IsCombinatorialManifold.exists_supported_image_preserving_carrier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S K : Geometry.SimplicialComplex ℝ E) [Finite S.faces] [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hKS : K.space ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {Φ : E → E} (hΦ : IsPLHomeomorphOn Φ univ univ)
    (hfix : EqOn Φ id (interior S.space)ᶜ) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧ N.space = Φ '' K.space ∧
      IsCombinatorialManifold 2 N ∧ IsConnected N.space ∧ IsCompact N.space ∧
      N.space ⊆ interior S.space ∧ CarriesFundamentalGroupOnto N.space S.space ∧
      Φ '' S.space = S.space ∧ Φ '' interior S.space = interior S.space := by
  have hΦK := hΦ.isPiecewiseAffineOn.mono_of_isPolyhedron
    (isPolyhedron_space K) (subset_univ K.space)
  obtain ⟨N, hNfin, hNspace, -⟩ := exists_isPLHomeomorphOn_image K hΦK
    (hΦ.bijOn.injOn.mono (subset_univ K.space))
  let _ : Finite N.faces := hNfin.to_subtype
  exact ⟨N, hNfin, hNspace,
    hK.supported_image_preserving_carrier S K N hconn hKS hgen hΦ hfix hNspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
