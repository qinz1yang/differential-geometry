import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.StageTransport
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLOn_conjugate_on_polyhedron {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (T : PLPieceIn E n M W) {τ : E → E}
    (hτ : IsPiecewiseAffineOn τ T.complex.space) (hmap : MapsTo τ T.complex.space T.complex.space)
    {S : Set E} (hS : IsPolyhedron S) (hST : S ⊆ T.complex.space) :
    IsPLOn n n (T.map ∘ τ ∘ Function.invFunOn T.map T.complex.space) (T.map '' S) := by
  obtain ⟨R, -, -⟩ := T.exists_restrict_of_isPolyhedron hS hST
  obtain ⟨Q⟩ := R.exists_pLPiece
  have hSW : T.map '' S ⊆ W := image_subset_iff.mpr fun _ hx => T.bijOn.mapsTo (hST hx)
  let q := Function.invFunOn T.map T.complex.space ∘ Q.piece.map
  have hq : IsPiecewiseAffineOn q Q.piece.complex.space :=
    Q.piece.isPiecewiseAffineOn_transition_of_subset T hSW
  have hqm : MapsTo q Q.piece.complex.space T.complex.space :=
    fun _ hx => T.bijOn.surjOn.mapsTo_invFunOn (hSW (Q.piece.bijOn.mapsTo hx))
  have hpa : IsPiecewiseAffineOn (τ ∘ q) Q.piece.complex.space := by
    have hp := hτ.comp hq
    have hs : Q.piece.complex.space ⊆ q ⁻¹' T.complex.space := hqm
    rwa [inter_eq_left.mpr hs] at hp
  have hpl := T.isPLOn_comp hpa (hmap.comp hqm)
  apply Q.piece.isPLOn_of_eqOn_comp_invFunOn hpl
  intro x hx
  dsimp [q, Function.comp_def]
  rw [Q.piece.bijOn.invOn_invFunOn.2 hx]

theorem PLPieceIn.exists_equiv_conjugate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [HasGroupoid M (plGroupoid n)] {W : Set M} (T : PLPieceIn E n M W)
    {τ : E → E} (hτ : IsPLHomeomorphOn τ T.complex.space T.complex.space)
    {K : Set E} (hfix : EqOn τ id (T.complex.space \ K)) :
    ∃ φ : M ≃ M, (∀ x ∈ T.complex.space, φ (T.map x) = T.map (τ x)) ∧
      EqOn φ id (T.map '' K)ᶜ ∧
      ∀ S : Set E, IsPolyhedron S → S ⊆ T.complex.space →
        IsPLHomeomorphInto n φ (T.map '' S) := by
  classical
  let q := Function.invFunOn T.map T.complex.space
  let σ := Function.invFunOn τ T.complex.space
  let F := T.map ∘ τ ∘ q
  let G := T.map ∘ σ ∘ q
  have hq : MapsTo q W T.complex.space := T.bijOn.surjOn.mapsTo_invFunOn
  have hσ : MapsTo σ T.complex.space T.complex.space := hτ.symm.bijOn.mapsTo
  have hFW : MapsTo F W W := T.bijOn.mapsTo.comp (hτ.bijOn.mapsTo.comp hq)
  have hGW : MapsTo G W W := T.bijOn.mapsTo.comp (hσ.comp hq)
  have hGF : LeftInvOn G F W := by
    intro x hx
    dsimp [G, F, q, σ, Function.comp_def]
    rw [T.bijOn.invOn_invFunOn.1 (hτ.bijOn.mapsTo (hq hx)),
      hτ.bijOn.invOn_invFunOn.1 (hq hx), T.bijOn.invOn_invFunOn.2 hx]
  have hFG : LeftInvOn F G W := by
    intro x hx
    dsimp [G, F, q, σ, Function.comp_def]
    rw [T.bijOn.invOn_invFunOn.1 (hσ (hq hx)),
      hτ.bijOn.invOn_invFunOn.2 (hq hx), T.bijOn.invOn_invFunOn.2 hx]
  let f := W.piecewise F id
  let g := W.piecewise G id
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ W
    · change W.piecewise G id (W.piecewise F id x) = x
      rw [piecewise_eq_of_mem W F id hx, piecewise_eq_of_mem W G id (hFW hx)]
      exact hGF hx
    · change W.piecewise G id (W.piecewise F id x) = x
      rw [piecewise_eq_of_notMem W F id hx]
      exact piecewise_eq_of_notMem W G id hx
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ W
    · change W.piecewise F id (W.piecewise G id x) = x
      rw [piecewise_eq_of_mem W G id hx, piecewise_eq_of_mem W F id (hGW hx)]
      exact hFG hx
    · change W.piecewise F id (W.piecewise G id x) = x
      rw [piecewise_eq_of_notMem W G id hx]
      exact piecewise_eq_of_notMem W F id hx
  let φ : M ≃ M := ⟨f, g, hgf, hfg⟩
  have hφF : EqOn φ F W := fun x hx => piecewise_eq_of_mem W F id hx
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x hx
    rw [hφF (T.bijOn.mapsTo hx)]
    dsimp [F, q, Function.comp_def]
    rw [T.bijOn.invOn_invFunOn.1 hx]
  · intro x hx
    by_cases hxW : x ∈ W
    · have hqK : q x ∉ K := fun h => hx ⟨q x, h, T.bijOn.invOn_invFunOn.2 hxW⟩
      rw [hφF hxW]
      dsimp [F, Function.comp_def]
      rw [hfix ⟨hq hxW, hqK⟩]
      exact T.bijOn.invOn_invFunOn.2 hxW
    · exact piecewise_eq_of_notMem W F id hxW
  · intro S hS hST
    have hSF : IsPLOn n n F (T.map '' S) :=
      isPLOn_conjugate_on_polyhedron T hτ.isPiecewiseAffineOn hτ.bijOn.mapsTo hS hST
    have hSφ : IsPLOn n n φ (T.map '' S) := by
      intro x hx
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem (hSF x hx)
        _ hx
      rintro y ⟨z, hz, rfl⟩
      exact hφF (T.bijOn.mapsTo (hST hz))
    exact hSφ.isPLHomeomorphInto
      (hS.isCompact.image_of_continuousOn (T.continuousOn.mono hST)) φ.injective.injOn

end DifferentialGeometry.Topology.PiecewiseLinear
