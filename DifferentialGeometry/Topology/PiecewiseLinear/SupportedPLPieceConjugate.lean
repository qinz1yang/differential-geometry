/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CellEnlargements
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLCellExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.exists_supported_conjugate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (T : PLPieceIn E n M W)
    {τ : E → E} (hτ : IsPLHomeomorphOn τ T.complex.space T.complex.space)
    {K : Set E} (hK : IsCompact K) (hKP : K ⊆ T.complex.space)
    (hKW : T.map '' K ⊆ interior W) (hfix : EqOn τ id (T.complex.space \ K)) :
    ∃ φ : M ≃ₜ M, IsPL n n φ ∧ IsPL n n φ.symm ∧
      (∀ x ∈ T.complex.space, φ (T.map x) = T.map (τ x)) ∧
      EqOn φ id (T.map '' K)ᶜ := by
  classical
  let q := Function.invFunOn T.map T.complex.space
  let σ := Function.invFunOn τ T.complex.space
  let F := T.map ∘ τ ∘ q
  let G := T.map ∘ σ ∘ q
  have hq : MapsTo q W T.complex.space := T.bijOn.surjOn.mapsTo_invFunOn
  have hσ : MapsTo σ T.complex.space T.complex.space := hτ.symm.bijOn.mapsTo
  have hF : IsPLOn n n F W := T.isPLOn_conjugate hτ.isPiecewiseAffineOn hτ.bijOn.mapsTo
  have hG : IsPLOn n n G W := T.isPLOn_conjugate hτ.symm.isPiecewiseAffineOn hσ
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
  have hFfix : EqOn F id (W \ T.map '' K) := by
    intro x hx
    have hqK : q x ∉ K := fun h => hx.2 ⟨q x, h, T.bijOn.invOn_invFunOn.2 hx.1⟩
    dsimp [F, Function.comp_def]
    rw [hfix ⟨hq hx.1, hqK⟩]
    exact T.bijOn.invOn_invFunOn.2 hx.1
  obtain ⟨φ, hφ, hφi, hφF, -, hφfix⟩ := exists_supported_isPL_homeomorph_extension
    (hK.image_of_continuousOn (T.continuousOn.mono hKP)).isClosed hKW hF hG hFW hGW
      hGF hFG hFfix
  refine ⟨φ, hφ, hφi, ?_, hφfix⟩
  intro x hx
  rw [hφF (T.bijOn.mapsTo hx)]
  dsimp [F, q, Function.comp_def]
  rw [T.bijOn.invOn_invFunOn.1 hx]

end DifferentialGeometry.Topology.PiecewiseLinear
