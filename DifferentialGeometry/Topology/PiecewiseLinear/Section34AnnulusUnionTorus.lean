import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusEuler
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.TorusOfOrientableEulerCharZero

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLTorus_union_of_isPLHomeomorphOn_annuli
    {J : Set E} {K : Set F} (hJ : IsPLSphere 1 J) (hK : IsPLSphere 1 K)
    {A B : Set (EuclideanSpace ℝ (Fin 3))}
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    {σ : F × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) A)
    (hσ : IsPLHomeomorphOn σ (K ×ˢ Icc (0 : ℝ) 1) B)
    (hleft : A ∩ B = ρ '' (J ×ˢ {(0 : ℝ), 1}))
    (hright : A ∩ B = σ '' (K ×ˢ {(0 : ℝ), 1})) : IsPLTorus (A ∪ B) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨L, hLfin, hL, hLc, hLspace, hLboundary⟩ :=
    hρ.exists_annulus_complex hJ zero_lt_one
  obtain ⟨M, hMfin, hM, hMc, hMspace, hMboundary⟩ :=
    hσ.exists_annulus_complex hK zero_lt_one
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite M.faces := hMfin.to_subtype
  have hboundaryL : L.space ∩ M.space = (boundaryComplex 2 L).space := by
    rw [hLspace, hMspace, hLboundary, hleft]
  have hboundaryM : L.space ∩ M.space = (boundaryComplex 2 M).space := by
    rw [hLspace, hMspace, hMboundary, hright]
  obtain ⟨N, hNfin, hN, hNspace⟩ :=
    exists_isCombinatorialManifold_space_union L M hL hM hboundaryL hboundaryM
  let _ : Finite N.faces := hNfin.to_subtype
  have hNc : IsConnected N.space := by
    rw [hNspace]
    apply IsConnected.union ?_ hLc hMc
    obtain ⟨x, hx⟩ := hJ.nonempty
    rw [hLspace, hMspace, hleft]
    exact ⟨ρ (x, 0), ⟨(x, 0), ⟨hx, Or.inl rfl⟩, rfl⟩⟩
  obtain ⟨P, hPfin, hPspace⟩ := hK.isPolyhedron.exists_simplicialComplex
  let _ : Finite P.faces := hPfin.to_subtype
  have hMχ : eulerChar M = 0 :=
    eulerChar_eq_zero_of_isPLHomeomorphOn_prod_Icc P M (hPspace.symm ▸ hK)
      zero_le_one (by rw [hPspace, hMspace]; exact hσ)
  have hNχ : eulerChar N = 0 := by
    rw [← eulerChar_eq_of_annulus_complement N L M hJ zero_lt_one
      (by rw [hLspace]; exact hρ) hNspace.symm
      (by rw [hLspace, hMspace]; exact hleft)]
    exact hMχ
  have htorus : IsPLTorus N.space := ⟨isPolyhedron_space N,
    hN.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero N hNc
      (hN.isOrientable_euclidean_three N hNc) hNχ⟩
  rwa [hNspace, hLspace, hMspace] at htorus

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem IsPLAnnulusWithEnds.isPLTorus_union
    {A B J₀ J₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : IsPLAnnulusWithEnds A J₀ J₁) (hB : IsPLAnnulusWithEnds B J₀ J₁)
    (hinter : A ∩ B = J₀ ∪ J₁) : IsPLTorus (A ∪ B) := by
  obtain ⟨J, ρ, hJ, hρ, hρ₀, hρ₁⟩ := hA
  obtain ⟨K, σ, hK, hσ, hσ₀, hσ₁⟩ := hB
  apply isPLTorus_union_of_isPLHomeomorphOn_annuli hJ hK hρ hσ
  · rw [hinter, hρ₀, hρ₁, ← image_union, ← prod_union, singleton_union]
  · rw [hinter, hσ₀, hσ₁, ← image_union, ← prod_union, singleton_union]

end DifferentialGeometry.Topology.PiecewiseLinear
