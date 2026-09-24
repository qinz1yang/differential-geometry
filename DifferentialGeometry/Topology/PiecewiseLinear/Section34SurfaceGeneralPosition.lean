import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.exists_relative_general_position_circles
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifold 2 K) (hL : IsCombinatorialManifold 2 L)
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (hΩ : IsOpen Ω) (hKΩ : K.space ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
      (N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (n : ℕ) (J : Fin n → Set (EuclideanSpace ℝ (Fin 3))),
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Ωᶜ ∧
      (∀ x, dist (H x) x < ε) ∧ N.faces.Finite ∧ IsCombinatorialManifold 2 N ∧
      N.space = H '' K.space ∧ N.space ⊆ Ω ∧
      (∀ x ∈ N.space ∩ L.space, HasPLCrossingAt N.space L.space x) ∧
      (∀ i, IsPLSphere 1 (J i)) ∧ (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      N.space ∩ L.space = ⋃ i, J i := by
  classical
  obtain ⟨a, h, -, hh, hclose, hfix, hspace, htrans⟩ :=
    exists_small_homeomorph_transverse_affineImage K L hΩ hKΩ hε
  let H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := h
      invFun := Function.invFunOn h univ
      left_inv := fun x => hh.bijOn.invOn_invFunOn.1 (mem_univ x)
      right_inv := fun x => hh.bijOn.invOn_invFunOn.2 (mem_univ x)
      continuous_toFun := continuousOn_univ.mp hh.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hh.isPiecewiseAffineOn_invFunOn.continuousOn }
  let N := affineImage K (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) a)
  have hNfin : N.faces.Finite := affineImage_faces_finite K _
  let _ : Finite N.faces := hNfin.to_subtype
  have hN : IsCombinatorialManifold 2 N :=
    hK.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage K _)
  have hNΩ : N.space ⊆ Ω := by
    rw [hspace]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    have heq : h x = x := hh.bijOn.injOn (mem_univ (h x)) (mem_univ x) (hfix hn)
    exact hn (heq.symm ▸ hKΩ hx)
  obtain ⟨hcross, ι, hι, C, hC, hdis, hcover⟩ :=
    exists_isPLSphere_cover_inter_of_transverse_faces (by simp) N L hN hL htrans
  let _ : Finite ι := hι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨H, N, n, fun i => C (e.symm i), hh, hfix, hclose, hNfin, hN,
    hspace, hNΩ, hcross, fun i => hC (e.symm i), ?_, ?_⟩
  · intro i j hij
    exact hdis (fun heq => hij (e.symm.injective heq))
  · rw [hcover]
    exact e.symm.surjective.iUnion_comp C |>.symm

end DifferentialGeometry.Topology.PiecewiseLinear
