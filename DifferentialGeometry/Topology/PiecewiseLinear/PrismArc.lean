import DifferentialGeometry.Topology.PiecewiseLinear.PrismHomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn {J : Set E} {θ : ℝ → E}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J) {f g : E → F}
    (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, 1) = g y) ∧
      (∀ (S : Set F), Convex ℝ S → MapsTo f J S → MapsTo g J S →
        MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) S) := by
  classical
  have hcomp : ∀ h : E → F, IsPiecewiseAffineOn h J → IsPiecewiseAffineOn (h ∘ θ) (Icc (0 : ℝ) 1) := by
    intro h hh
    have hcc := hh.comp hθ.isPiecewiseAffineOn
    have hset : Icc (0 : ℝ) 1 ∩ θ ⁻¹' J = Icc (0 : ℝ) 1 :=
      inter_eq_left.mpr (fun x hx => hθ.bijOn.mapsTo hx)
    rwa [hset] at hcc
  obtain ⟨n, s, Φ₁, hs0, hsn, hmono, hPA₁, hbot₁, htop₁, hl₁, hr₁, himg₁⟩ :=
    exists_isPiecewiseAffineOn_prism (hcomp f hf) (hcomp g hg)
  set ψ : E × ℝ → ℝ × ℝ := Prod.map (Function.invFunOn θ (Icc (0 : ℝ) 1)) id with hψ
  have hψPA : IsPiecewiseAffineOn ψ (J ×ˢ Icc (0 : ℝ) 1) :=
    hθ.isPiecewiseAffineOn_invFunOn.prodMap (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.id ℝ ℝ) isHPolytope_Icc)
  have hψmaps : MapsTo ψ (J ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hθ.bijOn.surjOn.mapsTo_invFunOn hz.1, hz.2⟩
  have hinv : ∀ y ∈ J, θ (Function.invFunOn θ (Icc (0 : ℝ) 1) y) = y :=
    fun y hy => hθ.bijOn.invOn_invFunOn.2 hy
  refine ⟨Φ₁ ∘ ψ, ?_, ?_, ?_, ?_⟩
  · have h := hPA₁.comp hψPA
    convert h using 1
    exact (Set.inter_eq_self_of_subset_left (fun z hz => hψmaps hz)).symm
  · intro y hy
    have : ψ (y, 0) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 0) := rfl
    rw [Function.comp_apply, this,
      hbot₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro y hy
    have : ψ (y, 1) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 1) := rfl
    rw [Function.comp_apply, this,
      htop₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro S hS hfS hgS z hz
    refine mapsTo_of_forall_mem_convexHull_cell hS himg₁ (fun i hi => ?_) (hψmaps hz)
    have hsm : ∀ j, j ≤ n → s j ∈ Icc (0 : ℝ) 1 :=
      fun j hj => mem_Icc_of_forall_lt_succ hmono hs0 hsn hj
    have hJ : ∀ j, j ≤ n → θ (s j) ∈ J := fun j hj => hθ.bijOn.mapsTo (hsm j hj)
    exact ⟨hfS (hJ i (by omega)), hfS (hJ (i + 1) (by omega)), hgS (hJ i (by omega)),
      hgS (hJ (i + 1) (by omega))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
