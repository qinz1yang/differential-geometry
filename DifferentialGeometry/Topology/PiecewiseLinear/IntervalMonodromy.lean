/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem endpoints_of_continuousOn_bijOn_Icc {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 1)) (hbij : BijOn u (Icc 0 1) (Icc 0 1)) :
    (u 0 = 0 ∧ u 1 = 1) ∨ (u 0 = 1 ∧ u 1 = 0) := by
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hu0 := hbij.mapsTo h0
  have hu1 := hbij.mapsTo h1
  obtain ⟨s, hs, hus⟩ := hbij.surjOn h0
  obtain ⟨t, ht, hut⟩ := hbij.surjOn h1
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one hcont hbij.injOn with hm | hm
  · have hleft := hm.monotoneOn h0 hs hs.1
    have hright := hm.monotoneOn ht h1 ht.2
    rw [hus] at hleft
    rw [hut] at hright
    exact Or.inl ⟨le_antisymm hleft hu0.1, le_antisymm hu1.2 hright⟩
  · have hleft := hm.antitoneOn h0 ht ht.1
    have hright := hm.antitoneOn hs h1 hs.2
    rw [hut] at hleft
    rw [hus] at hright
    exact Or.inr ⟨le_antisymm hu0.2 hleft, le_antisymm hright hu1.1⟩

private theorem isPLHomeomorphOn_one_sub :
    IsPLHomeomorphOn (fun x : ℝ => 1 - x) (Icc 0 1) (Icc 0 1) := by
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · intro x _ y _ heq
    linarith
  · intro y hy
    refine ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCylindricalDiagram.exists_isPLHomeomorphOn_mobiusComplex_of_reversing_endMap
    {f : ℝ × ℝ → E} {S : Set E} (hf : IsCylindricalDiagram f (Icc 0 1) S)
    {u : ℝ → ℝ} (hu : IsPLHomeomorphOn u (Icc 0 1) (Icc 0 1))
    (hfu : ∀ x ∈ Icc 0 1, f (x, 0) = f (u x, 1)) (hu0 : u 0 = 1) (hu1 : u 1 = 0) :
    ∃ j : (Fin 5 → ℝ) → E, IsPLHomeomorphOn j mobiusComplex.space S := by
  let w := u ∘ fun x : ℝ => 1 - x
  have hw : IsPLHomeomorphOn w (Icc 0 1) (Icc 0 1) := isPLHomeomorphOn_one_sub.trans hu
  have hw0 : w 0 = 0 := by simpa only [w, Function.comp_apply, sub_zero] using hu1
  have hw1 : w 1 = 1 := by simpa only [w, Function.comp_apply, sub_self] using hu0
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, _, _⟩ :=
    exists_isPLHomeomorphOn_unitSquare_of_fixed_endpoints hw hw0 hw1
  have hid : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  let g := f ∘ Ψ
  have hg : IsCylindricalDiagram g (Icc 0 1) S := hf.comp_of_ends hid hw hΨ hΨ0 hΨ1
  have hflip {x : ℝ} (hx : x ∈ Icc 0 1) : 1 - x ∈ Icc 0 1 :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hseam (x : ℝ) (hx : x ∈ Icc 0 1) : g (x, 1) = g (1 - x, 0) := by
    change f (Ψ (x, 1)) = f (Ψ (1 - x, 0))
    rw [hΨ1 x hx, hΨ0 (1 - x) (hflip hx)]
    exact (hfu (1 - x) (hflip hx)).symm
  have hbotinj : InjOn (fun x : ℝ => g (x, 0)) (Icc 0 1) := by
    intro x hx y hy hxy
    exact congrArg Prod.fst ((hg.isPLHomeomorphOn_bottom isHPolytope_Icc.isPolyhedron).bijOn.injOn
      (show (x, (0 : ℝ)) ∈ Icc 0 1 ×ˢ {0} from ⟨hx, rfl⟩)
      (show (y, (0 : ℝ)) ∈ Icc 0 1 ×ˢ {0} from ⟨hy, rfl⟩) hxy)
  have hcross {x y : ℝ × ℝ} (hx : x ∈ Icc 0 1 ×ˢ Icc 0 1)
      (hy : y ∈ Icc 0 1 ×ˢ Icc 0 1) (hxy : g x = g y)
      (hx0 : x.2 = 0) (hy1 : y.2 = 1) : x.1 = 1 - y.1 := by
    apply hbotinj hx.1 (hflip hy.1)
    calc
      g (x.1, 0) = g x := congrArg g (Prod.ext rfl hx0.symm)
      _ = g y := hxy
      _ = g (y.1, 1) := congrArg g (Prod.ext rfl hy1)
      _ = g (1 - y.1, 0) := hseam y.1 hy.1
  obtain ⟨j, hj⟩ := exists_isPLHomeomorphOn_mobiusComplex_of_square
    hg.isPiecewiseAffineOn hseam (fun x hx y hy hxy => by
      rcases hg.eq_or_endpoints x hx y hy hxy with heq | hends | hends
      · exact Or.inl heq
      · exact Or.inr (Or.inl ⟨hends.1, hends.2, hcross hx hy hxy hends.1 hends.2⟩)
      · have hparam := hcross hy hx hxy.symm hends.2 hends.1
        exact Or.inr (Or.inr ⟨hends.1, hends.2, by linarith⟩))
  exact ⟨j, hg.image_eq ▸ hj⟩

theorem IsCylindricalDiagram.endMap_endpoints_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {f : ℝ × ℝ → E} {S : Set E} (hf : IsCylindricalDiagram f (Icc 0 1) S) (hSK : S ⊆ K.space)
    {u : ℝ → ℝ} (hu : IsPLHomeomorphOn u (Icc 0 1) (Icc 0 1))
    (hfu : ∀ x ∈ Icc 0 1, f (x, 0) = f (u x, 1)) : u 0 = 0 ∧ u 1 = 1 := by
  rcases endpoints_of_continuousOn_bijOn_Icc hu.isPiecewiseAffineOn.continuousOn hu.bijOn with
    hends | hends
  · exact hends
  · obtain ⟨j, hj⟩ := hf.exists_isPLHomeomorphOn_mobiusComplex_of_reversing_endMap
      hu hfu hends.1 hends.2
    exact (not_isPLHomeomorphOn_mobiusComplex_of_isOrientable K hK hor hSK j hj).elim

theorem IsCylindricalDiagram.exists_endMap_id_of_isOrientable_interval
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {f : ℝ × ℝ → E} {S : Set E} (hf : IsCylindricalDiagram f (Icc 0 1) S) (hSK : S ⊆ K.space) :
    ∃ g : ℝ × ℝ → E, IsCylindricalDiagram g (Icc 0 1) S ∧
      ∀ x ∈ Icc 0 1, g (x, 0) = g (x, 1) := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap isHPolytope_Icc.isPolyhedron
  obtain ⟨hu0, hu1⟩ := hf.endMap_endpoints_of_isOrientable K hK hor hSK hu hfu
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, _, _⟩ :=
    exists_isPLHomeomorphOn_unitSquare_of_fixed_endpoints hu hu0 hu1
  exact hf.exists_endMap_id_of_pseudoIsotopicToId hu hfu ⟨Ψ, hΨ, hΨ0, hΨ1⟩
    (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id (E := ℝ))

end DifferentialGeometry.Topology.PiecewiseLinear
