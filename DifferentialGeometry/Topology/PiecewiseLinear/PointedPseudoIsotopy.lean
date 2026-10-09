/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPrismBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsPLPseudoIsotopicToId.conjugate
    {P : Set E} {Q : Set F} {u : E → E} (hiso : IsPLPseudoIsotopicToId u P)
    {w : F → E} (hw : IsPLHomeomorphOn w Q P) :
    IsPLPseudoIsotopicToId (Function.invFunOn w Q ∘ u ∘ w) Q := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hiso
  have hI : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hwP := hw.prodMap hI
  have hwPi := hw.symm.prodMap hI
  refine ⟨Prod.map (Function.invFunOn w Q) id ∘ Φ ∘ Prod.map w id,
    (hwP.trans hΦ).trans hwPi, fun x hx => ?_, fun x hx => ?_⟩
  · change Prod.map (Function.invFunOn w Q) id (Φ (w x, 0)) = (x, 0)
    rw [hΦ0 (w x) (hw.bijOn.mapsTo hx)]
    exact Prod.ext (hw.bijOn.invOn_invFunOn.1 hx) rfl
  · change Prod.map (Function.invFunOn w Q) id (Φ (w x, 1)) = _
    rw [hΦ1 (w x) (hw.bijOn.mapsTo hx)]
    rfl

theorem IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_axis
    {P : Set E} (hP : IsHPolytope P) {u : E → E}
    (hiso : IsPLPseudoIsotopicToId u P) {p : E} (hp : p ∈ interior P) (hup : u p = p) :
    ∃ Ψ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Ψ (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ P, Ψ (x, 0) = (x, 0)) ∧
      (∀ x ∈ P, Ψ (x, 1) = (u x, 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Ψ (p, t) = (p, t) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hiso
  have hQ : IsHPolytope (P ×ˢ Icc (0 : ℝ) 1) := hP.prod isHPolytope_Icc
  have hΦf : IsPLHomeomorphOn Φ (frontier (P ×ˢ Icc (0 : ℝ) 1))
      (frontier (P ×ˢ Icc (0 : ℝ) 1)) := by
    have h := hΦ.restrict hQ.isPolyhedron_frontier hQ.isClosed.frontier_subset
    rwa [hΦ.image_frontier rfl hQ.isClosed hQ.isClosed] at h
  obtain ⟨Ψ, hΨ, hΨf, hΨaxis⟩ := exists_isPLHomeomorphOn_prism_fixed_axis hP hp hΦf
    (hΦ0 p (interior_subset hp)) (by rw [hΦ1 p (interior_subset hp), hup])
  have hend : ∀ x ∈ P, ∀ a ∈ ({0, 1} : Set ℝ),
      (x, a) ∈ frontier (P ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx a ha
    rw [frontier_prod_eq, hP.isClosed.closure_eq, frontier_Icc zero_le_one]
    exact Or.inl ⟨hx, ha⟩
  refine ⟨Ψ, hΨ, fun x hx => ?_, fun x hx => ?_, hΨaxis⟩
  · rw [hΨf (hend x hx 0 (Or.inl rfl)), hΦ0 x hx]
  · rw [hΨf (hend x hx 1 (Or.inr rfl)), hΦ1 x hx]

theorem IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_axis_of_convex_model
    {P : Set E} {Q : Set F} (hQ : IsHPolytope Q)
    {u : E → E} (hiso : IsPLPseudoIsotopicToId u P)
    {w : F → E} (hw : IsPLHomeomorphOn w Q P)
    {q : F} (hq : q ∈ interior Q) (huw : u (w q) = w q) :
    ∃ Ψ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Ψ (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ P, Ψ (x, 0) = (x, 0)) ∧
      (∀ x ∈ P, Ψ (x, 1) = (u x, 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Ψ (w q, t) = (w q, t) := by
  have hu : MapsTo u P P := by
    obtain ⟨Θ, hΘ, -, hΘ1⟩ := hiso
    intro x hx
    have h := hΘ.bijOn.mapsTo (show (x, (1 : ℝ)) ∈ P ×ˢ Icc 0 1 from
      ⟨hx, by norm_num⟩)
    rw [hΘ1 x hx] at h
    exact h.1
  have hqQ := interior_subset hq
  have hvq : (Function.invFunOn w Q ∘ u ∘ w) q = q := by
    change Function.invFunOn w Q (u (w q)) = q
    rw [huw, hw.bijOn.invOn_invFunOn.1 hqQ]
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦq⟩ :=
    (hiso.conjugate hw).exists_isPLHomeomorphOn_fixed_axis hQ hq hvq
  have hI : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  refine ⟨Prod.map w id ∘ Φ ∘ Prod.map (Function.invFunOn w Q) id,
    ((hw.symm.prodMap hI).trans hΦ).trans (hw.prodMap hI),
    fun x hx => ?_, fun x hx => ?_, fun t ht => ?_⟩
  · change Prod.map w id (Φ (Function.invFunOn w Q x, 0)) = (x, 0)
    rw [hΦ0 _ (hw.symm.bijOn.mapsTo hx)]
    exact Prod.ext (hw.bijOn.invOn_invFunOn.2 hx) rfl
  · change Prod.map w id (Φ (Function.invFunOn w Q x, 1)) = (u x, 1)
    rw [hΦ1 _ (hw.symm.bijOn.mapsTo hx)]
    apply Prod.ext
    · change w (Function.invFunOn w Q (u (w (Function.invFunOn w Q x)))) = u x
      rw [hw.bijOn.invOn_invFunOn.2 hx, hw.bijOn.invOn_invFunOn.2 (hu hx)]
    · rfl
  · change Prod.map w id (Φ (Function.invFunOn w Q (w q), t)) = (w q, t)
    rw [hw.bijOn.invOn_invFunOn.1 hqQ, hΦq t ht]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
