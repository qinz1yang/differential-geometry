/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.ConjugateFamily
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.DiskMapHalfspaceScaling

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_chart_disk_move
    (e : OpenPartialHomeomorph E (Plane × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    {P : Set Plane} (hP : IsPLBall 2 P) (hPt : P ×ˢ {0} ⊆ e.target)
    {u : Plane → Plane} (hu : IsPLHomeomorphOn u P P) (huf : EqOn u id (frontier P))
    {S Y : Set E} (hS : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (hY : ∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2) :
    ∃ δ : ℝ, 0 < δ ∧ P ×ˢ Icc (-δ) δ ⊆ e.target ∧
      ∃ Φ : E ≃ₜ E, IsPLHomeomorphOn Φ univ univ ∧
        EqOn Φ id (e.symm '' (P ×ˢ Icc (-δ) δ))ᶜ ∧
        (∀ x ∈ P, Φ (e.symm (x, 0)) = e.symm (u x, 0)) ∧
        (∀ x, Φ x ∈ S ↔ x ∈ S) ∧ (∀ x, Φ x ∈ Y ↔ x ∈ Y) ∧
        ∃ H : E × unitInterval → E, Continuous H ∧
          (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) = Φ x) ∧
          (∀ t, EqOn (fun x => H (x, t)) id (e.symm '' (P ×ˢ Icc (-δ) δ))ᶜ) ∧
          (∀ t, MapsTo (fun x => H (x, t)) (e.symm '' (P ×ˢ Icc (-δ) δ))
            (e.symm '' (P ×ˢ Icc (-δ) δ))) ∧
          (∀ x t, x ∈ Y → H (x, t) ∈ Y) := by
  obtain ⟨W, V, _, hV, hPW, h0V, hWV⟩ :=
    generalized_tube_lemma hP.isPolyhedron.isCompact isCompact_singleton e.open_target hPt
  obtain ⟨δ, hδ, hδV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  have hbox : P ×ˢ Icc (-δ) δ ⊆ e.target := by
    apply (prod_mono hPW ?_).trans hWV
    simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using hδV
  obtain ⟨f, hf, hf0, hfix, hside, hplane, J, hJ, hJ0, hJ1, hJfix, hJbox, hJside, _⟩ :=
    exists_isPLHomeomorphOn_extension_halfspaces_thickness hP hu huf hδ
  have hcompact : IsCompact (P ×ˢ Icc (-δ) δ) := hP.isPolyhedron.isCompact.prod isCompact_Icc
  have hft : MapsTo f e.target e.target := by
    intro z hz
    by_contra hn
    have heq : f z = z := f.injective (hfix (fun h => hn (hbox h)))
    exact hn (heq.symm ▸ hz)
  have hJt : ∀ t, MapsTo (fun z => J (z, t)) e.target e.target := by
    intro t z hz
    by_cases hzb : z ∈ P ×ˢ Icc (-δ) δ
    · exact hbox (hJbox t hzb)
    · rw [hJfix t hzb]
      exact hz
  let Φ := e.conjugateHomeomorph f hcompact hbox hfix
  have hΦ : IsPLHomeomorphOn Φ univ univ := by
    apply isPLHomeomorphOn_openPartialHomeomorph Φ.toOpenPartialHomeomorph
    exact isPiecewiseAffineOn_conjugateMap e he hei
      (hf.isPiecewiseAffineOn.mono e.open_target (subset_univ _)) hft hcompact hbox hfix
  let H : E × unitInterval → E := fun z => e.conjugateMap (fun y => J (y, z.2)) z.1
  have hH : Continuous H := by
    exact (e.continuous_conjugateMap_family
      (hJ.comp (continuous_snd.prodMk continuous_fst)) hJt hcompact hbox hJfix).comp
        (continuous_snd.prodMk continuous_fst)
  refine ⟨δ, hδ, hbox, Φ, hΦ, e.conjugateMap_eqOn_compl hfix, ?_, ?_, ?_,
    H, hH, ?_, ?_, fun t => e.conjugateMap_eqOn_compl (hJfix t), ?_, ?_⟩
  · intro x hx
    change e.conjugateMap f (e.symm (x, 0)) = _
    have ht := hPt (show (x, (0 : ℝ)) ∈ P ×ˢ {0} from ⟨hx, rfl⟩)
    rw [e.conjugateMap_of_mem _ (e.map_target ht), e.right_inv ht, hf0 x hx]
  · exact fun x => e.conjugateMap_mem_iff (B := {z : Plane × ℝ | z.2 = 0})
      hft hS (fun z _ => hplane z) x
  · exact fun x => e.conjugateMap_mem_iff (B := {z : Plane × ℝ | 0 ≤ z.2})
      hft hY (fun z _ => hside z) x
  · intro x
    by_cases hx : x ∈ e.source
    · change e.conjugateMap (fun y => J (y, 0)) x = x
      rw [e.conjugateMap_of_mem _ hx, hJ0, e.left_inv hx]
    · exact e.conjugateMap_of_notMem _ hx
  · intro x
    change e.conjugateMap (fun y => J (y, 1)) x = e.conjugateMap f x
    exact congrArg (fun g => e.conjugateMap g x) (funext hJ1)
  · rintro t _ ⟨z, hz, rfl⟩
    change e.conjugateMap (fun y => J (y, t)) (e.symm z) ∈ _
    rw [e.conjugateMap_of_mem _ (e.map_target (hbox hz)), e.right_inv (hbox hz)]
    exact ⟨J (z, t), hJbox t hz, rfl⟩
  · intro x t hxY
    by_cases hx : x ∈ e.source
    · rw [show H (x, t) = e.symm (J (e x, t)) from e.conjugateMap_of_mem _ hx]
      apply (hY _ (e.map_target (hJt t (e.map_source hx)))).mpr
      rw [e.right_inv (hJt t (e.map_source hx))]
      exact hJside (e x) t ((hY x hx).mp hxY)
    · rw [show H (x, t) = x from e.conjugateMap_of_notMem _ hx]
      exact hxY

end DifferentialGeometry.Topology.PiecewiseLinear
