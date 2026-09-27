/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.ChartDiskCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeConjugation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_chart_bigon_removal (e : OpenPartialHomeomorph E (Plane × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    {P A C : Set Plane} {a b c d p q : Plane} (hP : IsPLBall 2 P)
    (hPt : P ×ˢ {0} ⊆ e.target)
    (hA : Schoenflies.IsCrosscut (frontier P) (A ∩ P) a b)
    (hC : Schoenflies.IsCrosscut (frontier P) (C ∩ P) c d)
    (hpair : (A ∩ P) ∩ (C ∩ P) = {p, q}) (hpq : p ≠ q)
    (hp : p ∈ interior P) (hq : q ∈ interior P)
    (hcrossp : HasPLCurveCrossingOnAt univ (A ∩ P) (C ∩ P) p)
    (hcrossq : HasPLCurveCrossingOnAt univ (A ∩ P) (C ∩ P) q)
    {S Y B D : Set E} (hS : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (hY : ∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2)
    (hB : ∀ x ∈ P, e.symm (x, 0) ∈ B ↔ x ∈ A)
    (hD : ∀ x ∈ P, e.symm (x, 0) ∈ D ↔ x ∈ C)
    (hDplane : ∀ z ∈ e.target, e.symm z ∈ D → z.2 = 0)
    (hfin : (B ∩ D).Finite) :
    ∃ (K : Set E) (Φ : E ≃ₜ E), IsCompact K ∧ K ⊆ e.source ∧
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Kᶜ ∧
      (∀ x, Φ x ∈ S ↔ x ∈ S) ∧ (∀ x, Φ x ∈ Y ↔ x ∈ Y) ∧
      Φ '' B ∩ D = (B ∩ D) \ K ∧ (Φ '' B ∩ D).ncard + 2 = (B ∩ D).ncard ∧
      ∃ H : E × unitInterval → E, Continuous H ∧
        (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) = Φ x) ∧
        (∀ t, EqOn (fun x => H (x, t)) id Kᶜ) ∧
        (∀ t, MapsTo (fun x => H (x, t)) K K) ∧
        (∀ x t, x ∈ Y → H (x, t) ∈ Y) := by
  obtain ⟨u, hu, huf, hud⟩ :=
    exists_isPLHomeomorphOn_disk_bigon_move hP hA hC hpair hpq hp hq hcrossp hcrossq
  obtain ⟨δ, hδ, hbox, Φ, hΦ, hfix, hmodel, hΦS, hΦY, H, hH, hH0, hH1,
    hHfix, hHK, hHY⟩ := exists_isPLHomeomorphOn_chart_disk_move e he hei hP hPt hu huf hS hY
  let K := e.symm '' (P ×ˢ Icc (-δ) δ)
  have hKsrc : K ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hbox hz)
  have hK : IsCompact K := (hP.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
    (e.continuousOn_symm.mono hbox)
  have hΦK : MapsTo Φ K K := mapsTo_of_injective_eqOn_compl Φ.injective hfix
  have hplane : ∀ x ∈ K, (e (Φ x)).2 = 0 ↔ (e x).2 = 0 := by
    intro x hx
    exact (hS _ (hKsrc (hΦK hx))).symm.trans ((hΦS x).trans (hS _ (hKsrc hx)))
  have hDK : ∀ z ∈ P ×ˢ Icc (-δ) δ, e.symm z ∈ D ↔ z.2 = 0 ∧ z.1 ∈ C := by
    intro z hz
    constructor
    · intro hzD
      have hz0 := hDplane z (hbox hz) hzD
      have heq : z = (z.1, 0) := Prod.ext rfl hz0
      exact ⟨hz0, (hD z.1 hz.1).mp (heq ▸ hzD)⟩
    · rintro ⟨hz0, hzC⟩
      have heq : z = (z.1, 0) := Prod.ext rfl hz0
      rw [heq]
      exact (hD z.1 hz.1).mpr hzC
  have hdisj : Disjoint (Φ '' (B ∩ K)) (D ∩ K) :=
    disjoint_image_inter_of_chart_disk_move e hδ.le hbox hu.bijOn.mapsTo
      hplane hmodel hB hDK hud
  have hcross : (B ∩ D) ∩ K = {e.symm (p, 0), e.symm (q, 0)} := by
    rw [crossings_inter_chart_prism e hδ.le hB hDK]
    have hpair' : (A ∩ C) ∩ P = {p, q} := by
      rw [← hpair]
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [hpair', image_insert_eq, image_singleton]
  have hpq' : e.symm (p, (0 : ℝ)) ≠ e.symm (q, 0) := by
    intro heq
    exact hpq (congrArg Prod.fst (e.symm.injOn
      (hPt (show (p, (0 : ℝ)) ∈ P ×ˢ {0} from ⟨interior_subset hp, rfl⟩))
      (hPt (show (q, (0 : ℝ)) ∈ P ×ˢ {0} from ⟨interior_subset hq, rfl⟩)) heq))
  exact ⟨K, Φ, hK, hKsrc, hΦ, hfix, hΦS, hΦY,
    image_inter_eq_sdiff_of_supported_disjoint Φ.injective hfix hdisj,
    ncard_image_inter_add_two_of_supported_disjoint Φ.injective hfix hdisj hpq' hcross hfin,
    H, hH, hH0, hH1, hHfix, hHK, hHY⟩

end DifferentialGeometry.Topology.PiecewiseLinear
