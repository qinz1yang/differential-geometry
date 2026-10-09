/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.Inversion
import DifferentialGeometry.Topology.Connected.BallComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellArcDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPreconnected_insert_invert_compl_ball {a : Schoenflies.Plane}
    (ha : a ∈ Metric.ball (0 : Schoenflies.Plane) 1) :
    IsPreconnected (insert a (Schoenflies.invert a '' (Metric.ball 0 1)ᶜ)) := by
  have hrank : 1 < Module.rank ℝ Schoenflies.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hs : IsPreconnected (Schoenflies.invert a '' (Metric.closedBall 0 1)ᶜ) := by
    refine (Topology.isPathConnected_compl_closedBall hrank 0 1).isConnected.isPreconnected.image
      _ ((Schoenflies.continuousOn_invert a).mono fun w hw hwa => ?_)
    rw [mem_singleton_iff] at hwa
    subst hwa
    exact hw (Metric.ball_subset_closedBall ha)
  refine hs.subset_closure ?_ ?_
  · exact (image_mono (compl_subset_compl.mpr Metric.ball_subset_closedBall)).trans
      (subset_insert _ _)
  · intro p hp
    rcases hp with hpa | ⟨w, hw, rfl⟩
    · rw [hpa, Metric.mem_closure_iff]
      intro ε hε
      set R : ℝ := ‖a‖ + 1 + ε⁻¹ with hRdef
      let u : Schoenflies.Plane := EuclideanSpace.single 0 1
      have hu : ‖u‖ = 1 := by simp [u]
      have hwnorm : ‖R • u‖ = R := by
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine ⟨Schoenflies.invert a (R • u), ⟨R • u, ?_, rfl⟩, ?_⟩
      · rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hwnorm, not_le]
        have : 0 < ε⁻¹ := inv_pos.mpr hε
        linarith [norm_nonneg a]
      · rw [dist_comm, Schoenflies.dist_invert_center]
        have hdist : ε⁻¹ < dist (R • u) a := by
          have h1 : ‖R • u‖ - ‖a‖ ≤ dist (R • u) a := by
            rw [dist_eq_norm]
            exact norm_sub_norm_le _ _
          rw [hwnorm] at h1
          linarith
        have hpos : 0 < ε⁻¹ := inv_pos.mpr hε
        calc (dist (R • u) a)⁻¹ < (ε⁻¹)⁻¹ := inv_strictAnti₀ hpos hdist
          _ = ε := inv_inv ε
    · have hwa : w ≠ a := fun hwp => hw (hwp ▸ ha)
      have hwcl : w ∈ closure (Metric.closedBall (0 : Schoenflies.Plane) 1)ᶜ := by
        rw [closure_compl, interior_closedBall (0 : Schoenflies.Plane) one_ne_zero]
        exact hw
      exact ((Schoenflies.continuousAt_invert hwa).continuousWithinAt).mem_closure_image hwcl

section ArcDiskSides

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_arc_eDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) {e : Finset E3} (he : e ∈ K.faces)
    (hcard : e.card = 2) {Δ : Set E3} (hΔN : Δ ⊆ interior N' \ h '' K.space)
    (hside : Δ \ frontier XK.space ⊆ interior XK.space ∨ Δ \ frontier XK.space ⊆ XK.spaceᶜ)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, ∃ g : ℝ → E3, IsPLHomeomorphOn g (Icc 0 1) S ∧
      ({g 0, g 1} : Set E3) = S ∩ frontier XK.space)
    {B₀ : Set E3} (hB₀ : B₀ ∈ Cs) (hB₀e : B₀ ⊆ Ec e) :
    ∃ B ∈ Cs, ∃ (B₁ DB : Set E3) (γ₁ : ℝ → E3) (rB : (Fin 3 → ℝ) → E3),
      B ⊆ Ec e ∧ IsPLHomeomorphOn γ₁ (Icc 0 1) B₁ ∧
      ({γ₁ 0, γ₁ 1} : Set E3) = B ∩ frontier XK.space ∧ B₁ ⊆ frontier XK.space ∧
      B ∩ B₁ = B ∩ frontier XK.space ∧ IsPLHomeomorphOn rB (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) DB ∧
      rB '' stdSimplexBoundary 2 = B ∪ B₁ ∧ DB ⊆ Ec e ∧ DB ⊆ interior N' \ h '' K.space ∧
      DB ∩ frontier XK.space = B₁ ∧ DB ∩ Δ = B := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hpc := hd.pseudoCell e he hcard
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hpc.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ (Eint e) := fun x hx y hy hxy => by rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hPE : h (e.centroid ℝ id) ∈ Eint e := hpc.centerMem
  have hEEc : Eint e ⊆ Ec e := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hT := h2.trace_subset hd he hcard
  obtain ⟨hJs, DJint, hcell, hsd, hP⟩ := h34 e he hcard
  have hDJint : DJint ⊆ Ec e ∩ XK.space := by
    obtain ⟨θ, hθ⟩ := id hcell
    rw [hθ]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  obtain ⟨hEXsub, himg⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hcell
    inter_subset_left (hsd.symm ▸ hJs) (hsd.symm ▸ hT.trans sdiff_subset) hP hPE
  rw [hsd] at himg
  have hainside : Ψ (h (e.centroid ℝ id)) ∈ Schoenflies.inside (Ψ '' (Ec e ∩ frontier XK.space)) :=
    himg ▸ mem_image_of_mem Ψ hP
  have hγ : Schoenflies.IsJordanCurve (Ψ '' (Ec e ∩ frontier XK.space)) :=
    isJordanCurve_image_of_isPLSphere_one hJs (hT.trans sdiff_subset) hΨc hΨi
  have hmemin : ∀ y ∈ Eint e,
      (Ψ y ∈ Schoenflies.inside (Ψ '' (Ec e ∩ frontier XK.space)) ↔ y ∈ DJint) := by
    intro y hy
    rw [← himg]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← hΨi (hEXsub (hDJint hz)) hy hzy]
    · exact fun hyD => ⟨y, hyD, rfl⟩
  have hCsΔ : ∀ S ∈ Cs, S ⊆ Δ := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).1
  have hSE : ∀ S ∈ Cs, S ⊆ Ec e → S ⊆ Eint e := by
    intro S hS hSe y hy
    have hyN := hΔN (hCsΔ S hS hy)
    have hEc : y ∈ Eint e ∪ Ebd e := hpc.carrierEq ▸ hSe hy
    refine hEc.resolve_right fun hbd => ?_
    rw [← hd.rimFrontier e he hcard] at hbd
    exact Set.disjoint_left.mp disjoint_interior_frontier hyN.1 hbd.2
  have hΨM : ContinuousOn Ψ (Eint e \ {h (e.centroid ℝ id)}) := hΨc.mono sdiff_subset
  have hΨne : ∀ y ∈ Eint e \ {h (e.centroid ℝ id)}, Ψ y ≠ Ψ (h (e.centroid ℝ id)) :=
    fun y hy hyP => hy.2 (hΨi hy.1 hPE hyP)
  rcases hside with hin | hout
  · refine h2.exists_arc_eDisk_of_chart hd h34 he hcard hΔN hfin hdisj hA hCs hB₀ hB₀e hΨM
      (hΦc.mono (image_subset_iff.mpr fun x hx => hΨb hx.1)) (fun x hx => hΦΨ x hx.1) hainside
      (fun ⟨y, hy, hyP⟩ => hΨne y hy hyP) ?_ isPreconnected_singleton (mem_singleton _)
      (Set.disjoint_left.mpr fun p hp ⟨y, hy, hyp⟩ =>
        hΨne y hy (hyp.trans (mem_singleton_iff.mp hp))) ?_
    · intro S hS hSe
      rintro _ ⟨y, ⟨hyS, hyX⟩, rfl⟩
      have hyE := hSE S hS hSe hyS
      refine (hmemin y hyE).mpr ?_
      have hyi : y ∈ interior XK.space := hin ⟨hCsΔ S hS hyS, hyX⟩
      have hyEX : y ∈ Ec e ∩ XK.space := ⟨hEEc hyE, interior_subset hyi⟩
      by_contra hn
      have hyJ : y ∈ Ec e ∩ frontier XK.space := hsd ▸ ⟨hyEX, hn⟩
      exact Set.disjoint_left.mp disjoint_interior_frontier hyi hyJ.2
    · rintro p ⟨hp, hpa⟩
      have hpb : p ∈ Metric.ball (0 : Schoenflies.Plane) 1 :=
        closure_inside_subset_ball hγ (image_subset_iff.mpr fun x hx => hΨb (hT hx).1) hp
      refine ⟨Φ p, ⟨hΦb hpb, fun hΦP => hpa ?_⟩, hΨΦ p hpb⟩
      rw [← hΨΦ p hpb, mem_singleton_iff.mp hΦP]
      exact mem_singleton _
  · set a := Ψ (h (e.centroid ℝ id)) with hadef
    have hab : a ∈ Metric.ball (0 : Schoenflies.Plane) 1 := hΨb hPE
    have hsides := Schoenflies.inversion_sides (fun _ hA' => Schoenflies.arc_complement hA')
      hγ hainside
    have hχimg : (Schoenflies.invert a ∘ Ψ) '' (Ec e ∩ frontier XK.space) =
        Schoenflies.invert a '' (Ψ '' (Ec e ∩ frontier XK.space)) := image_comp _ _ _
    have hainv : a ∈ Schoenflies.inside
        ((Schoenflies.invert a ∘ Ψ) '' (Ec e ∩ frontier XK.space)) := by
      rw [hχimg]
      exact Schoenflies.mem_inside_invert_image (fun _ hA' => Schoenflies.arc_complement hA')
        hγ hainside
    have hχne : ∀ y ∈ Eint e \ {h (e.centroid ℝ id)}, (Schoenflies.invert a ∘ Ψ) y ≠ a :=
      fun y hy hya => hΨne y hy (Schoenflies.invert_eq_center_iff.mp hya)
    have hχc : ContinuousOn (Schoenflies.invert a ∘ Ψ) (Eint e \ {h (e.centroid ℝ id)}) :=
      (Schoenflies.continuousOn_invert a).comp hΨM fun y hy hya => hΨne y hy hya
    have hξc : ContinuousOn (Φ ∘ Schoenflies.invert a)
        ((Schoenflies.invert a ∘ Ψ) '' (Eint e \ {h (e.centroid ℝ id)})) := by
      refine hΦc.comp ((Schoenflies.continuousOn_invert a).mono ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩ hya
        exact hχne y hy hya
      · rintro _ ⟨y, hy, rfl⟩
        change Schoenflies.invert a (Schoenflies.invert a (Ψ y)) ∈ Metric.ball 0 1
        rw [Schoenflies.invert_invert]
        exact hΨb hy.1
    refine h2.exists_arc_eDisk_of_chart hd h34 he hcard hΔN hfin hdisj hA hCs hB₀ hB₀e hχc hξc
      (fun x hx => by
        change Φ (Schoenflies.invert a (Schoenflies.invert a (Ψ x))) = x
        rw [Schoenflies.invert_invert, hΦΨ x hx.1]) hainv
      (fun ⟨y, hy, hya⟩ => hχne y hy hya) ?_ (isPreconnected_insert_invert_compl_ball hab)
      (mem_insert _ _) ?_ ?_
    · intro S hS hSe
      rintro _ ⟨y, ⟨hyS, hyX⟩, rfl⟩
      have hyE := hSE S hS hSe hyS
      have hyout : y ∉ XK.space := hout ⟨hCsΔ S hS hyS, hyX⟩
      have hΨy : Ψ y ∈ Schoenflies.outside (Ψ '' (Ec e ∩ frontier XK.space)) := by
        have hΨyC : Ψ y ∈ Schoenflies.inside (Ψ '' (Ec e ∩ frontier XK.space)) ∪
            Schoenflies.outside (Ψ '' (Ec e ∩ frontier XK.space)) := by
          rw [Schoenflies.inside_union_outside]
          rintro ⟨z, hz, hzy⟩
          have hzy' := hΨi (hT hz).1 hyE hzy
          exact hyout (hzy' ▸ (isPolyhedron_space XK).isClosed.frontier_subset hz.2)
        exact hΨyC.resolve_left fun hin' => hyout (hDJint ((hmemin y hyE).mp hin')).2
      have h1 : Schoenflies.invert a (Ψ y) ∈
          Schoenflies.invert a '' Schoenflies.outside (Ψ '' (Ec e ∩ frontier XK.space)) :=
        mem_image_of_mem _ hΨy
      rw [hsides.2.1] at h1
      rw [hχimg]
      exact h1.1
    · refine Set.disjoint_left.mpr ?_
      rintro p (rfl | ⟨w, hw, rfl⟩) ⟨y, hy, hyp⟩
      · exact hχne y hy hyp
      · have hwy : w = Ψ y := by
          have := congrArg (Schoenflies.invert a) hyp
          simp only [Function.comp_apply, Schoenflies.invert_invert] at this
          exact this.symm
        exact hw (hwy ▸ hΨb hy.1)
    · rintro p ⟨-, hpH⟩
      have hpa : p ≠ a := fun hpa => hpH (Or.inl hpa)
      have hwb : Schoenflies.invert a p ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
        by_contra hn
        exact hpH (Or.inr ⟨Schoenflies.invert a p, hn, Schoenflies.invert_invert a p⟩)
      refine ⟨Φ (Schoenflies.invert a p), ⟨hΦb hwb, fun hΦP => ?_⟩, ?_⟩
      · have h1 : Schoenflies.invert a p = a := by
          rw [← hΨΦ _ hwb, mem_singleton_iff.mp hΦP]
        exact hpa (Schoenflies.invert_eq_center_iff.mp h1)
      · change Schoenflies.invert a (Ψ (Φ (Schoenflies.invert a p))) = p
        rw [hΨΦ _ hwb, Schoenflies.invert_invert]

end ArcDiskSides

end DifferentialGeometry.Topology.PiecewiseLinear
