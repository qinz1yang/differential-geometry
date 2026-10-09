import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMap

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {M : ConnectedClosedOrientedManifold.{u} 3} {F : CollaredTorusFamily_C2a M.Carrier}

theorem isPreconnected_collarImage_S12 (i : Fin F.count) :
    IsPreconnected (F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 1)) := by
  refine (isPreconnected_univ.prod isPreconnected_Ioo).image _ ?_
  exact (F.collar i).toOpenPartialHomeomorph.continuousOn.mono
    (by change _ ⊆ (F.collar i).source; rw [F.source_eq]
        exact Ioo_subset_source_S12 le_rfl le_rfl)

theorem gPlus_target_S12 (i : Fin F.count) :
    (gPlus_S12 F i).target = F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    have hy : (gPlus_S12 F i).symm z ∈ (gPlus_S12 F i).source := (gPlus_S12 F i).map_target hz
    have hzy : gPlus_S12 F i ((gPlus_S12 F i).symm z) = z := (gPlus_S12 F i).right_inv hz
    have h2 : phiPlus_S12 ((F.collar i).symm ((gPlus_S12 F i).symm z)) ∈ (F.collar i).source :=
      hy.2
    rw [F.source_eq] at h2
    refine ⟨_, ⟨trivial, h2.1, h2.2⟩, ?_⟩
    exact hzy
  · rintro ⟨q, ⟨-, h1, h2⟩, rfl⟩
    have hp : (q.1, psi_S12 q.2) ∈ signedCollarSource := by
      have := strictMono_psi_S12 h1
      have h3 := psi_lt_one_S12 h2
      rw [psi_neg_one_S12] at this
      exact ⟨by change -1 < psi_S12 q.2; linarith, h3⟩
    have hy := mem_source_gPlus_S12 i hp (by change -1 < rho_S12 (psi_S12 q.2); rw [rho_psi_S12]; exact h1)
      (by change rho_S12 (psi_S12 q.2) < 1; rw [rho_psi_S12]; exact h2)
    have := (gPlus_S12 F i).map_source hy
    rwa [gPlus_apply_S12 i hp, show ((q.1, psi_S12 q.2).2 : ℝ) = psi_S12 q.2 from rfl, rho_psi_S12] at this

theorem gMinus_target_S12 (i : Fin F.count) :
    (gMinus_S12 F i).target = F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    have hy : (gMinus_S12 F i).symm z ∈ (gMinus_S12 F i).source := (gMinus_S12 F i).map_target hz
    have hzy : gMinus_S12 F i ((gMinus_S12 F i).symm z) = z := (gMinus_S12 F i).right_inv hz
    have h2 : phiMinus_S12 ((F.collar i).symm ((gMinus_S12 F i).symm z)) ∈ (F.collar i).source :=
      hy.2
    rw [F.source_eq] at h2
    refine ⟨_, ⟨trivial, h2.1, h2.2⟩, ?_⟩
    exact hzy
  · rintro ⟨q, ⟨-, h1, h2⟩, rfl⟩
    have h3 := psi_lt_one_S12 (show -q.2 < 1 by linarith)
    have h4 := strictMono_psi_S12 (show -1 < -q.2 by linarith)
    rw [psi_neg_one_S12] at h4
    have hp : (q.1, -psi_S12 (-q.2)) ∈ signedCollarSource :=
      ⟨by change -1 < -psi_S12 (-q.2); linarith, by change -psi_S12 (-q.2) < 1; linarith⟩
    have hr : -rho_S12 (-(-psi_S12 (-q.2))) = q.2 := by
      rw [neg_neg, rho_psi_S12]; ring
    have hy := mem_source_gMinus_S12 i hp
      (by change -1 < -rho_S12 (-(-psi_S12 (-q.2))); rw [hr]; exact h1)
      (by change -rho_S12 (-(-psi_S12 (-q.2))) < 1; rw [hr]; exact h2)
    have := (gMinus_S12 F i).map_source hy
    rwa [gMinus_apply_S12 i hp, show ((q.1, -psi_S12 (-q.2)).2 : ℝ) = -psi_S12 (-q.2) from rfl, hr] at this

theorem gPlus_eventuallyEq_id_S12 (i : Fin F.count) {q : Torus × ℝ} (h1 : 7/8 < q.2) (h2 : q.2 < 1) :
    gPlus_S12 F i =ᶠ[nhds (F.collar i q)] id := by
  have hq : q ∈ signedCollarSource := ⟨by linarith, h2⟩
  have hopen := isOpen_collarImage_S12 i (a := 7/8) (b := 1) (by norm_num) le_rfl
  refine Filter.eventually_of_mem (hopen.mem_nhds ⟨q, ⟨trivial, h1, h2⟩, rfl⟩) ?_
  rintro z ⟨q', ⟨-, h1', h2'⟩, rfl⟩
  have hq' : q' ∈ signedCollarSource := ⟨by linarith, h2'⟩
  rw [gPlus_apply_S12 i hq', rho_of_ge_S12 h1'.le]
  rfl

theorem gMinus_eventuallyEq_id_S12 (i : Fin F.count) {q : Torus × ℝ} (h1 : -1 < q.2) (h2 : q.2 < -7/8) :
    gMinus_S12 F i =ᶠ[nhds (F.collar i q)] id := by
  have hq : q ∈ signedCollarSource := ⟨h1, by linarith⟩
  have hopen := isOpen_collarImage_S12 i (a := -1) (b := -7/8) le_rfl (by norm_num)
  refine Filter.eventually_of_mem (hopen.mem_nhds ⟨q, ⟨trivial, h1, h2⟩, rfl⟩) ?_
  rintro z ⟨q', ⟨-, h1', h2'⟩, rfl⟩
  have hq' : q' ∈ signedCollarSource := ⟨h1', by linarith⟩
  rw [gMinus_apply_S12 i hq', rho_of_ge_S12 (by linarith : (7:ℝ)/8 ≤ -q'.2)]
  simp

/-- **`σ_i(t,s) ↦ σ_i(t,ρ s)` preserves the orientation of `M`** on its source. -/
theorem gPlus_orientation_S12 (i : Fin F.count) {y : M.Carrier}
    (hy : y ∈ (gPlus_S12 F i).source) :
    Orientation.map (Fin 3)
      (((gPlus_S12 F i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (M.orientation.orientation y) =
      M.orientation.orientation (gPlus_S12 F i y) := by
  have hq0 : ((1 : Torus), (15/16 : ℝ)) ∈ signedCollarSource := ⟨by norm_num, by norm_num⟩
  have hy0 := mem_source_gPlus_S12 i hq0
    (by change -1 < rho_S12 (15/16); rw [rho_of_ge_S12 (by norm_num)]; norm_num)
    (by change rho_S12 (15/16) < 1; rw [rho_of_ge_S12 (by norm_num)]; norm_num)
  refine orientation_propagate_S12 (gPlus_S12 F i) ?_ M.orientation hy0
    (orientation_of_eventuallyEq_id_S12 _ M.orientation hy0
      (gPlus_eventuallyEq_id_S12 i (q := ((1 : Torus), (15/16 : ℝ)))
        (by norm_num) (by norm_num))) hy
  rw [gPlus_target_S12]; exact isPreconnected_collarImage_S12 i

theorem gMinus_orientation_S12 (i : Fin F.count) {y : M.Carrier}
    (hy : y ∈ (gMinus_S12 F i).source) :
    Orientation.map (Fin 3)
      (((gMinus_S12 F i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (M.orientation.orientation y) =
      M.orientation.orientation (gMinus_S12 F i y) := by
  have hq0 : ((1 : Torus), (-15/16 : ℝ)) ∈ signedCollarSource := ⟨by norm_num, by norm_num⟩
  have hr : -rho_S12 (-(-15/16 : ℝ)) = -15/16 := by
    rw [show -(-15/16 : ℝ) = 15/16 by norm_num, rho_of_ge_S12 (by norm_num)]
    norm_num
  have hy0 := mem_source_gMinus_S12 i hq0
    (by change -1 < -rho_S12 (-(-15/16 : ℝ)); rw [hr]; norm_num)
    (by change -rho_S12 (-(-15/16 : ℝ)) < 1; rw [hr]; norm_num)
  refine orientation_propagate_S12 (gMinus_S12 F i) ?_ M.orientation hy0
    (orientation_of_eventuallyEq_id_S12 _ M.orientation hy0
      (gMinus_eventuallyEq_id_S12 i (q := ((1 : Torus), (-15/16 : ℝ)))
        (by norm_num) (by norm_num))) hy
  rw [gMinus_target_S12]; exact isPreconnected_collarImage_S12 i

section Local

variable (F)

/-- Local description of the stretch `R` on the cut carrier: near each point it is either the
inclusion, or an orientation-preserving local stretch `G` of `M` composed with the inclusion. -/
theorem rmapK_local_S12 (x : (cutCarrier_C2a F).Carrier) :
    ∃ u : Set (cutCarrier_C2a F).Carrier, IsOpen u ∧ x ∈ u ∧
      ((∀ y ∈ u, rmapK_S12 F y = cutIncl_C2a F y) ∨
       ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
        cutIncl_C2a F x ∈ G.source ∧
        (∀ (y : M.Carrier) (hy : y ∈ G.source),
          Orientation.map (Fin 3)
            ((G.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
              (by simp)).toLinearEquiv (M.orientation.orientation y) =
            M.orientation.orientation (G y)) ∧
        ∀ y ∈ u, rmapK_S12 F y = G (cutIncl_C2a F y)) := by
  have hval := contMDiff_cutIncl_S12 F
  by_cases hs : ∃ i, cutIncl_C2a F x ∈ slab_S12 F i
  · obtain ⟨i, q, ⟨-, hq1, hq2⟩, hxq⟩ := hs
    have hqs : q ∈ signedCollarSource := ⟨by linarith [hq1], by linarith [hq2]⟩
    have hge := half_le_abs_of_mem_cut_S12 F (x := x) i hqs hxq.symm
    rcases lt_or_gt_of_ne (show q.2 ≠ 0 by
      intro h0; rw [h0, abs_zero] at hge; linarith) with hneg | hpos
    · refine ⟨cutIncl_C2a F ⁻¹' (F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 0)),
        (isOpen_collarImage_S12 i le_rfl (by norm_num)).preimage hval.continuous,
        ⟨q, ⟨trivial, hqs.1, hneg⟩, hxq⟩, Or.inr ⟨gMinus_S12 F i, ?_, fun y hy => gMinus_orientation_S12 i hy, ?_⟩⟩
      · rw [← hxq]; exact mem_source_gMinus_S12 i hqs (neg_rho_neg_gt_S12 hqs.1)
          (neg_rho_neg_lt_one_S12 hneg.le)
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        have hq' : q' ∈ signedCollarSource := ⟨h1, by linarith⟩
        exact rmap_eq_gMinus_S12 (x := y) i hq' h2 hyq.symm
    · refine ⟨cutIncl_C2a F ⁻¹' (F.collar i '' (univ ×ˢ Ioo (0 : ℝ) 1)),
        (isOpen_collarImage_S12 i (by norm_num) le_rfl).preimage hval.continuous,
        ⟨q, ⟨trivial, hpos, hqs.2⟩, hxq⟩, Or.inr ⟨gPlus_S12 F i, ?_, fun y hy => gPlus_orientation_S12 i hy, ?_⟩⟩
      · rw [← hxq]; exact mem_source_gPlus_S12 i hqs (rho_gt_neg_one_S12 hpos.le)
          (rho_lt_one_S12 hqs.2)
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        have hq' : q' ∈ signedCollarSource := ⟨by linarith, h2⟩
        exact rmap_eq_gPlus_S12 (x := y) i hq' h1 hyq.symm
  · refine ⟨cutIncl_C2a F ⁻¹' (⋃ i, slab_S12 F i)ᶜ,
      (isClosed_iUnion_of_finite isClosed_slab_S12).isOpen_compl.preimage hval.continuous,
      fun h => hs (mem_iUnion.mp h), Or.inl ?_⟩
    intro y hy
    exact rmap_eq_val_S12 (x := y) (fun i h => hy (mem_iUnion.mpr ⟨i, h⟩))

theorem rmapK_mfderiv_bijective_S12 (x : (cutCarrier_C2a F).Carrier) :
    Bijective (mfderiv (cutCarrier_C2a F).model (𝓡 3) (rmapK_S12 F) x) := by
  obtain ⟨u, hu, hxu, h | ⟨G, hG, -, h⟩⟩ := rmapK_local_S12 F x
  · have he : rmapK_S12 F =ᶠ[nhds x] cutIncl_C2a F :=
      Filter.eventually_of_mem (hu.mem_nhds hxu) h
    rw [he.mfderiv_eq]
    exact cutIncl_mfderiv_bijective_C2a F x
  · have he : rmapK_S12 F =ᶠ[nhds x] G ∘ cutIncl_C2a F :=
      Filter.eventually_of_mem (hu.mem_nhds hxu) h
    rw [he.mfderiv_eq]
    have hL := G.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hG
    have hdG : MDifferentiableAt (𝓡 3) (𝓡 3) G (cutIncl_C2a F x) :=
      hL.mdifferentiableAt (by simp)
    have hdι : MDifferentiableAt (cutCarrier_C2a F).model (𝓡 3) (cutIncl_C2a F) x :=
      ((contMDiff_cutIncl_S12 F) x).mdifferentiableAt (by simp)
    rw [mfderiv_comp x hdG hdι]
    exact (hL.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
      (cutIncl_mfderiv_bijective_C2a F x)

set_option backward.isDefEq.respectTransparency false in
/-- **`R` preserves orientation**: the differential of `R : K → M` carries the orientation of the
cut carrier (pulled back from `M`) to that of `M`. -/
theorem rmapK_oriented_S12 (x : (cutCarrier_C2a F).Carrier) :
    Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective (cutCarrier_C2a F).model (𝓡 3) (rmapK_S12 F)
        (rmapK_mfderiv_bijective_S12 F) x).toLinearEquiv
      ((cutCarrier_C2a F).orientation.orientation x) =
      M.orientation.orientation (rmapK_S12 F x) := by
  obtain ⟨D0, hD0, hO0⟩ := cutIncl_oriented_C2a F x
  obtain ⟨u, hu, hxu, h | ⟨G, hG, hGo, h⟩⟩ := rmapK_local_S12 F x
  · have he : rmapK_S12 F =ᶠ[nhds x] cutIncl_C2a F :=
      Filter.eventually_of_mem (hu.mem_nhds hxu) h
    have key : ∀ (w : M.Carrier) (_ : w = cutIncl_C2a F x)
        (L : TangentSpace (cutCarrier_C2a F).model x ≃ₗ[ℝ] TangentSpace (𝓡 3) w),
        (∀ v, L v = D0 v) →
        Orientation.map (Fin 3) L ((cutCarrier_C2a F).orientation.orientation x) =
          M.orientation.orientation w := by
      rintro w rfl L hL
      have : L = D0.toLinearEquiv := LinearEquiv.ext hL
      rw [this]; exact hO0
    refine key (rmapK_S12 F x) (h x hxu) _ (fun v => ?_)
    change mfderiv (cutCarrier_C2a F).model (𝓡 3) (rmapK_S12 F) x v = D0 v
    rw [he.mfderiv_eq, ← hD0]; rfl
  · have he : rmapK_S12 F =ᶠ[nhds x] G ∘ cutIncl_C2a F :=
      Filter.eventually_of_mem (hu.mem_nhds hxu) h
    have hL := G.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hG
    have hdG : MDifferentiableAt (𝓡 3) (𝓡 3) G (cutIncl_C2a F x) :=
      hL.mdifferentiableAt (by simp)
    have hdι : MDifferentiableAt (cutCarrier_C2a F).model (𝓡 3) (cutIncl_C2a F) x :=
      ((contMDiff_cutIncl_S12 F) x).mdifferentiableAt (by simp)
    have key : ∀ (w : M.Carrier) (_ : w = G (cutIncl_C2a F x))
        (L : TangentSpace (cutCarrier_C2a F).model x ≃ₗ[ℝ] TangentSpace (𝓡 3) w),
        (∀ v, L v = (hL.mfderivToContinuousLinearEquiv (by simp)) (D0 v)) →
        Orientation.map (Fin 3) L ((cutCarrier_C2a F).orientation.orientation x) =
          M.orientation.orientation w := by
      rintro w rfl L hL'
      have : L = D0.toLinearEquiv.trans (hL.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv :=
        LinearEquiv.ext hL'
      rw [this]
      have hmap : Orientation.map (Fin 3)
          (D0.toLinearEquiv.trans (hL.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv)
            ((cutCarrier_C2a F).orientation.orientation x) =
          Orientation.map (Fin 3) (hL.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
            (Orientation.map (Fin 3) D0.toLinearEquiv ((cutCarrier_C2a F).orientation.orientation x)) := by
        generalize (cutCarrier_C2a F).orientation.orientation x = o
        induction o using Module.Ray.ind with
        | h v hv => rfl
      rw [hmap, hO0]
      exact hGo _ hG
    refine key (rmapK_S12 F x) (h x hxu) _ (fun v => ?_)
    change mfderiv (cutCarrier_C2a F).model (𝓡 3) (rmapK_S12 F) x v = _
    rw [he.mfderiv_eq, mfderiv_comp x hdG hdι, ← hD0]; rfl

end Local

end GC.LongTime.Ch12
