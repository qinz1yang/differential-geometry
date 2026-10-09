/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeOuterTrace
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTopologicalCellWithInterior.not_isPreconnected_sdiff {X : Type*}
    [TopologicalSpace X] {D Dint C : Set X} (hD : IsTopologicalCellWithInterior 2 D Dint)
    (hC : IsTopologicalSphere 1 C) (hCD : C ⊆ Dint) : ¬ IsPreconnected (Dint \ C) := by
  classical
  obtain ⟨θ, hθ⟩ := hD
  obtain ⟨φ⟩ := hC
  let κ : X → Schoenflies.Plane := fun y =>
    if hy : y ∈ D then (θ.symm ⟨y, hy⟩ : Schoenflies.Plane) else 0
  have hκ : ∀ y (hy : y ∈ D), κ y = θ.symm ⟨y, hy⟩ := fun y hy => dite_eq_left hy
  have hκc : ContinuousOn κ D := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : D.domRestrict κ = fun y => (θ.symm y : Schoenflies.Plane) :=
      funext fun y => hκ y.1 y.2
    rw [heq]
    exact continuous_subtype_val.comp θ.symm.continuous
  have hκi : InjOn κ D := by
    intro y hy z hz hyz
    rw [hκ y hy, hκ z hz] at hyz
    exact congrArg Subtype.val (θ.symm.injective (Subtype.ext hyz))
  have hintD : Dint ⊆ D := by
    rw [hθ]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hκint : ∀ y ∈ Dint, κ y ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
    intro y hy
    rw [hθ] at hy
    obtain ⟨w, ⟨q, hq, rfl⟩, rfl⟩ := hy
    rw [hκ _ (θ q).2, Subtype.coe_eta, Homeomorph.symm_apply_apply, mem_ball_zero_iff]
    exact hq
  have hθint : ∀ p (hp : p ∈ Metric.closedBall (0 : Schoenflies.Plane) 1), ‖p‖ < 1 →
      (θ ⟨p, hp⟩ : X) ∈ Dint := by
    intro p hp hp1
    rw [hθ]
    exact ⟨θ ⟨p, hp⟩, ⟨⟨p, hp⟩, hp1, rfl⟩, rfl⟩
  have hCD' : C ⊆ D := hCD.trans hintD
  let e : Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane := fun s => κ (φ.symm s)
  have he : Continuous e :=
    hκc.comp_continuous (continuous_subtype_val.comp φ.symm.continuous) fun s => hCD' (φ.symm s).2
  have hei : Function.Injective e := fun s t hst =>
    φ.symm.injective (Subtype.ext (hκi (hCD' (φ.symm s).2) (hCD' (φ.symm t).2) hst))
  have hJor := PlanarJordan.isJordanCurve_range_of_isEmbedding_circle
    (he.isClosedEmbedding hei).isEmbedding
  have hrange : range e = κ '' C := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨φ.symm s, (φ.symm s).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ ⟨y, hy⟩, by simp [e]⟩
  rw [hrange] at hJor
  have hγb : κ '' C ⊆ Metric.ball 0 1 := image_subset_iff.mpr fun y hy => hκint y (hCD hy)
  have himg : κ '' (Dint \ C) = Metric.ball 0 1 \ κ '' C := by
    ext p
    constructor
    · rintro ⟨y, ⟨hy, hyC⟩, rfl⟩
      refine ⟨hκint y hy, ?_⟩
      rintro ⟨z, hz, hzy⟩
      exact hyC (hκi (hCD' hz) (hintD hy) hzy ▸ hz)
    · rintro ⟨hp, hpC⟩
      have hp' : p ∈ Metric.closedBall (0 : Schoenflies.Plane) 1 := Metric.ball_subset_closedBall hp
      have hy := hθint p hp' (mem_ball_zero_iff.mp hp)
      have hκy : κ (θ ⟨p, hp'⟩ : X) = p := by
        rw [hκ _ (θ ⟨p, hp'⟩).2, Subtype.coe_eta, Homeomorph.symm_apply_apply]
      refine ⟨θ ⟨p, hp'⟩, ⟨hy, fun hyC => hpC ⟨_, hyC, hκy⟩⟩, hκy⟩
  intro hpre
  have hpre' : IsPreconnected (Metric.ball 0 1 \ κ '' C) :=
    himg ▸ hpre.image κ (hκc.mono (sdiff_subset.trans hintD))
  obtain ⟨r, hr1, hγr⟩ := exists_lt_subset_ball hJor.isClosed hγb
  have hcl := closure_inside_subset_ball hJor hγr
  have hsep := Schoenflies.jordan_curve_theorem hJor
  obtain ⟨p, hp⟩ := hsep.isConnected_inside.nonempty
  have hpb : p ∈ Metric.ball (0 : Schoenflies.Plane) 1 :=
    Metric.ball_subset_ball hr1.le (hcl (subset_closure hp))
  have hcov : Metric.ball 0 1 \ κ '' C ⊆
      Schoenflies.inside (κ '' C) ∪ Schoenflies.outside (κ '' C) := by
    intro z hz
    rw [Schoenflies.inside_union_outside]
    exact hz.2
  have hne : (Metric.ball 0 1 \ κ '' C ∩ Schoenflies.inside (κ '' C)).Nonempty :=
    ⟨p, ⟨hpb, Schoenflies.inside_subset_compl hp⟩, hp⟩
  have hsub := hpre'.subset_left_of_subset_union hsep.isOpen_inside hsep.isOpen_outside
    Schoenflies.disjoint_inside_outside hcov hne
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : Schoenflies.Plane))
    (r := 1)).mpr zero_le_one
  let c : ℝ := (max r 0 + 1) / 2
  let q : Schoenflies.Plane := c • v
  have hq : ‖q‖ = c := by
    rw [mem_sphere_zero_iff_norm] at hv
    simp only [q, norm_smul, hv, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hc1 : c < 1 := by
    have := max_lt hr1 zero_lt_one
    simp only [c]
    linarith
  have hcr : r ≤ c := by
    simp only [c]
    linarith [le_max_left r 0]
  have hqb : q ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
    rw [mem_ball_zero_iff, hq]
    exact hc1
  have hqr : q ∉ Metric.ball (0 : Schoenflies.Plane) r := by
    rw [mem_ball_zero_iff, hq]
    exact not_lt.mpr hcr
  exact hqr (hcl (subset_closure (hsub ⟨hqb, fun hqγ => hqr (hγr hqγ)⟩)))

theorem IsPseudoCell.subset_and_image_eq_inside {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {Ψ : E3 → Schoenflies.Plane}
    {Φ : Schoenflies.Plane → E3} (hΨc : ContinuousOn Ψ Eint)
    (hΦc : ContinuousOn Φ (Metric.ball 0 1)) (hΨb : MapsTo Ψ Eint (Metric.ball 0 1))
    (hΦb : MapsTo Φ (Metric.ball 0 1) Eint) (hΦΨ : ∀ x ∈ Eint, Φ (Ψ x) = x)
    (hΨΦ : ∀ p ∈ Metric.ball (0 : Schoenflies.Plane) 1, Ψ (Φ p) = p) {DJ DJint : Set E3}
    (hDJ : IsTopologicalCellWithInterior 2 DJ DJint) (hDJE : DJ ⊆ Ec)
    (hJ : IsPLSphere 1 (DJ \ DJint)) (hJE : DJ \ DJint ⊆ Eint) {Q : E3} (hQ : Q ∈ DJint)
    (hQE : Q ∈ Eint) :
    DJ ⊆ Eint ∧ Ψ '' DJint = Schoenflies.inside (Ψ '' (DJ \ DJint)) := by
  classical
  have hΨi : InjOn Ψ Eint := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hγ : Schoenflies.IsJordanCurve (Ψ '' (DJ \ DJint)) :=
    isJordanCurve_image_of_isPLSphere_one hJ hJE hΨc hΨi
  have hsep := Schoenflies.jordan_curve_theorem hγ
  have hγb : Ψ '' (DJ \ DJint) ⊆ Metric.ball 0 1 := image_subset_iff.mpr fun x hx => hΨb (hJE hx)
  have hclb := closure_inside_subset_ball hγ hγb
  have hmemE : ∀ {S : Set Schoenflies.Plane}, S ⊆ Metric.ball 0 1 →
      ∀ y ∈ Eint, y ∈ Φ '' S ↔ Ψ y ∈ S := by
    intro S hS y hy
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hΨΦ p (hS hp)]
      exact hp
    · exact fun h => ⟨Ψ y, h, hΦΨ y hy⟩
  have hΨJ : ∀ y ∈ Eint, Ψ y ∈ Ψ '' (DJ \ DJint) → y ∈ DJ \ DJint := by
    rintro y hy ⟨z, hz, hzy⟩
    rwa [← hΨi (hJE hz) hy hzy]
  obtain ⟨θ, hθ⟩ := hDJ
  let g : Schoenflies.Plane → E3 := fun p =>
    if hp : p ∈ Metric.closedBall (0 : Schoenflies.Plane) 1 then (θ ⟨p, hp⟩ : E3) else Q
  have hg : ∀ p (hp : p ∈ Metric.closedBall (0 : Schoenflies.Plane) 1), g p = θ ⟨p, hp⟩ :=
    fun p hp => dite_eq_left hp
  have hgc : ContinuousOn g (Metric.closedBall 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Metric.closedBall (0 : Schoenflies.Plane) 1).domRestrict g =
        fun p => (θ p : E3) := funext fun p => hg p.1 p.2
    rw [heq]
    exact continuous_subtype_val.comp θ.continuous
  have hgi : InjOn g (Metric.closedBall 0 1) := by
    intro p hp p' hp' hpp'
    rw [hg p hp, hg p' hp'] at hpp'
    exact congrArg Subtype.val (θ.injective (Subtype.ext hpp'))
  have hgDJ : g '' Metric.closedBall 0 1 = DJ := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hg p hp]
      exact (θ ⟨p, hp⟩).2
    · intro hy
      obtain ⟨⟨p, hp⟩, hpy⟩ := θ.surjective ⟨y, hy⟩
      exact ⟨p, hp, by rw [hg p hp, hpy]⟩
  have hgint : g '' Metric.ball 0 1 = DJint := by
    rw [hθ]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' := Metric.ball_subset_closedBall hp
      rw [hg p hp']
      exact ⟨θ ⟨p, hp'⟩, ⟨⟨p, hp'⟩, mem_ball_zero_iff.mp hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨p, hp⟩, hq, rfl⟩, rfl⟩
      exact ⟨p, mem_ball_zero_iff.mpr hq, hg p hp⟩
  have hDJc : IsCompact DJ := hgDJ ▸ (isCompact_closedBall 0 1).image_of_continuousOn hgc
  have hintD : DJint ⊆ DJ := hgint ▸ hgDJ ▸ image_mono Metric.ball_subset_closedBall
  have hDJpre : IsPreconnected DJint :=
    hgint ▸ (convex_ball (0 : Schoenflies.Plane) 1).isPreconnected.image g
      (hgc.mono Metric.ball_subset_closedBall)
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hpc.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hbdne : Ebd.Nonempty := by
    obtain ⟨φ⟩ := hpc.isSphere
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (r := 1)).mpr zero_le_one
    exact ⟨φ.symm ⟨v, hv⟩, (φ.symm ⟨v, hv⟩).2⟩
  have hEc : ∀ y ∈ Ec, y ∉ Ebd → y ∈ Eint := fun y hy hyb => by
    rw [hpc.carrierEq] at hy
    exact hy.resolve_right hyb
  have hEint : ∀ y ∈ Eint, y ∉ Ebd := fun y hy hyb =>
    Set.disjoint_left.mp hpc.disjointRim hy hyb
  set Z := Ψ '' (DJint ∩ Eint) with hZdef
  have hZopen : IsOpen Z := by
    let B₀ := Metric.ball (0 : Schoenflies.Plane) 1 ∩ g ⁻¹' Ebdᶜ
    have hB₀ : IsOpen B₀ := (hgc.mono Metric.ball_subset_closedBall).isOpen_inter_preimage
      Metric.isOpen_ball hbdc.isOpen_compl
    have hB₀E : MapsTo g B₀ Eint := fun p hp =>
      hEc _ (hDJE (hgDJ ▸ mem_image_of_mem g (Metric.ball_subset_closedBall hp.1))) hp.2
    have heq : Z = (Ψ ∘ g) '' B₀ := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyD, hyE⟩, rfl⟩
        rw [← hgint] at hyD
        obtain ⟨p, hp, rfl⟩ := hyD
        exact ⟨p, ⟨hp, hEint _ hyE⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨g p, ⟨hgint ▸ mem_image_of_mem g hp.1, hB₀E hp⟩, rfl⟩
    rw [heq]
    exact DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hB₀
      (hΨc.comp (hgc.mono fun p hp => Metric.ball_subset_closedBall hp.1) hB₀E)
      (hΨi.comp (hgi.mono fun p hp => Metric.ball_subset_closedBall hp.1) hB₀E)
  have hZsub : Z ⊆ Metric.ball 0 1 \ Ψ '' (DJ \ DJint) := by
    rintro _ ⟨y, ⟨hyD, hyE⟩, rfl⟩
    exact ⟨hΨb hyE, fun h => (hΨJ y hyE h).2 hyD⟩
  have hZcl : ∀ p ∈ Metric.ball 0 1 \ Ψ '' (DJ \ DJint), p ∈ closure Z → p ∈ Z := by
    rintro p ⟨hp, hpJ⟩ hpcl
    have hcont : ContinuousWithinAt Φ Z p :=
      (hΦc.continuousAt (Metric.isOpen_ball.mem_nhds hp)).continuousWithinAt
    have h1 := hcont.mem_closure_image hpcl
    have himg : Φ '' Z = DJint ∩ Eint := by
      rw [hZdef, image_image]
      exact image_congr (fun y hy => hΦΨ y hy.2) |>.trans (image_id _)
    rw [himg] at h1
    have hDJcl : closure (DJint ∩ Eint) ⊆ DJ :=
      closure_minimal (inter_subset_left.trans hintD) hDJc.isClosed
    have hyE := hΦb hp
    have hyD := hDJcl h1
    refine ⟨Φ p, ⟨?_, hyE⟩, hΨΦ p hp⟩
    by_contra hyint
    exact hpJ ⟨Φ p, ⟨hyD, hyint⟩, hΨΦ p hp⟩
  have hstep : ∀ T : Set Schoenflies.Plane, IsPreconnected T →
      T ⊆ Metric.ball 0 1 \ Ψ '' (DJ \ DJint) → (T ∩ Z).Nonempty → T ⊆ Z := by
    intro T hT hTs hTZ
    refine hT.subset_left_of_subset_union hZopen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) (fun p hp => ?_) hTZ
    by_cases hpcl : p ∈ closure Z
    · exact Or.inl (hZcl p (hTs hp) hpcl)
    · exact Or.inr hpcl
  set O' := Metric.ball (0 : Schoenflies.Plane) 1 \ closure (Schoenflies.inside
    (Ψ '' (DJ \ DJint))) with hO'def
  have hO'pre : IsPreconnected O' := by
    have h := isPreconnected_compl_union_iUnion_closure_inside {Ψ '' (DJ \ DJint)}
      (fun γ' hγ' => by rw [Finset.mem_singleton.mp hγ']; exact hγ)
      (fun a ha b hb hab =>
        (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim)
      (F₀ := (Metric.ball (0 : Schoenflies.Plane) 1)ᶜ) Metric.isOpen_ball.isClosed_compl
      (by rw [compl_compl]; exact (convex_ball (0 : Schoenflies.Plane) 1).isPreconnected)
      (fun γ' hγ' => by
        rw [Finset.mem_singleton.mp hγ']
        exact disjoint_compl_left_iff_subset.mpr hclb)
    have heq : ((Metric.ball (0 : Schoenflies.Plane) 1)ᶜ ∪ ⋃ γ' ∈
        ({Ψ '' (DJ \ DJint)} : Finset (Set Schoenflies.Plane)),
          closure (Schoenflies.inside γ'))ᶜ = O' := by
      rw [Finset.set_biUnion_singleton, compl_union, compl_compl]
      rfl
    rwa [heq] at h
  have hsplit : Metric.ball 0 1 \ Ψ '' (DJ \ DJint) ⊆
      Schoenflies.inside (Ψ '' (DJ \ DJint)) ∪ O' := by
    rintro p ⟨hp, hpJ⟩
    by_cases hpin : p ∈ Schoenflies.inside (Ψ '' (DJ \ DJint))
    · exact Or.inl hpin
    · refine Or.inr ⟨hp, ?_⟩
      rw [closure_inside_eq_union hγ]
      exact fun h => h.elim hpin hpJ
  have hinsub : Schoenflies.inside (Ψ '' (DJ \ DJint)) ⊆
      Metric.ball 0 1 \ Ψ '' (DJ \ DJint) := fun p hp =>
    ⟨hclb (subset_closure hp), Schoenflies.inside_subset_compl hp⟩
  have hO'sub : O' ⊆ Metric.ball 0 1 \ Ψ '' (DJ \ DJint) := fun p hp =>
    ⟨hp.1, fun hpJ => hp.2 (by rw [closure_inside_eq_union hγ]; exact Or.inr hpJ)⟩
  have hZpre : ∀ S ⊆ Metric.ball 0 1, S ⊆ Z → Φ '' S ⊆ DJint := by
    rintro S hSb hSZ _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy, hyp⟩ := hSZ hp
    rw [← hyp, hΦΨ y hy.2]
    exact hy.1
  have hKc : IsCompact (Φ '' closure (Schoenflies.inside (Ψ '' (DJ \ DJint)))) :=
    hsep.isBounded_inside.isCompact_closure.image_of_continuousOn (hΦc.mono hclb)
  have hKcE : Φ '' closure (Schoenflies.inside (Ψ '' (DJ \ DJint))) ⊆
      Φ '' Schoenflies.inside (Ψ '' (DJ \ DJint)) ∪ (DJ \ DJint) := by
    rw [closure_inside_eq_union hγ, image_union]
    refine union_subset_union_right _ ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hΦΨ y (hJE hy)]
    exact hy
  have hkey : Schoenflies.inside (Ψ '' (DJ \ DJint)) ⊆ Z → Disjoint DJint Ebd := by
    intro hinZ
    obtain ⟨W, hW, hWeq⟩ := continuousOn_iff'.mp hΨc _ hsep.isOpen_inside
    have hInW : ∀ y ∈ Eint, Ψ y ∈ Schoenflies.inside (Ψ '' (DJ \ DJint)) → y ∈ W := by
      intro y hy hyin
      have hmem : y ∈ Ψ ⁻¹' Schoenflies.inside (Ψ '' (DJ \ DJint)) ∩ Eint := ⟨hyin, hy⟩
      rw [hWeq] at hmem
      exact hmem.1
    have hWin : ∀ y ∈ Eint, y ∈ W → Ψ y ∈ Schoenflies.inside (Ψ '' (DJ \ DJint)) := by
      intro y hy hyW
      have hmem : y ∈ W ∩ Eint := ⟨hyW, hy⟩
      rw [← hWeq] at hmem
      exact hmem.1
    let V₁ := W ∩ Ebdᶜ
    let V₂ := (Φ '' closure (Schoenflies.inside (Ψ '' (DJ \ DJint))))ᶜ
    have hV₁ : IsOpen V₁ := hW.inter hbdc.isOpen_compl
    have hV₂ : IsOpen V₂ := hKc.isClosed.isOpen_compl
    have hcover : DJint ⊆ V₁ ∪ V₂ := by
      intro y hy
      by_cases hyK : y ∈ Φ '' closure (Schoenflies.inside (Ψ '' (DJ \ DJint)))
      · rcases hKcE hyK with hyin | hyJ
        · obtain ⟨p, hp, rfl⟩ := hyin
          have hpE := hΦb (hclb (subset_closure hp))
          exact Or.inl ⟨hInW _ hpE (by rw [hΨΦ p (hclb (subset_closure hp))]; exact hp),
            hEint _ hpE⟩
        · exact (hyJ.2 hy).elim
      · exact Or.inr hyK
    have hboth : ∀ y ∈ DJint, y ∈ V₁ → y ∉ V₂ := by
      intro y hy hy₁ hy₂
      have hyE := hEc y (hDJE (hintD hy)) hy₁.2
      exact hy₂ ⟨Ψ y, subset_closure (hWin y hyE hy₁.1), hΦΨ y hyE⟩
    obtain ⟨p₀, hp₀⟩ := hsep.isConnected_inside.nonempty
    have hp₀b := hclb (subset_closure hp₀)
    have hp₀E := hΦb hp₀b
    have hne₁ : (DJint ∩ V₁).Nonempty :=
      ⟨Φ p₀, hZpre _ (fun p hp => hclb (subset_closure hp)) hinZ ⟨p₀, hp₀, rfl⟩,
        hInW _ hp₀E (by rw [hΨΦ p₀ hp₀b]; exact hp₀), hEint _ hp₀E⟩
    refine Set.disjoint_left.mpr fun y hy hyb => ?_
    have hsub : DJint ⊆ V₁ := by
      by_contra hns
      obtain ⟨z, hz, hzV⟩ := not_subset.mp hns
      have hz₂ : z ∈ V₂ := (hcover hz).resolve_left hzV
      obtain ⟨w, hw, hw₁, hw₂⟩ := hDJpre V₁ V₂ hV₁ hV₂ hcover hne₁ ⟨z, hz, hz₂⟩
      exact hboth w hw hw₁ hw₂
    exact (hsub hy).2 hyb
  by_cases hA : (O' ∩ Z).Nonempty
  · exfalso
    have hO'Z := hstep O' hO'pre hO'sub hA
    have hOutD : Φ '' O' ⊆ DJint := hZpre O' (fun p hp => hp.1) hO'Z
    have hbdcl : Ebd ⊆ closure (Φ '' O') := by
      intro z hz
      have hzcl : z ∈ closure Eint := by
        rw [hpc.closureEq]
        exact Or.inr hz
      have hEsplit : Eint ⊆ Φ '' closure (Schoenflies.inside (Ψ '' (DJ \ DJint))) ∪
          Φ '' O' := by
        intro y hy
        by_cases hyin : Ψ y ∈ closure (Schoenflies.inside (Ψ '' (DJ \ DJint)))
        · exact Or.inl ⟨Ψ y, hyin, hΦΨ y hy⟩
        · exact Or.inr ⟨Ψ y, ⟨hΨb hy, hyin⟩, hΦΨ y hy⟩
      have h1 := closure_mono hEsplit hzcl
      rw [closure_union, hKc.isClosed.closure_eq] at h1
      refine h1.resolve_left ?_
      rintro ⟨p, hp, rfl⟩
      exact hEint _ (hΦb (hclb hp)) hz
    have hbdD : Ebd ⊆ DJint := by
      intro z hz
      have hzD : z ∈ DJ := closure_minimal (hOutD.trans hintD) hDJc.isClosed (hbdcl hz)
      by_contra hzint
      exact hEint z (hJE ⟨hzD, hzint⟩) hz
    have hnin : ¬ (Schoenflies.inside (Ψ '' (DJ \ DJint)) ∩ Z).Nonempty := by
      intro hB
      obtain ⟨z, hz⟩ := hbdne
      exact Set.disjoint_left.mp
        (hkey (hstep _ hsep.isConnected_inside.isPreconnected hinsub hB)) (hbdD hz) hz
    apply IsTopologicalCellWithInterior.not_isPreconnected_sdiff ⟨θ, hθ⟩ hpc.isSphere hbdD
    have heq : DJint \ Ebd = Φ '' O' := by
      ext y
      constructor
      · rintro ⟨hy, hyb⟩
        have hyE := hEc y (hDJE (hintD hy)) hyb
        have hyZ : Ψ y ∈ Z := ⟨y, ⟨hy, hyE⟩, rfl⟩
        rcases hsplit (hZsub hyZ) with hyin | hyO
        · exact (hnin ⟨Ψ y, hyin, hyZ⟩).elim
        · exact ⟨Ψ y, hyO, hΦΨ y hyE⟩
      · intro hy
        obtain ⟨p, hp, rfl⟩ := hy
        exact ⟨hOutD ⟨p, hp, rfl⟩, hEint _ (hΦb hp.1)⟩
    rw [heq]
    exact hO'pre.image Φ (hΦc.mono fun p hp => hp.1)
  · have hZin : Z ⊆ Schoenflies.inside (Ψ '' (DJ \ DJint)) := by
      intro p hp
      rcases hsplit (hZsub hp) with hpin | hpO
      · exact hpin
      · exact (hA ⟨p, hpO, hp⟩).elim
    have hQZ : Ψ Q ∈ Z := ⟨Q, ⟨hQ, hQE⟩, rfl⟩
    have hinZ := hstep _ hsep.isConnected_inside.isPreconnected hinsub ⟨Ψ Q, hZin hQZ, hQZ⟩
    have hdisj := hkey hinZ
    have hDJint : DJint ⊆ Eint := fun y hy =>
      hEc y (hDJE (hintD hy)) (Set.disjoint_left.mp hdisj hy)
    refine ⟨fun y hy => ?_, ?_⟩
    · by_cases hyint : y ∈ DJint
      · exact hDJint hyint
      · exact hJE ⟨hy, hyint⟩
    · have hZeq : Z = Ψ '' DJint := by
        rw [hZdef, inter_eq_left.mpr hDJint]
      rw [← hZeq]
      exact hZin.antisymm hinZ

end DifferentialGeometry.Topology.PiecewiseLinear
