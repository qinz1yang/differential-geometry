/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

theorem continuous_crossSeamChordPos : Continuous crossSeamChordPos := by
  unfold crossSeamChordPos
  exact (((continuous_fst.add continuous_snd).add continuous_const).div_const 2).prodMk
    (((continuous_fst.add continuous_snd).sub continuous_const).div_const 2)

theorem continuous_crossSeamChordNeg : Continuous crossSeamChordNeg := by
  unfold crossSeamChordNeg
  exact (((continuous_fst.add continuous_snd).sub continuous_const).div_const 2).prodMk
    (((continuous_fst.add continuous_snd).add continuous_const).div_const 2)

theorem continuous_crossSeamResolvePos : Continuous crossSeamResolvePos := by
  unfold crossSeamResolvePos
  exact continuous_crossSeamChordPos.prodMap continuous_id

theorem continuous_crossSeamResolveNeg : Continuous crossSeamResolveNeg := by
  unfold crossSeamResolveNeg
  exact continuous_crossSeamChordNeg.prodMap continuous_id

theorem continuous_crossSeamResolve : Continuous crossSeamResolve := by
  have hcover : (({true} : Set Bool) ×ˢ (univ : Set ((ℝ × ℝ) × ℝ))) ∪
      (({false} : Set Bool) ×ˢ (univ : Set ((ℝ × ℝ) × ℝ))) = univ := by
    ext ⟨b, x⟩
    cases b <;> simp
  rw [← continuousOn_univ, ← hcover]
  refine ContinuousOn.union_of_isClosed ?_ ?_ ((isClosed_discrete _).prod isClosed_univ)
    ((isClosed_discrete _).prod isClosed_univ)
  · refine ContinuousOn.congr
      (f := fun q : Bool × ((ℝ × ℝ) × ℝ) => crossSeamResolvePos q.2) ?_ ?_
    · exact (continuous_crossSeamResolvePos.comp continuous_snd).continuousOn
    · rintro ⟨b, x⟩ ⟨hb, -⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact crossSeamResolve_true x
  · refine ContinuousOn.congr
      (f := fun q : Bool × ((ℝ × ℝ) × ℝ) => crossSeamResolveNeg q.2) ?_ ?_
    · exact (continuous_crossSeamResolveNeg.comp continuous_snd).continuousOn
    · rintro ⟨b, x⟩ ⟨hb, -⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact crossSeamResolve_false x

noncomputable def crossSeamResolveHomotopy (s : ℝ) (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ :=
  ((1 - s) • q.2.1 + s • (crossSeamResolve q).1, q.2.2)

theorem crossSeamResolveHomotopy_snd (s : ℝ) (q : Bool × ((ℝ × ℝ) × ℝ)) :
    (crossSeamResolveHomotopy s q).2 = q.2.2 := rfl

theorem crossSeamResolveHomotopy_zero (q : Bool × ((ℝ × ℝ) × ℝ)) :
    crossSeamResolveHomotopy 0 q = crossSeamInclude q := by
  simp [crossSeamResolveHomotopy, crossSeamInclude]

theorem crossSeamResolveHomotopy_one (q : Bool × ((ℝ × ℝ) × ℝ)) :
    crossSeamResolveHomotopy 1 q = crossSeamResolve q := by
  obtain ⟨b, x⟩ := q
  refine Prod.ext ?_ ?_
  · simp [crossSeamResolveHomotopy]
  · cases b
    · exact (crossSeamResolveNeg_snd x).symm
    · exact (crossSeamResolvePos_snd x).symm

theorem continuous_crossSeamResolveHomotopy :
    Continuous fun z : ℝ × (Bool × ((ℝ × ℝ) × ℝ)) => crossSeamResolveHomotopy z.1 z.2 := by
  unfold crossSeamResolveHomotopy
  refine Continuous.prodMk ?_ continuous_snd.snd.snd
  exact ((continuous_const.sub continuous_fst).smul continuous_snd.snd.fst).add
    (continuous_fst.smul (continuous_crossSeamResolve.comp continuous_snd).fst)

theorem crossSeamResolveHomotopy_mem_endDisk {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource) :
    crossSeamResolveHomotopy s q ∈ spliceSquare ×ˢ ({q.2.2} : Set ℝ) := by
  obtain ⟨b, x⟩ := q
  have hs0 : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have hsum : (1 - s) + s = 1 := by ring
  rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;> subst hb
  · refine segment_crossSeamResolvePos_subset hx ⟨1 - s, s, hs0, hs.1, hsum, ?_⟩
    refine Prod.ext rfl ?_
    have h2 : (crossSeamResolvePos x).2 = x.2 := crossSeamResolvePos_snd x
    simp only [Prod.snd_add, Prod.smul_snd, h2, smul_eq_mul, crossSeamResolveHomotopy_snd]
    ring
  · refine segment_crossSeamResolveNeg_subset hx ⟨1 - s, s, hs0, hs.1, hsum, ?_⟩
    refine Prod.ext rfl ?_
    have h2 : (crossSeamResolveNeg x).2 = x.2 := crossSeamResolveNeg_snd x
    simp only [Prod.snd_add, Prod.smul_snd, h2, smul_eq_mul, crossSeamResolveHomotopy_snd]
    ring

theorem crossSeamResolveHomotopy_mem_spliceCylinder {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource) :
    crossSeamResolveHomotopy s q ∈ spliceCylinder := by
  have hbase : q.2.2 ∈ Icc (0 : ℝ) 1 := by
    rcases mem_bentSource.mp hq with ⟨-, hx⟩ | ⟨-, hx⟩
    · exact hx.2
    · exact hx.2
  exact ⟨(crossSeamResolveHomotopy_mem_endDisk hs hq).1, hbase⟩

theorem crossSeamResolveHomotopy_eq_of_mem_lateral (s : ℝ) {q : Bool × ((ℝ × ℝ) × ℝ)}
    (hq : q ∈ bentSource) (hlat : q.2.1 ∈ spliceSquareBoundary) :
    crossSeamResolveHomotopy s q = q.2 := by
  obtain ⟨b, x⟩ := q
  have hfix : (crossSeamResolve (b, x)).1 = x.1 := by
    rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;> subst hb
    · have hid : crossSeamResolvePos x = x :=
        crossSeamResolvePos_eqOn_lateral
          (⟨hx, hlat, hx.2⟩ : x ∈ bentSheetPos ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1))
      rw [crossSeamResolve_true, hid]
    · have hid : crossSeamResolveNeg x = x :=
        crossSeamResolveNeg_eqOn_lateral
          (⟨hx, hlat, hx.2⟩ : x ∈ bentSheetNeg ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1))
      rw [crossSeamResolve_false, hid]
  refine Prod.ext ?_ rfl
  change (1 - s) • x.1 + s • (crossSeamResolve (b, x)).1 = x.1
  rw [hfix, ← add_smul, show (1 - s) + s = (1 : ℝ) by ring, one_smul]

theorem exists_lift_homotopic_of_crossSeamBoundary
    {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {Θ : Type w}
    [TopologicalSpace Θ] {ρ : X → M} (hρ : IsEmbedding ρ)
    {chart : (ℝ × ℝ) × ℝ → M} (hchart : ContinuousOn chart spliceCylinder)
    {Ω₁ Ω₂ : Set Θ} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂) (hcover : Ω₁ ∪ Ω₂ = univ)
    {co : Θ → Bool × ((ℝ × ℝ) × ℝ)} (hco : ContinuousOn co Ω₁)
    (hsource : MapsTo co Ω₁ bentSource) {g h : C(Θ, M)}
    (hraw : ∀ θ ∈ Ω₁, g θ = chart (crossSeamInclude (co θ)))
    (hres : ∀ θ ∈ Ω₁, h θ = chart (crossSeamResolve (co θ)))
    (hrest : ∀ θ ∈ Ω₂, h θ = g θ)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (co θ).2.1 ∈ spliceSquareBoundary)
    (hends : ∀ θ ∈ Ω₁, (co θ).2.2 = 0 ∨ (co θ).2.2 = 1)
    (hdisk : chart '' spliceEndDisks ⊆ Set.range ρ)
    (γ : C(Θ, X)) (hγ : ∀ θ, ρ (γ θ) = g θ) :
    ∃ (δ : C(Θ, X)) (H : ContinuousMap.Homotopy γ δ), (∀ θ, ρ (δ θ) = h θ) ∧
      (∀ θ ∈ Ω₂, ∀ s : unitInterval, H (s, θ) = γ θ) ∧
      ∀ θ ∈ Ω₁, ∀ s : unitInterval,
        ρ (H (s, θ)) ∈ chart '' (spliceSquare ×ˢ ({(co θ).2.2} : Set ℝ)) := by
  classical
  obtain ⟨F, hFstrip, hFout⟩ :
      ∃ F : unitInterval × Θ → M,
        (∀ z : unitInterval × Θ, z.2 ∈ Ω₁ →
            F z = chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2))) ∧
          ∀ z : unitInterval × Θ, z.2 ∉ Ω₁ → F z = g z.2 :=
    ⟨fun z => if z.2 ∈ Ω₁ then chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2)) else g z.2,
      fun _ hz => ite_eq_left hz, fun _ hz => ite_eq_right hz⟩
  have hother : ∀ θ : Θ, θ ∉ Ω₁ → θ ∈ Ω₂ := by
    intro θ hθ
    have hmem : θ ∈ Ω₁ ∪ Ω₂ := by rw [hcover]; exact mem_univ θ
    exact hmem.resolve_left hθ
  have hstat : ∀ z : unitInterval × Θ, z.2 ∈ Ω₂ → F z = g z.2 := by
    intro z hz
    by_cases hz₁ : z.2 ∈ Ω₁
    · rw [hFstrip z hz₁,
        crossSeamResolveHomotopy_eq_of_mem_lateral _ (hsource hz₁) (hlateral z.2 ⟨hz₁, hz⟩)]
      exact (hraw z.2 hz₁).symm
    · exact hFout z hz₁
  have hcyl : ∀ z : unitInterval × Θ, z.2 ∈ Ω₁ →
      crossSeamResolveHomotopy (z.1 : ℝ) (co z.2) ∈ spliceCylinder := fun z hz =>
    crossSeamResolveHomotopy_mem_spliceCylinder z.1.2 (hsource hz)
  have hcont : Continuous F := by
    rw [← continuousOn_univ]
    have huniv : (univ : Set (unitInterval × Θ)) = univ ×ˢ Ω₁ ∪ univ ×ˢ Ω₂ := by
      rw [← Set.prod_union, hcover, Set.univ_prod_univ]
    rw [huniv]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_univ.prod hΩ₁)
      (isClosed_univ.prod hΩ₂)
    · have hinner : ContinuousOn (fun z : unitInterval × Θ => ((z.1 : ℝ), co z.2))
          (univ ×ˢ Ω₁) :=
        ((continuous_subtype_val.comp continuous_fst).continuousOn).prodMk
          (hco.comp continuous_snd.continuousOn fun z hz => hz.2)
      have hmodel : ContinuousOn
          (fun z : unitInterval × Θ => crossSeamResolveHomotopy (z.1 : ℝ) (co z.2))
          (univ ×ˢ Ω₁) :=
        continuous_crossSeamResolveHomotopy.comp_continuousOn hinner
      have hcomp : ContinuousOn
          (fun z : unitInterval × Θ => chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2)))
          (univ ×ˢ Ω₁) :=
        ContinuousOn.comp hchart hmodel fun z hz => hcyl z hz.2
      exact ContinuousOn.congr hcomp fun z hz => hFstrip z hz.2
    · exact ContinuousOn.congr ((g.continuous.comp continuous_snd).continuousOn)
        fun z hz => hstat z hz.2
  have hF0 : ∀ θ : Θ, F (0, θ) = g θ := by
    intro θ
    by_cases hθ : θ ∈ Ω₁
    · rw [hFstrip (0, θ) hθ]
      simp only [Set.Icc.coe_zero, crossSeamResolveHomotopy_zero]
      exact (hraw θ hθ).symm
    · exact hFout (0, θ) hθ
  have hF1 : ∀ θ : Θ, F (1, θ) = h θ := by
    intro θ
    by_cases hθ : θ ∈ Ω₁
    · rw [hFstrip (1, θ) hθ]
      simp only [Set.Icc.coe_one, crossSeamResolveHomotopy_one]
      exact (hres θ hθ).symm
    · rw [hFout (1, θ) hθ]
      exact (hrest θ (hother θ hθ)).symm
  have hFrange : ∀ z : unitInterval × Θ, F z ∈ range ρ := by
    intro z
    by_cases hz : z.2 ∈ Ω₁
    · have hmem := crossSeamResolveHomotopy_mem_endDisk z.1.2 (hsource hz)
      have hend : (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2)).2 ∈ ({0, 1} : Set ℝ) := by
        rw [crossSeamResolveHomotopy_snd]
        rcases hends z.2 hz with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.mpr h)
      rw [hFstrip z hz]
      exact hdisk ⟨_, ⟨hmem.1, hend⟩, rfl⟩
    · rw [hFout z hz]
      exact ⟨γ z.2, hγ z.2⟩
  choose L hL using hFrange
  have hLcont : Continuous L := by
    rw [hρ.isInducing.continuous_iff, show ρ ∘ L = F from funext hL]
    exact hcont
  have hL0 : ∀ θ : Θ, L (0, θ) = γ θ := fun θ =>
    hρ.injective ((hL (0, θ)).trans ((hF0 θ).trans (hγ θ).symm))
  refine ⟨⟨fun θ => L (1, θ), hLcont.comp (continuous_const.prodMk continuous_id)⟩,
    { toFun := L, continuous_toFun := hLcont, map_zero_left := hL0,
      map_one_left := fun _ => rfl }, fun θ => ?_, fun θ hθ s => ?_, fun θ hθ s => ?_⟩
  · exact (hL (1, θ)).trans (hF1 θ)
  · exact hρ.injective ((hL (s, θ)).trans ((hstat (s, θ) hθ).trans (hγ θ).symm))
  · change ρ (L (s, θ)) ∈ chart '' (spliceSquare ×ˢ ({(co θ).2.2} : Set ℝ))
    rw [hL (s, θ), hFstrip (s, θ) hθ]
    exact mem_image_of_mem _ (crossSeamResolveHomotopy_mem_endDisk s.2 (hsource hθ))

theorem exists_boundaryWordWitness_of_crossSeamBoundary
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {X : Type v} [TopologicalSpace X] {ρ : X → M} (hρ : IsEmbedding ρ)
    {G cell : SingularTwoCell M} (hdomain : cell.domain = G.domain)
    {chart : (ℝ × ℝ) × ℝ → M} (hchart : ContinuousOn chart spliceCylinder)
    {word : freeLoop X} (W : BoundaryWordWitness G ρ word)
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂) (hcover : Ω₁ ∪ Ω₂ = univ)
    {co : loopCircle → Bool × ((ℝ × ℝ) × ℝ)} (hco : ContinuousOn co Ω₁)
    (hsource : MapsTo co Ω₁ bentSource)
    (hraw : ∀ θ ∈ Ω₁, G (W.param θ) = chart (crossSeamInclude (co θ)))
    (hres : ∀ θ ∈ Ω₁, cell (W.param θ) = chart (crossSeamResolve (co θ)))
    (hrest : ∀ θ ∈ Ω₂, cell (W.param θ) = G (W.param θ))
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (co θ).2.1 ∈ spliceSquareBoundary)
    (hends : ∀ θ ∈ Ω₁, (co θ).2.2 = 0 ∨ (co θ).2.2 = 1)
    (hdisk : chart '' spliceEndDisks ⊆ Set.range ρ) :
    Nonempty (BoundaryWordWitness cell ρ word) := by
  let e : loopCircle ≃ₜ frontier cell.domain :=
    W.param.trans (Homeomorph.setCongr (congrArg frontier hdomain)).symm
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary hρ hchart hΩ₁ hΩ₂
    hcover hco hsource (g := G.boundary.comp ⟨⇑W.param, W.param.continuous⟩)
    (h := cell.boundary.comp ⟨⇑e, e.continuous⟩)
    (fun θ hθ => hraw θ hθ) (fun θ hθ => hres θ hθ) (fun θ hθ => hrest θ hθ)
    (fun θ hθ => hlateral θ hθ) hends hdisk W.loop W.realizes
  have hhom : ContinuousMap.Homotopic W.loop δ := ⟨H⟩
  exact ⟨{ param := e
           loop := δ
           realizes := hδ
           homotopic :=
             ContinuousMap.Homotopic.trans (ContinuousMap.Homotopic.symm hhom) W.homotopic }⟩

section NonVacuity

abbrev crossSeamExampleSpace : Type := (spliceCylinder : Set ((ℝ × ℝ) × ℝ))

abbrev crossSeamExampleIncl : crossSeamExampleSpace → (ℝ × ℝ) × ℝ := Subtype.val

theorem crossSeamExampleSpace_ne_univ : range crossSeamExampleIncl ≠ univ := by
  rw [Subtype.range_coe]
  intro hcontra
  have hmem : (((2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ spliceCylinder := by rw [hcontra]; trivial
  have h2 : (2 : ℝ) ≤ 1 := hmem.1.1.2
  linarith

noncomputable def crossSeamExampleCoord (t : unitInterval) : Bool × ((ℝ × ℝ) × ℝ) :=
  (true, (((t : ℝ), (0 : ℝ)), (0 : ℝ)))

theorem crossSeamExampleCoord_mem (t : unitInterval) :
    crossSeamExampleCoord t ∈ bentSource := by
  refine mem_bentSource.mpr (Or.inl ⟨rfl, ?_, ?_⟩)
  · exact mem_bentArcPos.mpr (Or.inl ⟨⟨t.2.1, t.2.2⟩, rfl⟩)
  · exact ⟨le_refl 0, zero_le_one⟩

theorem continuous_crossSeamExampleCoord : Continuous crossSeamExampleCoord := by
  unfold crossSeamExampleCoord
  exact continuous_const.prodMk ((continuous_subtype_val.prodMk continuous_const).prodMk
    continuous_const)

noncomputable def crossSeamExampleRaw : C(unitInterval, (ℝ × ℝ) × ℝ) :=
  ⟨fun t => crossSeamInclude (crossSeamExampleCoord t),
    continuous_crossSeamExampleCoord.snd⟩

noncomputable def crossSeamExampleResolved : C(unitInterval, (ℝ × ℝ) × ℝ) :=
  ⟨fun t => crossSeamResolve (crossSeamExampleCoord t),
    continuous_crossSeamResolve.comp continuous_crossSeamExampleCoord⟩

theorem crossSeamExampleRaw_mem (t : unitInterval) :
    crossSeamExampleRaw t ∈ spliceCylinder := by
  have hmem := crossSeamResolveHomotopy_mem_spliceCylinder (s := 0)
    ⟨le_refl 0, zero_le_one⟩ (crossSeamExampleCoord_mem t)
  rwa [crossSeamResolveHomotopy_zero] at hmem

theorem crossSeamExampleRaw_ne_resolved : crossSeamExampleRaw ≠ crossSeamExampleResolved := by
  intro hcontra
  have h := congrArg (fun f : C(unitInterval, (ℝ × ℝ) × ℝ) => (f 0).1.1) hcontra
  simp only [crossSeamExampleRaw, crossSeamExampleResolved, crossSeamExampleCoord,
    ContinuousMap.coe_mk, crossSeamInclude, crossSeamResolve_true, crossSeamResolvePos_fst,
    crossSeamChordPos_fst, Set.Icc.coe_zero] at h
  norm_num at h

noncomputable def crossSeamExampleLoop : C(unitInterval, crossSeamExampleSpace) :=
  ⟨fun t => ⟨crossSeamExampleRaw t, crossSeamExampleRaw_mem t⟩,
    crossSeamExampleRaw.continuous.subtype_mk _⟩

theorem exists_lift_homotopic_crossSeamExample :
    ∃ (δ : C(unitInterval, crossSeamExampleSpace))
      (_ : ContinuousMap.Homotopy crossSeamExampleLoop δ),
      (∀ t, crossSeamExampleIncl (δ t) = crossSeamExampleResolved t) ∧
        δ ≠ crossSeamExampleLoop := by
  have hlat : ∀ t : unitInterval, (t : ℝ) = 1 →
      (crossSeamExampleCoord t).2.1 ∈ spliceSquareBoundary := by
    intro t ht
    have hpt : (crossSeamExampleCoord t).2.1 = ((1 : ℝ), (0 : ℝ)) := Prod.ext ht rfl
    rw [hpt]
    refine mem_spliceSquareBoundary.mpr ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Or.inr (Or.inl rfl)⟩ <;> norm_num
  have hdisk : (id : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) '' spliceEndDisks ⊆
      Set.range crossSeamExampleIncl := by
    rw [Set.image_id, Subtype.range_coe]
    exact spliceEndDisks_subset_spliceCylinder
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary
    (ρ := crossSeamExampleIncl) (chart := id) (Θ := unitInterval)
    IsEmbedding.subtypeVal continuousOn_id isClosed_univ
    (isClosed_eq continuous_subtype_val continuous_const)
    (Set.univ_union _) continuous_crossSeamExampleCoord.continuousOn
    (fun t _ => crossSeamExampleCoord_mem t)
    (g := crossSeamExampleRaw) (h := crossSeamExampleResolved)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun t ht => by
      have hfix := crossSeamResolveHomotopy_eq_of_mem_lateral 1
        (crossSeamExampleCoord_mem t) (hlat t ht)
      rw [crossSeamResolveHomotopy_one] at hfix
      exact hfix)
    (fun t ht => hlat t ht.2) (fun _ _ => Or.inl rfl) hdisk
    crossSeamExampleLoop (fun _ => rfl)
  refine ⟨δ, H, hδ, ?_⟩
  intro hcontra
  refine crossSeamExampleRaw_ne_resolved (ContinuousMap.ext fun t => ?_)
  have hval := hδ t
  rw [hcontra] at hval
  exact hval

noncomputable def crossSeamExampleCentre : Bool × ((ℝ × ℝ) × ℝ) :=
  (true, (((0 : ℝ), (0 : ℝ)), (0 : ℝ)))

theorem crossSeamExampleCentre_mem : crossSeamExampleCentre ∈ bentSource := by
  refine mem_bentSource.mpr (Or.inl ⟨rfl, ?_, ?_⟩)
  · exact mem_bentArcPos.mpr (Or.inl ⟨⟨le_refl 0, zero_le_one⟩, rfl⟩)
  · exact ⟨le_refl 0, zero_le_one⟩

theorem crossSeamExampleCentre_mem_spliceCylinder :
    crossSeamInclude crossSeamExampleCentre ∈ spliceCylinder := by
  have hmem := crossSeamResolveHomotopy_mem_spliceCylinder (s := 0)
    ⟨le_refl 0, zero_le_one⟩ crossSeamExampleCentre_mem
  rwa [crossSeamResolveHomotopy_zero] at hmem

noncomputable def crossSeamExampleCentreLoop : freeLoop crossSeamExampleSpace :=
  ContinuousMap.const loopCircle
    ⟨crossSeamInclude crossSeamExampleCentre, crossSeamExampleCentre_mem_spliceCylinder⟩

theorem exists_lift_homotopic_crossSeamLoopExample :
    ∃ (δ : freeLoop crossSeamExampleSpace)
      (_ : ContinuousMap.Homotopy crossSeamExampleCentreLoop δ),
      (∀ θ, crossSeamExampleIncl (δ θ) = crossSeamResolve crossSeamExampleCentre) ∧
        δ ≠ crossSeamExampleCentreLoop := by
  have hdisk : (id : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) '' spliceEndDisks ⊆
      Set.range crossSeamExampleIncl := by
    rw [Set.image_id, Subtype.range_coe]
    exact spliceEndDisks_subset_spliceCylinder
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary
    (ρ := crossSeamExampleIncl) (chart := id) (Θ := loopCircle)
    (co := fun _ => crossSeamExampleCentre)
    IsEmbedding.subtypeVal continuousOn_id isClosed_univ isClosed_empty
    (Set.union_empty _) continuousOn_const (fun _ _ => crossSeamExampleCentre_mem)
    (g := ContinuousMap.const loopCircle (crossSeamInclude crossSeamExampleCentre))
    (h := ContinuousMap.const loopCircle (crossSeamResolve crossSeamExampleCentre))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ hθ => hθ.elim) (fun _ hθ => hθ.2.elim)
    (fun _ _ => Or.inl rfl) hdisk crossSeamExampleCentreLoop (fun _ => rfl)
  refine ⟨δ, H, hδ, ?_⟩
  intro hcontra
  have hval := hδ 0
  rw [hcontra] at hval
  have hfst := congrArg (fun y : (ℝ × ℝ) × ℝ => y.1.1) hval
  simp only [crossSeamExampleCentre, crossSeamExampleCentreLoop, crossSeamInclude,
    crossSeamResolve_true, crossSeamResolvePos_fst, crossSeamChordPos_fst,
    ContinuousMap.const_apply] at hfst
  norm_num at hfst

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
