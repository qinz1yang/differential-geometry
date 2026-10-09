/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InteriorTwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private noncomputable def signScale (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ :=
  (LinearEquiv.refl ℝ ℝ).prodCongr
    ((LinearEquiv.smulOfNeZero ℝ ℝ p hp).prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ q hq))

private theorem signScale_apply {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (z : ℝ × ℝ × ℝ) :
    signScale p q hp hq z = (z.1, p * z.2.1, q * z.2.2) := by
  simp [signScale]

private theorem hasPLTwoSidedCrossingAt_comm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A B : Set F} {x : F} (hx : HasPLTwoSidedCrossingAt A B x) :
    HasPLTwoSidedCrossingAt B A x := by
  obtain ⟨U, V, g, P, Q, hU, hV, hxU, hg, hgx, hP, hQ, hI, hsup, hnear⟩ := hx
  refine ⟨U, V, g, Q, P, hU, hV, hxU, hg, hgx, hQ, hP, ?_, ?_, ?_⟩
  · exact (congrArg (fun R : Submodule ℝ F => Module.finrank ℝ R) (inf_comm Q P)).trans hI
  · simpa only [sup_comm] using hsup
  · filter_upwards [hnear] with y hy
    exact hy.symm

private theorem exists_isOpen_image_inter_subset_image {X Y : Type*} [TopologicalSpace X]
    [Nonempty X] [TopologicalSpace Y] {f : X → Y} {A S : Set X} (hinj : InjOn f A)
    (hcont : ContinuousOn (Function.invFunOn f A) (f '' A)) {x : X} (hxA : x ∈ A)
    (hS : S ∈ 𝓝 x) : ∃ O : Set Y, IsOpen O ∧ f x ∈ O ∧ f '' A ∩ O ⊆ f '' S := by
  have hinvx : Function.invFunOn f A (f x) = x := hinj.leftInvOn_invFunOn hxA
  have hmem : Function.invFunOn f A ⁻¹' S ∈ 𝓝[f '' A] (f x) := by
    refine hcont (f x) ⟨x, hxA, rfl⟩ ?_
    rw [hinvx]
    exact hS
  obtain ⟨O, hO, hfxO, hsub⟩ := mem_nhdsWithin.mp hmem
  refine ⟨O, hO, hfxO, ?_⟩
  rintro _ ⟨⟨z, hzA, rfl⟩, hzO⟩
  refine ⟨Function.invFunOn f A (f z), hsub ⟨hzO, ⟨z, hzA, rfl⟩⟩, ?_⟩
  rw [hinj.leftInvOn_invFunOn hzA]

private theorem exists_isPreconnected_arc {J C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)} (hCpoly : IsPolyhedron C)
    (hρpl : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) C) {a : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ J) {Va : Set (EuclideanSpace ℝ (Fin 2))} (hVa : IsOpen Va) (haVa : a ∈ Va)
    {δ : ℝ} (hδpos : 0 < δ) :
    ∃ Ja : Set (EuclideanSpace ℝ (Fin 2)), Ja ⊆ J ∧ Ja ⊆ Va ∧ a ∈ Ja ∧ IsPreconnected Ja ∧
      Ja ∈ 𝓝[J] a := by
  classical
  have hCloc : LocallyConnectedSpace C := hCpoly.locallyConnectedSpace
  have hTloc : LocallyConnectedSpace (J ×ˢ Icc (-1 : ℝ) 1 :
      Set (EuclideanSpace ℝ (Fin 2) × ℝ)) := hρpl.homeomorph.locallyConnectedSpace
  have haT : ((a, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨ha, by constructor <;> norm_num⟩
  have hSopen : IsOpen ((Subtype.val ⁻¹' (Va ×ˢ Ioo (-δ) δ)) :
      Set (J ×ˢ Icc (-1 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin 2) × ℝ))) :=
    (hVa.prod isOpen_Ioo).preimage continuous_subtype_val
  have hx₀S : (⟨(a, 0), haT⟩ : (J ×ˢ Icc (-1 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin 2) × ℝ))) ∈
      Subtype.val ⁻¹' (Va ×ˢ Ioo (-δ) δ) := ⟨haVa, by constructor <;> linarith⟩
  have hK'open : IsOpen (connectedComponentIn (Subtype.val ⁻¹' (Va ×ˢ Ioo (-δ) δ))
      (⟨(a, 0), haT⟩ : (J ×ˢ Icc (-1 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin 2) × ℝ)))) :=
    hSopen.connectedComponentIn
  have hx₀K' : (⟨(a, 0), haT⟩ : (J ×ˢ Icc (-1 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin 2) × ℝ))) ∈
      connectedComponentIn (Subtype.val ⁻¹' (Va ×ˢ Ioo (-δ) δ)) ⟨(a, 0), haT⟩ :=
    mem_connectedComponentIn hx₀S
  obtain ⟨W, hWnhds, hWsub⟩ :=
    (mem_nhds_subtype _ ⟨(a, 0), haT⟩ _).mp (hK'open.mem_nhds hx₀K')
  refine ⟨Prod.fst '' (Subtype.val '' connectedComponentIn
    (Subtype.val ⁻¹' (Va ×ˢ Ioo (-δ) δ))
    (⟨(a, 0), haT⟩ : (J ×ˢ Icc (-1 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin 2) × ℝ)))),
    ?_, ?_, ⟨(a, 0), ⟨⟨(a, 0), haT⟩, hx₀K', rfl⟩, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨_, ⟨v, -, rfl⟩, rfl⟩
    exact v.2.1
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact (connectedComponentIn_subset _ _ hv).1
  · exact (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn).image _ continuous_fst.continuousOn
  · obtain ⟨W', hW'sub, hW'open, haW'⟩ := mem_nhds_iff.mp hWnhds
    obtain ⟨V₁, V₂, hV₁, hV₂, haV₁, h0V₂, hV12⟩ := isOpen_prod_iff.mp hW'open a 0 haW'
    refine mem_nhdsWithin.mpr ⟨V₁, hV₁, haV₁, ?_⟩
    rintro w ⟨hwV₁, hwJ⟩
    have hwT : ((w, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hwJ, by constructor <;> norm_num⟩
    exact ⟨(w, 0), ⟨⟨(w, 0), hwT⟩, hWsub (hW'sub (hV12 ⟨hwV₁, h0V₂⟩)), rfl⟩, rfl⟩

private theorem exists_collar_half_sign {J C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)} (hCpoly : IsPolyhedron C)
    (hρpl : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) C) (hρ0 : ∀ x ∈ J, ρ (x, 0) = x)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) (hCa : C ∈ 𝓝 a)
    {O : Set (EuclideanSpace ℝ (Fin 2))} (hO : IsOpen O) (haO : a ∈ O)
    {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ} (hGcont : ContinuousOn G O) (hGinj : InjOn G O)
    (hGzero : ∀ x ∈ C ∩ O, ((G x).2 = 0 ↔ x ∈ J)) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 2))) (σ : ℝ), σ ≠ 0 ∧ IsOpen P ∧ a ∈ P ∧ P ⊆ C ∩ O ∧
      ∀ x ∈ P, (0 < σ * (G x).2 ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)) := by
  classical
  have haC : a ∈ C := mem_of_mem_nhds hCa
  have haT : ((a, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨ha, by constructor <;> norm_num⟩
  have hρa : ρ (a, 0) = a := hρ0 a ha
  have hρcont : ContinuousOn ρ (J ×ˢ Icc (-1 : ℝ) 1) := hρpl.isPiecewiseAffineOn.continuousOn
  obtain ⟨Ja, δ, hδpos, hδ1, hJaJ, haJa, hJaconn, hJanhds, hJaO⟩ :
      ∃ (Ja : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧ Ja ⊆ J ∧ a ∈ Ja ∧
        IsPreconnected Ja ∧ Ja ∈ 𝓝[J] a ∧ ρ '' (Ja ×ˢ Ioo (-δ) δ) ⊆ O := by
    have hmem : ρ ⁻¹' O ∈ 𝓝[J ×ˢ Icc (-1 : ℝ) 1] ((a, (0 : ℝ))) := by
      refine hρcont _ haT ?_
      rw [hρa]
      exact hO.mem_nhds haO
    obtain ⟨O₁, hO₁, haO₁, hO₁sub⟩ := mem_nhdsWithin.mp hmem
    obtain ⟨Va, Vs, hVa, hVs, haVa, h0Vs, hbox⟩ := isOpen_prod_iff.mp hO₁ a 0 haO₁
    obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.mp hVs 0 h0Vs
    obtain ⟨δ, hδpos, hδ1, hIooVs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ Ioo (-δ) δ ⊆ Vs := by
      refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun t ht => hδ₀sub ?_⟩
      have h1 : min δ₀ 1 ≤ δ₀ := min_le_left _ _
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hIooIcc : Ioo (-δ) δ ⊆ Icc (-1 : ℝ) 1 := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨Ja, hJaJ, hJaVa, haJa, hJaconn, hJanhds⟩ :=
      exists_isPreconnected_arc hCpoly hρpl ha hVa haVa hδpos
    refine ⟨Ja, δ, hδpos, hδ1, hJaJ, haJa, hJaconn, hJanhds, ?_⟩
    rintro _ ⟨⟨w, s⟩, ⟨hw, hs⟩, rfl⟩
    exact hO₁sub ⟨hbox ⟨hJaVa hw, hIooVs hs⟩, ⟨hJaJ hw, hIooIcc hs⟩⟩
  have hIooIcc : Ioo (-δ) δ ⊆ Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hprodT : Ja ×ˢ Ioo (-δ) δ ⊆ J ×ˢ Icc (-1 : ℝ) 1 := fun z hz => ⟨hJaJ hz.1, hIooIcc hz.2⟩
  have hZC : ρ '' (Ja ×ˢ Ioo (-δ) δ) ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact hρpl.bijOn.mapsTo (hprodT hz)
  have hZsub : ρ '' (Ja ×ˢ Ioo (-δ) δ) ⊆ C ∩ O := fun x hx => ⟨hZC hx, hJaO hx⟩
  have hZnhds : ρ '' (Ja ×ˢ Ioo (-δ) δ) ∈ 𝓝 a := by
    have hψcont : ContinuousOn (Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1)) C :=
      hρpl.isPiecewiseAffineOn_invFunOn.continuousOn
    have hψa : Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1) a = (a, 0) := by
      have h1 := hρpl.bijOn.injOn.leftInvOn_invFunOn haT
      rwa [hρa] at h1
    have hprodnhds : Ja ×ˢ Ioo (-δ) δ ∈ 𝓝[J ×ˢ Icc (-1 : ℝ) 1] ((a, (0 : ℝ))) := by
      rw [nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod hJanhds
        (mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hδpos⟩))
    have htend : Filter.Tendsto (Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1)) (𝓝[C] a)
        (𝓝[J ×ˢ Icc (-1 : ℝ) 1] (Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1) a)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hψcont a haC)
        (Filter.eventually_of_mem self_mem_nhdsWithin fun x hx =>
          hρpl.bijOn.surjOn.mapsTo_invFunOn hx)
    rw [hψa] at htend
    obtain ⟨O₂, hO₂open, haO₂, hO₂sub⟩ := mem_nhdsWithin.mp (htend hprodnhds)
    refine Filter.mem_of_superset (Filter.inter_mem hCa (hO₂open.mem_nhds haO₂)) ?_
    rintro x ⟨hxC, hxO₂⟩
    exact ⟨Function.invFunOn ρ (J ×ˢ Icc (-1 : ℝ) 1) x, hO₂sub ⟨hxO₂, hxC⟩,
      hρpl.bijOn.invOn_invFunOn.2 hxC⟩
  have haZ : a ∈ interior (ρ '' (Ja ×ˢ Ioo (-δ) δ)) := mem_interior_iff_mem_nhds.mpr hZnhds
  have hzeroJ : ∀ w ∈ J, ∀ s : ℝ, s ∈ Icc (-1 : ℝ) 1 → ρ (w, s) ∈ J → s = 0 := by
    intro w hw s hs hmem
    have h1 : ρ (ρ (w, s), 0) = ρ (w, s) := hρ0 _ hmem
    have h2 := hρpl.bijOn.injOn
      (⟨hmem, by constructor <;> norm_num⟩ :
        ((ρ (w, s), (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (-1 : ℝ) 1)
      ⟨hw, hs⟩ h1
    exact (congrArg Prod.snd h2).symm
  have hsign : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) δ), ((G x).2 = 0 ↔ x ∈ J) := fun x hx =>
    hGzero x (hZsub hx)
  have hZpZ : ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ) ⊆ ρ '' (Ja ×ˢ Ioo (-δ) δ) := by
    rintro _ ⟨⟨w, s⟩, hws, rfl⟩
    exact ⟨(w, s), ⟨hws.1, by linarith [hws.2.1], hws.2.2⟩, rfl⟩
  have hZmZ : ρ '' (Ja ×ˢ Ioo (-δ) 0) ⊆ ρ '' (Ja ×ˢ Ioo (-δ) δ) := by
    rintro _ ⟨⟨w, s⟩, hws, rfl⟩
    exact ⟨(w, s), ⟨hws.1, hws.2.1, by linarith [hws.2.2]⟩, rfl⟩
  have hnzp : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), (G x).2 ≠ 0 := by
    rintro _ ⟨⟨w, s⟩, hws, rfl⟩ hzero
    have hJ' : ρ (w, s) ∈ J := (hsign _ (hZpZ ⟨(w, s), hws, rfl⟩)).mp hzero
    have hs0 := hzeroJ w (hJaJ hws.1) s (hIooIcc ⟨by linarith [hws.2.1], hws.2.2⟩) hJ'
    linarith [hws.2.1]
  have hnzm : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), (G x).2 ≠ 0 := by
    rintro _ ⟨⟨w, s⟩, hws, rfl⟩ hzero
    have hJ' : ρ (w, s) ∈ J := (hsign _ (hZmZ ⟨(w, s), hws, rfl⟩)).mp hzero
    have hs0 := hzeroJ w (hJaJ hws.1) s (hIooIcc ⟨hws.2.1, by linarith [hws.2.2]⟩) hJ'
    linarith [hws.2.2]
  have hconst : ∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsPreconnected S → S ⊆ O →
      (∀ x ∈ S, (G x).2 ≠ 0) → ∀ x ∈ S, ∀ x' ∈ S, 0 < (G x).2 → 0 < (G x').2 := by
    intro S hS hSO hSne x hx x' hx' hpos
    by_contra hcon
    have hneg : (G x').2 < 0 := lt_of_le_of_ne (not_lt.mp hcon) (hSne x' hx')
    have himg : IsPreconnected ((fun z => (G z).2) '' S) := hS.image _ (hGcont.mono hSO).snd
    obtain ⟨z, hz, hz0⟩ := himg.ordConnected.out ⟨x', hx', rfl⟩ ⟨x, hx, rfl⟩
      (⟨hneg.le, hpos.le⟩ : (0 : ℝ) ∈ Icc (G x').2 (G x).2)
    exact hSne z hz hz0
  have hZpconn : IsPreconnected (ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ)) :=
    (hJaconn.prod (convex_Ioo (0 : ℝ) δ).isPreconnected).image _
      (hρcont.mono fun z hz => ⟨hJaJ hz.1, hIooIcc ⟨by linarith [hz.2.1], hz.2.2⟩⟩)
  have hZmconn : IsPreconnected (ρ '' (Ja ×ˢ Ioo (-δ) 0)) :=
    (hJaconn.prod (convex_Ioo (-δ) (0 : ℝ)).isPreconnected).image _
      (hρcont.mono fun z hz => ⟨hJaJ hz.1, hIooIcc ⟨hz.2.1, by linarith [hz.2.2]⟩⟩)
  have hZpO : ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ) ⊆ O := fun x hx => hJaO (hZpZ hx)
  have hZmO : ρ '' (Ja ×ˢ Ioo (-δ) 0) ⊆ O := fun x hx => hJaO (hZmZ hx)
  have hGa : (G a).2 = 0 := (hGzero a ⟨haC, haO⟩).mpr ha
  have hGopen : IsOpen (G '' interior (ρ '' (Ja ×ˢ Ioo (-δ) δ))) := by
    refine invariance_of_domain_isOpen_image_of_finrank_eq ?_ isOpen_interior
      (hGcont.mono (interior_subset.trans hJaO)) (hGinj.mono (interior_subset.trans hJaO))
    simp [Module.finrank_prod]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hGopen (G a) ⟨a, haZ, rfl⟩
  have hnear : ∀ t : ℝ, |t| < ε →
      ∃ x ∈ interior (ρ '' (Ja ×ˢ Ioo (-δ) δ)), (G x).2 = t := by
    intro t ht
    have hdist : dist (((G a).1, t) : ℝ × ℝ) (G a) < ε := by
      rw [Prod.dist_eq]
      have h1 : dist ((G a).1) ((G a).1) = 0 := dist_self _
      have h2 : dist t ((G a).2) = |t| := by rw [Real.dist_eq, hGa, sub_zero]
      rw [h1, h2]
      exact max_lt hε ht
    obtain ⟨x, hx, hxeq⟩ := hball (Metric.mem_ball.mpr hdist)
    exact ⟨x, hx, by rw [hxeq]⟩
  obtain ⟨xp, hxp, hxpval⟩ := hnear (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨xm, hxm, hxmval⟩ := hnear (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
  have hclass : ∀ x ∈ interior (ρ '' (Ja ×ˢ Ioo (-δ) δ)), (G x).2 ≠ 0 →
      x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ) ∨ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0) := by
    intro x hx hne
    obtain ⟨⟨w, s⟩, hws, rfl⟩ := interior_subset hx
    rcases lt_trichotomy s 0 with hlt | heq | hgt
    · exact Or.inr ⟨(w, s), ⟨hws.1, hws.2.1, hlt⟩, rfl⟩
    · refine absurd ((hsign _ ⟨(w, s), hws, rfl⟩).mpr ?_) hne
      rw [heq, hρ0 w (hJaJ hws.1)]
      exact hJaJ hws.1
    · exact Or.inl ⟨(w, s), ⟨hws.1, hgt, hws.2.2⟩, rfl⟩
  obtain ⟨σ, hσ0, hσp, hσm⟩ : ∃ σ : ℝ, σ ≠ 0 ∧
      (∀ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), 0 < σ * (G x).2) ∧
      (∀ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), σ * (G x).2 < 0) := by
    by_cases hcase : ∃ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), 0 < (G x).2
    · obtain ⟨x₁, hx₁, hx₁pos⟩ := hcase
      have hallp : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), 0 < (G x).2 := fun x hx =>
        hconst _ hZpconn hZpO hnzp x₁ hx₁ x hx hx₁pos
      have hallm : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), (G x).2 < 0 := by
        intro x hx
        by_contra hcon
        have hxpos : 0 < (G x).2 := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (hnzm x hx))
        have hm : ∀ x' ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), 0 < (G x').2 := fun x' hx' =>
          hconst _ hZmconn hZmO hnzm x hx x' hx' hxpos
        rcases hclass xm hxm (by rw [hxmval]; intro hz; linarith) with hin | hin
        · have h := hallp xm hin
          rw [hxmval] at h
          linarith
        · have h := hm xm hin
          rw [hxmval] at h
          linarith
      exact ⟨1, one_ne_zero, fun x hx => by have := hallp x hx; linarith,
        fun x hx => by have := hallm x hx; linarith⟩
    · have hcase' : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), ¬0 < (G x).2 := fun x hx hpos =>
        hcase ⟨x, hx, hpos⟩
      have hallp : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (0 : ℝ) δ), (G x).2 < 0 := fun x hx =>
        lt_of_le_of_ne (not_lt.mp (hcase' x hx)) (hnzp x hx)
      have hallm : ∀ x ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), 0 < (G x).2 := by
        intro x hx
        by_contra hcon
        have hxneg : (G x).2 < 0 := lt_of_le_of_ne (not_lt.mp hcon) (hnzm x hx)
        have hm : ∀ x' ∈ ρ '' (Ja ×ˢ Ioo (-δ) 0), (G x').2 < 0 := by
          intro x' hx'
          by_contra hcon'
          have hx'pos : 0 < (G x').2 := lt_of_le_of_ne (not_lt.mp hcon') (Ne.symm (hnzm x' hx'))
          have := hconst _ hZmconn hZmO hnzm x' hx' x hx hx'pos
          linarith
        rcases hclass xp hxp (by rw [hxpval]; intro hz; linarith) with hin | hin
        · have h := hallp xp hin
          rw [hxpval] at h
          linarith
        · have h := hm xp hin
          rw [hxpval] at h
          linarith
      exact ⟨-1, by norm_num, fun x hx => by have := hallp x hx; linarith,
        fun x hx => by have := hallm x hx; linarith⟩
  refine ⟨interior (ρ '' (Ja ×ˢ Ioo (-δ) δ)), σ, hσ0, isOpen_interior, haZ,
    interior_subset.trans hZsub, ?_⟩
  intro x hx
  obtain ⟨⟨w, s⟩, hws, rfl⟩ := interior_subset hx
  have hwJ : w ∈ J := hJaJ hws.1
  have hsIcc : s ∈ Icc (-1 : ℝ) 1 := hIooIcc hws.2
  have hRHS : (∃ s' ∈ Ioc (0 : ℝ) 1, ∃ w' ∈ J, ρ (w, s) = ρ (w', s')) ↔ 0 < s := by
    constructor
    · rintro ⟨s', hs', w', hw', heq⟩
      have hpair := hρpl.bijOn.injOn ⟨hwJ, hsIcc⟩
        (⟨hw', ⟨by linarith [hs'.1], hs'.2⟩⟩ :
          ((w', s') : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (-1 : ℝ) 1) heq
      have hss : s = s' := congrArg Prod.snd hpair
      linarith [hs'.1]
    · intro hpos
      exact ⟨s, ⟨hpos, le_of_lt (lt_of_lt_of_le hws.2.2 hδ1)⟩, w, hwJ, rfl⟩
  rw [hRHS]
  rcases lt_trichotomy s 0 with hlt | heq | hgt
  · have hneg := hσm _ ⟨(w, s), ⟨hws.1, hws.2.1, hlt⟩, rfl⟩
    exact ⟨fun hcon => absurd hcon (by linarith), fun hcon => absurd hcon (by linarith)⟩
  · have hz : (G (ρ (w, s))).2 = 0 := by
      refine (hsign _ ⟨(w, s), hws, rfl⟩).mpr ?_
      rw [heq, hρ0 w hwJ]
      exact hwJ
    rw [hz, mul_zero]
    exact ⟨fun hcon => absurd hcon (lt_irrefl 0), fun hcon => absurd hcon (by linarith)⟩
  · exact ⟨fun _ => hgt, fun _ => hσp _ ⟨(w, s), ⟨hws.1, hgt, hws.2.2⟩, rfl⟩⟩

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

private theorem exists_marked_chart_pl_of_sheets (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J)
    {e₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} (hye : ⇑D a ∈ e₀.source)
    {A Bs : Set (EuclideanSpace ℝ (Fin 2))} (haA : a ∈ A) (hbB : τ a ∈ Bs)
    (hAP : A ⊆ D.domain ∩ ⇑D ⁻¹' e₀.source) (hBP : Bs ⊆ D.domain ∩ ⇑D ⁻¹' e₀.source)
    (hdisj : Disjoint A Bs) (hAn : A ∈ 𝓝[D.domain ∩ ⇑D ⁻¹' e₀.source] a)
    (hBn : Bs ∈ 𝓝[D.domain ∩ ⇑D ⁻¹' e₀.source] (τ a))
    (hplA : IsPLHomeomorphOn (⇑e₀ ∘ ⇑D) A ((⇑e₀ ∘ ⇑D) '' A))
    (hplB : IsPLHomeomorphOn (⇑e₀ ∘ ⇑D) Bs ((⇑e₀ ∘ ⇑D) '' Bs))
    (hcr : HasPLTwoSidedCrossingAt ((⇑e₀ ∘ ⇑D) '' A) ((⇑e₀ ∘ ⇑D) '' Bs) (e₀ (⇑D a)))
    (hfibnear : ∀ᶠ z in 𝓝 (e₀ (⇑D a)),
      (D.domain ∩ ⇑D ⁻¹' e₀.source) ∩ (⇑e₀ ∘ ⇑D) ⁻¹' {z} ⊆ A ∪ Bs) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), hD.IsMarkedCrossingChartAt c J τ ρ a e ∧
      ∃ g : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ),
        IsPLHomeomorphOn g g.source g.target ∧ e = e₀.trans g := by
  classical
  obtain ⟨hpre, hCpoly, hCint, hJC, hCnhds, hρpl, hρ0, hdpp, -, -, -, -, -⟩ := hρ
  obtain ⟨-, -, -, hτmaps, -, hτne, -, hτD, -⟩ := hτ
  have haC : a ∈ C := hJC ha
  have hτaJ : τ a ∈ J := hτmaps ha
  have hτaC : τ a ∈ C := hJC hτaJ
  have haD : a ∈ D.domain := interior_subset (hCint haC)
  have hDτ : ⇑D (τ a) = ⇑D a := hτD a ha
  have hDcontA : ContinuousAt (⇑D) a :=
    (D.continuousOn a haD).continuousAt (mem_interior_iff_mem_nhds.mp (hCint haC))
  have hDcontB : ContinuousAt (⇑D) (τ a) :=
    (D.continuousOn (τ a) (interior_subset (hCint hτaC))).continuousAt
      (mem_interior_iff_mem_nhds.mp (hCint hτaC))
  have hPnhdsA : (D.domain ∩ ⇑D ⁻¹' e₀.source) ∈ 𝓝 a :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hCint haC))
      (hDcontA (e₀.open_source.mem_nhds hye))
  have hPnhdsB : (D.domain ∩ ⇑D ⁻¹' e₀.source) ∈ 𝓝 (τ a) :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hCint hτaC))
      (hDcontB (by rw [hDτ]; exact e₀.open_source.mem_nhds hye))
  have hAnhds : A ∈ 𝓝 a := by
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hAn
    exact Filter.mem_of_superset (Filter.inter_mem hV hPnhdsA) hVsub
  have hBnhds : Bs ∈ 𝓝 (τ a) := by
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hBn
    exact Filter.mem_of_superset (Filter.inter_mem hV hPnhdsB) hVsub
  have hDinjA : InjOn (⇑D) A := fun x hx x' hx' hxx =>
    hplA.bijOn.injOn hx hx' (congrArg (⇑e₀) hxx)
  have hDinjB : InjOn (⇑D) Bs := fun x hx x' hx' hxx =>
    hplB.bijOn.injOn hx hx' (congrArg (⇑e₀) hxx)
  obtain ⟨U, V, hmap, L, hU, hV, hyU, hh, hhy, hnear⟩ := hcr.exists_linearEquiv_normalForm
  have hN : {z | z ∈ U ∧ ((z ∈ (⇑e₀ ∘ ⇑D) '' A ↔ (L (hmap z)).2.2 = 0) ∧
      (z ∈ (⇑e₀ ∘ ⇑D) '' Bs ↔ (L (hmap z)).2.1 = 0)) ∧
      (D.domain ∩ ⇑D ⁻¹' e₀.source) ∩ (⇑e₀ ∘ ⇑D) ⁻¹' {z} ⊆ A ∪ Bs} ∈ 𝓝 (e₀ (⇑D a)) := by
    filter_upwards [hU.mem_nhds hyU, hnear, hfibnear] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨O₁, hO₁sub, hO₁open, hyO₁⟩ := mem_nhds_iff.mp hN
  have hO₁U : O₁ ⊆ U := fun z hz => (hO₁sub hz).1
  have hOzopen : IsOpen (e₀.source ∩ ⇑e₀ ⁻¹' O₁) :=
    e₀.continuousOn.isOpen_inter_preimage e₀.open_source hO₁open
  have hyOz : ⇑D a ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := ⟨hye, hyO₁⟩
  have himA : ∀ z ∈ e₀.source, (z ∈ ⇑D '' A ↔ ⇑e₀ z ∈ (⇑e₀ ∘ ⇑D) '' A) := by
    intro z hz
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨x, hx, e₀.injOn (hAP hx).2 hz hxz⟩
  have himB : ∀ z ∈ e₀.source, (z ∈ ⇑D '' Bs ↔ ⇑e₀ z ∈ (⇑e₀ ∘ ⇑D) '' Bs) := by
    intro z hz
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨x, hx, e₀.injOn (hBP hx).2 hz hxz⟩
  have hsheetA : ∀ z ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁,
      (z ∈ ⇑D '' A ↔ (L (hmap (⇑e₀ z))).2.2 = 0) := fun z hz =>
    (himA z hz.1).trans (hO₁sub hz.2).2.1.1
  have hsheetB : ∀ z ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁,
      (z ∈ ⇑D '' Bs ↔ (L (hmap (⇑e₀ z))).2.1 = 0) := fun z hz =>
    (himB z hz.1).trans (hO₁sub hz.2).2.1.2
  have hfibz : ∀ z ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁, ∀ x ∈ D.domain, ⇑D x = z → x ∈ A ∪ Bs := by
    intro z hz x hx hxz
    refine (hO₁sub hz.2).2.2 ⟨⟨hx, ?_⟩, ?_⟩
    · change ⇑D x ∈ e₀.source
      rw [hxz]
      exact hz.1
    · change ⇑e₀ (⇑D x) = ⇑e₀ z
      rw [hxz]
  have hφ₀ : IsPLHomeomorphOn ((fun w => L w) ∘ hmap) U ((fun w => L w) '' V) :=
    hh.trans (isPLHomeomorphOn_linearEquiv L hV)
  have hOaN : A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁) ∈ 𝓝 a :=
    Filter.inter_mem hAnhds (hDcontA (hOzopen.mem_nhds hyOz))
  have hObN : Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁) ∈ 𝓝 (τ a) :=
    Filter.inter_mem hBnhds (hDcontB (by rw [hDτ]; exact hOzopen.mem_nhds hyOz))
  have hOaA : interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)) ⊆ A := fun x hx =>
    (interior_subset hx).1
  have hObB : interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)) ⊆ Bs := fun x hx =>
    (interior_subset hx).1
  have hOaZ : ∀ x ∈ interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)),
      ⇑D x ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := fun x hx => (interior_subset hx).2
  have hObZ : ∀ x ∈ interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)),
      ⇑D x ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := fun x hx => (interior_subset hx).2
  have hcompA : ContinuousOn (fun x => L (hmap (⇑e₀ (⇑D x))))
      (interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) := by
    have h1 : ContinuousOn (⇑D) (interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) :=
      D.continuousOn.mono fun x hx => (hAP (hOaA hx)).1
    have h2 : ContinuousOn (fun x => ⇑e₀ (⇑D x))
        (interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) :=
      e₀.continuousOn.comp h1 fun x hx => (hOaZ x hx).1
    exact hφ₀.isPiecewiseAffineOn.continuousOn.comp h2 fun x hx => hO₁U (hOaZ x hx).2
  have hcompB : ContinuousOn (fun x => L (hmap (⇑e₀ (⇑D x))))
      (interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) := by
    have h1 : ContinuousOn (⇑D) (interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) :=
      D.continuousOn.mono fun x hx => (hBP (hObB hx)).1
    have h2 : ContinuousOn (fun x => ⇑e₀ (⇑D x))
        (interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) :=
      e₀.continuousOn.comp h1 fun x hx => (hObZ x hx).1
    exact hφ₀.isPiecewiseAffineOn.continuousOn.comp h2 fun x hx => hO₁U (hObZ x hx).2
  have hinjcore : ∀ x x' : EuclideanSpace ℝ (Fin 2), ⇑D x ∈ e₀.source → ⇑D x' ∈ e₀.source →
      ⇑e₀ (⇑D x) ∈ U → ⇑e₀ (⇑D x') ∈ U →
      L (hmap (⇑e₀ (⇑D x))) = L (hmap (⇑e₀ (⇑D x'))) → ⇑D x = ⇑D x' := by
    intro x x' hx hx' hxU hx'U heq
    exact e₀.injOn hx hx' (hh.bijOn.injOn hxU hx'U (L.injective heq))
  have hGinjA : InjOn (fun x => ((L (hmap (⇑e₀ (⇑D x)))).1, (L (hmap (⇑e₀ (⇑D x)))).2.1))
      (interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) := by
    intro x hx x' hx' hGeq
    have h22 : (L (hmap (⇑e₀ (⇑D x)))).2.2 = 0 := (hsheetA _ (hOaZ x hx)).mp ⟨x, hOaA hx, rfl⟩
    have h22' : (L (hmap (⇑e₀ (⇑D x')))).2.2 = 0 :=
      (hsheetA _ (hOaZ x' hx')).mp ⟨x', hOaA hx', rfl⟩
    have hGeq' : ((L (hmap (⇑e₀ (⇑D x)))).1, (L (hmap (⇑e₀ (⇑D x)))).2.1) =
        ((L (hmap (⇑e₀ (⇑D x')))).1, (L (hmap (⇑e₀ (⇑D x')))).2.1) := hGeq
    rw [Prod.mk.injEq] at hGeq'
    have heq : L (hmap (⇑e₀ (⇑D x))) = L (hmap (⇑e₀ (⇑D x'))) := by
      simp only [Prod.ext_iff]
      exact ⟨hGeq'.1, hGeq'.2, h22.trans h22'.symm⟩
    exact hDinjA (hOaA hx) (hOaA hx') (hinjcore x x' (hOaZ x hx).1 (hOaZ x' hx').1
      (hO₁U (hOaZ x hx).2) (hO₁U (hOaZ x' hx').2) heq)
  have hGinjB : InjOn (fun x => ((L (hmap (⇑e₀ (⇑D x)))).1, (L (hmap (⇑e₀ (⇑D x)))).2.2))
      (interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁))) := by
    intro x hx x' hx' hGeq
    have h21 : (L (hmap (⇑e₀ (⇑D x)))).2.1 = 0 := (hsheetB _ (hObZ x hx)).mp ⟨x, hObB hx, rfl⟩
    have h21' : (L (hmap (⇑e₀ (⇑D x')))).2.1 = 0 :=
      (hsheetB _ (hObZ x' hx')).mp ⟨x', hObB hx', rfl⟩
    have hGeq' : ((L (hmap (⇑e₀ (⇑D x)))).1, (L (hmap (⇑e₀ (⇑D x)))).2.2) =
        ((L (hmap (⇑e₀ (⇑D x')))).1, (L (hmap (⇑e₀ (⇑D x')))).2.2) := hGeq
    rw [Prod.mk.injEq] at hGeq'
    have heq : L (hmap (⇑e₀ (⇑D x))) = L (hmap (⇑e₀ (⇑D x'))) := by
      simp only [Prod.ext_iff]
      exact ⟨hGeq'.1, h21.trans h21'.symm, hGeq'.2⟩
    exact hDinjB (hObB hx) (hObB hx') (hinjcore x x' (hObZ x hx).1 (hObZ x' hx').1
      (hO₁U (hObZ x hx).2) (hO₁U (hObZ x' hx').2) heq)
  have hGzeroA : ∀ x ∈ C ∩ interior (A ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)),
      ((L (hmap (⇑e₀ (⇑D x)))).2.1 = 0 ↔ x ∈ J) := by
    intro x hx
    have hxA : x ∈ A := hOaA hx.2
    have hxz : ⇑D x ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := hOaZ x hx.2
    constructor
    · intro hzero
      obtain ⟨x', hx'B, hx'eq⟩ := (hsheetB _ hxz).mpr hzero
      have hne : x ≠ x' := fun hxx => Set.disjoint_left.mp hdisj hxA (hxx ▸ hx'B)
      have hdp : x ∈ doublePointPreimage (⇑D) D.domain :=
        ⟨(hAP hxA).1, x, (hAP hxA).1, x', (hBP hx'B).1, hne, rfl, hx'eq⟩
      exact hdpp.subset ⟨hdp, hx.1⟩
    · intro hxJ
      have hτx : τ x ∈ J := hτmaps hxJ
      have hτxD : τ x ∈ D.domain := interior_subset (hCint (hJC hτx))
      have hτxeq : ⇑D (τ x) = ⇑D x := hτD x hxJ
      rcases hfibz (⇑D x) hxz (τ x) hτxD hτxeq with hin | hin
      · exact absurd (hDinjA hin hxA hτxeq) (hτne x hxJ)
      · exact (hsheetB _ hxz).mp ⟨τ x, hin, hτxeq⟩
  have hGzeroB : ∀ x ∈ C ∩ interior (Bs ∩ ⇑D ⁻¹' (e₀.source ∩ ⇑e₀ ⁻¹' O₁)),
      ((L (hmap (⇑e₀ (⇑D x)))).2.2 = 0 ↔ x ∈ J) := by
    intro x hx
    have hxB : x ∈ Bs := hObB hx.2
    have hxz : ⇑D x ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := hObZ x hx.2
    constructor
    · intro hzero
      obtain ⟨x', hx'A, hx'eq⟩ := (hsheetA _ hxz).mpr hzero
      have hne : x ≠ x' := fun hxx => Set.disjoint_left.mp hdisj (hxx ▸ hx'A) hxB
      have hdp : x ∈ doublePointPreimage (⇑D) D.domain :=
        ⟨(hBP hxB).1, x, (hBP hxB).1, x', (hAP hx'A).1, hne, rfl, hx'eq⟩
      exact hdpp.subset ⟨hdp, hx.1⟩
    · intro hxJ
      have hτx : τ x ∈ J := hτmaps hxJ
      have hτxD : τ x ∈ D.domain := interior_subset (hCint (hJC hτx))
      have hτxeq : ⇑D (τ x) = ⇑D x := hτD x hxJ
      rcases hfibz (⇑D x) hxz (τ x) hτxD hτxeq with hin | hin
      · exact (hsheetA _ hxz).mp ⟨τ x, hin, hτxeq⟩
      · exact absurd (hDinjB hin hxB hτxeq) (hτne x hxJ)
  obtain ⟨Pa, σa, hσa, hPaopen, haPa, hPasub, hPasign⟩ :=
    exists_collar_half_sign hCpoly hρpl hρ0 ha (hCnhds a ha) isOpen_interior
      (mem_interior_iff_mem_nhds.mpr hOaN) (hcompA.fst.prodMk hcompA.snd.fst) hGinjA hGzeroA
  obtain ⟨Pb, σb, hσb, hPbopen, hbPb, hPbsub, hPbsign⟩ :=
    exists_collar_half_sign hCpoly hρpl hρ0 hτaJ (hCnhds (τ a) hτaJ) isOpen_interior
      (mem_interior_iff_mem_nhds.mpr hObN) (hcompB.fst.prodMk hcompB.snd.snd) hGinjB hGzeroB
  have hPaA : Pa ⊆ A := fun x hx => hOaA (hPasub hx).2
  have hPbB : Pb ⊆ Bs := fun x hx => hObB (hPbsub hx).2
  obtain ⟨L', hL'eq⟩ : ∃ L' : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] ℝ × ℝ × ℝ,
      ∀ w, L' w = ((L w).1, σa * (L w).2.1, σb * (L w).2.2) :=
    ⟨L.trans (signScale σa σb hσa hσb), fun w => by
      rw [LinearEquiv.trans_apply, signScale_apply]⟩
  have hL'21 : ∀ w, (L' w).2.1 = σa * (L w).2.1 := fun w => by rw [hL'eq]
  have hL'22 : ∀ w, (L' w).2.2 = σb * (L w).2.2 := fun w => by rw [hL'eq]
  have hφ' : IsPLHomeomorphOn ((fun w => L' w) ∘ hmap) U ((fun w => L' w) '' V) :=
    hh.trans (isPLHomeomorphOn_linearEquiv L' hV)
  have hL'V : IsOpen ((fun w => L' w) '' V) :=
    L'.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
  have himgopen : IsOpen (((fun w => L' w) ∘ hmap) '' O₁) :=
    hφ'.isOpen_image_of_isOpen hL'V hO₁open hO₁U
  let g := (hφ'.restrict_isOpen hO₁open hO₁U himgopen).toOpenPartialHomeomorph
    hO₁open himgopen
  have hg : IsPLHomeomorphOn g g.source g.target :=
    hφ'.restrict_isOpen hO₁open hO₁U himgopen
  let e := e₀.trans g
  have hesrc : e.source = e₀.source ∩ ⇑e₀ ⁻¹' O₁ := OpenPartialHomeomorph.trans_source e₀ g
  have heapp : ∀ z, e z = L' (hmap (⇑e₀ z)) := fun _ => rfl
  have hyE : ⇑D a ∈ e.source := by
    rw [hesrc]
    exact hyOz
  have hzeroE : e (⇑D a) = 0 := by
    rw [heapp, hhy, map_zero]
  have hsheetA' : ∀ z ∈ e.source, (z ∈ ⇑D '' A ↔ (e z).2.2 = 0) := by
    intro z hz
    rw [hesrc] at hz
    rw [heapp, hL'22, mul_eq_zero]
    simp only [hσb, false_or]
    exact hsheetA z hz
  have hsheetB' : ∀ z ∈ e.source, (z ∈ ⇑D '' Bs ↔ (e z).2.1 = 0) := by
    intro z hz
    rw [hesrc] at hz
    rw [heapp, hL'21, mul_eq_zero]
    simp only [hσa, false_or]
    exact hsheetB z hz
  have hpair : ∀ z : M, ((e z).2 = 0 ↔ ((e z).2.1 = 0 ∧ (e z).2.2 = 0)) := by
    intro z
    constructor
    · intro hz
      exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
    · rintro ⟨h1, h2⟩
      have hh2 : ((e z).2.1, (e z).2.2) = ((0 : ℝ), (0 : ℝ)) := by rw [h1, h2]
      exact hh2
  obtain ⟨O₂, hO₂open, hO₂mem, hO₂sub⟩ := exists_isOpen_image_inter_subset_image
    hplA.bijOn.injOn hplA.isPiecewiseAffineOn_invFunOn.continuousOn haA
    (hPaopen.mem_nhds haPa)
  obtain ⟨O₃, hO₃open, hO₃mem, hO₃sub⟩ := exists_isOpen_image_inter_subset_image
    hplB.bijOn.injOn hplB.isPiecewiseAffineOn_invFunOn.continuousOn hbB
    (hPbopen.mem_nhds hbPb)
  have hO₃mem' : ⇑e₀ (⇑D a) ∈ O₃ := by
    have h := hO₃mem
    rw [Function.comp_apply, hDτ] at h
    exact h
  have hNopen : IsOpen (e.source ∩ (e₀.source ∩ ⇑e₀ ⁻¹' (O₂ ∩ O₃))) :=
    e.open_source.inter
      (e₀.continuousOn.isOpen_inter_preimage e₀.open_source (hO₂open.inter hO₃open))
  have hNmem : ⇑D a ∈ e.source ∩ (e₀.source ∩ ⇑e₀ ⁻¹' (O₂ ∩ O₃)) :=
    ⟨hyE, hye, hO₂mem, hO₃mem'⟩
  have hshrinkA : ∀ z ∈ e.source ∩ (e₀.source ∩ ⇑e₀ ⁻¹' (O₂ ∩ O₃)),
      z ∈ ⇑D '' A → z ∈ ⇑D '' Pa := by
    rintro z hz ⟨x, hxA, rfl⟩
    obtain ⟨x', hx'Pa, hx'eq⟩ := hO₂sub ⟨⟨x, hxA, rfl⟩, hz.2.2.1⟩
    exact ⟨x', hx'Pa, e₀.injOn (hAP (hPaA hx'Pa)).2 (hAP hxA).2 hx'eq⟩
  have hshrinkB : ∀ z ∈ e.source ∩ (e₀.source ∩ ⇑e₀ ⁻¹' (O₂ ∩ O₃)),
      z ∈ ⇑D '' Bs → z ∈ ⇑D '' Pb := by
    rintro z hz ⟨x, hxB, rfl⟩
    obtain ⟨x', hx'Pb, hx'eq⟩ := hO₃sub ⟨⟨x, hxB, rfl⟩, hz.2.2.2⟩
    exact ⟨x', hx'Pb, e₀.injOn (hBP (hPbB hx'Pb)).2 (hBP hxB).2 hx'eq⟩
  have hevA : ∀ᶠ z in 𝓝 (⇑D a), z ∈ ⇑D '' Pa ↔ (e z).2.2 = 0 := by
    filter_upwards [hNopen.mem_nhds hNmem] with z hz
    rw [← hsheetA' z hz.1]
    exact ⟨fun hzz => image_mono hPaA hzz, hshrinkA z hz⟩
  have hevB : ∀ᶠ z in 𝓝 (⇑D a), z ∈ ⇑D '' Pb ↔ (e z).2.1 = 0 := by
    filter_upwards [hNopen.mem_nhds hNmem] with z hz
    rw [← hsheetB' z hz.1]
    exact ⟨fun hzz => image_mono hPbB hzz, hshrinkB z hz⟩
  have hevC : ∀ᶠ z in 𝓝 (⇑D a), z ∈ hD.singularSet.branchCarrier c ↔ (e z).2 = 0 := by
    filter_upwards [hNopen.mem_nhds hNmem] with z hz
    rw [hpair z, ← hsheetB' z hz.1, ← hsheetA' z hz.1]
    have hzsrc : z ∈ e₀.source ∩ ⇑e₀ ⁻¹' O₁ := by
      rw [← hesrc]
      exact hz.1
    constructor
    · intro hzc
      obtain ⟨x, hxdom, x', hx'dom, hne, hxz, hx'z⟩ :=
        hD.singularSet.branchCarrier_subset_doublePointSet c hzc
      rcases hfibz z hzsrc x hxdom hxz with h1 | h1
      · rcases hfibz z hzsrc x' hx'dom hx'z with h2 | h2
        · exact absurd (hDinjA h1 h2 (hxz.trans hx'z.symm)) hne
        · exact ⟨⟨x', h2, hx'z⟩, ⟨x, h1, hxz⟩⟩
      · rcases hfibz z hzsrc x' hx'dom hx'z with h2 | h2
        · exact ⟨⟨x, h1, hxz⟩, ⟨x', h2, hx'z⟩⟩
        · exact absurd (hDinjB h1 h2 (hxz.trans hx'z.symm)) hne
    · rintro ⟨hzB, hzA⟩
      obtain ⟨x, hxPa, hxz⟩ := hshrinkA z hz hzA
      obtain ⟨x', hx'Pb, hx'z⟩ := hshrinkB z hz hzB
      have hne : x ≠ x' := fun hxx =>
        Set.disjoint_left.mp (hdisj.mono hPaA hPbB) hxPa (hxx ▸ hx'Pb)
      have hxdom : x ∈ D.domain := (hAP (hPaA hxPa)).1
      have hx'dom : x' ∈ D.domain := (hBP (hPbB hx'Pb)).1
      have hdp : x ∈ doublePointPreimage (⇑D) D.domain :=
        ⟨hxdom, x, hxdom, x', hx'dom, hne, rfl, hx'z.trans hxz.symm⟩
      have hxJ : x ∈ J := hdpp.subset ⟨hdp, (hPasub hxPa).1⟩
      have hxpre : x ∈ hD.branchPreimage c := by
        rw [hpre]
        exact hxJ
      rw [← hxz]
      exact hxpre.2
  refine ⟨e, ?_, g, hg, rfl⟩
  refine ⟨ha, hyE, hzeroE, Pa, Pb, haPa, hbPb, hdisj.mono hPaA hPbB,
    fun x hx => (hAP (hPaA hx)).1, fun x hx => (hBP (hPbB hx)).1,
    hPaopen.mem_nhds haPa, hPbopen.mem_nhds hbPb, hDinjA.mono hPaA, hDinjB.mono hPbB,
    fun x hx => ?_, fun x hx => ?_, hevA, hevB, hevC, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hesrc]
    exact hOaZ x (hPasub hx).2
  · rw [hesrc]
    exact hObZ x (hPbsub hx).2
  · rw [heapp, hL'21]
    exact hPasign x hx
  · rw [heapp, hL'22]
    exact hPbsign x hx

theorem exists_markedCrossingChartAt_with_pl_transition (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), hD.IsMarkedCrossingChartAt c J τ ρ a e ∧
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M,
        ∃ g : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ),
          IsPLHomeomorphOn g g.source g.target ∧ e = e₀.trans g := by
  classical
  obtain ⟨hpre, -, hCint, hJC, -, -, -, -, -, -, -, -, -⟩ := id hρ
  obtain ⟨-, -, -, hτmaps, -, hτne, -, hτD, -⟩ := id hτ
  have haD : a ∈ D.domain := interior_subset (hCint (hJC ha))
  have hτaD : τ a ∈ D.domain := interior_subset (hCint (hJC (hτmaps ha)))
  have hapre : a ∈ hD.branchPreimage c := by
    rw [hpre]
    exact ha
  have hyBd : ⇑D a ∉ BdM := Set.disjoint_left.mp
    (hD.singularSet.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch hc) hapre.2
  have hyDouble : ⇑D a ∈ doublePointSet (⇑D) D.domain :=
    hD.singularSet.branchCarrier_subset_doublePointSet c hapre.2
  obtain ⟨e₀, he₀, hye, hcross⟩ :=
    hD.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary hyDouble hyBd
  suffices ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ),
      hD.IsMarkedCrossingChartAt c J τ ρ a e ∧
        ∃ g : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ),
          IsPLHomeomorphOn g g.source g.target ∧ e = e₀.trans g by
    obtain ⟨e, he, g, hg, heq⟩ := this
    exact ⟨e, he, e₀, he₀, g, hg, heq⟩
  obtain ⟨p, q, A, Bs, hpA, hqB, hfp, hfq, hAP, hBP, hdisj, hAn, hBn, hplA, hplB, hcr,
    hfibn⟩ := hcross
  have hfib : D.domain ∩ ⇑D ⁻¹' {⇑D a} = {a, τ a} := by
    refine ((Set.toFinite ({a, τ a} : Set (EuclideanSpace ℝ (Fin 2)))).eq_of_subset_of_encard_le
      ?_ ?_).symm
    · rintro x (rfl | rfl)
      · exact ⟨haD, rfl⟩
      · exact ⟨hτaD, hτD a ha⟩
    · rw [Set.encard_pair (Ne.symm (hτne a ha))]
      exact hD.fiber_le_two _
  have hDp : ⇑D p = ⇑D a := e₀.injOn (hAP hpA).2 hye hfp
  have hDq : ⇑D q = ⇑D a := e₀.injOn (hBP hqB).2 hye hfq
  have hpmem : p ∈ ({a, τ a} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [← hfib]
    exact ⟨(hAP hpA).1, hDp⟩
  have hqmem : q ∈ ({a, τ a} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [← hfib]
    exact ⟨(hBP hqB).1, hDq⟩
  have hpq : p ≠ q := fun hh => Set.disjoint_left.mp hdisj hpA (hh ▸ hqB)
  rcases hpmem with hp | hp
  · subst hp
    rcases hqmem with hq | hq
    · exact absurd hq.symm hpq
    · subst hq
      exact hD.exists_marked_chart_pl_of_sheets hτ hρ ha hye hpA hqB hAP hBP hdisj
        hAn hBn hplA hplB hcr hfibn
  · subst hp
    rcases hqmem with hq | hq
    · subst hq
      refine hD.exists_marked_chart_pl_of_sheets hτ hρ ha hye hqB hpA hBP hAP
        hdisj.symm hBn hAn hplB hplA (hasPLTwoSidedCrossingAt_comm hcr) ?_
      filter_upwards [hfibn] with z hz
      rw [Set.union_comm]
      exact hz
    · exact absurd hq.symm hpq

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
