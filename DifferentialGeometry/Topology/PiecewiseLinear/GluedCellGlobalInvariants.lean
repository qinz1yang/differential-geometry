/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def UniformInjectivityScale {α : Type*} [PseudoMetricSpace α] {β : Type*} (S : Set α)
    (f : α → β) (η : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y < η → f x = f y → x = y

open Classical in
def StarInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    (T : Geometry.SimplicialComplex ℝ E) (g : E → β) : Prop :=
  ∀ v ∈ T.vertices, InjOn g (starComplex T v).space

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open Classical in
theorem exists_globalInvariants_of_gluedCell (D D' : SingularTwoCell M)
    {BdM B C V : Set M} {ε δ κ : ℝ}
    {T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) (hκ : 0 < κ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hclose : ∀ x ∈ D.domain, dist (D' x) (D x) < δ) (hstar : StarInj T (⇑D'))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVopen : IsOpen V) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V)
    (hbdbuf : ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    MapsTo (⇑D') D'.domain C ∧ (∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}) ∧
      (∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U) ∧
      (∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2) ∧
      D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) M,
        (∀ x : frontier D.domain, H (0, x) = D x) ∧
        (∀ x : frontier D.domain, H (1, x) = D' x) ∧
        ∀ (t : unitInterval) (x : frontier D.domain),
          H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
  let _ := hVopen
  let _ := hRman
  let _ := hRdom
  let _ := hsub
  have hcert_eval := hcert (⇑D') hclose hstar
  have hinj : UniformInjectivityScale D.domain (⇑D') κ := hcert_eval.1
  have hfiber : ∀ y, (D.domain ∩ (⇑D') ⁻¹' {y}).encard ≤ 2 := hcert_eval.2
  have hclosed_dom : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isClosed
  have hfr_sub : frontier D.domain ⊆ D.domain :=
    frontier_subset_closure.trans (closure_subset_iff_isClosed.mpr hclosed_dom)
  have hC1 : MapsTo (⇑D') D'.domain C := by
    rw [hdom']
    intro x hx
    by_cases hxR : x ∈ Rc.space
    · rw [hglue hxR]
      let z := simplicialMap Rs φ x
      have hz : dist z (ec (D x)) < ε := hsmall x hxR
      have hzV : z ∈ ec '' V := hchartbuf x hxR z hz
      obtain ⟨y, hyV, hyz⟩ := hzV
      have hysrc : y ∈ ec.source := hVec hyV
      have hy_eq : ec.symm z = y := by rw [← hyz, ec.left_inv hysrc]
      dsimp only
      rw [hy_eq]
      have h0 : 0 ≤ ℓ (ec y) := by
        rw [hyz]
        exact hpnonneg x hxR
      exact (hCchart y hysrc).2 h0
    · rw [hglueoff hxR]
      exact hmapC hx
  have hC2 : ∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z} := by
    intro z hz
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    by_cases hxR : x ∈ Rc.space
    · rw [hglue hxR]
      let w := simplicialMap Rs φ x
      have hw : dist w (ec (D x)) < ε := hsmall x hxR
      have hwV : w ∈ ec '' V := hchartbuf x hxR w hw
      obtain ⟨y, hyV, hyw⟩ := hwV
      have hysrc : y ∈ ec.source := hVec hyV
      have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
      dsimp only
      rw [hy_eq]
      have hne1 : y ≠ z := fun h => hz (h ▸ hyV)
      have hne2 : D x ≠ z := fun h => hz (h ▸ hRV hxR)
      simp [hne1, hne2]
    · rw [hglueoff hxR]
  have hC3 : ∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U := by
    intro x hx
    rw [hdom'] at hx ⊢
    refine ⟨D.domain ∩ Metric.ball x (κ / 2), ?_, ?_⟩
    · exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x (half_pos hκ))
    · intro a ha b hb hab
      have hax : dist a x < κ / 2 := Metric.mem_ball.mp ha.2
      have hbx : dist b x < κ / 2 := Metric.mem_ball.mp hb.2
      have hdist : dist a b < κ := by
        have h1 := dist_triangle a x b
        rw [dist_comm x b] at h1
        linarith
      exact hinj a ha.1 b hb.1 hdist hab
  have hC4 : ∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2 := by
    rw [hdom']
    exact hfiber
  have hC5 : D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain := by
    rw [hdom']
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hxdom, hxBd⟩
      by_cases hxR : x ∈ Rc.space
      · rw [hglue hxR] at hxBd
        let w := simplicialMap Rs φ x
        have hw : dist w (ec (D x)) < ε := hsmall x hxR
        have hwV : w ∈ ec '' V := hchartbuf x hxR w hw
        obtain ⟨y, hyV, hyw⟩ := hwV
        have hysrc : y ∈ ec.source := hVec hyV
        have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
        dsimp only at hxBd
        rw [hy_eq] at hxBd
        have hℓy : ℓ (ec y) = 0 := (hBdchart y hysrc).1 hxBd
        rw [hyw] at hℓy
        have hxL : x ∈ Lc.space := (hpzero x hxR).1 hℓy
        rw [hLspace] at hxL
        exact hxL.2
      · rw [hglueoff hxR] at hxBd
        have : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := ⟨hxdom, hxBd⟩
        rwa [hproper] at this
    · intro hxfr
      have hxdom : x ∈ D.domain := hfr_sub hxfr
      refine ⟨hxdom, ?_⟩
      by_cases hxR : x ∈ Rc.space
      · rw [hglue hxR]
        let w := simplicialMap Rs φ x
        have hw : dist w (ec (D x)) < ε := hsmall x hxR
        have hwV : w ∈ ec '' V := hchartbuf x hxR w hw
        obtain ⟨y, hyV, hyw⟩ := hwV
        have hysrc : y ∈ ec.source := hVec hyV
        have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
        dsimp only
        rw [hy_eq]
        apply (hBdchart y hysrc).2
        rw [hyw]
        have hxL : x ∈ Lc.space := by
          rw [hLspace]
          exact ⟨hxR, hxfr⟩
        exact (hpzero x hxR).2 hxL
      · rw [hglueoff hxR]
        have : x ∈ D.domain ∩ ⇑D ⁻¹' BdM := by rwa [hproper]
        exact this.2
  refine ⟨hC1, hC2, hC3, hC4, hC5, ?_⟩
  have _ : Finite Rc.faces := hRfin.to_subtype
  have hRc_poly : IsPolyhedron Rc.space := isPolyhedron_space Rc
  have hRc_closed : IsClosed Rc.space := hRc_poly.isClosed
  have hD_cont : Continuous (fun p : unitInterval × frontier D.domain => D p.2.1) :=
    D.boundary.continuous.comp continuous_snd
  have hD'fr_cont : Continuous (fun x : frontier D.domain => D' x.1) :=
    continuousOn_iff_continuous_domRestrict.mp
      (D'.continuousOn.mono (hdom'.symm ▸ hfr_sub))
  have hD'_cont : Continuous (fun p : unitInterval × frontier D.domain => D' p.2.1) :=
    hD'fr_cont.comp continuous_snd
  have hD'ec : ∀ x ∈ Rc.space, ec (D' x) = simplicialMap Rs φ x := by
    intro x hxR
    let w := simplicialMap Rs φ x
    have hw : dist w (ec (D x)) < ε := hsmall x hxR
    have hwV : w ∈ ec '' V := hchartbuf x hxR w hw
    obtain ⟨y, hyV, hyw⟩ := hwV
    have hysrc : y ∈ ec.source := hVec hyV
    have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
    have hg := hglue hxR
    dsimp only at hg
    calc ec (D' x) = ec (ec.symm w) := by rw [hg]
      _ = ec y := by rw [hy_eq]
      _ = w := hyw
  let Z : unitInterval × frontier D.domain → EuclideanSpace ℝ (Fin 3) := fun ⟨t, x⟩ =>
    (1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • ec (D' x.1)
  let Hfun : unitInterval × frontier D.domain → M := fun ⟨t, x⟩ =>
    if x.1 ∈ Rc.space then
      ec.symm (Z ⟨t, x⟩)
    else
      D x.1
  have hπ_cont : Continuous (fun p : unitInterval × frontier D.domain => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hU_open : IsOpen {p : unitInterval × frontier D.domain | p.2.1 ∈ Ω} :=
    hΩ.preimage hπ_cont
  have hV_open : IsOpen {p : unitInterval × frontier D.domain | p.2.1 ∈ Rc.spaceᶜ ∪ Nb} :=
    (hRc_closed.isOpen_compl.union hNb).preimage hπ_cont
  have hUV : {p : unitInterval × frontier D.domain | p.2.1 ∈ Ω} ∪
      {p : unitInterval × frontier D.domain | p.2.1 ∈ Rc.spaceᶜ ∪ Nb} = univ := by
    ext ⟨t, x⟩
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, mem_univ, iff_true]
    by_cases hxΩ : x.1 ∈ Ω
    · exact Or.inl hxΩ
    · right
      by_cases hxR : x.1 ∈ Rc.space
      · right
        exact hNbfr ⟨hxR, hxΩ⟩
      · left
        exact hxR
  have hcontV :
      ContinuousOn Hfun {p : unitInterval × frontier D.domain | p.2.1 ∈ Rc.spaceᶜ ∪ Nb} := by
    refine hD_cont.continuousOn.congr fun ⟨t, x⟩ hp => ?_
    dsimp [Hfun]
    by_cases hxR : x.1 ∈ Rc.space
    · have hxNb : x.1 ∈ Nb := by
        rcases hp with h1 | h2
        · exact absurd hxR h1
        · exact h2
      have hxA : x.1 ∈ Ac.space := hNbA ⟨hxR, hxNb⟩
      have hfroz : simplicialMap Rs φ x.1 = ec (D x.1) := hfrozen hxA
      have hxV : D x.1 ∈ V := hRV hxR
      have hxsrc : D x.1 ∈ ec.source := hVec hxV
      have hxD' : D' x.1 = D x.1 := by
        have := hglue hxR
        dsimp only at this
        rw [hfroz] at this
        rw [this, ec.left_inv hxsrc]
      rw [ite_eq_left hxR]
      dsimp [Z]
      rw [hxD']
      have hcomb : (1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • ec (D x.1) = ec (D x.1) := by
        rw [← add_smul]
        have : 1 - (t : ℝ) + (t : ℝ) = 1 := sub_add_cancel 1 (t : ℝ)
        rw [this, one_smul]
      rw [hcomb, ec.left_inv hxsrc]
    · rw [ite_eq_right hxR]
  have hU_sub : ∀ p : unitInterval × frontier D.domain, p.2.1 ∈ Ω → p.2.1 ∈ Rc.space :=
    fun p hp => hΩR ⟨hfr_sub p.2.2, hp⟩
  have hU_mapsD : MapsTo (fun p : unitInterval × frontier D.domain => D p.2.1)
      {p | p.2.1 ∈ Ω} ec.source :=
    fun p hp => hVec (hRV (hU_sub p hp))
  have hU_mapsD' : MapsTo (fun p : unitInterval × frontier D.domain => D' p.2.1)
      {p | p.2.1 ∈ Ω} ec.source := by
    intro p hp
    have hxR := hU_sub p hp
    have hg := hglue hxR
    dsimp only at hg
    let w := simplicialMap Rs φ p.2.1
    have hw : dist w (ec (D p.2.1)) < ε := hsmall p.2.1 hxR
    have hwV : w ∈ ec '' V := hchartbuf p.2.1 hxR w hw
    obtain ⟨y, hyV, hyw⟩ := hwV
    have hysrc : y ∈ ec.source := hVec hyV
    have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
    dsimp only
    rw [hg, hy_eq]
    exact hysrc
  have hD_ec_cont : ContinuousOn (fun p : unitInterval × frontier D.domain => ec (D p.2.1))
      {p | p.2.1 ∈ Ω} :=
    ec.continuousOn.comp hD_cont.continuousOn hU_mapsD
  have hD'_ec_cont : ContinuousOn (fun p : unitInterval × frontier D.domain => ec (D' p.2.1))
      {p | p.2.1 ∈ Ω} :=
    ec.continuousOn.comp hD'_cont.continuousOn hU_mapsD'
  have ht1_cont : Continuous (fun p : unitInterval × frontier D.domain => 1 - (p.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have ht2_cont : Continuous (fun p : unitInterval × frontier D.domain => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hZ1_cont : ContinuousOn (fun p : unitInterval × frontier D.domain =>
      (1 - (p.1 : ℝ)) • ec (D p.2.1)) {p | p.2.1 ∈ Ω} :=
    ht1_cont.continuousOn.smul hD_ec_cont
  have hZ2_cont : ContinuousOn (fun p : unitInterval × frontier D.domain =>
      (p.1 : ℝ) • ec (D' p.2.1)) {p | p.2.1 ∈ Ω} :=
    ht2_cont.continuousOn.smul hD'_ec_cont
  have hZ_cont : ContinuousOn Z {p | p.2.1 ∈ Ω} := hZ1_cont.add hZ2_cont
  have hZ_target : MapsTo Z {p | p.2.1 ∈ Ω} ec.target := by
    intro ⟨t, x⟩ hp
    have hxR : x.1 ∈ Rc.space := hU_sub ⟨t, x⟩ hp
    dsimp [Z]
    rw [hD'ec x.1 hxR]
    let w := simplicialMap Rs φ x.1
    have hw : dist w (ec (D x.1)) < ε := hsmall x.1 hxR
    have hε_pos : 0 < ε := dist_nonneg.trans_lt hw
    have hm1 : ec (D x.1) ∈ Metric.ball (ec (D x.1)) ε := Metric.mem_ball_self hε_pos
    have hm2 : w ∈ Metric.ball (ec (D x.1)) ε :=
      Metric.mem_ball.mpr (dist_comm w (ec (D x.1)) ▸ hw)
    have ha : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
    have hb : 0 ≤ (t : ℝ) := t.2.1
    have hab : 1 - (t : ℝ) + (t : ℝ) = 1 := sub_add_cancel 1 (t : ℝ)
    have hmem_ball := convex_ball (ec (D x.1)) ε hm1 hm2 ha hb hab
    have hdist : dist ((1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • w) (ec (D x.1)) < ε := by
      exact Metric.mem_ball.mp hmem_ball
    have hzV := hchartbuf x.1 hxR _ hdist
    obtain ⟨y, hyV, hyz⟩ := hzV
    have hysrc : y ∈ ec.source := hVec hyV
    rw [← hyz]
    exact ec.map_source hysrc
  have hcontU : ContinuousOn Hfun {p : unitInterval × frontier D.domain | p.2.1 ∈ Ω} := by
    have h_eq : EqOn Hfun (fun p => ec.symm (Z p)) {p | p.2.1 ∈ Ω} := by
      intro ⟨t, x⟩ hp
      have hxR : x.1 ∈ Rc.space := hU_sub ⟨t, x⟩ hp
      dsimp [Hfun]
      rw [ite_eq_left hxR]
    refine (ec.continuousOn_symm.comp hZ_cont hZ_target).congr (fun p hp => h_eq hp)
  have hcont_univ : ContinuousOn Hfun univ := by
    rw [← hUV]
    exact hcontU.union_of_isOpen hcontV hU_open hV_open
  have hHcont : Continuous Hfun := continuousOn_univ.mp hcont_univ
  let H : ContinuousMap (unitInterval × frontier D.domain) M := ⟨Hfun, hHcont⟩
  have hH0 : ∀ x : frontier D.domain, H (0, x) = D x := by
    intro x
    change Hfun (0, x) = D x
    dsimp [Hfun]
    by_cases hxR : x.1 ∈ Rc.space
    · rw [ite_eq_left hxR]
      dsimp [Z]
      have hcomb : (1 - (0 : ℝ)) • ec (D x.1) + (0 : ℝ) • ec (D' x.1) = ec (D x.1) := by
        rw [sub_zero, one_smul, zero_smul, add_zero]
      rw [hcomb]
      have hxV : D x.1 ∈ V := hRV hxR
      have hxsrc : D x.1 ∈ ec.source := hVec hxV
      exact ec.left_inv hxsrc
    · rw [ite_eq_right hxR]
  have hH1 : ∀ x : frontier D.domain, H (1, x) = D' x := by
    intro x
    change Hfun (1, x) = D' x
    dsimp [Hfun]
    by_cases hxR : x.1 ∈ Rc.space
    · rw [ite_eq_left hxR]
      dsimp [Z]
      have hcomb : (1 - (1 : ℝ)) • ec (D x.1) + (1 : ℝ) • ec (D' x.1) = ec (D' x.1) := by
        rw [sub_self, zero_smul, zero_add, one_smul]
      rw [hcomb]
      have hg := hglue hxR
      dsimp only at hg
      let w := simplicialMap Rs φ x.1
      have hw : dist w (ec (D x.1)) < ε := hsmall x.1 hxR
      have hwV : w ∈ ec '' V := hchartbuf x.1 hxR w hw
      obtain ⟨y, hyV, hyw⟩ := hwV
      have hysrc : y ∈ ec.source := hVec hyV
      have hy_eq : ec.symm w = y := by rw [← hyw, ec.left_inv hysrc]
      rw [hg, hy_eq]
      exact ec.left_inv hysrc
    · rw [ite_eq_right hxR]
      exact (hglueoff hxR).symm
  have hHbd : ∀ (t : unitInterval) (x : frontier D.domain),
      H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
    intro t x
    change Hfun (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (Hfun (t, x))
    dsimp [Hfun]
    by_cases hxR : x.1 ∈ Rc.space
    · rw [ite_eq_left hxR]
      dsimp [Z]
      rw [hD'ec x.1 hxR]
      let w := simplicialMap Rs φ x.1
      have hw : dist w (ec (D x.1)) < ε := hsmall x.1 hxR
      have hε_pos : 0 < ε := dist_nonneg.trans_lt hw
      have hm1 : ec (D x.1) ∈ Metric.ball (ec (D x.1)) ε := Metric.mem_ball_self hε_pos
      have hm2 : w ∈ Metric.ball (ec (D x.1)) ε :=
        Metric.mem_ball.mpr (dist_comm w (ec (D x.1)) ▸ hw)
      have ha : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
      have hb : 0 ≤ (t : ℝ) := t.2.1
      have hab : 1 - (t : ℝ) + (t : ℝ) = 1 := sub_add_cancel 1 (t : ℝ)
      have hmem_ball := convex_ball (ec (D x.1)) ε hm1 hm2 ha hb hab
      have hdist : dist ((1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • w) (ec (D x.1)) < ε := by
        exact Metric.mem_ball.mp hmem_ball
      have hzV := hchartbuf x.1 hxR _ hdist
      obtain ⟨y, hyV, hyz⟩ := hzV
      have hysrc : y ∈ ec.source := hVec hyV
      have hy_eq : ec.symm ((1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • w) = y := by
        rw [← hyz, ec.left_inv hysrc]
      have hxdom : x.1 ∈ D.domain := hfr_sub x.2
      have hxfr : x.1 ∈ frontier D.domain := x.2
      have hxL : x.1 ∈ Lc.space := by rw [hLspace]; exact ⟨hxR, hxfr⟩
      have hℓw : ℓ w = 0 := (hpzero x.1 hxR).2 hxL
      have hDxBd : D x.1 ∈ BdM := by
        have : x.1 ∈ D.domain ∩ ⇑D ⁻¹' BdM := by rwa [hproper]
        exact this.2
      have hxV : D x.1 ∈ V := hRV hxR
      have hDxsrc : D x.1 ∈ ec.source := hVec hxV
      have hℓDx : ℓ (ec (D x.1)) = 0 := (hBdchart (D x.1) hDxsrc).1 hDxBd
      have hℓcomb : ℓ ((1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • w) = 0 := by
        rw [map_add, map_smul, map_smul, hℓDx, hℓw, smul_zero, smul_zero, add_zero]
      have hℓy : ℓ (ec y) = 0 := by rw [hyz, hℓcomb]
      have hyBd : y ∈ BdM := (hBdchart y hysrc).2 hℓy
      have hyBd' : ec.symm ((1 - (t : ℝ)) • ec (D x.1) + (t : ℝ) • w) ∈ BdM := by
        rw [hy_eq]
        exact hyBd
      refine ⟨hyBd', ?_⟩
      exact hbdbuf x.1 ⟨hxR, hxfr⟩ _ hdist hyBd'
    · rw [ite_eq_right hxR]
      have hxdom : x.1 ∈ D.domain := hfr_sub x.2
      have hxfr : x.1 ∈ frontier D.domain := x.2
      have hDxBd : D x.1 ∈ BdM := by
        have : x.1 ∈ D.domain ∩ ⇑D ⁻¹' BdM := by rwa [hproper]
        exact this.2
      refine ⟨hDxBd, ?_⟩
      have hrange : D x.1 ∈ Set.range D.boundary := ⟨x, rfl⟩
      exact hbuffer (D x.1) hrange
  exact ⟨H, hH0, hH1, hHbd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
