import DifferentialGeometry.Analysis.ODE.Flow.Interval
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import DifferentialGeometry.Topology.Manifold.ExtChartAt

set_option autoImplicit false

noncomputable section

open Asymptotics Bundle Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

local instance endomorphismTopology :
    TopologicalSpace (TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) F V F V

local instance endomorphismFiberBundle :
    FiberBundle (F →L[ℝ] F) (fun x => V x →L[ℝ] V x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) F V F V

local instance endomorphismVectorBundle :
    VectorBundle ℝ (F →L[ℝ] F) (fun x => V x →L[ℝ] V x) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) F V F V

private theorem continuousLinearMap_comp_hasDerivAt
    {G K : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [ContinuousSMul ℝ G]
    [AddCommGroup K] [Module ℝ K] [TopologicalSpace K]
    [ContinuousSMul ℝ K]
    (L : G →L[ℝ] K) {f : ℝ → G} {f' : G} {x : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => L (f t)) (L f') x := by
  change HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') x at h
  change HasFDerivAt (fun t => L (f t))
    (ContinuousLinearMap.toSpanSingleton ℝ (L f')) x
  rw [hasFDerivAt_iff_isLittleOTVS] at h ⊢
  simpa only [map_sub, map_smul, ContinuousLinearMap.toSpanSingleton_apply] using
    L.isBigOTVS_fun_comp.trans_isLittleOTVS h

private theorem continuousLinearMap_comp_hasDerivWithinAt
    {G K : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [ContinuousSMul ℝ G]
    [AddCommGroup K] [Module ℝ K] [TopologicalSpace K]
    [ContinuousSMul ℝ K]
    (L : G →L[ℝ] K) {f : ℝ → G} {f' : G} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun t => L (f t)) (L f') s x := by
  change HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ f') s x at h
  change HasFDerivWithinAt (fun t => L (f t))
    (ContinuousLinearMap.toSpanSingleton ℝ (L f')) s x
  rw [hasFDerivWithinAt_iff_isLittleOTVS] at h ⊢
  simpa only [map_sub, map_smul, ContinuousLinearMap.toSpanSingleton_apply] using
    L.isBigOTVS_fun_comp.trans_isLittleOTVS h

theorem fiberwise_linear_ode_solution_contMDiffOn
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (B : ∀ x : M, V x →L[ℝ] V x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M =>
        (⟨x, B x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (hΦ₀ : ∀ x : M, Φ t₀ x = B x)
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)) := by
  intro p₀ hp₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let x₀ := p₀.2
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F →L[ℝ] F) ∞
    (fun p : ℝ × M =>
      ContinuousLinearMap.inCoordinates F V F V x₀ p.2 x₀ p.2 (Φ p.1 p.2))
    (Ioo a b ×ˢ (univ : Set M)) p₀
  let c := extChartAt I x₀
  let e := trivializationAt F V x₀
  let eHom := e.continuousLinearMap (RingHom.id ℝ) e
  let U : Set E := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU_open : IsOpen U := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target_of_boundarylessManifold (I := I) x₀) e.open_baseSet
  have hx₀_source : x₀ ∈ c.source := mem_extChartAt_source x₀
  have hcx₀_target : c x₀ ∈ c.target := c.map_source hx₀_source
  have hx₀_e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  have hcx₀_U : c x₀ ∈ U := by
    refine ⟨hcx₀_target, ?_⟩
    change c.symm (c x₀) ∈ e.baseSet
    rw [c.left_inv hx₀_source]
    exact hx₀_e
  let Acoord : E → ℝ → (F →L[ℝ] F) := fun z t =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (A t (c.symm z))
  have hAcoord : ContDiffOn ℝ ∞ (Function.uncurry Acoord) (U ×ˢ Ioo a b) := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hparam : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : E × ℝ => (p.2, c.symm p.1)) (U ×ˢ Ioo a b) :=
      contMDiffOn_snd.prodMk (hsymm.comp contMDiffOn_fst fun p hp => hp.1)
    have hsection := hA.comp hparam fun p hp => ⟨hp.2, mem_univ _⟩
    have hbase : Set.MapsTo
        (fun p : E × ℝ =>
          (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (U ×ˢ Ioo a b) eHom.source := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : E × ℝ =>
          (eHom
            (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2)
        (U ×ˢ Ioo a b) := fun p hp => (hcoord p hp).snd
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hsnd.congr fun p hp => by
      obtain ⟨z, t⟩ := p
      obtain ⟨hz, ht⟩ := hp
      change (eHom
          (⟨c.symm z, A t (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Acoord z t
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Acoord,
        ContinuousLinearMap.inCoordinates]
  let Bcoord : E → (F →L[ℝ] F) := fun z =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (B (c.symm z))
  have hBcoord : ContDiffOn ℝ ∞ Bcoord U := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hsection : ContMDiffOn 𝓘(ℝ, E) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun z : E =>
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) U := by
      exact (hB.comp_contMDiffOn hsymm).congr fun z hz => rfl
    have hbase : Set.MapsTo
        (fun z : E =>
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        U eHom.source := by
      intro z hz
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun z : E =>
          (eHom
            (⟨c.symm z, B (c.symm z)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2) U :=
      fun z hz => (hcoord z hz).snd
    rw [← contMDiffOn_iff_contDiffOn]
    exact hsnd.congr fun z hz => by
      change (eHom
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Bcoord z
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Bcoord,
        ContinuousLinearMap.inCoordinates]
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  let Z₀ : E → F := fun z => Bcoord z v
  let Z : E → ℝ → F :=
    linearODESolution Acoord a b t₀ Z₀
  have hZ₀ : ContDiffOn ℝ ∞ Z₀ U := hBcoord.clm_apply contDiffOn_const
  have hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Ioo a b) :=
    linearODESolution_contDiffOn_top ht₀ hU_open hAcoord hZ₀
  have hZ_mfld : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (Function.uncurry Z) (U ×ˢ Ioo a b) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hZ
    exact hZ
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ c x₀ :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (by simp)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (c p.2, p.1))
      (Ioo a b ×ˢ (univ : Set M)) p₀ :=
    (hchart.comp p₀ contMDiffAt_snd).contMDiffWithinAt.prodMk contMDiffWithinAt_fst
  have hZ_at : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (Function.uncurry Z) (c x₀, p₀.1) :=
    hZ_mfld.contMDiffAt
      ((hU_open.prod isOpen_Ioo).mem_nhds ⟨hcx₀_U, hp₀.1⟩)
  have hcandidate : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M => Z (c p.2) p.1)
      (Ioo a b ×ˢ (univ : Set M)) p₀ :=
    hZ_at.comp_contMDiffWithinAt p₀ hmove
  apply hcandidate.congr_of_eventuallyEq
  · have hc_source : ∀ᶠ p : ℝ × M in
        𝓝[Ioo a b ×ˢ (univ : Set M)] p₀, p.2 ∈ c.source :=
      continuousWithinAt_snd
        ((isOpen_extChartAt_source (I := I) x₀).mem_nhds hx₀_source)
    have he_base : ∀ᶠ p : ℝ × M in
        𝓝[Ioo a b ×ˢ (univ : Set M)] p₀, p.2 ∈ e.baseSet :=
      continuousWithinAt_snd (e.open_baseSet.mem_nhds hx₀_e)
    filter_upwards [self_mem_nhdsWithin, hc_source, he_base] with p hp hp_c hp_e
    have hcp_U : c p.2 ∈ U := by
      refine ⟨c.map_source hp_c, ?_⟩
      change c.symm (c p.2) ∈ e.baseSet
      rw [c.left_inv hp_c]
      exact hp_e
    let Y : ℝ → F := fun s =>
      ContinuousLinearMap.inCoordinates F V F V x₀ p.2 x₀ p.2 (Φ s p.2) v
    have hAcoord_x : ContinuousOn (Acoord (c p.2)) (Ioo a b) :=
      ContinuousOn.uncurry_left (a := c p.2) (sα := U) (sβ := Ioo a b)
        hcp_U hAcoord.continuousOn
    have hY_deriv : ∀ s ∈ Ioo a b,
        HasDerivAt Y (Acoord (c p.2) s (Y s)) s := by
      intro s hs
      let vin : V p.2 := e.symmL ℝ p.2 v
      have hraw := hΦ p.2 vin s hs
      have hcomp :=
        continuousLinearMap_comp_hasDerivAt (e.continuousLinearMapAt ℝ p.2) hraw
      have hderiv :
          Acoord (c p.2) s (Y s) =
            e.continuousLinearMapAt ℝ p.2 (A s p.2 (Φ s p.2 vin)) := by
        simp only [Acoord, Y, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply]
        rw [c.left_inv hp_c]
        rw [e.symmL_continuousLinearMapAt hp_e]
      have hfun : Y = fun t => e.continuousLinearMapAt ℝ p.2 (Φ t p.2 vin) := by
        rfl
      rw [hderiv, hfun]
      exact hcomp
    have hZ_deriv : ∀ s ∈ Ioo a b,
        HasDerivAt (Z (c p.2)) (Acoord (c p.2) s (Z (c p.2) s)) s := by
      intro s hs
      exact linearODESolution_hasDerivAt ht₀ hAcoord.continuousOn hcp_U hs
    have hinit : Y t₀ = Z (c p.2) t₀ := by
      have hZ_init : Z (c p.2) t₀ = Z₀ (c p.2) :=
        linearODESolution_initial Acoord a b t₀ Z₀ (c p.2)
      rw [hZ_init]
      simp only [Y, hΦ₀, Z₀, Bcoord, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      rw [c.left_inv hp_c]
    have heq := linearODE_unique_on_Ioo ht₀ hAcoord_x hY_deriv hZ_deriv hinit
    exact heq hp.1
  · let Y : ℝ → F := fun s =>
      ContinuousLinearMap.inCoordinates F V F V x₀ x₀ x₀ x₀ (Φ s x₀) v
    have hAcoord_x : ContinuousOn (Acoord (c x₀)) (Ioo a b) :=
      ContinuousOn.uncurry_left (a := c x₀) (sα := U) (sβ := Ioo a b)
        hcx₀_U hAcoord.continuousOn
    have hY_deriv : ∀ s ∈ Ioo a b,
        HasDerivAt Y (Acoord (c x₀) s (Y s)) s := by
      intro s hs
      let vin : V x₀ := e.symmL ℝ x₀ v
      have hraw := hΦ x₀ vin s hs
      have hcomp :=
        continuousLinearMap_comp_hasDerivAt (e.continuousLinearMapAt ℝ x₀) hraw
      have hderiv :
          Acoord (c x₀) s (Y s) =
            e.continuousLinearMapAt ℝ x₀ (A s x₀ (Φ s x₀ vin)) := by
        simp only [Acoord, Y, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply]
        rw [c.left_inv hx₀_source]
        rw [e.symmL_continuousLinearMapAt hx₀_e]
      have hfun : Y = fun t => e.continuousLinearMapAt ℝ x₀ (Φ t x₀ vin) := by
        rfl
      rw [hderiv, hfun]
      exact hcomp
    have hZ_deriv : ∀ s ∈ Ioo a b,
        HasDerivAt (Z (c x₀)) (Acoord (c x₀) s (Z (c x₀) s)) s := by
      intro s hs
      exact linearODESolution_hasDerivAt ht₀ hAcoord.continuousOn hcx₀_U hs
    have hinit : Y t₀ = Z (c x₀) t₀ := by
      have hZ_init : Z (c x₀) t₀ = Z₀ (c x₀) :=
        linearODESolution_initial Acoord a b t₀ Z₀ (c x₀)
      rw [hZ_init]
      simp only [Y, hΦ₀, Z₀, Bcoord, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      rw [c.left_inv hx₀_source]
    have heq := linearODE_unique_on_Ioo ht₀ hAcoord_x hY_deriv hZ_deriv hinit
    exact heq hp₀.1

theorem fiberwise_linear_ode_solution_contMDiff
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (hΦ₀ : ∀ x : M, Φ t₀ x = ContinuousLinearMap.id ℝ (V x))
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t) :
    ∀ t ∈ Ioo a b,
      ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun x : M =>
          (⟨x, Φ t x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) := by
  intro target htarget x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let c := extChartAt I x₀
  let e := trivializationAt F V x₀
  let eHom := e.continuousLinearMap (RingHom.id ℝ) e
  let U : Set E := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU_open : IsOpen U := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target_of_boundarylessManifold (I := I) x₀) e.open_baseSet
  have hx₀_source : x₀ ∈ c.source := mem_extChartAt_source x₀
  have hcx₀_target : c x₀ ∈ c.target := c.map_source hx₀_source
  have hx₀_e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  have hcx₀_U : c x₀ ∈ U := by
    refine ⟨hcx₀_target, ?_⟩
    change c.symm (c x₀) ∈ e.baseSet
    rw [c.left_inv hx₀_source]
    exact hx₀_e
  let Acoord : E → ℝ → (F →L[ℝ] F) := fun z t =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (A t (c.symm z))
  have hAcoord : ContDiffOn ℝ ∞ (Function.uncurry Acoord) (U ×ˢ Ioo a b) := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hparam : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : E × ℝ => (p.2, c.symm p.1)) (U ×ˢ Ioo a b) :=
      contMDiffOn_snd.prodMk (hsymm.comp contMDiffOn_fst fun p hp => hp.1)
    have hsection := hA.comp hparam fun p hp => ⟨hp.2, mem_univ _⟩
    have hbase : Set.MapsTo
        (fun p : E × ℝ =>
          (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (U ×ˢ Ioo a b) eHom.source := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : E × ℝ =>
          (eHom
            (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2)
        (U ×ˢ Ioo a b) := fun p hp => (hcoord p hp).snd
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hsnd.congr fun p hp => by
      obtain ⟨z, t⟩ := p
      obtain ⟨hz, ht⟩ := hp
      change (eHom
          (⟨c.symm z, A t (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Acoord z t
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Acoord,
        ContinuousLinearMap.inCoordinates]
  apply contMDiffAt_clm_of_pointwise
  intro v
  let Z : E → ℝ → F :=
    linearODESolution Acoord a b t₀ (fun _ : E => v)
  have hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Ioo a b) :=
    linearODESolution_contDiffOn_top ht₀ hU_open hAcoord contDiffOn_const
  have hZslice : ContDiffAt ℝ ∞ (fun z : E => Z z target) (c x₀) := by
    have hslice : ContDiffOn ℝ ∞ (fun z : E => Z z target) U := by
      have hpair : ContDiffOn ℝ ∞ (fun z : E => (z, target)) U :=
        contDiffOn_id.prodMk contDiffOn_const
      intro z hz
      have hzt : (z, target) ∈ U ×ˢ Ioo a b := ⟨hz, htarget⟩
      exact (hZ (z, target) hzt).comp z (hpair z hz)
        (fun y hy => show (y, target) ∈ U ×ˢ Ioo a b from ⟨hy, htarget⟩)
    exact hslice.contDiffAt (hU_open.mem_nhds hcx₀_U)
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ c x₀ :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (by simp)
  have hcandidate : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun x : M => Z (c x) target) x₀ :=
    hZslice.contMDiffAt.comp x₀ hchart
  apply hcandidate.congr_of_eventuallyEq
  have hc_source : ∀ᶠ x in 𝓝 x₀, x ∈ c.source :=
    (isOpen_extChartAt_source (I := I) x₀).mem_nhds hx₀_source
  have he_base : ∀ᶠ x in 𝓝 x₀, x ∈ e.baseSet := e.open_baseSet.mem_nhds hx₀_e
  filter_upwards [hc_source, he_base] with x hx_c hx_e
  have hcx_U : c x ∈ U := by
    refine ⟨c.map_source hx_c, ?_⟩
    change c.symm (c x) ∈ e.baseSet
    rw [c.left_inv hx_c]
    exact hx_e
  let Y : ℝ → F := fun s =>
    ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ s x) v
  have hAcoord_x : ContinuousOn (Acoord (c x)) (Ioo a b) :=
    ContinuousOn.uncurry_left (a := c x) (sα := U) (sβ := Ioo a b)
      hcx_U hAcoord.continuousOn
  have hY_deriv : ∀ s ∈ Ioo a b,
      HasDerivAt Y (Acoord (c x) s (Y s)) s := by
    intro s hs
    let vin : V x := e.symmL ℝ x v
    have hraw := hΦ x vin s hs
    have hcomp :=
      continuousLinearMap_comp_hasDerivAt (e.continuousLinearMapAt ℝ x) hraw
    have hderiv :
        Acoord (c x) s (Y s) =
          e.continuousLinearMapAt ℝ x (A s x (Φ s x vin)) := by
      simp only [Acoord, Y, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      rw [c.left_inv hx_c]
      rw [e.symmL_continuousLinearMapAt hx_e]
    have hfun : Y = fun t => e.continuousLinearMapAt ℝ x (Φ t x vin) := by
      rfl
    rw [hderiv, hfun]
    exact hcomp
  have hZ_deriv : ∀ s ∈ Ioo a b,
      HasDerivAt (Z (c x)) (Acoord (c x) s (Z (c x) s)) s := by
    intro s hs
    exact linearODESolution_hasDerivAt ht₀ hAcoord.continuousOn hcx_U hs
  have hinit : Y t₀ = Z (c x) t₀ := by
    have hZ_init : Z (c x) t₀ = v :=
      linearODESolution_initial Acoord a b t₀ (fun _ : E => v) (c x)
    rw [hZ_init]
    simp only [Y, hΦ₀, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact e.continuousLinearMapAt_symmL hx_e v
  have heq := linearODE_unique_on_Ioo ht₀ hAcoord_x hY_deriv hZ_deriv hinit
  exact heq htarget

theorem fiberwise_linear_ode_solution_contMDiff_right
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (hΦ₀ : ∀ x : M, Φ t₀ x = ContinuousLinearMap.id ℝ (V x))
    (hΦ_cont : ∀ x : M, ∀ v : V x,
      ContinuousOn (fun t : ℝ => Φ t x v) (Icc t₀ b))
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ico t₀ b,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Ici t₀) t) :
    ∀ t ∈ Ioo t₀ b,
      ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun x : M =>
          (⟨x, Φ t x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) := by
  intro target htarget x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let c := extChartAt I x₀
  let e := trivializationAt F V x₀
  let eHom := e.continuousLinearMap (RingHom.id ℝ) e
  let U : Set E := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU_open : IsOpen U := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target_of_boundarylessManifold (I := I) x₀) e.open_baseSet
  have hx₀_source : x₀ ∈ c.source := mem_extChartAt_source x₀
  have hcx₀_target : c x₀ ∈ c.target := c.map_source hx₀_source
  have hx₀_e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  have hcx₀_U : c x₀ ∈ U := by
    refine ⟨hcx₀_target, ?_⟩
    change c.symm (c x₀) ∈ e.baseSet
    rw [c.left_inv hx₀_source]
    exact hx₀_e
  let Acoord : E → ℝ → (F →L[ℝ] F) := fun z t =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (A t (c.symm z))
  have hAcoord : ContDiffOn ℝ ∞ (Function.uncurry Acoord) (U ×ˢ Ioo a b) := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hparam : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : E × ℝ => (p.2, c.symm p.1)) (U ×ˢ Ioo a b) :=
      contMDiffOn_snd.prodMk (hsymm.comp contMDiffOn_fst fun p hp => hp.1)
    have hsection := hA.comp hparam fun p hp => ⟨hp.2, mem_univ _⟩
    have hbase : Set.MapsTo
        (fun p : E × ℝ =>
          (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (U ×ˢ Ioo a b) eHom.source := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : E × ℝ =>
          (eHom
            (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2)
        (U ×ˢ Ioo a b) := fun p hp => (hcoord p hp).snd
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hsnd.congr fun p hp => by
      obtain ⟨z, t⟩ := p
      obtain ⟨hz, ht⟩ := hp
      change (eHom
          (⟨c.symm z, A t (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Acoord z t
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Acoord,
        ContinuousLinearMap.inCoordinates]
  apply contMDiffAt_clm_of_pointwise
  intro v
  let Z : E → ℝ → F :=
    linearODESolution Acoord a b t₀ (fun _ : E => v)
  have hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Ioo a b) :=
    linearODESolution_contDiffOn_top ht₀ hU_open hAcoord contDiffOn_const
  have hZslice : ContDiffAt ℝ ∞ (fun z : E => Z z target) (c x₀) := by
    have hslice : ContDiffOn ℝ ∞ (fun z : E => Z z target) U := by
      have hpair : ContDiffOn ℝ ∞ (fun z : E => (z, target)) U :=
        contDiffOn_id.prodMk contDiffOn_const
      intro z hz
      have hzt : (z, target) ∈ U ×ˢ Ioo a b :=
        ⟨hz, lt_trans ht₀.1 htarget.1, htarget.2⟩
      exact (hZ (z, target) hzt).comp z (hpair z hz)
        (fun y hy => show (y, target) ∈ U ×ˢ Ioo a b from
          ⟨hy, lt_trans ht₀.1 htarget.1, htarget.2⟩)
    exact hslice.contDiffAt (hU_open.mem_nhds hcx₀_U)
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ c x₀ :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (by simp)
  have hcandidate : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun x : M => Z (c x) target) x₀ :=
    hZslice.contMDiffAt.comp x₀ hchart
  apply hcandidate.congr_of_eventuallyEq
  have hc_source : ∀ᶠ x in 𝓝 x₀, x ∈ c.source :=
    (isOpen_extChartAt_source (I := I) x₀).mem_nhds hx₀_source
  have he_base : ∀ᶠ x in 𝓝 x₀, x ∈ e.baseSet := e.open_baseSet.mem_nhds hx₀_e
  filter_upwards [hc_source, he_base] with x hx_c hx_e
  have hcx_U : c x ∈ U := by
    refine ⟨c.map_source hx_c, ?_⟩
    change c.symm (c x) ∈ e.baseSet
    rw [c.left_inv hx_c]
    exact hx_e
  let Y : ℝ → F := fun s =>
    ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ s x) v
  let vin : V x := e.symmL ℝ x v
  have hfun : Y = fun t => e.continuousLinearMapAt ℝ x (Φ t x vin) := by
    rfl
  have htime_sub : Icc t₀ target ⊆ Icc t₀ b := fun s hs =>
    ⟨hs.1, le_trans hs.2 (le_of_lt htarget.2)⟩
  have hY_cont : ContinuousOn Y (Icc t₀ target) := by
    rw [hfun]
    exact (e.continuousLinearMapAt ℝ x).continuous.comp_continuousOn
      ((hΦ_cont x vin).mono htime_sub)
  have hAcoord_x : ContinuousOn (Acoord (c x)) (Ioo a b) :=
    ContinuousOn.uncurry_left (a := c x) (sα := U) (sβ := Ioo a b)
      hcx_U hAcoord.continuousOn
  have hY_deriv : ∀ s ∈ Ico t₀ target,
      HasDerivWithinAt Y (Acoord (c x) s (Y s)) (Ici s) s := by
    intro s hs
    have hs_b : s ∈ Ico t₀ b := ⟨hs.1, lt_trans hs.2 htarget.2⟩
    have hraw : HasDerivWithinAt (fun r : ℝ => Φ r x vin)
        (A s x (Φ s x vin)) (Ici s) s :=
      by
        have hraw₀ := hΦ x vin s hs_b
        change HasFDerivWithinAt (fun r : ℝ => Φ r x vin)
          (ContinuousLinearMap.toSpanSingleton ℝ (A s x (Φ s x vin))) (Ici t₀) s at hraw₀
        change HasFDerivWithinAt (fun r : ℝ => Φ r x vin)
          (ContinuousLinearMap.toSpanSingleton ℝ (A s x (Φ s x vin))) (Ici s) s
        exact hraw₀.mono (fun r hr => le_trans hs.1 hr)
    have hcomp :=
      continuousLinearMap_comp_hasDerivWithinAt (e.continuousLinearMapAt ℝ x) hraw
    have hderiv :
        Acoord (c x) s (Y s) =
          e.continuousLinearMapAt ℝ x (A s x (Φ s x vin)) := by
      simp only [Acoord, Y, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      rw [c.left_inv hx_c]
      rw [e.symmL_continuousLinearMapAt hx_e]
    rw [hderiv, hfun]
    exact hcomp
  have hIcc_sub : Icc t₀ target ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ht₀.1 hs.1, lt_of_le_of_lt hs.2 htarget.2⟩
  have hZ_deriv_at : ∀ s ∈ Icc t₀ target,
      HasDerivAt (Z (c x)) (Acoord (c x) s (Z (c x) s)) s := by
    intro s hs
    exact linearODESolution_hasDerivAt ht₀ hAcoord.continuousOn hcx_U (hIcc_sub hs)
  have hZ_cont : ContinuousOn (Z (c x)) (Icc t₀ target) := fun s hs =>
    (hZ_deriv_at s hs).continuousAt.continuousWithinAt
  have hZ_deriv : ∀ s ∈ Ico t₀ target,
      HasDerivWithinAt (Z (c x)) (Acoord (c x) s (Z (c x) s)) (Ici s) s :=
    fun s hs => (hZ_deriv_at s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hinit : Y t₀ = Z (c x) t₀ := by
    have hZ_init : Z (c x) t₀ = v :=
      linearODESolution_initial Acoord a b t₀ (fun _ : E => v) (c x)
    rw [hZ_init]
    simp only [Y, hΦ₀, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact e.continuousLinearMapAt_symmL hx_e v
  have hnorm_cont : ContinuousOn (fun s => ‖Acoord (c x) s‖) (Icc t₀ target) :=
    (hAcoord_x.mono hIcc_sub).norm
  have hIcc_nonempty : (Icc t₀ target).Nonempty :=
    ⟨t₀, left_mem_Icc.mpr (le_of_lt htarget.1)⟩
  obtain ⟨q, hq, hmaxq⟩ := isCompact_Icc.exists_isMaxOn hIcc_nonempty hnorm_cont
  let K : NNReal := ⟨‖Acoord (c x) q‖, norm_nonneg _⟩
  have hv_lip : ∀ s ∈ Ico t₀ target,
      LipschitzOnWith K (Acoord (c x) s) (univ : Set F) := by
    intro s hs
    have hle : ‖Acoord (c x) s‖ ≤ (K : ℝ) :=
      hmaxq (Ico_subset_Icc_self hs)
    exact ((Acoord (c x) s).lipschitzWith_of_opNorm_le
      hle).lipschitzOnWith
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun s y => Acoord (c x) s y) (s := fun _ => (univ : Set F))
    hv_lip hY_cont hY_deriv (fun _ _ => mem_univ _)
    hZ_cont hZ_deriv (fun _ _ => mem_univ _) hinit
  exact heq ⟨le_of_lt htarget.1, le_rfl⟩

theorem fiberwise_linear_ode_solution_contMDiffOn_right
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (hΦ₀ : ∀ x : M, Φ t₀ x = ContinuousLinearMap.id ℝ (V x))
    (hΦ_cont : ∀ x : M, ∀ v : V x,
      ContinuousOn (fun t : ℝ => Φ t x v) (Icc t₀ b))
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ico t₀ b,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Ici t₀) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo t₀ b ×ˢ (univ : Set M)) := by
  let r : ℝ := (t₀ + b) / 2
  have hr : r ∈ Ioo t₀ b := by
    dsimp [r]
    constructor <;> linarith [ht₀.2]
  let B : ∀ x : M, V x →L[ℝ] V x := fun x => Φ r x
  have hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M =>
        (⟨x, B x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) := by
    exact fiberwise_linear_ode_solution_contMDiff_right
      ht₀ A Φ hA hΦ₀ hΦ_cont hΦ r hr
  have hA' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo t₀ b ×ˢ (univ : Set M)) := by
    exact hA.mono fun p hp => ⟨⟨lt_trans ht₀.1 hp.1.1, hp.1.2⟩, hp.2⟩
  have hΦ' : ∀ x : M, ∀ v : V x, ∀ t ∈ Ioo t₀ b,
      HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t := by
    intro x v t ht
    have hraw := hΦ x v t ⟨le_of_lt ht.1, ht.2⟩
    change HasFDerivWithinAt (fun s : ℝ => Φ s x v)
      (ContinuousLinearMap.toSpanSingleton ℝ (A t x (Φ t x v))) (Ici t₀) t at hraw
    change HasFDerivAt (fun s : ℝ => Φ s x v)
      (ContinuousLinearMap.toSpanSingleton ℝ (A t x (Φ t x v))) t
    exact hraw.hasFDerivAt (Ici_mem_nhds ht.1)
  exact fiberwise_linear_ode_solution_contMDiffOn
    hr A Φ hA' B hB (fun x => rfl) hΦ'

theorem fiberwise_linear_ode_total_map_contMDiff
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (hΦ₀ : ∀ x : M, Φ t₀ x = ContinuousLinearMap.id ℝ (V x))
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace F V => (⟨p.1, Φ t p.1 p.2⟩ : TotalSpace F V)) := by
  have hsection := fiberwise_linear_ode_solution_contMDiff ht₀ A Φ hA hΦ₀ hΦ t ht
  have hsection' : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : TotalSpace F V =>
        (⟨p.1, Φ t p.1⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) :=
    hsection.comp (contMDiff_proj V)
  exact hsection'.clm_bundle_apply contMDiff_id

theorem fiberwise_linear_ode_total_map_contMDiff_right
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M)))
    (hΦ₀ : ∀ x : M, Φ t₀ x = ContinuousLinearMap.id ℝ (V x))
    (hΦ_cont : ∀ x : M, ∀ v : V x,
      ContinuousOn (fun t : ℝ => Φ t x v) (Icc t₀ b))
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ico t₀ b,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Ici t₀) t)
    {t : ℝ} (ht : t ∈ Ioo t₀ b) :
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace F V => (⟨p.1, Φ t p.1 p.2⟩ : TotalSpace F V)) := by
  have hsection :=
    fiberwise_linear_ode_solution_contMDiff_right ht₀ A Φ hA hΦ₀ hΦ_cont hΦ t ht
  have hsection' : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : TotalSpace F V =>
        (⟨p.1, Φ t p.1⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) :=
    hsection.comp (contMDiff_proj V)
  exact hsection'.clm_bundle_apply contMDiff_id

private theorem model_fundamental_solution
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A : ℝ → F →L[ℝ] F) (hA : ContinuousOn A (Ioo a b)) :
    ∃ Z : ℝ → F →L[ℝ] F,
      Z t₀ = ContinuousLinearMap.id ℝ F ∧
      (∀ t ∈ Ioo a b, HasDerivAt Z ((A t).comp (Z t)) t) ∧
      ∀ t ∈ Ioo a b, Function.Bijective (Z t) := by
  let B : ℝ → ℝ → (F →L[ℝ] F) →L[ℝ] F →L[ℝ] F :=
    fun _ t => ContinuousLinearMap.compL ℝ F F F (A t)
  have hB : ContinuousOn (Function.uncurry B) ((univ : Set ℝ) ×ˢ Ioo a b) := by
    exact (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn
      (hA.comp continuousOn_snd fun _ hp => hp.2)
  let Z : ℝ → F →L[ℝ] F :=
    linearODESolution B a b t₀ (fun _ => ContinuousLinearMap.id ℝ F) 0
  have hZ₀ : Z t₀ = ContinuousLinearMap.id ℝ F := linearODESolution_initial _ _ _ _ _ _
  have hZ : ∀ t ∈ Ioo a b, HasDerivAt Z ((A t).comp (Z t)) t := by
    intro t ht
    exact linearODESolution_hasDerivAt ht₀ hB (mem_univ (0 : ℝ)) ht
  refine ⟨Z, hZ₀, hZ, ?_⟩
  intro t ht
  have hinj : Function.Injective (Z t) := by
    intro v w hvw
    let Y : ℝ → F := fun s => Z s (v - w)
    have hY : ∀ s ∈ Ioo a b, HasDerivAt Y (A s (Y s)) s := by
      intro s hs
      simpa [Y] using (hZ s hs).clm_apply (hasDerivAt_const s (v - w))
    have hzero : ∀ s ∈ Ioo a b,
        HasDerivAt (fun _ : ℝ => (0 : F)) (A s 0) s := by
      intro s _
      simpa using hasDerivAt_const s (0 : F)
    have hinit : Y t = 0 := by simp [Y, map_sub, hvw]
    have h := linearODE_unique_on_Ioo ht hA hY hzero hinit ht₀
    apply sub_eq_zero.mp
    simpa [Y, hZ₀] using h
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (Z t).toLinearMap)).mp hinj⟩

theorem exists_fiberwise_linear_ode_solution
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, V x →L[ℝ] V x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t) ∧
      (∀ x : M, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s : ℝ => Φ s x) ((A t x).comp (Φ t x)) t) ∧
      ∀ t ∈ Ioo a b, ∀ x : M, Function.Bijective (Φ t x) := by
  classical
  let Acoord : M → ℝ → F →L[ℝ] F := fun x t =>
    ContinuousLinearMap.inCoordinates F V F V x x x x (A t x)
  have hAcoord : ∀ x, ContinuousOn (Acoord x) (Ioo a b) := by
    intro x t ht
    have h := hA.contMDiffAt (x := (t, x))
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
    rw [contMDiffAt_hom_bundle] at h
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
    exact (h.2.comp t hpair).continuousAt.continuousWithinAt
  choose Z hZ₀ hZ hZbij using fun x => model_fundamental_solution ht₀ (Acoord x) (hAcoord x)
  let e : ∀ x : M, V x ≃L[ℝ] F := VectorBundle.continuousLinearEquivAt ℝ F V
  have hAeq : ∀ x t, Acoord x t = (e x).toContinuousLinearMap.comp
      ((A t x).comp (e x).symm.toContinuousLinearMap) := by
    intro x t
    exact ContinuousLinearMap.inCoordinates_eq
      (mem_baseSet_trivializationAt F V x) (mem_baseSet_trivializationAt F V x)
  let Φ : ℝ → ∀ x : M, V x →L[ℝ] V x := fun t x =>
    (e x).symm.toContinuousLinearMap.comp ((Z x t).comp (e x).toContinuousLinearMap)
  have hΦ₀ : ∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x) := by
    intro x
    ext v
    simp [Φ, hZ₀]
  have hΦop : ∀ x : M, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => Φ s x) ((A t x).comp (Φ t x)) t := by
    intro x t ht
    have h := continuousLinearMap_comp_hasDerivAt
      ((e x).symm.arrowCongr (e x).symm).toContinuousLinearMap (hZ x t ht)
    have hderiv : (e x).symm.arrowCongr (e x).symm ((Acoord x t).comp (Z x t)) =
        (A t x).comp (Φ t x) := by
      ext v
      simp [Φ, hAeq, ContinuousLinearMap.comp_apply]
    change HasDerivAt (fun s => Φ s x)
      ((e x).symm.arrowCongr (e x).symm ((Acoord x t).comp (Z x t))) t at h
    rw [hderiv] at h
    exact h
  have hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t := by
    intro x v t ht
    have h := (hZ x t ht).clm_apply (hasDerivAt_const t (e x v))
    have h' := continuousLinearMap_comp_hasDerivAt (e x).symm.toContinuousLinearMap h
    simpa [Φ, hAeq, ContinuousLinearMap.comp_apply] using h'
  have hΦsmooth := fiberwise_linear_ode_solution_contMDiffOn
    ht₀ A Φ hA (Φ t₀)
    (fiberwise_linear_ode_solution_contMDiff ht₀ A Φ hA hΦ₀ hΦ t₀ ht₀)
    (fun _ => rfl) hΦ
  refine ⟨Φ, hΦ₀, hΦsmooth, hΦ, hΦop, ?_⟩
  intro t ht x
  exact (e x).symm.bijective.comp ((hZbij x t ht).comp (e x).bijective)

private theorem fiberwise_linear_ode_contMDiffOn_closed_interval
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc a b ×ˢ (univ : Set M)))
    (B : ∀ x : M, V x →L[ℝ] V x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M =>
        (⟨x, B x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (hΦ₀ : ∀ x : M, Φ t₀ x = B x)
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Icc a b) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc a b ×ˢ (univ : Set M)) := by
  intro p₀ hp₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let x₀ := p₀.2
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F →L[ℝ] F) ∞
    (fun p : ℝ × M =>
      ContinuousLinearMap.inCoordinates F V F V x₀ p.2 x₀ p.2 (Φ p.1 p.2))
    (Icc a b ×ˢ (univ : Set M)) p₀
  let c := extChartAt I x₀
  let e := trivializationAt F V x₀
  let eHom := e.continuousLinearMap (RingHom.id ℝ) e
  let U : Set E := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU_open : IsOpen U := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target_of_boundarylessManifold (I := I) x₀) e.open_baseSet
  have hx₀_source : x₀ ∈ c.source := mem_extChartAt_source x₀
  have hcx₀_target : c x₀ ∈ c.target := c.map_source hx₀_source
  have hx₀_e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  have hcx₀_U : c x₀ ∈ U := by
    refine ⟨hcx₀_target, ?_⟩
    change c.symm (c x₀) ∈ e.baseSet
    rw [c.left_inv hx₀_source]
    exact hx₀_e
  let Acoord : E → ℝ → (F →L[ℝ] F) := fun z t =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (A t (c.symm z))
  have hAcoord : ContDiffOn ℝ ∞ (Function.uncurry Acoord) (U ×ˢ Icc a b) := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hparam : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : E × ℝ => (p.2, c.symm p.1)) (U ×ˢ Icc a b) :=
      contMDiffOn_snd.prodMk (hsymm.comp contMDiffOn_fst fun p hp => hp.1)
    have hsection := hA.comp hparam fun p hp => ⟨hp.2, mem_univ _⟩
    have hbase : Set.MapsTo
        (fun p : E × ℝ =>
          (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (U ×ˢ Icc a b) eHom.source := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : E × ℝ =>
          (eHom
            (⟨c.symm p.1, A p.2 (c.symm p.1)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2)
        (U ×ˢ Icc a b) := fun p hp => (hcoord p hp).snd
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hsnd.congr fun p hp => by
      obtain ⟨z, t⟩ := p
      obtain ⟨hz, ht⟩ := hp
      change (eHom
          (⟨c.symm z, A t (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Acoord z t
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Acoord,
        ContinuousLinearMap.inCoordinates]
  let Bcoord : E → (F →L[ℝ] F) := fun z =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (B (c.symm z))
  have hBcoord : ContDiffOn ℝ ∞ Bcoord U := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm U :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
    have hsection : ContMDiffOn 𝓘(ℝ, E) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun z : E =>
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) U := by
      exact (hB.comp_contMDiffOn hsymm).congr fun z hz => rfl
    have hbase : Set.MapsTo
        (fun z : E =>
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        U eHom.source := by
      intro z hz
      rw [eHom.mem_source]
      exact ⟨hz.2, hz.2⟩
    have hcoord := eHom.contMDiffOn.comp hsection hbase
    have hsnd : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun z : E =>
          (eHom
            (⟨c.symm z, B (c.symm z)⟩ :
              TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2) U :=
      fun z hz => (hcoord z hz).snd
    rw [← contMDiffOn_iff_contDiffOn]
    exact hsnd.congr fun z hz => by
      change (eHom
          (⟨c.symm z, B (c.symm z)⟩ :
            TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))).2 = Bcoord z
      simp only [eHom, e, Bundle.Trivialization.continuousLinearMap_apply, Bcoord,
        ContinuousLinearMap.inCoordinates]
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  let Z₀ : E → F := fun z => Bcoord z v
  let Z : E → ℝ → F := fun z t =>
    ContinuousLinearMap.inCoordinates F V F V x₀ (c.symm z) x₀ (c.symm z)
      (Φ t (c.symm z)) v
  have hZ₀ : ContDiffOn ℝ ∞ Z₀ U := hBcoord.clm_apply contDiffOn_const
  have hZinit : ∀ z ∈ U, Z z t₀ = Z₀ z := by
    intro z hz
    simp only [Z, Z₀, Bcoord, hΦ₀]
  have hZderiv : ∀ z ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Z z) (Acoord z t (Z z t)) (Icc a b) t := by
    intro z hz t ht
    let vin : V (c.symm z) := e.symmL ℝ (c.symm z) v
    have hraw := hΦ (c.symm z) vin t ht
    have hcomp := continuousLinearMap_comp_hasDerivWithinAt
      (e.continuousLinearMapAt ℝ (c.symm z)) hraw
    have hderiv : Acoord z t (Z z t) =
        e.continuousLinearMapAt ℝ (c.symm z) (A t (c.symm z) (Φ t (c.symm z) vin)) := by
      simp only [Acoord, Z, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [e.symmL_continuousLinearMapAt hz.2]
    rw [hderiv]
    exact hcomp
  have hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) (U ×ˢ Icc a b) :=
    linear_ode_solution_contDiffOn_Icc ht₀ hU_open hAcoord hZ₀ hZinit hZderiv
  have hZ_mfld : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (Function.uncurry Z) (U ×ˢ Icc a b) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hZ
    exact hZ
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ c x₀ :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (by simp)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (c p.2, p.1)) (Icc a b ×ˢ (univ : Set M)) p₀ :=
    (hchart.comp p₀ contMDiffAt_snd).contMDiffWithinAt.prodMk contMDiffWithinAt_fst
  have hcandidate : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M => Z (c p.2) p.1) (Icc a b ×ˢ (univ : Set M)) p₀ := by
    have hlocal := (hZ_mfld (c x₀, p₀.1) ⟨hcx₀_U, hp₀.1⟩).comp' p₀ hmove
    apply hlocal.mono_of_mem_nhdsWithin
    have hU : ∀ᶠ p : ℝ × M in 𝓝[Icc a b ×ˢ (univ : Set M)] p₀, c p.2 ∈ U :=
      (hchart.continuousAt.comp continuousAt_snd).continuousWithinAt
        (hU_open.mem_nhds hcx₀_U)
    filter_upwards [self_mem_nhdsWithin, hU] with p hp hpU
    exact ⟨hp, hpU, hp.1⟩
  apply hcandidate.congr_of_eventuallyEq
  · have hc_source : ∀ᶠ p : ℝ × M in
        𝓝[Icc a b ×ˢ (univ : Set M)] p₀, p.2 ∈ c.source :=
      continuousWithinAt_snd
        ((isOpen_extChartAt_source (I := I) x₀).mem_nhds hx₀_source)
    filter_upwards [hc_source] with p hp
    dsimp only [Z]
    rw [c.left_inv hp]
  · dsimp only [Z]
    rw [c.left_inv hx₀_source]

theorem fiberwise_linear_ode_solution_contMDiffOn_interval
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (J ×ˢ (univ : Set M)))
    (B : ∀ x : M, V x →L[ℝ] V x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M =>
        (⟨x, B x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (hΦ₀ : ∀ x : M, Φ t₀ x = B x)
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ J,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) J t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (J ×ˢ (univ : Set M)) := by
  intro p hp
  obtain ⟨a, b, ht₀C, htC, hCJ, hCnhds⟩ :=
    hJ.exists_Icc_subset_mem_nhdsWithin ht₀ hp.1
  have hlocal := fiberwise_linear_ode_contMDiffOn_closed_interval ht₀C A Φ
    (hA.mono (prod_mono_left hCJ)) B hB hΦ₀
    (fun x v t ht => HasFDerivWithinAt.mono (hΦ x v t (hCJ ht)) hCJ)
  apply (hlocal p ⟨htC, hp.2⟩).mono_of_mem_nhdsWithin
  have hmaps : MapsTo (Prod.fst : ℝ × M → ℝ) (J ×ˢ (univ : Set M)) J := fun _ hq => hq.1
  have htime : Tendsto Prod.fst (𝓝[J ×ˢ (univ : Set M)] p) (𝓝[J] p.1) :=
    continuousWithinAt_fst.tendsto_nhdsWithin hmaps
  filter_upwards [htime hCnhds] with q hq
  exact ⟨hq, mem_univ _⟩

theorem fiberwise_linear_ode_solution_contMDiffOn_Icc
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc a b ×ˢ (univ : Set M)))
    (B : ∀ x : M, V x →L[ℝ] V x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M =>
        (⟨x, B x⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (hΦ₀ : ∀ x : M, Φ t₀ x = B x)
    (hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Icc a b) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc a b ×ˢ (univ : Set M)) :=
  fiberwise_linear_ode_solution_contMDiffOn_interval ordConnected_Icc ht₀ A Φ hA B hB hΦ₀ hΦ

private theorem model_fundamental_solution_on_interval
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (A : ℝ → F →L[ℝ] F) (hA : ContinuousOn A J) :
    ∃ Z : ℝ → F →L[ℝ] F,
      Z t₀ = ContinuousLinearMap.id ℝ F ∧
      (∀ t ∈ J, HasDerivWithinAt Z ((A t).comp (Z t)) J t) ∧
      ∀ t ∈ J, Function.Bijective (Z t) := by
  obtain ⟨Z, hZ₀, hZ⟩ := exists_linear_ode_solution_on_interval hJ ht₀
    ((ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ F)
  refine ⟨Z, hZ₀, hZ, ?_⟩
  intro t ht
  have hinj : Function.Injective (Z t) := by
    intro v w hvw
    let Y : ℝ → F := fun s => Z s (v - w)
    have hY : ∀ s ∈ J, HasDerivWithinAt Y (A s (Y s)) J s := by
      intro s hs
      simpa [Y] using (hZ s hs).clm_apply (hasDerivWithinAt_const s J (v - w))
    have hzero : ∀ s ∈ J,
        HasDerivWithinAt (fun _ : ℝ => (0 : F)) (A s 0) J s := by
      intro s _
      simpa using hasDerivWithinAt_const s J (0 : F)
    have hinit : Y t = 0 := by simp [Y, map_sub, hvw]
    have h := linear_ode_unique_on_interval hJ ht hA hY hzero hinit ht₀
    apply sub_eq_zero.mp
    simpa [Y, hZ₀] using h
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (Z t).toLinearMap)).mp hinj⟩

theorem exists_fiberwise_linear_ode_solution_on_interval
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (A : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (J ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, V x →L[ℝ] V x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (F →L[ℝ] F)
            (fun x => V x →L[ℝ] V x))) (J ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : V x, ∀ t ∈ J,
        HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) J t) ∧
      (∀ x : M, ∀ t ∈ J,
        HasDerivWithinAt (fun s : ℝ => Φ s x) ((A t x).comp (Φ t x)) J t) ∧
      (∀ t ∈ J, ∀ x : M, ∀ v : V x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v) ∧
      ∀ t ∈ J, ∀ x : M, Function.Bijective (Φ t x) := by
  classical
  let Acoord : M → ℝ → F →L[ℝ] F := fun x t =>
    ContinuousLinearMap.inCoordinates F V F V x x x x (A t x)
  have hAcoord : ∀ x, ContinuousOn (Acoord x) J := by
    intro x t ht
    have h := hA (t, x) ⟨ht, mem_univ x⟩
    rw [contMDiffWithinAt_hom_bundle] at h
    have hpair : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ => (s, x)) J t :=
      contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
    have hmaps : MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ (univ : Set M)) :=
      fun s hs => ⟨hs, mem_univ x⟩
    exact (h.2.comp (f := fun s : ℝ => (s, x)) t hpair hmaps).continuousWithinAt
  choose Z hZ₀ hZ hZbij using fun x =>
    model_fundamental_solution_on_interval hJ ht₀ (Acoord x) (hAcoord x)
  let e : ∀ x : M, V x ≃L[ℝ] F := VectorBundle.continuousLinearEquivAt ℝ F V
  have hAeq : ∀ x t, Acoord x t = (e x).toContinuousLinearMap.comp
      ((A t x).comp (e x).symm.toContinuousLinearMap) := by
    intro x t
    exact ContinuousLinearMap.inCoordinates_eq
      (mem_baseSet_trivializationAt F V x) (mem_baseSet_trivializationAt F V x)
  let Φ : ℝ → ∀ x : M, V x →L[ℝ] V x := fun t x =>
    (e x).symm.toContinuousLinearMap.comp ((Z x t).comp (e x).toContinuousLinearMap)
  have hΦ₀ : ∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x) := by
    intro x
    ext v
    simp [Φ, hZ₀]
  have hΦop : ∀ x : M, ∀ t ∈ J,
      HasDerivWithinAt (fun s : ℝ => Φ s x) ((A t x).comp (Φ t x)) J t := by
    intro x t ht
    have h := continuousLinearMap_comp_hasDerivWithinAt
      ((e x).symm.arrowCongr (e x).symm).toContinuousLinearMap (hZ x t ht)
    have hderiv : (e x).symm.arrowCongr (e x).symm ((Acoord x t).comp (Z x t)) =
        (A t x).comp (Φ t x) := by
      ext v
      simp [Φ, hAeq, ContinuousLinearMap.comp_apply]
    change HasDerivWithinAt (fun s => Φ s x)
      ((e x).symm.arrowCongr (e x).symm ((Acoord x t).comp (Z x t))) J t at h
    rw [hderiv] at h
    exact h
  have hΦ : ∀ x : M, ∀ v : V x, ∀ t ∈ J,
      HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) J t := by
    intro x v t ht
    have h := (hZ x t ht).clm_apply (hasDerivWithinAt_const t J (e x v))
    have h' := continuousLinearMap_comp_hasDerivWithinAt (e x).symm.toContinuousLinearMap h
    simpa [Φ, hAeq, ContinuousLinearMap.comp_apply] using h'
  have hid : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x : M => (⟨x, ContinuousLinearMap.id ℝ (V x)⟩ :
        TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) := by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    apply (contMDiffAt_const (c := ContinuousLinearMap.id ℝ F)).congr_of_eventuallyEq
    let e := trivializationAt F V x
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x)] with y hy
    ext v
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    exact e.continuousLinearMapAt_symmL hy v
  have hΦsmooth := fiberwise_linear_ode_solution_contMDiffOn_interval
    hJ ht₀ A Φ hA (fun x => ContinuousLinearMap.id ℝ (V x)) hid hΦ₀ hΦ
  have hΦbij : ∀ t ∈ J, ∀ x : M, Function.Bijective (Φ t x) := by
    intro t ht x
    exact (e x).symm.bijective.comp ((hZbij x t ht).comp (e x).bijective)
  have hΦinv : ∀ t ∈ J, ∀ x, (Φ t x).IsInvertible := by
    intro t ht x
    let L : F →L[ℝ] F := (e x).toContinuousLinearMap.comp
      ((Φ t x).comp (e x).symm.toContinuousLinearMap)
    have hbij : Function.Bijective L :=
      (e x).bijective.comp ((hΦbij t ht x).comp (e x).symm.bijective)
    have hinv : L.IsInvertible :=
      ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, by ext; rfl⟩
    simpa only [L, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv] using hinv
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine ⟨Φ, hΦ₀, hΦsmooth, hΦsmooth.clm_bundle_inverse
    (fun p hp => hΦinv p.1 hp.1 p.2), hΦ, hΦop, ?_, hΦbij⟩
  intro t ht x v
  obtain ⟨L, hL⟩ := hΦinv t ht x
  rw [← hL]
  simp

theorem exists_fiberwise_linear_ode_solution_on_Icc
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (A : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, V x →L[ℝ] V x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (Icc a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (F →L[ℝ] F)
            (fun x => V x →L[ℝ] V x))) (Icc a b ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : V x, ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) (Icc a b) t) ∧
      (∀ x : M, ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s : ℝ => Φ s x) ((A t x).comp (Φ t x)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ x : M, ∀ v : V x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v) ∧
      ∀ t ∈ Icc a b, ∀ x : M, Function.Bijective (Φ t x) :=
  exists_fiberwise_linear_ode_solution_on_interval ordConnected_Icc ht₀ A hA

end DifferentialGeometry.Analysis.ODE.Flow

end
