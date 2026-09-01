import DifferentialGeometry.Analysis.ODE.Flow.ParametricLinearODE
import DifferentialGeometry.Bundle.ClmSectionSmooth

set_option autoImplicit false

noncomputable section

open Asymptotics Bundle Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.ODE.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
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

theorem fiberwise_linear_ode_solution_contMDiff
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))))
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
      (isOpen_extChartAt_target (I := I) x₀) e.open_baseSet
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
    have hsection := hA.comp_contMDiffOn hparam
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
      linearODESolution_init Acoord a b t₀ (fun _ : E => v) (c x)
    rw [hZ_init]
    simp only [Y, hΦ₀, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact e.continuousLinearMapAt_symmL hx_e v
  have heq := linearODE_unique_on_Ioo ht₀ hAcoord_x hY_deriv hZ_deriv hinit
  exact heq htarget

theorem fiberwise_linear_ode_total_map_contMDiff
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A Φ : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))))
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

end DifferentialGeometry.Analysis.ODE.Flow

end
