import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballLoop

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
open GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A conjugate of a null-homotopic loop is null-homotopic. -/
theorem conj_homotopic_refl_CPF3 {X : Type*} [TopologicalSpace X] {a b : X} (wv : Path a b)
    (γ : Path a a) (h : γ.Homotopic (Path.refl a)) :
    (wv.symm.trans (γ.trans wv)).Homotopic (Path.refl b) := by
  have h1 : (wv.symm.trans (γ.trans wv)).Homotopic (wv.symm.trans ((Path.refl a).trans wv)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.hcomp h (Path.Homotopic.refl _))
  have h2 : ((Path.refl a).trans wv).Homotopic wv := ⟨Path.Homotopy.reflTrans wv⟩
  have h3 : (wv.symm.trans wv).Homotopic (Path.refl b) := Path.Homotopic.symm ⟨Path.Homotopy.reflSymmTrans wv⟩
  exact h1.trans ((Path.Homotopic.hcomp (Path.Homotopic.refl _) h2).trans h3)


theorem semicircle_nullhomotopic_CPF3 {X : Type*} [TopologicalSpace X]
    (ψ : CuspHalfSpace → X) (hψ : Continuous ψ) {cov : E2 → Torus} (hcov : Continuous cov)
    (x0 x1 : E2) (Lp : Path x0 x1) (hxx : cov x1 = cov x0)
    (hnull : ∀ Γ : C(unitInterval, X), (∀ s, Γ s = ψ (cov (Lp s), halfZero)) →
      Γ.HomotopicRel (ContinuousMap.const unitInterval (ψ (cov x0, halfZero))) {0, 1})
    (σ : Path (emb x0 1) (emb x1 1)) (P : C(unitInterval, X))
    (hP : ∀ s, P s = ψ (cuspChart cov (σ s))) :
    P.HomotopicRel (ContinuousMap.const unitInterval (ψ (cov x0, hp 1))) {0, 1} := by
  have hFt : Continuous (fun x : E3 => ψ (cuspChart cov x)) := hψ.comp (continuous_cuspChart hcov)
  let Ft : C(E3, X) := ⟨_, hFt⟩
  let wv : Path (ψ (cov x0, halfZero)) (ψ (cov x0, hp 1)) :=
    { toFun := fun s => ψ (cov x0, hp s)
      continuous_toFun := hψ.comp (continuous_const.prodMk
        (continuous_hp.comp continuous_subtype_val))
      source' := by simp [hp_zero]
      target' := by simp }
  let Γp : Path (ψ (cov x0, halfZero)) (ψ (cov x0, halfZero)) :=
    { toFun := fun s => ψ (cov (Lp s), halfZero)
      continuous_toFun := hψ.comp ((hcov.comp Lp.continuous).prodMk continuous_const)
      source' := by simp
      target' := by simp [hxx] }
  have hΓ : Γp.Homotopic (Path.refl _) := hnull Γp.toContinuousMap (fun s => rfl)
  have hL1 := conj_homotopic_refl_CPF3 wv Γp hΓ
  let v0 : Path (emb x0 1) (emb x0 0) :=
    { toFun := fun s => emb x0 (1 - (s : ℝ))
      continuous_toFun := by
        have := continuous_emb.comp (continuous_const.prodMk
          (continuous_const.sub continuous_subtype_val) : Continuous
            (fun s : unitInterval => (x0, 1 - (s : ℝ))))
        exact this
      source' := by simp
      target' := by simp }
  let lt : Path (emb x0 0) (emb x1 0) :=
    { toFun := fun s => emb (Lp s) 0
      continuous_toFun := continuous_emb.comp (Lp.continuous.prodMk continuous_const)
      source' := by simp
      target' := by simp }
  let v1 : Path (emb x1 0) (emb x1 1) :=
    { toFun := fun s => emb x1 (s : ℝ)
      continuous_toFun := continuous_emb.comp (continuous_const.prodMk continuous_subtype_val)
      source' := by simp
      target' := by simp }
  let Λ := v0.trans (lt.trans v1)
  have hσΛ : σ.Homotopic Λ := SimplyConnectedSpace.paths_homotopic σ Λ
  have hmap := hσΛ.map Ft
  have h1 : P.HomotopicRel (σ.map Ft.continuous).toContinuousMap {0, 1} := by
    have : P = (σ.map Ft.continuous).toContinuousMap := by
      ext s; exact hP s
    rw [this]; exact ContinuousMap.HomotopicRel.refl _
  have h3 : (Λ.map Ft.continuous).toContinuousMap = (wv.symm.trans (Γp.trans wv)).toContinuousMap := by
    ext s
    simp only [Path.map_coe, Path.coe_toContinuousMap, Path.trans_apply, Function.comp_apply, Λ]
    split_ifs with h h1
    · simp [Ft, v0, wv, cuspChart_emb]
    · simp [Ft, lt, Γp, cuspChart_emb, hp_zero]
    · simp [Ft, v1, wv, cuspChart_emb, hxx]
  have h2 : (σ.map Ft.continuous).toContinuousMap.HomotopicRel
      (Λ.map Ft.continuous).toContinuousMap {0, 1} := hmap
  have h4 : (wv.symm.trans (Γp.trans wv)).toContinuousMap.HomotopicRel
      (Path.refl (ψ (cov x0, hp 1))).toContinuousMap {0, 1} := hL1
  rw [h3] at h2
  exact h1.trans (h2.trans h4)


universe u

theorem continuous_scCurve (x0 x1 : E2) (R : ℝ) : Continuous (scCurve x0 x1 R) := by
  unfold scCurve
  have h1 : Continuous (scF R) := continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_scF R τ).continuousAt
  have h2 : Continuous (scH R) := continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_scH R τ).continuousAt
  fun_prop

/-- **Key contradiction.**  If a lift `Lp` of a loop of the cusp cross-section ends at a different
point of the plane (same point of the torus) and its image under the cusp map is null-homotopic,
then we get a null-homotopic nonconstant geodesic loop in the hyperbolic manifold. -/
theorem loop_false_CPF3 {Hm : FiniteVolumeHyperbolicModel.{u}} (C : HyperbolicCusp)
    (ψ : CuspHalfSpace → Hm.Carrier) (hψ : ContMDiff halfCollarModel (𝓡 3) ∞ ψ)
    (hψinj : Function.Injective ψ)
    (hiso : ∀ p (v w : TangentSpace halfCollarModel p),
      Hm.metric.inner (ψ p) (mfderiv halfCollarModel (𝓡 3) ψ p v)
        (mfderiv halfCollarModel (𝓡 3) ψ p w) = C.metric.inner p v w)
    {cov : E2 → Torus} (hcov : ContMDiff 𝓘(ℝ, E2) torusModel ∞ cov)
    (hcovm : ∀ (x v w : E2), C.torusMetric.inner (cov x) (mfderiv 𝓘(ℝ, E2) torusModel cov x v)
        (mfderiv 𝓘(ℝ, E2) torusModel cov x w) = inner ℝ v w)
    (x0 x1 : E2) (Lp : Path x0 x1) (hxx : cov x1 = cov x0) (hne : x1 ≠ x0)
    (hnull : ∀ Γ : C(unitInterval, Hm.Carrier), (∀ s, Γ s = ψ (cov (Lp s), halfZero)) →
      Γ.HomotopicRel (ContinuousMap.const unitInterval (ψ (cov x0, halfZero))) {0, 1}) :
    False := by
  have hℓpos : 0 < ‖x1 - x0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨a, R, ha, hR, hFa, hHa, hHma, hHge, hHgt⟩ :=
    exists_semicircle_CPF3 (s := 1) (ℓ := ‖x1 - x0‖) one_pos hℓpos
  have hγm := scCurve_neg hFa hHma hne
  have hγp := scCurve_pos hFa hHa hne
  have hgeo := scCurve_geodesic C ψ hψ hiso hcov hcovm hne hR hHge
  have hcontγ := continuous_scCurve x0 x1 R
  have hcontc : Continuous (fun τ => ψ (cuspChart cov (scCurve x0 x1 R τ))) :=
    hψ.continuous.comp ((continuous_cuspChart hcov.continuous).comp hcontγ)
  let σ : Path (emb x0 1) (emb x1 1) :=
    { toFun := fun s => scCurve x0 x1 R (-a + 2 * a * (s : ℝ))
      continuous_toFun := hcontγ.comp (by fun_prop)
      source' := by simpa using hγm
      target' := by
        have : -a + 2 * a = a := by ring
        simpa [this] using hγp }
  let P : C(unitInterval, Hm.Carrier) :=
    ⟨fun s => ψ (cuspChart cov (scCurve x0 x1 R (-a + 2 * a * (s : ℝ)))),
      hcontc.comp (by fun_prop)⟩
  have hPnull := semicircle_nullhomotopic_CPF3 ψ hψ.continuous hcov.continuous x0 x1 Lp hxx hnull
    σ P (fun s => rfl)
  have hc0 : ψ (cuspChart cov (scCurve x0 x1 R (-a))) = ψ (cov x0, hp 1) := by
    rw [hγm, cuspChart_emb]
  have hPnull' : P.HomotopicRel (ContinuousMap.const unitInterval
      (ψ (cuspChart cov (scCurve x0 x1 R (-a))))) {0, 1} := by
    rw [hc0]; exact hPnull
  have hconst := horo_hadamard_CPF3 Hm ha hgeo hcontc.continuousOn P (fun s => rfl) hPnull' a
    ⟨by linarith, le_rfl⟩
  have hinj := hψinj hconst
  have hdepth : hp 1 = hp (scH R 0) := by
    have h2 := congrArg Prod.snd hinj
    simp only [hγp, cuspChart_emb] at h2
    have h3 : cuspChart cov (scCurve x0 x1 R 0) = (cov (planeProj (scCurve x0 x1 R 0)), hp (scH R 0)) := by
      simp [cuspChart, depthPt_eq, scCurve_two]
    rw [h3] at h2
    exact h2
  have hv := congrArg (fun p : EuclideanHalfSpace 1 => p.val.ofLp 0) hdepth
  simp only [hp, halfPoint] at hv
  have hmax : max (scH R 0) 0 = scH R 0 := max_eq_left (by linarith)
  rw [hmax] at hv
  simp at hv
  linarith

end GC.LongTime.CuspP1
