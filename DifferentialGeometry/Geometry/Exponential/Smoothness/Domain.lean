import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve
import DifferentialGeometry.Analysis.ODE.Flow.Complete
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Geodesic.Maximal.Uniqueness

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.ODE
open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem exists_contMDiff_eq_expMap_nhds
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    ∃ U : Set E, IsOpen U ∧ v ∈ U ∧
      ∃ F : E → M,
        ContMDiff 𝓘(ℝ, E) I ∞ F ∧
        (∀ w ∈ U, (show TangentSpace I p from w) ∈ expDomain (I := I) g p) ∧
        (∀ w ∈ U, expMap (I := I) g p (show TangentSpace I p from w) = F w) := by
  classical
  change HasGeodesicAt (I := I) g p v 1 at hv
  obtain ⟨_γ, J, hJ_open, hJ_conn, h0J, h1J, f, _hproj, hf0, hf_on⟩ := hv
  obtain ⟨ε0, hε0_pos, hball0⟩ := Metric.isOpen_iff.mp hJ_open 0 h0J
  obtain ⟨ε1, hε1_pos, hball1⟩ := Metric.isOpen_iff.mp hJ_open 1 h1J
  let δ : ℝ := min ε0 ε1 / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ₀ : δ < ε0 := by
    dsimp [δ]
    have hmin : min ε0 ε1 ≤ ε0 := min_le_left _ _
    nlinarith
  have hδ₁ : δ < ε1 := by
    dsimp [δ]
    have hmin : min ε0 ε1 ≤ ε1 := min_le_right _ _
    nlinarith
  let c : ℝ := -δ
  let a : ℝ := -δ / 2
  let b : ℝ := 1 + δ / 2
  let d : ℝ := 1 + δ
  have hc_lt_a : c < a := by dsimp [c, a]; linarith
  have ha_lt_zero : a < 0 := by dsimp [a]; linarith
  have hone_lt_b : 1 < b := by dsimp [b]; linarith
  have hb_lt_d : b < d := by dsimp [b, d]; linarith
  have hcJ : c ∈ J := by
    apply hball0
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [c]
    rw [sub_zero, abs_neg, abs_of_nonneg hδ_pos.le]
    exact hδ₀
  have hdJ : d ∈ J := by
    apply hball1
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [d]
    rw [add_sub_cancel_left, abs_of_nonneg hδ_pos.le]
    exact hδ₁
  have hcdJ : Set.Icc c d ⊆ J := hJ_conn.ordConnected.out hcJ hdJ
  have h0cd : (0 : ℝ) ∈ Set.Ioo c d := by
    constructor <;> dsimp [c, d] <;> linarith
  have h0ab : (0 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> linarith
  have h1ab : (1 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> linarith
  let K : Set (TangentBundle I M) := f '' Set.Icc c d
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn ((hf_on.mono hcdJ).continuousOn)
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_bump_nhds (I := I.tangent) hK
  change {q : TangentBundle I M | χ q = 1} ∈ 𝓝ˢ K at hχone
  obtain ⟨O, hO_open, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχone
  let X : (q : TangentBundle I M) → TangentSpace I.tangent q :=
    fun q => χ q • geodesicVectorField (I := I) g q
  have hX : ContMDiff I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    exact hχ.smul_section (contMDiff_geodesicVectorField (I := I) g)
  have hXc : IsCompact (tsupport X) := by
    change HasCompactSupport (χ • geodesicVectorField (I := I) g)
    exact hχc.smul_right
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hcomplete : ∀ q : TangentBundle I M,
      ∃ η : ℝ → TangentBundle I M, η 0 = q ∧ IsMIntegralCurve η X :=
    exists_globalIntegralCurve_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I.tangent) I.tangent ∞
      (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) :=
    contMDiff_curveAt X hX hcomplete
  have hf_X : IsMIntegralCurveOn f X (Set.Ioo c d) := by
    have hf_g := hf_on.mono (Set.Ioo_subset_Icc_self.trans hcdJ)
    intro t ht
    have hftK : f t ∈ K := ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
    have hχt : χ (f t) = 1 := hOχ (hKO hftK)
    simpa only [X, hχt, one_smul] using hf_g t ht
  let q₀ : TangentBundle I M := ⟨p, v⟩
  have hcut_eq : Set.EqOn (curveAt X hcomplete q₀) f (Set.Ioo c d) := by
    apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := (0 : ℝ)) h0cd (hX.of_le (by norm_num))
      ((curveAt_integralCurve X hcomplete q₀).isMIntegralCurveOn (Set.Ioo c d)) hf_X
    rw [curveAt_zero, hf0]
  let S : Set (ℝ × TangentBundle I M) :=
    (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) ⁻¹' O
  have hS_open : IsOpen S := hO_open.preimage hflow.continuous
  have hslice : Set.Icc a b ×ˢ ({q₀} : Set (TangentBundle I M)) ⊆ S := by
    rintro ⟨t, q⟩ ⟨ht, rfl⟩
    have htcd : t ∈ Set.Ioo c d := ⟨lt_of_lt_of_le hc_lt_a ht.1,
      lt_of_le_of_lt ht.2 hb_lt_d⟩
    exact hKO ⟨t, ⟨le_of_lt htcd.1, le_of_lt htcd.2⟩, (hcut_eq htcd).symm⟩
  obtain ⟨W, U₀, _hW_open, hU₀_open, hIccW, hq₀U, hWU⟩ :=
    generalized_tube_lemma (isCompact_Icc : IsCompact (Set.Icc a b))
      (isCompact_singleton : IsCompact ({q₀} : Set (TangentBundle I M))) hS_open hslice
  have hq₀U' : q₀ ∈ U₀ := hq₀U rfl
  let U : Set E := (fun w : E => (⟨p, w⟩ : TangentBundle I M)) ⁻¹' U₀
  have hU_open : IsOpen U :=
    hU₀_open.preimage (contMDiff_tangentFiber (I := I) (n := 0) p).continuous
  have hvU : v ∈ U := by
    change q₀ ∈ U₀
    exact hq₀U'
  let F : E → M := fun w => (curveAt X hcomplete
    (⟨p, w⟩ : TangentBundle I M) 1).proj
  have hF : ContMDiff 𝓘(ℝ, E) I ∞ F := by
    have hlaunch : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod I.tangent) ∞
        (fun w : E => ((1 : ℝ), (⟨p, w⟩ : TangentBundle I M))) :=
      contMDiff_const.prodMk (contMDiff_tangentFiber (I := I) p)
    have hlift : ContMDiff 𝓘(ℝ, E) I.tangent ∞
        (fun w : E => curveAt X hcomplete
          (⟨p, w⟩ : TangentBundle I M) 1) := by
      exact hflow.comp hlaunch
    exact (contMDiff_proj (TangentSpace I)).comp hlift
  have hnear (w : E) (hw : w ∈ U) :
      (show TangentSpace I p from w) ∈ expDomain (I := I) g p ∧
        expMap (I := I) g p (show TangentSpace I p from w) = F w := by
    let q : TangentBundle I M := ⟨p, w⟩
    let η : ℝ → TangentBundle I M := curveAt X hcomplete q
    have hη_g : IsMIntegralCurveOn η (geodesicVectorField (I := I) g)
        (Set.Ioo a b) := by
      intro t ht
      have hflowO : curveAt X hcomplete q t ∈ O := by
        have hpair : (t, q) ∈ W ×ˢ U₀ :=
          ⟨hIccW ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hw⟩
        exact hWU hpair
      have hχt : χ (η t) = 1 := hOχ hflowO
      have hder := (curveAt_integralCurve X hcomplete q).isMIntegralCurveOn
        (Set.Ioo a b) t ht
      simpa only [η, X, hχt, one_smul] using hder
    have hgeo : IsGeodesicOnWithInitial (I := I) g
        (projectCurve (I := I) η) (Set.Ioo a b) p w := by
      refine ⟨η, (fun _ => rfl), ?_, hη_g⟩
      simp only [η, q, curveAt_zero]
    have hwdom : (show TangentSpace I p from w) ∈ expDomain (I := I) g p := by
      change HasGeodesicAt (I := I) g p w 1
      exact ⟨projectCurve (I := I) η, Set.Ioo a b, isOpen_Ioo,
        isPreconnected_Ioo, h0ab, h1ab, hgeo⟩
    have heq := maximalGeodesic_eqOn (I := I) g isOpen_Ioo isPreconnected_Ioo h0ab hgeo
    refine ⟨hwdom, ?_⟩
    change maximalGeodesic g p w 1 = (η 1).proj
    exact heq h1ab
  exact ⟨U, hU_open, hvU, F, hF, (fun w hw => (hnear w hw).1),
    (fun w hw => (hnear w hw).2)⟩

theorem contMDiffAt_expMap
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w)) v := by
  obtain ⟨U, hU_open, hvU, F, hF, _hdom, heq⟩ :=
    exists_contMDiff_eq_expMap_nhds (I := I) g p hv
  have heq_ev :
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w)) =ᶠ[𝓝 v] F :=
    Filter.eventuallyEq_of_mem (hU_open.mem_nhds hvU) (fun w hw => heq w hw)
  exact hF.contMDiffAt.congr_of_eventuallyEq heq_ev

theorem mfderiv_expMap_add_smul
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (s₀ : ℝ)
    (hx : (show TangentSpace I p from x + s₀ • w) ∈ expDomain (I := I) g p) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
      expMap (I := I) g p (show TangentSpace I p from x + s • w)) s₀ (1 : ℝ) =
      mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
        (x + s₀ • w) w := by
  have hline : HasFDerivAt (fun s : ℝ => x + s • w)
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) s₀ := by
    simpa using! ((hasFDerivAt_id s₀).smul_const w).const_add x
  have hlineMF : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s : ℝ => x + s • w) s₀ (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv, hline.fderiv]
    change (1 : ℝ) • w = w
    exact one_smul ℝ w
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := fun s : ℝ => x + s • w) (x := s₀)
    (contMDiffAt_expMap (I := I) g p hx |>.mdifferentiableAt (by decide))
    hline.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hlineMF] at hcomp
  exact hcomp

theorem mfderiv_expMap_smul
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t₀ : ℝ)
    (ht : (show TangentSpace I p from t₀ • a) ∈ expDomain (I := I) g p) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ (1 : ℝ)
      = mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (t₀ • a)
          (show TangentSpace I p from a) := by
  have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) t₀) :=
    (contMDiffAt_expMap (I := I) g p ht).mdifferentiableAt (by decide)
  have hsmul_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => u • a) :=
      contMDiff_id.smul contMDiff_const
    exact hs.contMDiffAt.mdifferentiableAt (by decide)
  have hcomp : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘
        (fun u : ℝ => u • a) := rfl
  rw [hcomp, mfderiv_comp t₀ hexp_mdiff hsmul_mdiff]
  have hlaunch : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun u : ℝ => u • a)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) t₀ := by
      exact (hasFDerivAt_id (t₀ : ℝ)).smul_const a
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) (1 : ℝ) = a
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  exact (ContinuousLinearMap.comp_apply _ _ _).trans
    (congrArg
      (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (t₀ • a))
      hlaunch)

theorem isOpen_expDomain
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (expDomain (I := I) g p) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  obtain ⟨U, hU_open, hvU, _F, _hF, hdom, _heq⟩ :=
    exists_contMDiff_eq_expMap_nhds (I := I) g p hv
  exact Filter.mem_of_superset (hU_open.mem_nhds hvU) hdom

theorem contMDiffOn_expMap
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w))
      (expDomain (I := I) g p) :=
  fun _ hv => (contMDiffAt_expMap (I := I) g p hv).contMDiffWithinAt

theorem exists_contMDiff_extension_expMap_smul
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {r : ℝ} (hr : r • v ∈ expDomain g p) :
    ∃ Γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ Γ ∧
      ∀ t ∈ uIcc 0 r, Γ =ᶠ[𝓝 t] (fun s => expMap g p (s • v)) := by
  let U : Set ℝ := {t | t • v ∈ expDomain g p}
  have hU : IsOpen U :=
    (isOpen_expDomain g p).preimage (continuous_id.smul continuous_const)
  obtain ⟨η, J, hJ, hconn, h0, hrJ, hη⟩ := smul_mem_expDomain_iff.mp hr
  have hseg : uIcc 0 r ⊆ U := by
    intro t ht
    exact smul_mem_expDomain_iff.mpr
      ⟨η, J, hJ, hconn, h0, hconn.ordConnected.uIcc_subset h0 hrJ ht, hη⟩
  let vE : E := v
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => s • vE) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_id.smul contDiff_const
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : ℕ∞)
      (fun s => expMap g p (s • v)) U :=
    (contMDiffOn_expMap g p).comp hline.contMDiffOn (fun _ ht => ht)
  exact hcurve.exists_extension_uIcc hU hseg

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
