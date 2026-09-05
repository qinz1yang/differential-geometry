import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CompactTrajectory

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_curveAt [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ curveAt v hcomplete p.2 p.1) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hv1 : CMDiff 1 (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hslice (s : ℝ) :
      ContMDiff I I ∞ (fun x : M ↦ curveAt v hcomplete x s) := by
    let R : ℝ := |s| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hzero : (0 : ℝ) ∈ Ioo (-R) R := by constructor <;> linarith
    have hs : s ∈ Ioo (-R) R := by
      constructor
      · dsimp [R]
        linarith [neg_abs_le s]
      · dsimp [R]
        linarith [le_abs_self s]
    have hsm := flow_slice_smooth (I := I) (v := v) hv
      (D := Set.univ) isOpen_univ (a := -R) (b := R) (t₀ := 0) hzero
      (F := fun x t ↦ curveAt v hcomplete x t)
      (fun x _ ↦ curveAt_zero v hcomplete x)
      (fun x _ ↦ (curveAt_integralCurve v hcomplete x).continuous.continuousOn)
      (fun x _ t _ ↦ curveAt_integralCurve v hcomplete x t)
    exact contMDiffOn_univ.mp (hsm s hs)
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M ↦
        (TotalSpace.mk' E q.2 (v q.2) : TangentBundle I M)) :=
    hv.comp contMDiff_snd
  rintro ⟨t₀, x₀⟩
  let y₀ : M := curveAt v hcomplete x₀ t₀
  rcases local_flow_jointSmooth_and_integralCurve
      (E := E) (I := I) (M := M) (X := fun _ : ℝ ↦ v) htime (0 : ℝ) y₀ with
    ⟨U, hUopen, hyU, T, hT, Ψ, hΨinit, hΨsm, hΨbare⟩
  have hΨsm' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M ↦ Ψ q.2 q.1) (Ioo (-T) T ×ˢ U) := by
    simpa [sub_eq_add_neg] using hΨsm
  have hΨbare' : ∀ p ∈ U, ∀ t ∈ Ioo (-T) T,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ Ψ p s) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Ψ p t))) := by
    simpa [sub_eq_add_neg] using hΨbare
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := by constructor <;> linarith
  have hagree : ∀ p ∈ U, ∀ t ∈ Ioo (-T) T,
      curveAt v hcomplete p t = Ψ p t := by
    intro p hp t ht
    have hcurve : IsMIntegralCurveOn (curveAt v hcomplete p) v (Ioo (-T) T) :=
      (curveAt_integralCurve v hcomplete p).isMIntegralCurveOn _
    have hlocal : IsMIntegralCurveOn (Ψ p) v (Ioo (-T) T) :=
      fun s hs ↦ (hΨbare' p hp s hs).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := 0) (a := -T) (b := T) hzero hv1 hcurve hlocal (by
        rw [curveAt_zero v hcomplete p]
        exact (hΨinit p hp).symm)
    exact heq ht
  have hyU' : curveAt v hcomplete x₀ t₀ ∈ U := by simpa only [y₀] using hyU
  have hslice_t₀ := hslice t₀
  have hstate : {x : M | curveAt v hcomplete x t₀ ∈ U} ∈ 𝓝 x₀ :=
    hslice_t₀.continuous.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hyU')
  let V : Set (ℝ × M) := Ioo (t₀ - T) (t₀ + T) ×ˢ
    {x : M | curveAt v hcomplete x t₀ ∈ U}
  have hVnhds : V ∈ 𝓝 (t₀, x₀) := by
    exact prod_mem_nhds
      (isOpen_Ioo.mem_nhds (by constructor <;> linarith)) hstate
  have hVeq : ∀ t x, (t, x) ∈ V →
      curveAt v hcomplete x t =
        Ψ (curveAt v hcomplete x t₀) (t - t₀) := by
    intro t x htx
    have ht : t - t₀ ∈ Ioo (-T) T := by
      dsimp only [V] at htx
      constructor <;> linarith [htx.1.1, htx.1.2]
    have hstep : curveAt v hcomplete x t =
        curveAt v hcomplete (curveAt v hcomplete x t₀) (t - t₀) := by
      have h := curveAt_add v hv1 hcomplete x t₀ (t - t₀)
      rw [show t₀ + (t - t₀) = t by ring] at h
      exact h
    rw [hstep]
    exact hagree (curveAt v hcomplete x t₀) htx.2 (t - t₀) ht
  have hmain : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ Ψ (curveAt v hcomplete p.2 t₀) (p.1 - t₀))
      (t₀, x₀) := by
    have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ p.1 - t₀) (t₀, x₀) := by
      have hsub : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (fun t : ℝ ↦ t - t₀) t₀ :=
        (contDiff_id.sub contDiff_const).contDiffAt.contMDiffAt
      have hcomp := ContMDiffAt.comp (x := (t₀, x₀))
        (M := ℝ × M) (M' := ℝ) (M'' := ℝ)
        (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
        (f := Prod.fst) (g := fun t : ℝ ↦ t - t₀) hsub
        (contMDiffAt_fst (p := (t₀, x₀)))
      simpa [Function.comp_def] using hcomp
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M ↦ curveAt v hcomplete p.2 t₀) (t₀, x₀) := by
      have hcomp := ContMDiffAt.comp (x := (t₀, x₀))
        (M := ℝ × M) (M' := M) (M'' := M)
        (I := 𝓘(ℝ, ℝ).prod I) (I' := I) (I'' := I)
        (f := Prod.snd) (g := fun x : M ↦ curveAt v hcomplete x t₀)
        hslice_t₀.contMDiffAt (contMDiffAt_snd (p := (t₀, x₀)))
      simpa [Function.comp_def] using hcomp
    have hpair := hfst.prodMk hsnd
    have hp : (t₀ - t₀, curveAt v hcomplete x₀ t₀) ∈ Ioo (-T) T ×ˢ U :=
      ⟨by simpa using hzero, hyU'⟩
    have hΨat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M ↦ Ψ q.2 q.1)
        (t₀ - t₀, curveAt v hcomplete x₀ t₀) :=
      (hΨsm' _ hp).contMDiffAt
        (prod_mem_nhds (isOpen_Ioo.mem_nhds hp.1) (hUopen.mem_nhds hyU'))
    have hcomp := hΨat.comp (t₀, x₀) hpair
    simpa [Function.comp_def] using hcomp
  have heq : (fun p : ℝ × M ↦ curveAt v hcomplete p.2 p.1) =ᶠ[𝓝 (t₀, x₀)]
      (fun p : ℝ × M ↦ Ψ (curveAt v hcomplete p.2 t₀) (p.1 - t₀)) :=
    Filter.eventuallyEq_of_mem hVnhds (fun p hp ↦ hVeq p.1 p.2 hp)
  exact hmain.congr_of_eventuallyEq heq

noncomputable def curveAtDiffeomorph [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t : ℝ) : Diffeomorph I I M M ∞ := by
  have hv1 : CMDiff 1 (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hsmooth (s : ℝ) :
      ContMDiff I I ∞ (fun x : M ↦ curveAt v hcomplete x s) := by
    have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M ↦ (s, x)) :=
      contMDiff_const.prodMk contMDiff_id
    simpa [Function.comp_def] using
      (contMDiff_curveAt v hv hcomplete).comp hpair
  exact
    { toEquiv :=
        { toFun := fun x ↦ curveAt v hcomplete x t
          invFun := fun x ↦ curveAt v hcomplete x (-t)
          left_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x t (-t)
            simpa only [add_neg_cancel, curveAt_zero] using h.symm
          right_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x (-t) t
            simpa only [neg_add_cancel, curveAt_zero] using h.symm }
      contMDiff_toFun := hsmooth t
      contMDiff_invFun := hsmooth (-t) }

section Diffeomorph

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I I.tangent ∞
    (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

@[simp]
theorem curveAtDiffeomorph_apply (t : ℝ) (x : M) :
    curveAtDiffeomorph v hv hcomplete t x = curveAt v hcomplete x t := rfl

@[simp]
theorem curveAtDiffeomorph_symm (t : ℝ) :
    (curveAtDiffeomorph v hv hcomplete t).symm =
      curveAtDiffeomorph v hv hcomplete (-t) := by
  ext x
  rfl

@[simp]
theorem curveAtDiffeomorph_zero :
    curveAtDiffeomorph v hv hcomplete 0 = Diffeomorph.refl I M ∞ := by
  ext x
  exact curveAt_zero v hcomplete x

theorem curveAtDiffeomorph_add (s t : ℝ) :
    curveAtDiffeomorph v hv hcomplete (s + t) =
      (curveAtDiffeomorph v hv hcomplete s).trans
        (curveAtDiffeomorph v hv hcomplete t) := by
  ext x
  exact curveAt_add v (hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
    hcomplete x s t

end Diffeomorph

end DifferentialGeometry.Analysis.ODE
