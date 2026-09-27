import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

noncomputable section

open scoped Manifold ContDiff

namespace Diffeomorph

open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem suspension_time (V : ℝ × E → E)
    (hc : ∀ p : ℝ × E, ∃ γ : ℝ → ℝ × E, γ 0 = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, ℝ × E)) γ (fun q => (1, V q))) (p : ℝ × E) (t : ℝ) :
    (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc p t).1 = p.1 + t := by
  let γ := curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc p
  have hd : ∀ u : ℝ, HasDerivAt (fun s => (γ s).1) 1 u := by
    intro u
    have h : HasFDerivAt γ ((1 : ℝ →L[ℝ] ℝ).smulRight (1, V (γ u))) u :=
      (curveAt_integralCurve (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc p u).hasFDerivAt
    have h' : HasDerivAt γ (1, V (γ u)) u := by simpa using h.hasDerivAt
    exact h'.fst
  have hz : ∀ u : ℝ, HasDerivAt (fun s => (γ s).1 - s) 0 u := by
    intro u
    convert (hd u).sub (hasDerivAt_id u) using 1 <;> first | rfl | norm_num
  have h := is_const_of_deriv_eq_zero (fun u => (hz u).differentiableAt)
    (fun u => (hz u).deriv) t 0
  have h₀ : γ 0 = p := curveAt_zero _ hc p
  change (γ t).1 = p.1 + t
  simp only [h₀, sub_zero] at h
  linarith

private theorem suspension_complete [CompleteSpace E]
    (V : ℝ × E → E) (hV : ContDiff ℝ 1 V) (hs : HasCompactSupport V) :
    ∀ p : ℝ × E, ∃ γ : ℝ → ℝ × E, γ 0 = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, ℝ × E)) γ (fun q => (1, V q)) := by
  apply exists_globalIntegralCurve_of_hasCompactSupport_sub_const
    (fun q : ℝ × E => (1, V q)) (contDiff_const.prodMk hV) (1, 0)
  simpa only [Prod.mk_sub_mk, sub_self, sub_zero, Function.comp_def] using
    hs.comp_left (g := fun z : E => ((0 : ℝ), z)) rfl

private theorem suspension_transport_comp (V : ℝ × E → E) (hV : ContDiff ℝ 1 V)
    (hc : ∀ p : ℝ × E, ∃ γ : ℝ → ℝ × E, γ 0 = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, ℝ × E)) γ (fun q => (1, V q)))
    (s t u : ℝ) (x : E) :
    (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (s, x) (u - s)).2 =
      (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc
        (t, (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc
          (s, x) (t - s)).2) (u - t)).2 := by
  let W : (p : ℝ × E) → TangentSpace 𝓘(ℝ, ℝ × E) p := fun q => (1, V q)
  have hW : ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ × E)).tangent 1
      (fun p : ℝ × E => (⟨p, W p⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × E))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (contDiff_const.prodMk hV)
  have hp : curveAt W hc (s, x) (t - s) = (t, (curveAt W hc (s, x) (t - s)).2) := by
    apply Prod.ext
    · simpa using suspension_time V hc (s, x) (t - s)
    · rfl
  have h := curveAt_add W hW hc (s, x) (t - s) (u - t)
  rw [show (t - s) + (u - t) = u - s by ring, hp] at h
  exact congrArg Prod.snd h

private theorem contDiff_suspension_transport [FiniteDimensional ℝ E]
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V)
    (hc : ∀ p : ℝ × E, ∃ γ : ℝ → ℝ × E, γ 0 = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, ℝ × E)) γ (fun q => (1, V q))) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ × E =>
      (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc
        (p.1, p.2.2) (p.2.1 - p.1)).2) := by
  have hW : ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ × E)).tangent ∞
      (fun p : ℝ × E => (⟨p, (1, V p)⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × E))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (contDiff_const.prodMk hV)
  have hj : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E) =>
      curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc p.2 p.1) := by
    apply ContMDiff.contDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiff_curveAt _ hW hc
  exact (hj.comp ((contDiff_fst.comp contDiff_snd |>.sub contDiff_fst).prodMk
    (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)))).snd

variable [FiniteDimensional ℝ E] (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V)
  (hs : HasCompactSupport V)

def timeDependentFlow (s t : ℝ) : E ≃ₘ[ℝ] E := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := suspension_complete V (hV.of_le (by simp)) hs
  let T := fun s t x =>
    (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (s, x) (t - s)).2
  have hj := contDiff_suspension_transport V hV hc
  refine
    { toEquiv :=
        { toFun := T s t
          invFun := T t s
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := (hj.comp (contDiff_const.prodMk
        (contDiff_const.prodMk contDiff_id))).contMDiff
      contMDiff_invFun := (hj.comp (contDiff_const.prodMk
        (contDiff_const.prodMk contDiff_id))).contMDiff }
  · intro x
    have h := suspension_transport_comp V (hV.of_le (by simp)) hc s t s x
    rw [sub_self] at h
    exact h.symm.trans (congrArg Prod.snd
      (curveAt_zero (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (s, x)))
  · intro x
    have h := suspension_transport_comp V (hV.of_le (by simp)) hc t s t x
    rw [sub_self] at h
    exact h.symm.trans (congrArg Prod.snd
      (curveAt_zero (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (t, x)))

theorem timeDependentFlow_apply (s t : ℝ) (x : E) :
    timeDependentFlow V hV hs s t x =
      (curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) (by
        let : CompleteSpace E := FiniteDimensional.complete ℝ E
        exact suspension_complete V (hV.of_le (by simp)) hs) (s, x) (t - s)).2 := rfl

@[simp] theorem timeDependentFlow_refl (s : ℝ) :
    timeDependentFlow V hV hs s s = Diffeomorph.refl 𝓘(ℝ, E) E ∞ := by
  apply Diffeomorph.ext
  intro x
  rw [timeDependentFlow_apply, sub_self]
  exact congrArg Prod.snd (curveAt_zero (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) _ (s, x))

@[simp] theorem timeDependentFlow_symm (s t : ℝ) :
    (timeDependentFlow V hV hs s t).symm = timeDependentFlow V hV hs t s := by
  apply Diffeomorph.ext
  intro x
  rfl

theorem timeDependentFlow_trans (s t u : ℝ) :
    (timeDependentFlow V hV hs s t).trans (timeDependentFlow V hV hs t u) =
      timeDependentFlow V hV hs s u := by
  apply Diffeomorph.ext
  intro x
  exact (suspension_transport_comp V (hV.of_le (by simp)) _ s t u x).symm

theorem contDiff_timeDependentFlow :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ × E => timeDependentFlow V hV hs p.1 p.2.1 p.2.2) :=
  contDiff_suspension_transport V hV _

theorem contDiff_timeDependentFlow_symm :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ × E => (timeDependentFlow V hV hs p.1 p.2.1).symm p.2.2) := by
  exact (contDiff_timeDependentFlow V hV hs).comp
    ((contDiff_fst.comp contDiff_snd).prodMk
      (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)))

theorem isIntegralCurve_timeDependentFlow (s : ℝ) (x : E) :
    IsIntegralCurve (fun t => timeDependentFlow V hV hs s t x) (fun t y => V (t, y)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := suspension_complete V (hV.of_le (by simp)) hs
  let γ := curveAt (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (s, x)
  intro t
  have hd : HasFDerivAt γ ((1 : ℝ →L[ℝ] ℝ).smulRight (1, V (γ (t - s)))) (t - s) :=
    (curveAt_integralCurve (I := 𝓘(ℝ, ℝ × E)) (fun q => (1, V q)) hc (s, x) (t - s)).hasFDerivAt
  have hd' : HasDerivAt γ (1, V (γ (t - s))) (t - s) := by simpa using hd.hasDerivAt
  have hsnd : HasDerivAt (fun u => (γ u).2) (V (γ (t - s))) (t - s) := hd'.snd
  have hshift := hsnd.scomp t ((hasDerivAt_id t).sub_const s)
  have hp : γ (t - s) = (t, (γ (t - s)).2) := by
    apply Prod.ext
    · simpa using suspension_time V hc (s, x) (t - s)
    · rfl
  have hv : V (γ (t - s)) = V (t, (γ (t - s)).2) := congrArg V hp
  rw [hv] at hshift
  change HasDerivAt (fun u => (γ (u - s)).2) (V (t, (γ (t - s)).2)) t
  simpa only [Function.comp_def, id_eq, one_smul] using hshift

open Set in
theorem timeDependentFlow_eqOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X : ℝ × V → V) (hX : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {γ : ℝ → V} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ∀ t ∈ Ico a b, HasDerivWithinAt γ (X (t, γ t)) (Ici t) t) :
    EqOn (fun t => Diffeomorph.timeDependentFlow X hX hXc a t (γ a)) γ (Icc a b) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hX (by simp)
  have hslice (t : ℝ) : LipschitzWith L (fun x : V => X (t, x)) := by
    simpa only [mul_one, Function.comp_def] using hL.comp (LipschitzWith.prodMk_left t)
  have hflow := Diffeomorph.isIntegralCurve_timeDependentFlow X hX hXc a (γ a)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t _ => (hslice t).lipschitzOnWith)
    (continuous_iff_continuousAt.mpr (fun t => (hflow t).continuousAt)).continuousOn
    (fun t _ => (hflow t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    hγ hγ' (fun _ _ => mem_univ _)
    (by simp only [Diffeomorph.timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq])

theorem timeDependentFlow_apply_eq_of_isIntegralCurve {γ : ℝ → E}
    (hγ : IsIntegralCurve γ (fun t x => V (t, x))) (s t : ℝ) :
    timeDependentFlow V hV hs s t (γ s) = γ t := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hV (by simp)
  have hslice (u : ℝ) : LipschitzWith K (fun x : E => V (u, x)) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
      hK.dist_le_mul (u, x) (u, y)
  have hflow := isIntegralCurve_timeDependentFlow V hV hs s (γ s)
  have heq := ODE_solution_unique_univ (s := fun _ => Set.univ)
    (fun u => (hslice u).lipschitzOnWith)
    (fun u => ⟨hflow u, Set.mem_univ _⟩)
    (fun u => ⟨hγ u, Set.mem_univ _⟩)
    (t₀ := s) (by simp only [timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq])
  exact congrFun heq t

theorem timeDependentFlow_apply_eq_self_of_forall_eq_zero {x : E}
    (hx : ∀ t : ℝ, V (t, x) = 0) (s t : ℝ) : timeDependentFlow V hV hs s t x = x := by
  apply timeDependentFlow_apply_eq_of_isIntegralCurve V hV hs (γ := fun _ => x) ?_ s t
  intro u
  change HasDerivAt (fun _ : ℝ => x) (V (u, x)) u
  rw [hx]
  exact hasDerivAt_const u x

theorem timeDependentFlow_eqOn_compl_image_tsupport (s t : ℝ) :
    Set.EqOn (timeDependentFlow V hV hs s t) id (Prod.snd '' tsupport V)ᶜ ∧
      Set.EqOn (timeDependentFlow V hV hs s t).symm id (Prod.snd '' tsupport V)ᶜ := by
  have hz : ∀ x ∉ Prod.snd '' tsupport V, ∀ u : ℝ, V (u, x) = 0 := by
    intro x hx u
    apply image_eq_zero_of_notMem_tsupport
    exact fun hp => hx ⟨(u, x), hp, rfl⟩
  constructor
  · intro x hx
    exact timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hs (hz x hx) s t
  · intro x hx
    rw [timeDependentFlow_symm]
    exact timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hs (hz x hx) t s

theorem timeDependentFlow_exists_isCompact_eqOn :
    ∃ K : Set E, IsCompact K ∧ ∀ s t : ℝ,
      Set.EqOn (timeDependentFlow V hV hs s t) id Kᶜ ∧
        Set.EqOn (timeDependentFlow V hV hs s t).symm id Kᶜ :=
  ⟨Prod.snd '' tsupport V, hs.image continuous_snd,
    timeDependentFlow_eqOn_compl_image_tsupport V hV hs⟩

theorem timeDependentFlow_eq_refl_of_eq_zero_on (s t : ℝ)
    (hz : ∀ u ∈ Set.uIcc s t, ∀ x, V (u, x) = 0) :
    timeDependentFlow V hV hs s t = Diffeomorph.refl 𝓘(ℝ, E) E ∞ := by
  apply Diffeomorph.ext
  intro x
  let γ := fun u => timeDependentFlow V hV hs s u x
  have hγ : IsIntegralCurve γ (fun u y => V (u, y)) :=
    isIntegralCurve_timeDependentFlow V hV hs s x
  have hcont : ContinuousOn γ (Set.Icc (min s t) (max s t)) :=
    (continuous_iff_continuousAt.mpr (fun u => (hγ u).continuousAt)).continuousOn
  have hconst := constant_of_has_deriv_right_zero hcont (fun u hu => by
    have heq : V (u, γ u) = 0 := hz u ⟨hu.1, hu.2.le⟩ (γ u)
    rw [← heq]
    exact (hγ u).hasDerivWithinAt (s := Set.Ici u))
  have ht := hconst t ⟨min_le_right _ _, le_max_right _ _⟩
  have hstart := hconst s ⟨min_le_left _ _, le_max_left _ _⟩
  change γ t = x
  calc
    γ t = γ s := ht.trans hstart.symm
    _ = x := by simp only [γ, timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq]

theorem map_timeDependentFlow_eq_of_map_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ p, L (V p) = 0) (s t : ℝ) (x : E) :
    L (timeDependentFlow V hV hs s t x) = L x := by
  have hd (u : ℝ) : HasDerivAt (fun v => L (timeDependentFlow V hV hs s v x)) 0 u := by
    simpa only [hL, Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt u
      (isIntegralCurve_timeDependentFlow V hV hs s x u)
  have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  simpa only [timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq] using h

theorem timeDependentFlow_sub_mem_of_mem_submodule (S : Submodule ℝ E)
    (hS : ∀ p, V p ∈ S) (s t : ℝ) (x : E) :
    timeDependentFlow V hV hs s t x - x ∈ S := by
  let : IsClosed (S : Set E) := S.closed_of_finiteDimensional
  have h := map_timeDependentFlow_eq_of_map_eq_zero V hV hs S.mkQL
    (fun p => by exact (Submodule.Quotient.mk_eq_zero S).mpr (hS p)) s t x
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (timeDependentFlow V hV hs s t x - x) = 0
  rw [map_sub, h, sub_self]

end Diffeomorph

end
