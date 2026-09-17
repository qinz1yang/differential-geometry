import DifferentialGeometry.Topology.Manifold.AddCircle.AffinePeriodicLift
import DifferentialGeometry.Analysis.Calculus.Inverse.InjectiveParameterizedInverse
import DifferentialGeometry.Topology.Compactness.UniformBounds
import DifferentialGeometry.Topology.Manifold.AddCircle.PeriodicExtension
import DifferentialGeometry.Topology.Manifold.AddCircle.VectorField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Reparametrization
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

noncomputable section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_extended_affine_periodic_lift
    {a b : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ Icc a b))
    (hp : ∀ p ∈ univ ×ˢ Icc a b, g (p.1 + 1, p.2) = g p + 1)
    (hinit : ∀ x, g (x, a) = x) (hab : a ≤ b) :
    ∃ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F ∧
      (∀ t x, F (t, x + 1) = F (t, x) + 1) ∧
      (∀ t ∈ Icc a b, ∀ x, F (t, x) = g (x, t)) ∧
      ∀ x, F (a, x) = x := by
  let beta : ℝ → ℝ → ℝ := fun t x => g (x, t) - x
  have hbeta : ContDiffOn ℝ ∞ (Function.uncurry beta) (Icc a b ×ˢ univ) :=
    (hg.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩)).sub contDiffOn_snd
  have hbper : ∀ t ∈ Icc a b, Periodic (beta t) 1 := by
    intro t ht x
    change g (x + 1, t) - (x + 1) = g (x, t) - x
    rw [hp (x, t) ⟨mem_univ x, ht⟩]
    ring
  obtain ⟨gamma, hgamma, hgammaeq⟩ :=
    AddCircle.exists_contMDiff_extension_of_periodic hbeta hbper
  let F : ℝ × ℝ → ℝ := fun p => p.2 + gamma (p.1, (p.2 : AddCircle (1 : ℝ)))
  have hF : ContDiff ℝ ∞ F := by
    have hcomp := hgamma.comp
      (contMDiff_fst.prodMk (AddCircle.contMDiff_coe.comp contMDiff_snd))
    have hreal : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => gamma (p.1, (p.2 : AddCircle (1 : ℝ)))) := by
      rw [← contMDiff_iff_contDiff, ← chartedSpaceSelf_prod,
        modelWithCornersSelf_prod]
      exact hcomp
    exact contDiff_snd.add hreal
  have heq : ∀ t ∈ Icc a b, ∀ x, F (t, x) = g (x, t) := by
    intro t ht x
    change x + gamma (t, (x : AddCircle (1 : ℝ))) = _
    rw [hgammaeq t ht x]
    dsimp only [beta]
    ring
  refine ⟨F, hF, ?_, heq, fun x => (heq a ⟨le_rfl, hab⟩ x).trans (hinit x)⟩
  intro t x
  dsimp only [F]
  rw [AddCircle.coe_add_period]
  ring

private theorem exists_open_pos_deriv_of_affine_periodic_initial_identity
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t x, F (t, x + 1) = F (t, x) + 1)
    {a : ℝ} (hinit : ∀ x, F (a, x) = x) :
    ∃ V : Set ℝ, IsOpen V ∧ a ∈ V ∧
      ∀ t ∈ V, ∀ x, 0 < deriv (fun y => F (t, y)) x := by
  let D : ℝ × ℝ → ℝ := fun p => fderiv ℝ F p (0, 1)
  have hD : ContDiff ℝ ∞ D :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDder (t x : ℝ) : deriv (fun y => F (t, y)) x = D (t, x) := by
    exact ((hF.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))).deriv
  have hDper : ∀ t, Periodic (fun x => D (t, x)) 1 := by
    intro t x
    change D (t, x + 1) = D (t, x)
    rw [← hDder t (x + 1), ← deriv_comp_add_const]
    have heq : (fun y => F (t, y + 1)) = fun y => F (t, y) + 1 := funext (hper t)
    rw [heq, deriv_add_const, hDder]
  let d : ℝ × AddCircle (1 : ℝ) → ℝ := fun p => (hDper p.1).lift p.2
  have hd : Continuous d :=
    (AddCircle.contMDiff_periodic_lift_family hD hDper).continuous
  have hda (z : AddCircle (1 : ℝ)) : d (a, z) = 1 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change D (a, x) = 1
    rw [← hDder]
    have heq : (fun y => F (a, y)) = id := funext hinit
    rw [heq, deriv_id]
  obtain ⟨m, hm, V, hV, hbound⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound
      (K := (univ : Set (AddCircle (1 : ℝ)))) (q₀ := a) isCompact_univ
      (d := fun p : AddCircle (1 : ℝ) × ℝ => d (p.2, p.1))
      (fun _ _ => hd.continuousAt.comp
        (continuousAt_snd.prodMk continuousAt_fst))
      (fun z _ => by rw [hda]; norm_num)
  obtain ⟨U, hUV, hU, haU⟩ := mem_nhds_iff.mp hV
  refine ⟨U, hU, haU, ?_⟩
  intro t ht x
  rw [hDder]
  exact hm.trans_le (hbound (x : AddCircle (1 : ℝ)) (mem_univ _) t (hUV ht))

private def homeomorph_of_affine_periodic_inverse
    (F R : ℝ → ℝ) (hF : Continuous F)
    (hpF : ∀ x, F (x + 1) = F x + 1)
    (hpR : ∀ x, R (x + 1) = R x + 1)
    (hleft : LeftInverse R F) (hright : RightInverse R F) :
    AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ) := by
  have hperF : Periodic (fun x => (F x : AddCircle (1 : ℝ))) 1 := by
    intro x
    change (F (x + 1) : AddCircle (1 : ℝ)) = (F x : AddCircle (1 : ℝ))
    rw [hpF, AddCircle.coe_add_period]
  have hperR : Periodic (fun x => (R x : AddCircle (1 : ℝ))) 1 := by
    intro x
    change (R (x + 1) : AddCircle (1 : ℝ)) = (R x : AddCircle (1 : ℝ))
    rw [hpR, AddCircle.coe_add_period]
  let e : AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) :=
    { toFun := hperF.lift
      invFun := hperR.lift
      left_inv := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
        change ((R (F x) : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ))
        rw [hleft]
      right_inv := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
        change ((F (R x) : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ))
        rw [hright] }
  have he : Continuous e :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hF).quotient_liftOn' _
  exact he.homeoOfEquivCompactToT2

private theorem exists_smooth_homeomorph_family_of_affine_periodic_initial_identity
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t x, F (t, x + 1) = F (t, x) + 1)
    {a : ℝ} (hinit : ∀ x, F (a, x) = x) :
    ∃ V : Set ℝ, IsOpen V ∧ a ∈ V ∧
      ∃ P : ℝ → (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)),
        (∀ t ∈ V, ∀ x : ℝ, P t (x : AddCircle (1 : ℝ)) =
          (F (t, x) : AddCircle (1 : ℝ))) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × AddCircle (1 : ℝ) => P p.1 p.2) (V ×ˢ univ) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × AddCircle (1 : ℝ) => (P p.1).symm p.2) (V ×ˢ univ) := by
  classical
  obtain ⟨V, hV, haV, hpos⟩ :=
    exists_open_pos_deriv_of_affine_periodic_initial_identity hF hper hinit
  have hslice (t : ℝ) : ContDiff ℝ ∞ (fun x => F (t, x)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hbij (t : ℝ) (ht : t ∈ V) : Bijective (fun x => F (t, x)) := by
    have hmono := strictMono_of_deriv_pos (hpos t ht)
    let L : CircleDeg1Lift :=
      { toFun := fun x => F (t, x)
        monotone' := hmono.monotone
        map_add_one' := hper t }
    exact ⟨hmono.injective, (CircleDeg1Lift.continuous_iff_surjective L).mp
      (hslice t).continuous⟩
  have hvertical (t : ℝ) (ht : t ∈ V) (x : ℝ) : fderiv ℝ F (t, x) (0, 1) ≠ 0 := by
    have hd := ((hF.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))).deriv
    rw [← hd]
    exact (hpos t ht x).ne'
  obtain ⟨R, hR, hleft, hright⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_inverse_of_bijective
      hV hF.contDiffOn hbij hvertical
  have hRp (t : ℝ) (ht : t ∈ V) (x : ℝ) : R (t, x + 1) = R (t, x) + 1 := by
    apply (hbij t ht).injective
    change F (t, R (t, x + 1)) = F (t, R (t, x) + 1)
    rw [hright t ht (x + 1), hper, hright t ht x]
  let P : ℝ → (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) := fun t =>
    if ht : t ∈ V then homeomorph_of_affine_periodic_inverse
      (fun x => F (t, x)) (fun x => R (t, x)) (hslice t).continuous
      (hper t) (hRp t ht) (hleft t ht) (hright t ht)
    else Homeomorph.refl _
  have hP (t : ℝ) (ht : t ∈ V) (x : ℝ) :
      P t (x : AddCircle (1 : ℝ)) = (F (t, x) : AddCircle (1 : ℝ)) := by
    simp only [P, dif_pos ht]
    rfl
  have hPinv (t : ℝ) (ht : t ∈ V) (x : ℝ) :
      (P t).symm (x : AddCircle (1 : ℝ)) = (R (t, x) : AddCircle (1 : ℝ)) := by
    simp only [P, dif_pos ht]
    rfl
  refine ⟨V, hV, haV, P, hP, ?_, ?_⟩
  · apply AddCircle.contMDiffOn_of_comp_coe
    have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ℝ => (F p : AddCircle (1 : ℝ))) (V ×ˢ univ) := by
      have hh := AddCircle.contMDiff_coe.comp hF.contMDiff
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hh.contMDiffOn
    exact hh.congr (fun p hp => hP p.1 hp.1 p.2)
  · apply AddCircle.contMDiffOn_of_comp_coe
    have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ℝ => (R p : AddCircle (1 : ℝ))) (V ×ˢ univ) := by
      have hh := AddCircle.contMDiff_coe.comp_contMDiffOn hR.contMDiffOn
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hh
    exact hh.congr (fun p hp => hPinv p.1 hp.1 p.2)

theorem CurveMap.SmoothOn.exists_reparametrization_of_initial_identity
    {c : CurveMap (AddCircle (1 : ℝ))} {a b : ℝ} (hab : a < b)
    (hc : c.SmoothOn (I := 𝓘(ℝ, ℝ)) (Icc a b))
    (hinit : ∀ z, c z a = z) :
    ∃ tau > 0, a + tau ≤ b ∧ ∃ P : CircleReparametrization (Icc a (a + tau)),
      ∀ t ∈ Icc a (a + tau), ∀ z, P.map t z = c z t := by
  obtain ⟨g, hg, hglift, hgperiod, hginitial⟩ :=
    AddCircle.exists_contDiffOn_affine_periodic_lift_of_initial_identity hab.le hc
      (fun p => by simp only [CurveMap.lift, AddCircle.coe_add_period])
      (fun x => hinit (x : AddCircle (1 : ℝ)))
  obtain ⟨F, hF, hFperiod, hFg, hFinitial⟩ :=
    exists_extended_affine_periodic_lift hg hgperiod hginitial hab.le
  obtain ⟨V, hV, haV, P, hP, hPsmooth, hPinverse⟩ :=
    exists_smooth_homeomorph_family_of_affine_periodic_initial_identity hF hFperiod hFinitial
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let tau := min (r / 2) ((b - a) / 2)
  have htau : 0 < tau := lt_min (half_pos hr) (half_pos (sub_pos.mpr hab))
  have htaub : a + tau ≤ b := by
    have h := min_le_right (r / 2) ((b - a) / 2)
    dsimp only [tau]
    linarith
  have hsubV : Icc a (a + tau) ⊆ V := by
    intro t ht
    apply hrV
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have h := min_le_left (r / 2) ((b - a) / 2)
    have htupper := ht.2
    dsimp only [tau] at htupper
    linarith
  let Q : CircleReparametrization (Icc a (a + tau)) :=
    CircleReparametrization.ofContMDiffOn P
      (hPsmooth.mono (prod_mono hsubV (subset_refl _)))
      (hPinverse.mono (prod_mono hsubV (subset_refl _)))
  refine ⟨tau, htau, htaub, Q, ?_⟩
  intro t ht z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  change P t (x : AddCircle (1 : ℝ)) = c (x : AddCircle (1 : ℝ)) t
  rw [hP t (hsubV ht) x, hFg t ⟨ht.1, ht.2.trans htaub⟩ x]
  exact hglift (x, t) ⟨mem_univ x, ht.1, ht.2.trans htaub⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
