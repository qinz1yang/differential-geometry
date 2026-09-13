import DifferentialGeometry.Topology.Manifold.SphereRadialExtension
import DifferentialGeometry.Analysis.Calculus.Cutoff.Basic

set_option autoImplicit false

noncomputable section

open Set Metric Manifold Module Filter Topology
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem exists_radialCutoff :
    ∃ cut : ℝ → ℝ, ContDiff ℝ ∞ cut ∧ cut 1 = 1 ∧
      (∀ r, r ≤ 1 / 2 → cut r = 0) ∧ (∀ r, 3 / 2 ≤ r → cut r = 0) := by
  obtain ⟨χ, hχ, hχ1, hχs, -⟩ := DifferentialGeometry.Analysis.exists_bump_one_on
    (E := ℝ) (K := ({1} : Set ℝ)) (U := Set.Ioo (1 / 2 : ℝ) (3 / 2))
    isCompact_singleton isOpen_Ioo (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      norm_num)
  refine ⟨χ, hχ, hχ1 (by simp), ?_, ?_⟩
  · intro r hr
    by_contra h
    exact absurd (hχs (subset_tsupport χ h)).1 (not_lt.mpr hr)
  · intro r hr
    by_contra h
    exact absurd (hχs (subset_tsupport χ h)).2 (not_lt.mpr hr)

theorem sphereRadialExtension_apply_sphere
    (f : sphere (0 : E) 1 → sphere (0 : E) 1) (v : sphere (0 : E) 1) :
    sphereRadialExtension f (v : E) = (f v : E) := by
  have hv : (v : E) ≠ 0 := ne_zero_of_mem_unit_sphere v
  have hd : (⟨‖(v : E)‖⁻¹ • (v : E),
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hv)⟩ : sphere (0 : E) 1) = v := by
    apply Subtype.ext
    simp only [norm_eq_of_mem_sphere v, inv_one, one_smul]
  rw [sphereRadialExtension_of_ne_zero f hv, hd, norm_eq_of_mem_sphere v, one_smul]

theorem exists_sphereRadialSuspension
    (A : ℝ → Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞)
    (hA : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞ fun q : ℝ × sphere (0 : E) 1 => A q.1 q.2)
    (hAi : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞ fun q : ℝ × sphere (0 : E) 1 => (A q.1).symm q.2)
    (hA0 : A 0 = Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x, ‖F x‖ = ‖x‖) ∧
      (∀ x, ‖x‖ ≤ 1 / 2 → F x = x) ∧
      (∀ x, 3 / 2 ≤ ‖x‖ → F x = x) ∧
      (∀ v : sphere (0 : E) 1, F (v : E) = (A 1 v : E)) := by
  obtain ⟨cut, hcut, hcut1, hcut0, hcut2⟩ := exists_radialCutoff
  let famA : ℝ → sphere (0 : E) 1 → sphere (0 : E) 1 := fun p z => A (cut p) z
  let famB : ℝ → sphere (0 : E) 1 → sphere (0 : E) 1 := fun p z => (A (cut p)).symm z
  let Ffun : E → E := fun x => sphereRadialExtension (famA ‖x‖) x
  let Gfun : E → E := fun x => sphereRadialExtension (famB ‖x‖) x
  have hcutc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ cut := hcut.contMDiff
  have hfamA : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × sphere (0 : E) 1 => famA q.1 q.2) := by
    have hmap : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
        (fun q : ℝ × sphere (0 : E) 1 => (cut q.1, q.2)) :=
      (hcutc.comp contMDiff_fst).prodMk contMDiff_snd
    exact hA.comp hmap
  have hfamB : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × sphere (0 : E) 1 => famB q.1 q.2) := by
    have hmap : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
        (fun q : ℝ × sphere (0 : E) 1 => (cut q.1, q.2)) :=
      (hcutc.comp contMDiff_fst).prodMk contMDiff_snd
    exact hAi.comp hmap
  have hA0fun : famA 0 = id := by
    funext z
    change A (cut 0) z = z
    rw [hcut0 0 (by norm_num), hA0]
    rfl
  have hB0fun : famB 0 = id := by
    funext z
    change (A (cut 0)).symm z = z
    rw [hcut0 0 (by norm_num), hA0]
    rfl
  have hfamA0 : ∀ {r : ℝ}, cut r = 0 → famA r = famA 0 := by
    intro r hr
    change (fun z => A (cut r) z) = (fun z => A (cut 0) z)
    rw [hr, hcut0 0 (by norm_num)]
  have hfamB0 : ∀ {r : ℝ}, cut r = 0 → famB r = famB 0 := by
    intro r hr
    change (fun z => (A (cut r)).symm z) = (fun z => (A (cut 0)).symm z)
    rw [hr, hcut0 0 (by norm_num)]
  have hFsmall : ∀ x : E, ‖x‖ ≤ 1 / 2 → Ffun x = x := by
    intro x hx
    rw [show Ffun x = sphereRadialExtension (famA ‖x‖) x from rfl,
      hfamA0 (hcut0 ‖x‖ hx), hA0fun, sphereRadialExtension_id]
    rfl
  have hFlarge : ∀ x : E, 3 / 2 ≤ ‖x‖ → Ffun x = x := by
    intro x hx
    rw [show Ffun x = sphereRadialExtension (famA ‖x‖) x from rfl,
      hfamA0 (hcut2 ‖x‖ hx), hA0fun, sphereRadialExtension_id]
    rfl
  have hGsmall : ∀ x : E, ‖x‖ ≤ 1 / 2 → Gfun x = x := by
    intro x hx
    rw [show Gfun x = sphereRadialExtension (famB ‖x‖) x from rfl,
      hfamB0 (hcut0 ‖x‖ hx), hB0fun, sphereRadialExtension_id]
    rfl
  have hFnrm : ∀ x : E, ‖Ffun x‖ = ‖x‖ := fun x => norm_sphereRadialExtension (famA ‖x‖) x
  have hGnrm : ∀ x : E, ‖Gfun x‖ = ‖x‖ := fun x => norm_sphereRadialExtension (famB ‖x‖) x
  have hF0 : Ffun 0 = 0 := by
    simp [Ffun, sphereRadialExtension]
  have hG0 : Gfun 0 = 0 := by
    simp [Gfun, sphereRadialExtension]
  have hGF : Function.LeftInverse Gfun Ffun := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [hF0, hG0]
    · have hnorm : ‖Ffun x‖ = ‖x‖ := hFnrm x
      have hcut : cut ‖Ffun x‖ = cut ‖x‖ := by rw [hnorm]
      have hcomp : famB ‖Ffun x‖ ∘ famA ‖x‖ = id := by
        funext z
        change (A (cut ‖Ffun x‖)).symm (A (cut ‖x‖) z) = z
        rw [hcut]
        exact Diffeomorph.symm_apply_apply _ z
      calc Gfun (Ffun x)
          = sphereRadialExtension (famB ‖Ffun x‖)
              (sphereRadialExtension (famA ‖x‖) x) := rfl
        _ = sphereRadialExtension (famB ‖Ffun x‖ ∘ famA ‖x‖) x := by
              rw [sphereRadialExtension_comp]; rfl
        _ = sphereRadialExtension id x := by rw [hcomp]
        _ = x := by rw [sphereRadialExtension_id]; rfl
  have hFG : Function.RightInverse Gfun Ffun := by
    intro y
    by_cases hy : y = 0
    · subst hy
      rw [hG0, hF0]
    · have hnorm : ‖Gfun y‖ = ‖y‖ := hGnrm y
      have hcut : cut ‖Gfun y‖ = cut ‖y‖ := by rw [hnorm]
      have hcomp : famA ‖Gfun y‖ ∘ famB ‖y‖ = id := by
        funext z
        change A (cut ‖Gfun y‖) ((A (cut ‖y‖)).symm z) = z
        rw [hcut]
        exact Diffeomorph.apply_symm_apply _ z
      calc Ffun (Gfun y)
          = sphereRadialExtension (famA ‖Gfun y‖)
              (sphereRadialExtension (famB ‖y‖) y) := rfl
        _ = sphereRadialExtension (famA ‖Gfun y‖ ∘ famB ‖y‖) y := by
              rw [sphereRadialExtension_comp]; rfl
        _ = sphereRadialExtension id y := by rw [hcomp]
        _ = y := by rw [sphereRadialExtension_id]; rfl
  have hnormOn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) {x : E | x ≠ 0} := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  have hpair : ContDiffOn ℝ ∞ (fun x : E => (‖x‖, x)) {x : E | x ≠ 0} :=
    hnormOn.prodMk contDiffOn_id
  have hFoff : ContDiffOn ℝ ∞ Ffun {x : E | x ≠ 0} :=
    (contDiffOn_sphereRadialExtension_family famA hfamA).comp hpair (fun x hx => hx)
  have hGoff : ContDiffOn ℝ ∞ Gfun {x : E | x ≠ 0} :=
    (contDiffOn_sphereRadialExtension_family famB hfamB).comp hpair (fun x hx => hx)
  have hFcont : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Ffun := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)]
        with y hy
      exact hFsmall y (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hy))
    · exact (hFoff.contMDiffOn).contMDiffAt (isOpen_ne.mem_nhds hx)
  have hGcont : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Gfun := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)]
        with y hy
      exact hGsmall y (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hy))
    · exact (hGoff.contMDiffOn).contMDiffAt (isOpen_ne.mem_nhds hx)
  let F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toEquiv := { toFun := Ffun, invFun := Gfun, left_inv := hGF, right_inv := hFG },
      contMDiff_toFun := hFcont, contMDiff_invFun := hGcont }
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hFnrm x
  · exact hFsmall
  · exact hFlarge
  · intro v
    calc F (v : E) = sphereRadialExtension (famA ‖(v : E)‖) (v : E) := rfl
      _ = ((famA ‖(v : E)‖) v : E) := sphereRadialExtension_apply_sphere (famA ‖(v : E)‖) v
      _ = (A (cut ‖(v : E)‖) v : E) := rfl
      _ = (A (cut 1) v : E) := by rw [norm_eq_of_mem_sphere v]
      _ = (A 1 v : E) := by rw [hcut1]

theorem exists_sphereRadialSuspension_nontrivial
    (A : ℝ → Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞)
    (hA : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞ fun q : ℝ × sphere (0 : E) 1 => A q.1 q.2)
    (hAi : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞ fun q : ℝ × sphere (0 : E) 1 => (A q.1).symm q.2)
    (hA0 : A 0 = Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞)
    (hA1 : A 1 ≠ Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x, ‖F x‖ = ‖x‖) ∧
      (∀ x, ‖x‖ ≤ 1 / 2 → F x = x) ∧
      (∀ x, 3 / 2 ≤ ‖x‖ → F x = x) ∧
      (∀ v : sphere (0 : E) 1, F (v : E) = (A 1 v : E)) ∧
      F ≠ Diffeomorph.refl 𝓘(ℝ, E) E ∞ := by
  obtain ⟨F, h1, h2, h3, h4⟩ := exists_sphereRadialSuspension A hA hAi hA0
  refine ⟨F, h1, h2, h3, h4, ?_⟩
  intro hF
  apply hA1
  refine Diffeomorph.ext fun v => ?_
  have h : (A 1 v : E) = (v : E) := by
    have h2' : (Diffeomorph.refl 𝓘(ℝ, E) E ∞) v = (A 1 v : E) := by
      rw [← hF]
      exact h4 v
    simpa using h2'.symm
  exact Subtype.ext h

end DifferentialGeometry.Topology.Manifold
