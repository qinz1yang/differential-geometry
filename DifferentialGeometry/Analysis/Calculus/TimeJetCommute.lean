import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Prod

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_deriv_time_comm {G : ℝ → E → F} (t : ℝ) (x : E)
    (hG : ContDiff ℝ ∞ (Function.uncurry G)) :
    fderiv ℝ (fun y => deriv (fun s => G s y) t) x
      = deriv (fun s => fderiv ℝ (fun y => G s y) x) t := by
  set H : ℝ × E → F := Function.uncurry G with hHdef
  have hHcd : ContDiff ℝ ∞ H := hG
  have hHdiff : Differentiable ℝ H := hHcd.differentiable (by simp)
  have hHcd1 : ContDiff ℝ ∞ (fderiv ℝ H) := hHcd.fderiv_right (m := ∞) (by simp)
  have hHdiff1 : Differentiable ℝ (fderiv ℝ H) := hHcd1.differentiable (by simp)
  have hDs : (fun y => deriv (fun s => G s y) t) = (fun y => fderiv ℝ H (t, y) (1, 0)) := by
    funext y
    have hpair : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × E)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact ((hHdiff (t, y)).hasFDerivAt.comp_hasDerivAt t hpair).deriv
  have hFy : (fun s => fderiv ℝ (fun y => G s y) x)
      = (fun s => (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    funext s
    have hpair : HasFDerivAt (fun y : E => ((s, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
      (hasFDerivAt_const (s : ℝ) x).prodMk (hasFDerivAt_id x)
    exact ((hHdiff (s, x)).hasFDerivAt.comp x hpair).fderiv
  rw [hDs, hFy]
  have hLHS : fderiv ℝ (fun y => fderiv ℝ H (t, y) (1, 0)) x
      = ((fderiv ℝ (fderiv ℝ H) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)).flip (1, 0) := by
    have hcomp : HasFDerivAt (fun y : E => fderiv ℝ H (t, y))
        ((fderiv ℝ (fderiv ℝ H) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
      have hpair : HasFDerivAt (fun y : E => ((t, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
        (hasFDerivAt_const (t : ℝ) x).prodMk (hasFDerivAt_id x)
      exact (hHdiff1 (t, x)).hasFDerivAt.comp x hpair
    have happly := (ContinuousLinearMap.apply ℝ F ((1, 0) : ℝ × E)).hasFDerivAt.comp x hcomp
    simpa [ContinuousLinearMap.flip_apply] using happly.fderiv
  have hRHS : deriv (fun s => (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) t
      = (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ H (s, x))
        (fderiv ℝ (fderiv ℝ H) (t, x) (1, 0)) t := by
      have hpair : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × E)) (1, 0) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
      exact (hHdiff1 (t, x)).hasFDerivAt.comp_hasDerivAt t hpair
    exact (((ContinuousLinearMap.compL ℝ E (ℝ × E) F).flip
      (ContinuousLinearMap.inr ℝ ℝ E)).hasFDerivAt.comp_hasDerivAt t hcomp).deriv
  rw [hLHS, hRHS]
  ext u
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  exact second_derivative_symmetric (f := H) (fun y => (hHdiff y).hasFDerivAt)
    ((hHdiff1 (t, x)).hasFDerivAt) (0, u) (1, 0)

theorem fderiv_deriv_hasDerivAt_comm (Φ : ℝ × E → ℝ) (s₀ : ℝ) (y₀ : E) (v : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (s₀, y₀)) :
    HasDerivAt
      (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v)
      (fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) s₀) y₀ v)
      s₀ := by
  have hΦ_dfderiv : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (s₀, y₀) := hΦ.fderiv_right (by simp)
  have get_diff_nhd : ∀ (p₀ : ℝ × E), ContDiffAt ℝ ∞ Φ p₀ →
      ∀ᶠ p : ℝ × E in nhds p₀, DifferentiableAt ℝ Φ p := fun p₀ hp => by
    obtain ⟨f', u, hu, _, hfu⟩ :=
      contDiffAt_one_iff.mp (hp.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞))
    exact Filter.eventually_of_mem hu fun p hp => (hfu p hp).differentiableAt
  have hΦ_s : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ Φ (s, y₀) :=
    (continuous_id.prodMk (continuous_const (y := y₀))).continuousAt (get_diff_nhd _ hΦ)
  have hΦ_y : ∀ᶠ y : E in nhds y₀, DifferentiableAt ℝ Φ (s₀, y) :=
    (continuous_const (y := s₀) |>.prodMk continuous_id).continuousAt (get_diff_nhd _ hΦ)
  have lhs_eq : (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v) =ᶠ[nhds s₀]
      (fun s => fderiv ℝ Φ (s, y₀) (0, v)) := by
    filter_upwards [hΦ_s] with s hs
    have h : HasFDerivAt (fun y => Φ (s, y))
        ((fderiv ℝ Φ (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y₀ :=
      hs.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right s y₀)
    rw [h.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have h_fderiv_s : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
      ((fderiv ℝ (fderiv ℝ Φ) (s₀, y₀)).comp (ContinuousLinearMap.inl ℝ ℝ E)) s₀ :=
    (hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp s₀
      (hasFDerivAt_prodMk_left s₀ y₀)
  have h_sv : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (1, 0) (0, v)) s₀ := by
    have h_d : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
        (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (1, 0)) s₀ := by
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
        using h_fderiv_s.hasDerivAt
    simpa [map_zero] using h_d.clm_apply (hasDerivAt_const s₀ ((0 : ℝ), v))
  have hsymm : IsSymmSndFDerivAt ℝ Φ (s₀, y₀) :=
    hΦ.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have h_sv' : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (0, v) (1, 0)) s₀ := by
    rwa [hsymm ((1 : ℝ), (0 : E)) ((0 : ℝ), v)] at h_sv
  have rhs_eq : fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) s₀) y₀ v =
      fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (0, v) (1, 0) := by
    have h_eq : (fun y => deriv (fun s => Φ (s, y)) s₀) =ᶠ[nhds y₀]
        (fun y => fderiv ℝ Φ (s₀, y) (1, 0)) := by
      filter_upwards [hΦ_y] with y hy
      have := hy.hasFDerivAt.comp_hasDerivAt (s₀ : ℝ)
        (hasFDerivAt_prodMk_left s₀ y).hasDerivAt
      exact this.deriv
    rw [Filter.EventuallyEq.fderiv_eq h_eq]
    have h_chain : HasFDerivAt (fun y => fderiv ℝ Φ (s₀, y) ((1 : ℝ), (0 : E)))
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp
          ((fderiv ℝ (fderiv ℝ Φ) (s₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))) y₀ :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp y₀
        ((hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp y₀
          (hasFDerivAt_prodMk_right s₀ y₀))
    simp [h_chain.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          ContinuousLinearMap.inr_apply]
  rw [rhs_eq]
  exact h_sv'.congr_of_eventuallyEq lhs_eq

theorem fderiv_iteratedDeriv_time_comm {G : ℝ → E → F} (a : ℕ) (t₀ : ℝ) (x : E)
    (hG : ContDiff ℝ ∞ (Function.uncurry G)) :
    fderiv ℝ (fun y => iteratedDeriv a (fun t => G t y) t₀) x
      = iteratedDeriv a (fun t => fderiv ℝ (fun y => G t y) x) t₀ := by
  induction a generalizing G with
  | zero => simp only [iteratedDeriv_zero]
  | succ a ih =>
    have hHdiff : Differentiable ℝ (Function.uncurry G) := hG.differentiable (by simp)
    have hHcd1 : ContDiff ℝ ∞ (fderiv ℝ (Function.uncurry G)) := hG.fderiv_right (m := ∞) (by simp)
    have hG' : ContDiff ℝ ∞ (Function.uncurry (fun t y => deriv (fun s => G s y) t)) := by
      have heq : (Function.uncurry (fun t y => deriv (fun s => G s y) t))
          = (fun p : ℝ × E => fderiv ℝ (Function.uncurry G) p (1, 0)) := by
        funext p
        obtain ⟨t, y⟩ := p
        have hpair : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × E)) (1, 0) t :=
          (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
        exact ((hHdiff (t, y)).hasFDerivAt.comp_hasDerivAt t hpair).deriv
      rw [heq]
      exact (ContinuousLinearMap.apply ℝ F ((1, 0) : ℝ × E)).contDiff.comp hHcd1
    have hlhs : (fun y => iteratedDeriv (a + 1) (fun t => G t y) t₀)
        = (fun y => iteratedDeriv a (fun t => deriv (fun s => G s y) t) t₀) := by
      funext y; rw [iteratedDeriv_succ']
    rw [hlhs, ih hG', iteratedDeriv_succ']
    congr 1
    funext t
    exact fderiv_deriv_time_comm t x hG

theorem fderiv_derivWithin_time_comm {G : ℝ → E → F} {sₜ : Set ℝ} {V : Set E}
    (hsₜ : UniqueDiffOn ℝ sₜ) (hsacc : sₜ ⊆ closure (interior sₜ)) (hV : IsOpen V)
    {t : ℝ} (ht : t ∈ sₜ) {x : E} (hx : x ∈ V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (sₜ ×ˢ V)) :
    fderiv ℝ (fun y => derivWithin (fun s => G s y) sₜ t) x
      = derivWithin (fun s => fderiv ℝ (fun y => G s y) x) sₜ t := by
  set H : ℝ × E → F := Function.uncurry G with hHdef
  set S : Set (ℝ × E) := sₜ ×ˢ V with hSdef
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod hsₜ hV.uniqueDiffOn
  have hSacc : S ⊆ closure (interior S) := by
    have hsub : interior sₜ ×ˢ V ⊆ interior S := by
      rw [hSdef, interior_prod_eq, hV.interior_eq]
    refine fun q hq => closure_mono hsub ?_
    rw [hSdef] at hq
    rw [closure_prod_eq]
    exact ⟨hsacc hq.1, subset_closure hq.2⟩
  have hmem : (t, x) ∈ S := ⟨ht, hx⟩
  have hHcdOn : ContDiffOn ℝ ∞ H S := hG
  have hHdiffOn : DifferentiableOn ℝ H S := hHcdOn.differentiableOn (by simp)
  have hHcdOn1 : ContDiffOn ℝ ∞ (fderivWithin ℝ H S) S :=
    hHcdOn.fderivWithin hUD (by simp)
  have hHdiffOn1 : DifferentiableOn ℝ (fderivWithin ℝ H S) S := hHcdOn1.differentiableOn (by simp)
  have h2le : (minSmoothness ℝ 2 : WithTop ℕ∞) ≤ ∞ := by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top
  have hsymm : IsSymmSndFDerivWithinAt ℝ H S (t, x) :=
    (hHcdOn.contDiffWithinAt hmem).isSymmSndFDerivWithinAt h2le hUD (hSacc hmem) hmem
  have hDs : Set.EqOn (fun y => derivWithin (fun s => G s y) sₜ t)
      (fun y => fderivWithin ℝ H S (t, y) (1, 0)) V := by
    intro y hy
    have hmaps : Set.MapsTo (fun s : ℝ => ((s, y) : ℝ × E)) sₜ S := fun s hs => ⟨hs, hy⟩
    have hpair : HasDerivWithinAt (fun s : ℝ => ((s, y) : ℝ × E)) (1, 0) sₜ t :=
      (hasDerivWithinAt_id t sₜ).prodMk (hasDerivWithinAt_const t sₜ y)
    exact ((hHdiffOn (t, y) ⟨ht, hy⟩).hasFDerivWithinAt.comp_hasDerivWithinAt t hpair
      hmaps).derivWithin
      (hsₜ t ht)
  have hFy : Set.EqOn (fun s => fderiv ℝ (fun y => G s y) x)
      (fun s => (fderivWithin ℝ H S (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) sₜ := by
    intro s hs
    have hmaps : Set.MapsTo (fun y : E => ((s, y) : ℝ × E)) V S := fun y hy => ⟨hs, hy⟩
    have hpair : HasFDerivWithinAt (fun y : E => ((s, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) V
      x :=
      ((hasFDerivAt_const (s : ℝ) x).prodMk (hasFDerivAt_id x)).hasFDerivWithinAt
    exact (((hHdiffOn (s, x) ⟨hs, hx⟩).hasFDerivWithinAt.comp x hpair hmaps).hasFDerivAt
      (hV.mem_nhds hx)).fderiv
  rw [(Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hDs).fderiv_eq,
    derivWithin_congr hFy (hFy ht)]
  have hLHS : fderiv ℝ (fun y => fderivWithin ℝ H S (t, y) (1, 0)) x
      = ((fderivWithin ℝ (fderivWithin ℝ H S) S (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)).flip
          (1, 0) := by
    have hmaps : Set.MapsTo (fun y : E => ((t, y) : ℝ × E)) V S := fun y hy => ⟨ht, hy⟩
    have hpair : HasFDerivWithinAt (fun y : E => ((t, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) V
      x :=
      ((hasFDerivAt_const (t : ℝ) x).prodMk (hasFDerivAt_id x)).hasFDerivWithinAt
    have hcomp : HasFDerivWithinAt (fun y : E => fderivWithin ℝ H S (t, y))
        ((fderivWithin ℝ (fderivWithin ℝ H S) S (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) V x :=
      (hHdiffOn1 (t, x) ⟨ht, hx⟩).hasFDerivWithinAt.comp x hpair hmaps
    have happly := (ContinuousLinearMap.apply ℝ F
      ((1, 0) : ℝ × E)).hasFDerivAt.comp_hasFDerivWithinAt
      x hcomp
    simpa [ContinuousLinearMap.flip_apply] using (happly.hasFDerivAt (hV.mem_nhds hx)).fderiv
  have hRHS : derivWithin (fun s => (fderivWithin ℝ H S (s, x)).comp
    (ContinuousLinearMap.inr ℝ ℝ E))
        sₜ t
      = (fderivWithin ℝ (fderivWithin ℝ H S) S (t, x) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hmaps : Set.MapsTo (fun s : ℝ => ((s, x) : ℝ × E)) sₜ S := fun s hs => ⟨hs, hx⟩
    have hpair : HasDerivWithinAt (fun s : ℝ => ((s, x) : ℝ × E)) (1, 0) sₜ t :=
      (hasDerivWithinAt_id t sₜ).prodMk (hasDerivWithinAt_const t sₜ x)
    have hcomp : HasDerivWithinAt (fun s : ℝ => fderivWithin ℝ H S (s, x))
        (fderivWithin ℝ (fderivWithin ℝ H S) S (t, x) (1, 0)) sₜ t :=
      (hHdiffOn1 (t, x) ⟨ht, hx⟩).hasFDerivWithinAt.comp_hasDerivWithinAt t hpair hmaps
    exact (((ContinuousLinearMap.compL ℝ E (ℝ × E) F).flip
      (ContinuousLinearMap.inr ℝ ℝ E)).hasFDerivAt.comp_hasDerivWithinAt t hcomp).derivWithin
        (hsₜ t ht)
  rw [hLHS, hRHS]
  ext u
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  exact hsymm.eq (0, u) (1, 0)

theorem fderiv_iteratedDerivWithin_time_comm {G : ℝ → E → F} {sₜ : Set ℝ} {V : Set E}
    (hsₜ : UniqueDiffOn ℝ sₜ) (hsacc : sₜ ⊆ closure (interior sₜ)) (hV : IsOpen V)
    (a : ℕ) {t₀ : ℝ} (ht₀ : t₀ ∈ sₜ) {x : E} (hx : x ∈ V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (sₜ ×ˢ V)) :
    fderiv ℝ (fun y => iteratedDerivWithin a (fun t => G t y) sₜ t₀) x
      = iteratedDerivWithin a (fun t => fderiv ℝ (fun y => G t y) x) sₜ t₀ := by
  induction a generalizing G with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ a ih =>
    set S : Set (ℝ × E) := sₜ ×ˢ V with hSdef
    have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod hsₜ hV.uniqueDiffOn
    have hG' : ContDiffOn ℝ ∞
        (Function.uncurry (fun t y => derivWithin (fun s => G s y) sₜ t)) S := by
      have hHcdOn1 : ContDiffOn ℝ ∞ (fderivWithin ℝ (Function.uncurry G) S) S :=
        hG.fderivWithin hUD (by simp)
      have heq : Set.EqOn (fun p : ℝ × E => fderivWithin ℝ (Function.uncurry G) S p (1, 0))
          (Function.uncurry (fun t y => derivWithin (fun s => G s y) sₜ t)) S := by
        rintro ⟨t', y'⟩ ⟨ht', hy'⟩
        have hmaps : Set.MapsTo (fun s : ℝ => ((s, y') : ℝ × E)) sₜ S := fun s hs => ⟨hs, hy'⟩
        have hpair : HasDerivWithinAt (fun s : ℝ => ((s, y') : ℝ × E)) (1, 0) sₜ t' :=
          (hasDerivWithinAt_id t' sₜ).prodMk (hasDerivWithinAt_const t' sₜ y')
        exact (((hG.differentiableOn (by simp)) (t', y')
          ⟨ht', hy'⟩).hasFDerivWithinAt.comp_hasDerivWithinAt
          t' hpair hmaps).derivWithin (hsₜ t' ht') |>.symm
      exact (((ContinuousLinearMap.apply ℝ F ((1, 0) : ℝ × E)).contDiff.comp_contDiffOn
        hHcdOn1)).congr (fun p hp => (heq hp).symm)
    have hlhs : (fun y => iteratedDerivWithin (a + 1) (fun t => G t y) sₜ t₀)
        = (fun y => iteratedDerivWithin a (fun t => derivWithin (fun s => G s y) sₜ t) sₜ t₀) := by
      funext y; rw [iteratedDerivWithin_succ']
    rw [hlhs, ih hG', iteratedDerivWithin_succ']
    refine iteratedDerivWithin_congr (fun t ht => ?_) ht₀
    exact fderiv_derivWithin_time_comm hsₜ hsacc hV ht hx hG

theorem spatialFDeriv_contDiffOn {G : ℝ → E → F} {sₜ : Set ℝ} {V : Set E}
    (hsₜ : UniqueDiffOn ℝ sₜ) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (sₜ ×ˢ V)) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t y => fderiv ℝ (G t) y)) (sₜ ×ˢ V) := by
  set S : Set (ℝ × E) := sₜ ×ˢ V with hSdef
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod hsₜ hV.uniqueDiffOn
  have hHcdOn1 : ContDiffOn ℝ ∞ (fderivWithin ℝ (Function.uncurry G) S) S :=
    hG.fderivWithin hUD (by simp)
  have heq : Set.EqOn (Function.uncurry (fun t y => fderiv ℝ (G t) y))
      (fun p : ℝ × E => (fderivWithin ℝ (Function.uncurry G) S p).comp
        (ContinuousLinearMap.inr ℝ ℝ E)) S := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hmaps : Set.MapsTo (fun y' : E => ((t, y') : ℝ × E)) V S := fun y' hy' => ⟨ht, hy'⟩
    have hpair : HasFDerivWithinAt (fun y' : E => ((t, y') : ℝ × E))
        (ContinuousLinearMap.inr ℝ ℝ E) V y :=
      ((hasFDerivAt_const (t : ℝ) y).prodMk (hasFDerivAt_id y)).hasFDerivWithinAt
    exact (((hG.differentiableOn (by simp) (t, y) ⟨ht, hy⟩).hasFDerivWithinAt.comp y hpair
      hmaps).hasFDerivAt (hV.mem_nhds hy)).fderiv
  exact (((ContinuousLinearMap.compL ℝ E (ℝ × E) F).flip
    (ContinuousLinearMap.inr ℝ ℝ E)).contDiff.comp_contDiffOn hHcdOn1).congr heq

end Analysis
end DifferentialGeometry

end
