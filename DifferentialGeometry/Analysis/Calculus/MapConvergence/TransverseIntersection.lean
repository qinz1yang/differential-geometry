import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- Surjectivity of the derivative forces its center value to remain in the
local image under convergence of values and locally uniform first derivatives. -/
theorem eventually_mem_image_of_surjective_fderiv_of_c1_convergence
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {f₀ : E → F}
    (hf : ∀ᶠ n in atTop, DifferentiableOn ℝ (f n) U)
    (hf₀ : ContDiffOn ℝ 1 f₀ U)
    (hval : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hder : ∀ K : Set E, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n x => fderiv ℝ (f n) x)
        (fun x => fderiv ℝ f₀ x) atTop K)
    {a : E} (ha : a ∈ U)
    (hsurj : Function.Surjective (fderiv ℝ f₀ a)) :
    ∀ᶠ n in atTop, f₀ a ∈ f n '' U := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let L := fderiv ℝ f₀ a
  obtain ⟨B, hB⟩ := L.exists_nonlinearRightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let c : NNReal := B.nnnorm⁻¹ / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hmargin : 0 < (B.nnnorm : ℝ)⁻¹ - (c : ℝ) := by
    have hc_lt : c < B.nnnorm⁻¹ :=
      NNReal.half_lt_self (ne_of_gt (inv_pos.mpr hB))
    exact sub_pos.mpr (by exact_mod_cast hc_lt)
  have hDc : ContinuousAt (fderiv ℝ f₀) a :=
    (hf₀.contDiffAt (hU.mem_nhds ha)).continuousAt_fderiv (by norm_num)
  have hnear : {x | ‖fderiv ℝ f₀ x - L‖ < (c : ℝ) / 2} ∈ 𝓝 a := by
    filter_upwards [hDc.preimage_mem_nhds (ball_mem_nhds L (half_pos hcR))] with x hx
    change dist (fderiv ℝ f₀ x) L < (c : ℝ) / 2 at hx
    simpa only [dist_eq_norm] using hx
  obtain ⟨s, hs, hsU⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds ha) hnear)
  let r : ℝ := s / 2
  have hr : 0 < r := half_pos hs
  have hball : closedBall a r ⊆ U ∩
      {x | ‖fderiv ℝ f₀ x - L‖ < (c : ℝ) / 2} :=
    (closedBall_subset_ball (half_lt_self hs)).trans hsU
  have hKU : closedBall a r ⊆ U := fun x hx => (hball hx).1
  have hdu : ∀ᶠ n in atTop, ∀ x ∈ closedBall a r,
      ‖fderiv ℝ (f n) x - fderiv ℝ f₀ x‖ < (c : ℝ) / 2 := by
    have hh := (Metric.tendstoUniformlyOn_iff.mp
      (hder (closedBall a r) (isCompact_closedBall a r) hKU))
      ((c : ℝ) / 2) (half_pos hcR)
    simpa only [dist_eq_norm, norm_sub_rev] using hh
  have hv : ∀ᶠ n in atTop,
      dist (f n a) (f₀ a) < ((B.nnnorm : ℝ)⁻¹ - (c : ℝ)) * r :=
    (hval a ha).eventually_mem (ball_mem_nhds _ (mul_pos hmargin hr))
  filter_upwards [hf, hdu, hv] with n hfn hdn hvn
  have hdiff : ∀ x ∈ closedBall a r, DifferentiableAt ℝ (f n) x :=
    fun x hx => (hfn x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  have hbound : ∀ x ∈ closedBall a r, ‖fderiv ℝ (f n) x - L‖ ≤ (c : ℝ) := by
    intro x hx
    calc
      ‖fderiv ℝ (f n) x - L‖ ≤
          ‖fderiv ℝ (f n) x - fderiv ℝ f₀ x‖ + ‖fderiv ℝ f₀ x - L‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (c : ℝ) / 2 + (c : ℝ) / 2 :=
        add_le_add (hdn x hx).le (hball hx).2.le
      _ = c := add_halves _
  have happ : ApproximatesLinearOn (f n) L (closedBall a r) c := by
    intro x hx y hy
    exact (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le'
      (x := y) (y := x) hdiff hbound hy hx
  have htarget : f₀ a ∈ closedBall (f n a)
      (((B.nnnorm : ℝ)⁻¹ - (c : ℝ)) * r) := by
    simpa only [mem_closedBall, dist_comm] using hvn.le
  obtain ⟨x, hx, hfx⟩ :=
    happ.surjOn_closedBall_of_nonlinearRightInverse B hr.le Subset.rfl htarget
  exact ⟨x, hKU hx, hfx⟩

private theorem difference_pair_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x y : E}
    (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    fderiv ℝ (fun p : E × E => f p.1 - f p.2) (x, y) =
      (fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E E) -
        (fderiv ℝ f y).comp (ContinuousLinearMap.snd ℝ E E) := by
  exact ((hx.hasFDerivAt.comp (x, y) hasFDerivAt_fst).sub
    (hy.hasFDerivAt.comp (x, y) hasFDerivAt_snd)).fderiv

private theorem norm_comp_fst_sub_comp_snd_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] F) :
    ‖A.comp (ContinuousLinearMap.fst ℝ E E) -
      B.comp (ContinuousLinearMap.snd ℝ E E)‖ ≤ ‖A‖ + ‖B‖ := by
  have hfst : ‖A.comp (ContinuousLinearMap.fst ℝ E E)‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A‖ * ‖ContinuousLinearMap.fst ℝ E E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_fst_le ℝ E E) (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  have hsnd : ‖B.comp (ContinuousLinearMap.snd ℝ E E)‖ ≤ ‖B‖ := by
    calc
      _ ≤ ‖B‖ * ‖ContinuousLinearMap.snd ℝ E E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_snd_le ℝ E E) (norm_nonneg _)
      _ = ‖B‖ := mul_one _
  exact (norm_sub_le _ _).trans (add_le_add hfst hsnd)

/-- A literal local C1 limit of injective maps has no transverse double point.
The proof constructs collisions of the approximants on the off-diagonal source
product. It does not assume individual rank or injectivity of the limit. -/
theorem not_surjective_coprod_fderiv_of_injective_c1_limit
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {f₀ : E → F}
    (hf : ∀ᶠ n in atTop, DifferentiableOn ℝ (f n) U)
    (hf₀ : ContDiffOn ℝ 1 f₀ U)
    (hinj : ∀ᶠ n in atTop, Set.InjOn (f n) U)
    (hval : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hder : ∀ K : Set E, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n x => fderiv ℝ (f n) x)
        (fun x => fderiv ℝ f₀ x) atTop K)
    {a b : E} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) (heq : f₀ a = f₀ b) :
    ¬ Function.Surjective ((fderiv ℝ f₀ a).coprod (-(fderiv ℝ f₀ b))) := by
  intro hsurj
  let V : Set (E × E) := (U ×ˢ U) \ {p | p.1 = p.2}
  have hV : IsOpen V := (hU.prod hU).sdiff (isClosed_eq continuous_fst continuous_snd)
  let H : ℕ → E × E → F := fun n p => f n p.1 - f n p.2
  let H₀ : E × E → F := fun p => f₀ p.1 - f₀ p.2
  have habV : (a, b) ∈ V := ⟨⟨ha, hb⟩, hab⟩
  have hH : ∀ᶠ n in atTop, DifferentiableOn ℝ (H n) V := by
    filter_upwards [hf] with n hn
    exact ((hn.comp differentiableOn_fst (fun p hp => hp.1.1)).sub
      (hn.comp differentiableOn_snd (fun p hp => hp.1.2)))
  have hH₀ : ContDiffOn ℝ 1 H₀ V :=
    (hf₀.comp contDiffOn_fst (fun p hp => hp.1.1)).sub
      (hf₀.comp contDiffOn_snd (fun p hp => hp.1.2))
  have hHv : ∀ p ∈ V, Tendsto (fun n => H n p) atTop (𝓝 (H₀ p)) :=
    fun p hp => (hval p.1 hp.1.1).sub (hval p.2 hp.1.2)
  have hHd : ∀ K : Set (E × E), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun n p => fderiv ℝ (H n) p)
        (fun p => fderiv ℝ H₀ p) atTop K := by
    intro K hK hKV
    have hfstU : Prod.fst '' K ⊆ U := by
      rintro _ ⟨p, hp, rfl⟩
      exact (hKV hp).1.1
    have hsndU : Prod.snd '' K ⊆ U := by
      rintro _ ⟨p, hp, rfl⟩
      exact (hKV hp).1.2
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he : 0 < ε / 2 := half_pos hε
    have hd1 := (Metric.tendstoUniformlyOn_iff.mp
      (hder _ (hK.image continuous_fst) hfstU)) (ε / 2) he
    have hd2 := (Metric.tendstoUniformlyOn_iff.mp
      (hder _ (hK.image continuous_snd) hsndU)) (ε / 2) he
    filter_upwards [hf, hd1, hd2] with n hn hn1 hn2 p hp
    have hpU := (hKV hp).1
    have hd (m : E) (hm : m ∈ U) : DifferentiableAt ℝ (f n) m :=
      (hn m hm).differentiableAt (hU.mem_nhds hm)
    have hd₀ (m : E) (hm : m ∈ U) : DifferentiableAt ℝ f₀ m :=
      (hf₀.contDiffAt (hU.mem_nhds hm)).differentiableAt (by norm_num)
    have hnorm1 : ‖fderiv ℝ (f n) p.1 - fderiv ℝ f₀ p.1‖ < ε / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn1 p.1 ⟨p, hp, rfl⟩
    have hnorm2 : ‖fderiv ℝ (f n) p.2 - fderiv ℝ f₀ p.2‖ < ε / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn2 p.2 ⟨p, hp, rfl⟩
    have hform : fderiv ℝ (H n) p - fderiv ℝ H₀ p =
        (fderiv ℝ (f n) p.1 - fderiv ℝ f₀ p.1).comp
          (ContinuousLinearMap.fst ℝ E E) -
        (fderiv ℝ (f n) p.2 - fderiv ℝ f₀ p.2).comp
          (ContinuousLinearMap.snd ℝ E E) := by
      rw [show fderiv ℝ (H n) p = _ from difference_pair_fderiv (hd p.1 hpU.1) (hd p.2 hpU.2),
        show fderiv ℝ H₀ p = _ from difference_pair_fderiv (hd₀ p.1 hpU.1) (hd₀ p.2 hpU.2)]
      apply ContinuousLinearMap.ext
      intro z
      change (fderiv ℝ (f n) p.1 z.1 - fderiv ℝ (f n) p.2 z.2) -
          (fderiv ℝ f₀ p.1 z.1 - fderiv ℝ f₀ p.2 z.2) =
        (fderiv ℝ (f n) p.1 z.1 - fderiv ℝ f₀ p.1 z.1) -
          (fderiv ℝ (f n) p.2 z.2 - fderiv ℝ f₀ p.2 z.2)
      abel
    rw [dist_eq_norm, norm_sub_rev, hform]
    exact (norm_comp_fst_sub_comp_snd_le _ _).trans_lt
      (by linarith [hnorm1, hnorm2])
  have hHsurj : Function.Surjective (fderiv ℝ H₀ (a, b)) := by
    have hda := (hf₀.contDiffAt (hU.mem_nhds ha)).differentiableAt (by norm_num)
    have hdb := (hf₀.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_num)
    have he : fderiv ℝ H₀ (a, b) =
        (fderiv ℝ f₀ a).coprod (-(fderiv ℝ f₀ b)) := by
      rw [show fderiv ℝ H₀ (a, b) = _ from difference_pair_fderiv hda hdb]
      apply ContinuousLinearMap.ext
      intro z
      change fderiv ℝ f₀ a z.1 - fderiv ℝ f₀ b z.2 =
        fderiv ℝ f₀ a z.1 + -(fderiv ℝ f₀ b z.2)
      exact sub_eq_add_neg _ _
    rwa [he]
  have hroot := eventually_mem_image_of_surjective_fderiv_of_c1_convergence
    hV hH hH₀ hHv hHd habV hHsurj
  obtain ⟨n, hn, hninj⟩ := (hroot.and hinj).exists
  obtain ⟨p, hp, hpvalue⟩ := hn
  have hzero : f n p.1 = f n p.2 := by
    apply sub_eq_zero.mp
    simpa only [H, H₀, heq, sub_self] using hpvalue
  exact hp.2 (hninj hp.1.1 hp.1.2 hzero)

end DifferentialGeometry.Analysis
