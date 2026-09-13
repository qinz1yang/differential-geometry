import DifferentialGeometry.Analysis.Complex.GradientRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.Bilinear
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set InnerProductSpace
open scoped NNReal

namespace DifferentialGeometry.Analysis

private theorem holderOn_of_dist_le
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {s : Set E} {C α : ℝ≥0} {f : E → F}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) :
    HolderOnWith C α f s := by
  intro x hx y hy
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow] using h x hx y hy

private theorem holderOn_add
    {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    {s : Set E} {C D α : ℝ≥0} {f g : E → F}
    (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s) :
    HolderOnWith (C + D) α (fun x => f x + g x) s :=
  HolderWith.restrict_iff.mp (hf.holderWith.add hg.holderWith)

private theorem holderOn_sub
    {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    {s : Set E} {C D α : ℝ≥0} {f g : E → F}
    (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s) :
    HolderOnWith (C + D) α (fun x => f x - g x) s :=
  HolderWith.restrict_iff.mp (Schauder.holderWith_sub hf.holderWith hg.holderWith)

private theorem holderOn_bilinear
    {E V W U : Type*} [MetricSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    {s : Set E} {C D M N α : ℝ≥0}
    (L : V →L[ℝ] W →L[ℝ] U) (hL : ∀ v w, ‖L v w‖ ≤ ‖v‖ * ‖w‖)
    {f : E → V} {g : E → W}
    (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s)
    (hfn : ∀ x ∈ s, ‖f x‖ ≤ M) (hgn : ∀ x ∈ s, ‖g x‖ ≤ N) :
    HolderOnWith (M * D + N * C) α (fun x => L (f x) (g x)) s :=
  HolderWith.restrict_iff.mp (Schauder.holderWith_bilinear_of_norm_le L hL
    hf.holderWith hg.holderWith (fun x => hfn x x.2) (fun x => hgn x x.2))

private theorem holderOn_mul
    {E : Type*} [MetricSpace E] {s : Set E} {C D M N α : ℝ≥0}
    {f g : E → ℝ} (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s)
    (hfn : ∀ x ∈ s, ‖f x‖ ≤ M) (hgn : ∀ x ∈ s, ‖g x‖ ≤ N) :
    HolderOnWith (M * D + N * C) α (fun x => f x * g x) s :=
  holderOn_bilinear (ContinuousLinearMap.mul ℝ ℝ)
    (fun v w => by simp only [ContinuousLinearMap.mul_apply', norm_mul]; rfl)
    hf hg hfn hgn

private theorem holderOn_clm_apply
    {E V W : Type*} [MetricSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set E} {C D M N α : ℝ≥0}
    {f : E → V →L[ℝ] W} {g : E → V}
    (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s)
    (hfn : ∀ x ∈ s, ‖f x‖ ≤ M) (hgn : ∀ x ∈ s, ‖g x‖ ≤ N) :
    HolderOnWith (M * D + N * C) α (fun x => f x (g x)) s :=
  holderOn_bilinear (ContinuousLinearMap.id ℝ (V →L[ℝ] W))
    (fun f v => f.le_opNorm v) hf hg hfn hgn

private theorem holderOn_linear_isometry
    {E V W : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set E} {C α : ℝ≥0} (L : V →ₗᵢ[ℝ] W)
    {f : E → V} (hf : HolderOnWith C α f s) :
    HolderOnWith C α (fun x => L (f x)) s := by
  intro x hx y hy
  simpa only [L.isometry.edist_eq] using hf x hx y hy

private theorem holderOn_inv
    {E : Type*} [PseudoMetricSpace E] {s : Set E} {C α l : ℝ≥0}
    {f : E → ℝ} (hl : 0 < l) (hf : HolderOnWith C α f s)
    (hfn : ∀ x ∈ s, (l : ℝ) ≤ f x) :
    HolderOnWith (C / l ^ 2) α (fun x => (f x)⁻¹) s := by
  apply holderOn_of_dist_le
  intro x hx y hy
  have hlr : (0 : ℝ) < l := hl
  have hxpos := hlr.trans_le (hfn x hx)
  have hypos := hlr.trans_le (hfn y hy)
  rw [dist_eq_norm, inv_sub_inv hxpos.ne' hypos.ne', norm_div, norm_mul,
    Real.norm_of_nonneg hxpos.le, Real.norm_of_nonneg hypos.le, norm_sub_rev]
  calc
    ‖f x - f y‖ / (f x * f y) ≤
      ((C : ℝ) * dist x y ^ (α : ℝ)) / ((l : ℝ) ^ 2) := by
      apply div_le_div₀ (by positivity) _ (by positivity)
      · simpa only [pow_two] using mul_le_mul (hfn x hx) (hfn y hy) hlr.le hxpos.le
      · simpa only [dist_eq_norm] using hf.dist_le hx hy
    _ = ((C / l ^ 2 : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by push_cast; ring

private theorem norm_inv_le
    {l a : ℝ} (hl : 0 < l) (ha : l ≤ a) : ‖a⁻¹‖ ≤ l⁻¹ := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (hl.le.trans ha))]
  exact inv_anti₀ hl ha

private theorem holderOn_bilin_apply
    {E V : Type*} [MetricSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set E} {C H J G M N α : ℝ≥0}
    {B : E → V →L[ℝ] V →L[ℝ] ℝ} {u v : E → V}
    (hB : HolderOnWith C α B s) (hu : HolderOnWith H α u s)
    (hv : HolderOnWith J α v s)
    (hBn : ∀ x ∈ s, ‖B x‖ ≤ G) (hun : ∀ x ∈ s, ‖u x‖ ≤ M)
    (hvn : ∀ x ∈ s, ‖v x‖ ≤ N) :
    HolderOnWith (G * M * J + N * (G * H + M * C)) α
      (fun x => B x (u x) (v x)) s := by
  apply holderOn_clm_apply (holderOn_clm_apply hB hu hBn hun) hv
  · intro x hx
    exact ((B x).le_opNorm (u x)).trans
      (mul_le_mul (hBn x hx) (hun x hx) (norm_nonneg _) G.coe_nonneg)
  · exact hvn

private theorem norm_bilin_apply_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} {u v : V} {G M N : ℝ≥0}
    (hB : ‖B‖ ≤ G) (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ N) :
    ‖B u v‖ ≤ (G : ℝ) * M * N := by
  exact (B.le_opNorm₂ u v).trans
    (mul_le_mul (mul_le_mul hB hu (norm_nonneg _) G.coe_nonneg) hv
      (norm_nonneg _) (mul_nonneg G.coe_nonneg M.coe_nonneg))

private theorem holderOn_div
    {E : Type*} [MetricSpace E] {s : Set E} {C D M α l : ℝ≥0}
    {f g : E → ℝ} (hl : 0 < l)
    (hf : HolderOnWith C α f s) (hg : HolderOnWith D α g s)
    (hfn : ∀ x ∈ s, ‖f x‖ ≤ M) (hgn : ∀ x ∈ s, (l : ℝ) ≤ g x) :
    HolderOnWith (C / l + M * D / l ^ 2) α (fun x => f x / g x) s := by
  have hi : ∀ x ∈ s, ‖(g x)⁻¹‖ ≤ (l⁻¹ : ℝ≥0) :=
    fun x hx => norm_inv_le (show (0 : ℝ) < l from hl) (hgn x hx)
  have h := holderOn_mul hf (holderOn_inv hl hg hgn) hfn hi
  have he : C / l + M * D / l ^ 2 = M * (D / l ^ 2) + l⁻¹ * C := by ring
  rw [he]
  simpa only [div_eq_mul_inv] using h

private theorem holderOn_complex_pair
    {E : Type*} [PseudoMetricSpace E] {s : Set E} {C D α : ℝ≥0}
    {a b : E → ℝ} (ha : HolderOnWith C α a s) (hb : HolderOnWith D α b s) :
    HolderOnWith (C + D) α (fun z => (a z : ℂ) + (b z : ℂ) * Complex.I) s := by
  apply holderOn_of_dist_le
  intro x hx y hy
  rw [dist_eq_norm]
  have he : ((a x : ℂ) + (b x : ℂ) * Complex.I) -
      ((a y : ℂ) + (b y : ℂ) * Complex.I) =
      ((a x - a y : ℝ) : ℂ) + ((b x - b y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((a x - a y : ℝ) : ℂ)‖ + ‖((b x - b y : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = dist (a x) (a y) + dist (b x) (b y) := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, dist_eq_norm]
    _ ≤ (C : ℝ) * dist x y ^ (α : ℝ) + D * dist x y ^ (α : ℝ) :=
      add_le_add (ha.dist_le hx hy) (hb.dist_le hx hy)
    _ = ((C + D : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by push_cast; ring

private theorem holderOn_twice
    {E : Type*} [PseudoMetricSpace E] {s : Set E} {C α : ℝ≥0}
    {f : E → ℝ} (hf : HolderOnWith C α f s) :
    HolderOnWith (2 * C) α (fun z => 2 * f z) s := by
  convert holderOn_add hf hf using 1 <;> simp only [two_mul]

private theorem toDual_complex_pair (D : ℂ →L[ℝ] ℝ) :
    toDual ℝ ℂ ((D 1 : ℂ) + (D Complex.I : ℂ) * Complex.I) = D := by
  have hr := (toDual ℝ ℂ).apply_symm_apply D
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hr
  have hi := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hr
  simp only [toDual_apply_apply, Complex.inner, one_mul, Complex.conj_re] at h1
  simp only [toDual_apply_apply, Complex.inner, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, zero_mul, one_mul, zero_sub,
    neg_neg] at hi
  rw [← h1, ← hi, Complex.re_add_im]
  exact hr

private theorem holderOn_fderivWithin_of_sq_add_eq
    {s : Set ℂ} (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f s)
    {a q : ℂ → ℂ} {C A α D : ℝ≥0} (hα : 0 < α)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (ha : HolderOnWith A α a s) (hq : HolderOnWith C α q s)
    (he : ∀ z ∈ s, ((fderivWithin ℝ f s z 1 : ℂ) +
      (fderivWithin ℝ f s z Complex.I : ℂ) * Complex.I + a z) ^ 2 = q z) :
    HolderOnWith (NNReal.sqrt (6 * C) + A * D ^ ((α : ℝ) - (α / 2 : ℝ≥0)))
      (α / 2) (fderivWithin ℝ f s) s := by
  let grad (z : ℂ) := (fderivWithin ℝ f s z 1 : ℂ) +
    (fderivWithin ℝ f s z Complex.I : ℂ) * Complex.I
  have hgc : ContinuousOn grad s := by
    have hdf := hf.continuousOn_fderivWithin hu (by norm_num)
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hdf.clm_apply continuousOn_const)).add
      ((Complex.continuous_ofReal.comp_continuousOn
        (hdf.clm_apply continuousOn_const)).mul_const _)
  have hsq : HolderOnWith C α (fun z => (grad z + a z) ^ 2) s := by
    intro x hx y hy
    change edist ((grad x + a x) ^ 2) ((grad y + a y) ^ 2) ≤ _
    rw [he x hx, he y hy]
    exact hq x hx y hy
  have hh := Complex.holderOnWith_of_sq hs (hgc.add (ha.continuousOn hα)) hsq
  have hw := ha.of_le hdiam (show α / 2 ≤ α by exact div_le_self (by positivity) (by norm_num))
  have hg : HolderOnWith (NNReal.sqrt (6 * C) + A * D ^ ((α : ℝ) - (α / 2 : ℝ≥0)))
      (α / 2) grad s := by
    simpa only [Pi.add_apply, add_sub_cancel_right] using holderOn_sub hh hw
  have hD := holderOn_linear_isometry (toDual ℝ ℂ).toLinearIsometry hg
  simpa only [grad, LinearIsometryEquiv.coe_toLinearIsometry, toDual_complex_pair] using hD

theorem holderOnWith_fderivWithin_of_conformal_pair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f s)
    {B : ℂ → V →L[ℝ] V →L[ℝ] ℝ} {v w : ℂ → V} {t : V}
    {C H G M l α D : ℝ≥0} (hl : 0 < l) (hα : 0 < α)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hB : HolderOnWith C α B s) (hv : HolderOnWith H α v s)
    (hw : HolderOnWith H α w s)
    (hBn : ∀ z ∈ s, ‖B z‖ ≤ G) (hvn : ∀ z ∈ s, ‖v z‖ ≤ M)
    (hwn : ∀ z ∈ s, ‖w z‖ ≤ M) (ht : ‖t‖ ≤ 1)
    (hBs : ∀ z ∈ s, (B z).toBilinForm.IsSymm)
    (hBt : ∀ z ∈ s, (l : ℝ) ≤ B z t t)
    (horth : ∀ z ∈ s, B z (v z + fderivWithin ℝ f s z 1 • t)
      (w z + fderivWithin ℝ f s z Complex.I • t) = 0)
    (heq : ∀ z ∈ s, B z (v z + fderivWithin ℝ f s z 1 • t)
      (v z + fderivWithin ℝ f s z 1 • t) =
      B z (w z + fderivWithin ℝ f s z Complex.I • t)
        (w z + fderivWithin ℝ f s z Complex.I • t)) :
    let K := G * M / l
    let A := (G * H + M * C) / l + G * M * C / l ^ 2
    let R := (G * M * H + M * (G * H + M * C)) / l + G * M * M * C / l ^ 2
    HolderOnWith (NNReal.sqrt (6 * (8 * K * A + 4 * R)) +
      (2 * A) * D ^ ((α : ℝ) - (α / 2 : ℝ≥0))) (α / 2)
      (fderivWithin ℝ f s) s := by
  dsimp only
  let K := G * M / l
  let A := (G * H + M * C) / l + G * M * C / l ^ 2
  let R := (G * M * H + M * (G * H + M * C)) / l + G * M * M * C / l ^ 2
  let k (z : ℂ) := B z t t
  let a (z : ℂ) := B z (v z) t / k z
  let b (z : ℂ) := B z (w z) t / k z
  let Rvv (z : ℂ) := B z (v z) (v z) / k z
  let Rww (z : ℂ) := B z (w z) (w z) / k z
  let Rvw (z : ℂ) := B z (v z) (w z) / k z
  have hc : HolderOnWith 0 α (fun _ : ℂ => t) s := by
    intro x hx y hy
    simp only [edist_self, zero_le]
  have htn : ∀ z ∈ s, ‖(fun _ : ℂ => t) z‖ ≤ (1 : ℝ≥0) := fun _ _ => ht
  have hk : HolderOnWith C α k s := by
    simpa only [k, mul_one, mul_zero, add_zero, zero_add, one_mul] using
      holderOn_bilin_apply hB hc hc hBn htn htn
  have hnum (u : ℂ → V) (hun : ∀ z ∈ s, ‖u z‖ ≤ M) (z : ℂ) (hz : z ∈ s) :
      ‖B z (u z) t‖ ≤ ((G * M : ℝ≥0) : ℝ) := by
    simpa only [mul_one, NNReal.coe_mul, NNReal.coe_one] using
      norm_bilin_apply_le (hBn z hz) (hun z hz) (show ‖t‖ ≤ (1 : ℝ≥0) from ht)
  have ha : HolderOnWith A α a s := by
    simpa only [A, a, mul_zero, add_zero, zero_add, one_mul] using
      holderOn_div hl (holderOn_bilin_apply hB hv hc hBn hvn htn) hk (hnum v hvn) hBt
  have hb : HolderOnWith A α b s := by
    simpa only [A, b, mul_zero, add_zero, zero_add, one_mul] using
      holderOn_div hl (holderOn_bilin_apply hB hw hc hBn hwn htn) hk (hnum w hwn) hBt
  have hnorm (u : ℂ → V) (hun : ∀ z ∈ s, ‖u z‖ ≤ M) (z : ℂ) (hz : z ∈ s) :
      ‖B z (u z) t / k z‖ ≤ (K : ℝ) := by
    rw [norm_div, Real.norm_of_nonneg ((show (0 : ℝ) < l from hl).le.trans (hBt z hz))]
    exact div_le_div₀ (by positivity) (hnum u hun z hz) (show (0 : ℝ) < l from hl) (hBt z hz)
  have han : ∀ z ∈ s, ‖a z‖ ≤ K := hnorm v hvn
  have hbn : ∀ z ∈ s, ‖b z‖ ≤ K := hnorm w hwn
  have hr (u v' : ℂ → V) (hu' : HolderOnWith H α u s) (hv' : HolderOnWith H α v' s)
      (hun : ∀ z ∈ s, ‖u z‖ ≤ M) (hvn' : ∀ z ∈ s, ‖v' z‖ ≤ M) :
      HolderOnWith R α (fun z => B z (u z) (v' z) / k z) s := by
    apply holderOn_div hl (holderOn_bilin_apply hB hu' hv' hBn hun hvn') hk
    · intro z hz
      simpa only [NNReal.coe_mul] using norm_bilin_apply_le (hBn z hz) (hun z hz) (hvn' z hz)
    · exact hBt
  have hvv : HolderOnWith R α Rvv s := hr v v hv hv hvn hvn
  have hww : HolderOnWith R α Rww s := hr w w hw hw hwn hwn
  have hvw : HolderOnWith R α Rvw s := hr v w hv hw hvn hwn
  have haa : HolderOnWith (2 * K * A) α (fun z => a z ^ 2) s := by
    convert holderOn_mul ha ha han han using 1 <;> (try simp only [pow_two])
    ring
  have hbb : HolderOnWith (2 * K * A) α (fun z => b z ^ 2) s := by
    convert holderOn_mul hb hb hbn hbn using 1 <;> (try simp only [pow_two])
    ring
  have hab : HolderOnWith (2 * K * A) α (fun z => a z * b z) s := by
    convert holderOn_mul ha hb han hbn using 1
    ring
  have hreal := holderOn_add (holderOn_sub (holderOn_sub haa hbb) hvv) hww
  have himag := holderOn_sub (holderOn_twice hab) (holderOn_twice hvw)
  have hQ : HolderOnWith (8 * K * A + 4 * R) α
      (fun z => ((a z ^ 2 - b z ^ 2 - Rvv z + Rww z : ℝ) : ℂ) +
        ((2 * (a z * b z) - 2 * Rvw z : ℝ) : ℂ) * Complex.I) s := by
    convert holderOn_complex_pair hreal himag using 1
    · rfl
    · ring
  have hA : HolderOnWith (2 * A) α (fun z => (a z : ℂ) + (b z : ℂ) * Complex.I) s := by
    simpa only [two_mul] using holderOn_complex_pair ha hb
  apply holderOn_fderivWithin_of_sq_add_eq hs hu hf hα hdiam hA hQ
  intro z hz
  have hh := sq_add_eq_of_conformal_pair (B z) (hBs z hz) (v z) (w z) t
    (fderivWithin ℝ f s z 1) (fderivWithin ℝ f s z Complex.I)
    ((show (0 : ℝ) < l from hl).trans_le (hBt z hz)).ne' (horth z hz) (heq z hz)
  dsimp only [a, b, k, Rvv, Rww, Rvw]
  convert hh using 1 <;> push_cast <;> ring

private theorem lipschitzOnWith_comp_of_derivative_bounds
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set E} (hs : Convex ℝ s) {X : E → V} {g : V → W}
    (hX : DifferentiableOn ℝ X s) (hg : ∀ z ∈ s, DifferentiableAt ℝ g (X z))
    {G L : ℝ≥0} (hDX : ∀ z ∈ s, ‖fderivWithin ℝ X s z‖ ≤ L)
    (hDg : ∀ z ∈ s, ‖fderiv ℝ g (X z)‖ ≤ G) :
    LipschitzOnWith (G * L) (g ∘ X) s := by
  apply hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz => (hg z hz).hasFDerivAt.comp_hasFDerivWithinAt z (hX z hz).hasFDerivWithinAt)
  intro z hz
  apply NNReal.coe_le_coe.mp
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hDg z hz) (hDX z hz) (norm_nonneg _) G.coe_nonneg)

private theorem holderOn_clm_apply_unit
    {E V W : Type*} [MetricSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set E} {C α : ℝ≥0} {f : E → V →L[ℝ] W} {v : V}
    (hf : HolderOnWith C α f s) (hv : ‖v‖ ≤ 1) :
    HolderOnWith C α (fun z => f z v) s := by
  apply holderOn_of_dist_le
  intro x hx y hy
  calc
    dist (f x v) (f y v) = ‖(f x - f y) v‖ := by rw [dist_eq_norm]; rfl
    _ ≤ ‖f x - f y‖ * ‖v‖ := (f x - f y).le_opNorm v
    _ ≤ ‖f x - f y‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ ≤ C * dist x y ^ (α : ℝ) := by simpa only [dist_eq_norm] using hf.dist_le hx hy

private theorem fderivWithin_sub_smul_const_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} (hu : UniqueDiffOn ℝ s) {X : ℂ → V} {f : ℂ → ℝ}
    (hX : DifferentiableOn ℝ X s) (hf : DifferentiableOn ℝ f s) (t : V)
    {z : ℂ} (hz : z ∈ s) :
    fderivWithin ℝ (fun z => X z - f z • t) s z + (fderivWithin ℝ f s z).smulRight t =
      fderivWithin ℝ X s z := by
  have h := ((hX z hz).hasFDerivWithinAt.sub ((hf z hz).hasFDerivWithinAt.smul_const t)).fderivWithin (hu z hz)
  change fderivWithin ℝ (fun z => X z - f z • t) s z = _ at h
  rw [h]
  exact sub_add_cancel _ _

private theorem holderOn_recover_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} (hu : UniqueDiffOn ℝ s) {X : ℂ → V} {f : ℂ → ℝ} {t : V}
    (hX : DifferentiableOn ℝ X s) (hf : DifferentiableOn ℝ f s)
    {A C α : ℝ≥0} (ht : ‖t‖ ≤ 1)
    (hY : HolderOnWith A α (fderivWithin ℝ (fun z => X z - f z • t) s) s)
    (hZ : HolderOnWith C α (fderivWithin ℝ f s) s) :
    HolderOnWith (A + C) α (fderivWithin ℝ X s) s := by
  apply holderOn_of_dist_le
  intro x hx y hy
  rw [dist_eq_norm, ← fderivWithin_sub_smul_const_add hu hX hf t hx,
    ← fderivWithin_sub_smul_const_add hu hX hf t hy]
  have he :
      (fderivWithin ℝ (fun z => X z - f z • t) s x + (fderivWithin ℝ f s x).smulRight t) -
        (fderivWithin ℝ (fun z => X z - f z • t) s y + (fderivWithin ℝ f s y).smulRight t) =
      (fderivWithin ℝ (fun z => X z - f z • t) s x - fderivWithin ℝ (fun z => X z - f z • t) s y) +
        (fderivWithin ℝ f s x - fderivWithin ℝ f s y).smulRight t := by
    ext u
    simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖fderivWithin ℝ (fun z => X z - f z • t) s x - fderivWithin ℝ (fun z => X z - f z • t) s y‖ +
      ‖(fderivWithin ℝ f s x - fderivWithin ℝ f s y).smulRight t‖ := norm_add_le _ _
    _ ≤ (A : ℝ) * dist x y ^ (α : ℝ) + C * dist x y ^ (α : ℝ) := by
      apply add_le_add
      · simpa only [dist_eq_norm] using hY.dist_le hx hy
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        calc
          _ ≤ ‖fderivWithin ℝ f s x - fderivWithin ℝ f s y‖ := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (norm_nonneg _)
          _ ≤ _ := by simpa only [dist_eq_norm] using hZ.dist_le hx hy
    _ = ((A + C : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by push_cast; ring

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private local instance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

theorem holderOnWith_fderivWithin_of_conformal_transverse
    {s : Set ℂ} (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s)
    {X : ℂ → V} {f : ℂ → ℝ} (hX : DifferentiableOn ℝ X s) (hf : ContDiffOn ℝ 1 f s)
    {g : V → V →L[ℝ] V →L[ℝ] ℝ} {t : V}
    {G G' L H M l α D : ℝ≥0} (hl : 0 < l) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g (X z))
    (hDg : ∀ z ∈ s, ‖fderiv ℝ g (X z)‖ ≤ (G' : ℝ))
    (hDX : ∀ z ∈ s, ‖fderivWithin ℝ X s z‖ ≤ L)
    (hY : HolderOnWith H α (fderivWithin ℝ (fun z => X z - f z • t) s) s)
    (hDY : ∀ z ∈ s, ‖fderivWithin ℝ (fun z => X z - f z • t) s z‖ ≤ M)
    (hgn : ∀ z ∈ s, ‖g (X z)‖ ≤ G) (ht : ‖t‖ ≤ 1)
    (hgs : ∀ z ∈ s, (g (X z)).toBilinForm.IsSymm)
    (hgt : ∀ z ∈ s, (l : ℝ) ≤ g (X z) t t)
    (horth : ∀ z ∈ s, g (X z) (fderivWithin ℝ X s z 1) (fderivWithin ℝ X s z Complex.I) = 0)
    (heq : ∀ z ∈ s, g (X z) (fderivWithin ℝ X s z 1) (fderivWithin ℝ X s z 1) =
      g (X z) (fderivWithin ℝ X s z Complex.I) (fderivWithin ℝ X s z Complex.I)) :
    let C := G' * L * D ^ ((1 : ℝ) - (α : ℝ))
    let K := G * M / l
    let A := (G * H + M * C) / l + G * M * C / l ^ 2
    let R := (G * M * H + M * (G * H + M * C)) / l + G * M * M * C / l ^ 2
    let Z := NNReal.sqrt (6 * (8 * K * A + 4 * R)) + (2 * A) * D ^ ((α : ℝ) - (α / 2 : ℝ≥0))
    HolderOnWith Z (α / 2) (fderivWithin ℝ f s) s ∧
      HolderOnWith (H * D ^ ((α : ℝ) - (α / 2 : ℝ≥0)) + Z) (α / 2) (fderivWithin ℝ X s) s := by
  dsimp only
  let B := g ∘ X
  let v (z : ℂ) := fderivWithin ℝ (fun z => X z - f z • t) s z 1
  let w (z : ℂ) := fderivWithin ℝ (fun z => X z - f z • t) s z Complex.I
  have hXd := hX
  have hfd := hf.differentiableOn (by norm_num)
  have hB := (lipschitzOnWith_comp_of_derivative_bounds hs hXd hg hDX hDg).holderOnWith.of_le hdiam hα1
  have hv : HolderOnWith H α v s := holderOn_clm_apply_unit hY (by simp)
  have hw : HolderOnWith H α w s := holderOn_clm_apply_unit hY (by simp)
  have hnorm (u : ℂ) (hun : ‖u‖ ≤ 1) (z : ℂ) (hz : z ∈ s) :
      ‖fderivWithin ℝ (fun z => X z - f z • t) s z u‖ ≤ M := by
    calc
      _ ≤ ‖fderivWithin ℝ (fun z => X z - f z • t) s z‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M : ℝ) * 1 := mul_le_mul (hDY z hz) hun (norm_nonneg _) M.coe_nonneg
      _ = M := mul_one _
  have hdec (z : ℂ) (hz : z ∈ s) (u : ℂ) :
      fderivWithin ℝ (fun z => X z - f z • t) s z u + fderivWithin ℝ f s z u • t =
        fderivWithin ℝ X s z u := by
    exact congrArg (fun L : ℂ →L[ℝ] V => L u) (fderivWithin_sub_smul_const_add hu hXd hfd t hz)
  have ho (z : ℂ) (hz : z ∈ s) : B z (v z + fderivWithin ℝ f s z 1 • t)
      (w z + fderivWithin ℝ f s z Complex.I • t) = 0 := by
    dsimp only [v, w, B, Function.comp_def]
    rw [hdec z hz, hdec z hz]
    exact horth z hz
  have he (z : ℂ) (hz : z ∈ s) : B z (v z + fderivWithin ℝ f s z 1 • t)
      (v z + fderivWithin ℝ f s z 1 • t) =
      B z (w z + fderivWithin ℝ f s z Complex.I • t) (w z + fderivWithin ℝ f s z Complex.I • t) := by
    dsimp only [v, w, B, Function.comp_def]
    rw [hdec z hz, hdec z hz]
    exact heq z hz
  have hfH := holderOnWith_fderivWithin_of_conformal_pair hs hu hf hl hα hdiam hB hv hw hgn
    (hnorm 1 (by simp)) (hnorm Complex.I (by simp)) ht hgs hgt ho he
  refine ⟨?_, ?_⟩
  · simpa only [NNReal.coe_one] using hfH
  · apply holderOn_recover_derivative hu hXd hfd ht
      (hY.of_le hdiam (show α / 2 ≤ α from div_le_self (by positivity) (by norm_num)))
    simpa only [NNReal.coe_one] using hfH

end

end DifferentialGeometry.Analysis
