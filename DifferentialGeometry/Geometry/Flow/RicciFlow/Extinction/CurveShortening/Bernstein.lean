import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.DerivativeEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IntegralBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {D : RealTimeInterval} {a b s u : ℝ}
namespace CurveMap

private theorem scalar_linear_upper_bound (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u)) (f : ℝ → ℝ → ℝ)
    (hper : ∀ t ∈ Icc s u, Function.Periodic (fun x => f x t) 1)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
    (L F : ℝ)
    (hpde : ∀ x t, t ∈ Icc s u → derivWithin (f x) (Icc s u) t ≤ c.ds g (c.ds g f) x t + F)
    (hinit : ∀ x, f x s ≤ L) :
    ∀ x t, t ∈ Icc s u → f x t ≤ L + F * (t - s) := by
  classical
  let fbar : CurveMap ℝ := fun x t => if ht : t ∈ Icc s u then (hper t ht).lift x else 0
  have heq (x t : ℝ) (ht : t ∈ Icc s u) : fbar.lift x t = f x t := by
    simp only [CurveMap.lift, fbar, dif_pos ht, Function.Periodic.lift_coe]
  have hfbar : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fbar.lift p.1 p.2) (univ ×ˢ Icc s u) :=
    hf.congr (fun p hp => heq p.1 p.2 hp.2)
  have hspace (t : ℝ) (ht : t ∈ Icc s u) : (fun x => fbar.lift x t) = fun x => f x t :=
    funext (fun x => heq x t ht)
  have hds (x t : ℝ) (ht : t ∈ Icc s u) : c.ds g (c.ds g fbar.lift) x t = c.ds g (c.ds g f) x t := by
    simp only [CurveMap.ds, hspace t ht]
  have hdt (x t : ℝ) (ht : t ∈ Icc s u) : derivWithin (fbar.lift x) (Icc s u) t =
      derivWithin (f x) (Icc s u) t := derivWithin_congr (fun r hr => heq x r hr) (heq x t ht)
  have hh := rfs_csf_maximum_principle g hsu c hc hi fbar (fun _ _ => 0) hfbar
    (by change ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) _; exact contDiffOn_const)
    0 (fun _ => F) (fun t => L + F * (t - s)) continuousOn_const (by
      intro t ht
      convert ((((hasDerivAt_id t).sub_const s).const_mul F).const_add L).hasDerivWithinAt using 1 <;> first | rfl | simp)
    (by
      intro x t ht
      change derivWithin (fbar.lift x) (Icc s u) t ≤ c.ds g (c.ds g fbar.lift) x t + 0 * _ + 0 * _ + F
      rw [hdt x t ht, hds x t ht]
      simpa only [zero_mul, add_zero] using hpde x t ht)
    (by intro x; simpa only [heq x s ⟨le_rfl, hsu.le⟩, sub_self, mul_zero, add_zero] using hinit x)
  intro x t ht
  simpa only [heq x t ht] using hh x t ht

theorem curvatureDerivative_bernstein_bound
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (C Λ : ℝ) (hC : B.C ≤ C) (hΛ : 1 ≤ Λ) (hlen : u - s = 1 / Λ)
    (hk : ∀ x t, t ∈ Icc s u → c.curvatureSq B.family.metric x t ≤ Λ)
    (hDR : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 5
      (totalNabla0SFun 4 (B.family.connection t) (B.family.rm04 t) (c.lift x t)) ≤ C ^ 2)
    (hDDRic : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 4
      (totalNabla0SFun 3 (B.family.connection t)
        (covStep (B.family.metric t) 2 (B.family.ricci t)) (c.lift x t)) ≤ C ^ 2) :
    ∀ x, c.normSq B.family.metric (c.Ds B.family.metric (c.curvatureVector B.family.metric)) x u ≤
      4 * (1 + 64 * (1 + C)) ^ 2 * Λ ^ 2 := by
  let g := B.family.metric
  let Hc := c.curvatureVector g
  let V := c.Ds g Hc
  let f0 := c.curvatureSq g
  let f1 := c.normSq g V
  let d := 64 * (1 + C)
  let b := 1 + d
  let F : ℝ → ℝ → ℝ := fun x t => (t - s) * f1 x t + b * f0 x t
  have hJ : Icc s u ⊆ D.regular := fun t ht => B.regular (hwindow ht)
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV := Field.smoothOn_Ds g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed Hc hH
  have hf0 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f0 p.1 p.2) (univ ×ˢ Icc s u) :=
    Field.smoothOn_inner g B.smooth hJ c hc.smooth Hc Hc hH hH
  have hf1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f1 p.1 p.2) (univ ×ˢ Icc s u) :=
    Field.smoothOn_inner g B.smooth hJ c hc.smooth V V hV hV
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc s u) :=
    ((contDiffOn_snd.sub contDiffOn_const).mul hf1).add (contDiffOn_const.mul hf0)
  have hper : ∀ t ∈ Icc s u, Function.Periodic (fun x => F x t) 1 := by
    intro t ht
    have hγ (x : ℝ) := (contMDiffOn_univ.mp (c.space_slice_contMDiffOn (Icc s u) hc.smooth t ht)).mdifferentiable (by simp) x
    have hDs (Z : c.Field (I := I)) (hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M)))
        (hZper : Function.Periodic (fun x => Z x t) 1) :
        Function.Periodic (fun x => c.Ds g Z x t) 1 := by
      intro x
      dsimp only [CurveMap.Ds]
      rw [c.speed_add_period g t x (hγ (x + 1)), c.Dx_add_period g t x Z hZper hZ (hγ (x + 1))]
      rfl
    have hHp : Function.Periodic (fun x => Hc x t) 1 := hDs (c.unitTangent g)
      (c.unitTangent_contMDiff g (Icc s u) hc.smooth hc.immersed t ht)
      (fun x => c.unitTangent_add_period g t x (hγ (x + 1)))
    have hVp : Function.Periodic (fun x => V x t) 1 := hDs Hc
      (c.curvatureVector_contMDiff g (Icc s u) hc.smooth hc.immersed t ht) hHp
    intro x
    change (t - s) * (g t).inner (c.lift (x + 1) t) (V (x + 1) t) (V (x + 1) t) +
      b * (g t).inner (c.lift (x + 1) t) (Hc (x + 1) t) (Hc (x + 1) t) = _
    have hHp' : Hc (x + 1) t = Hc x t := hHp x
    have hVp' : V (x + 1) t = V x t := hVp x
    have hl : c.lift (x + 1) t = c.lift x t := c.lift_add_period t x
    rw [hHp', hVp', hl]
    rfl
  have hspace (f : ℝ → ℝ → ℝ)
      (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
      (t : ℝ) (ht : t ∈ Icc s u) : ContDiff ℝ ∞ (fun x => f x t) := by
    have hh := hf.comp ((contDiff_id.prodMk contDiff_const).contDiffOn (s := univ))
      (fun x _ => ⟨mem_univ x, ht⟩)
    exact contDiffOn_univ.mp hh
  have hdspace (f : ℝ → ℝ → ℝ)
      (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
      (t : ℝ) (ht : t ∈ Icc s u) : ContDiff ℝ ∞ (fun x => c.ds g f x t) := by
    have hh : ContDiff ℝ ∞ (fun x => deriv (fun y => f y t) x) := by
      simpa using (hspace f hf t ht).iterate_deriv 1
    exact ((c.speed_contDiff g (Icc s u) hc.smooth hc.immersed t ht).inv
      (fun x => (c.speed_pos g hc.immersed x t ht).ne')).mul hh
  have htime (f : ℝ → ℝ → ℝ)
      (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u))
      (x t : ℝ) (ht : t ∈ Icc s u) : DifferentiableWithinAt ℝ (f x) (Icc s u) t := by
    have hp : ContDiffWithinAt ℝ ∞ (fun r : ℝ => (x, r)) (Icc s u) t :=
      contDiffWithinAt_const.prodMk contDiffWithinAt_id
    exact ((hf (x, t) ⟨mem_univ x, ht⟩).comp t hp (fun r hr => ⟨mem_univ x, hr⟩)).differentiableWithinAt (by simp)
  have hds (x t : ℝ) (ht : t ∈ Icc s u) :
      c.ds g F x t = (t - s) * c.ds g f1 x t + b * c.ds g f0 x t := by
    have h1 := (hspace f1 hf1 t ht).differentiable (by simp) x
    have h0 := (hspace f0 hf0 t ht).differentiable (by simp) x
    dsimp only [CurveMap.ds, F]
    rw [deriv_fun_add (h1.const_mul (t - s)) (h0.const_mul b), deriv_const_mul_field, deriv_const_mul_field]
    ring
  have hlap (x t : ℝ) (ht : t ∈ Icc s u) :
      c.ds g (c.ds g F) x t = (t - s) * c.ds g (c.ds g f1) x t + b * c.ds g (c.ds g f0) x t := by
    have h1 := (hdspace f1 hf1 t ht).differentiable (by simp) x
    have h0 := (hdspace f0 hf0 t ht).differentiable (by simp) x
    change (c.speed g x t)⁻¹ * deriv (fun y => c.ds g F y t) x = _
    rw [funext (fun y => hds y t ht), deriv_fun_add (h1.const_mul (t - s)) (h0.const_mul b),
      deriv_const_mul_field, deriv_const_mul_field]
    dsimp only [CurveMap.ds]
    ring
  have hdt (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (F x) (Icc s u) t = f1 x t + (t - s) * derivWithin (f1 x) (Icc s u) t +
        b * derivWithin (f0 x) (Icc s u) t := by
    have h1 := (htime f1 hf1 x t ht).hasDerivWithinAt
    have h0 := (htime f0 hf0 x t ht).hasDerivWithinAt
    have hθ : HasDerivWithinAt (fun r : ℝ => r - s) 1 (Icc s u) t :=
      (hasDerivWithinAt_id t (Icc s u)).sub_const s
    have hh := ((hθ.mul h1).add (h0.const_mul b)).derivWithin (uniqueDiffOn_Icc hsu t ht)
    change derivWithin (F x) (Icc s u) t = _ at hh
    simpa only [one_mul, mul_one] using hh
  have hC0 : 0 ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hd1 : 1 ≤ d := by dsimp only [d]; linarith only [hC0]
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hpde : ∀ x t, t ∈ Icc s u →
      derivWithin (F x) (Icc s u) t ≤ c.ds g (c.ds g F) x t + (d + b * d) * Λ ^ 2 := by
    intro x t ht
    have hθ0 : 0 ≤ t - s := sub_nonneg.mpr ht.1
    have hθ : t - s ≤ 1 / Λ := by rw [← hlen]; linarith only [ht.2]
    have hθΛ : Λ * (t - s) ≤ 1 := by nlinarith only [(le_div_iff₀ hΛpos).mp hθ]
    have hθ1 : t - s ≤ 1 := by nlinarith only [hθΛ, mul_nonneg (sub_nonneg.mpr hΛ) hθ0]
    have h1 := c.curvatureDerivative_evolution_le_of_tensor_bounds B hsu hwindow hc x t ht C Λ hC hΛ
      (hk x t ht) (hDR x t ht) (hDDRic x t ht)
    change derivWithin (f1 x) (Icc s u) t - c.ds g (c.ds g f1) x t ≤
      -c.normSq g (c.Ds g V) x t + d * Λ * f1 x t + d * Λ ^ 2 at h1
    have h1' : derivWithin (f1 x) (Icc s u) t - c.ds g (c.ds g f1) x t ≤
        d * Λ * f1 x t + d * Λ ^ 2 := h1.trans (by linarith [c.normSq_nonneg g (c.Ds g V) x t])
    have h0 := curvature_evolution_le_of_curvatureSq_le B hsu hwindow c hc x t ht hΛ (hk x t ht)
    change derivWithin (f0 x) (Icc s u) t - c.ds g (c.ds g f0) x t ≤
      -2 * f1 x t + (4 + 4 * B.C) * Λ ^ 2 at h0
    have hcoeff : 4 + 4 * B.C ≤ d := by dsimp only [d]; linarith only [hC, hC0]
    have h0' : derivWithin (f0 x) (Icc s u) t - c.ds g (c.ds g f0) x t ≤
        -2 * f1 x t + d * Λ ^ 2 :=
      h0.trans (by linarith only [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Λ)])
    have hh1 := mul_le_mul_of_nonneg_left h1' hθ0
    have hh0 := mul_le_mul_of_nonneg_left h0' hb0
    have hneg : 1 + d * Λ * (t - s) - 2 * b ≤ 0 := by
      dsimp only [b]
      nlinarith only [mul_le_mul_of_nonneg_left hθΛ hd0, hd1]
    have hn := mul_nonpos_of_nonpos_of_nonneg hneg (c.normSq_nonneg g V x t)
    have hforce := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hd0 (sq_nonneg Λ))
    rw [hdt x t ht, hlap x t ht]
    change (1 + d * Λ * (t - s) - 2 * b) * f1 x t ≤ 0 at hn
    linarith only [hh1, hh0, hn, hforce]
  have hinit : ∀ x, F x s ≤ b * Λ := by
    intro x
    have hh := mul_le_mul_of_nonneg_left (hk x s ⟨le_rfl, hsu.le⟩) hb0
    simpa only [F, sub_self, zero_mul, zero_add] using hh
  have hmp := scalar_linear_upper_bound g hsu c hc.smooth hc.immersed F hper hf
    (b * Λ) ((d + b * d) * Λ ^ 2) hpde hinit
  intro x
  have hx := hmp x u ⟨hsu.le, le_rfl⟩
  change (u - s) * f1 x u + b * f0 x u ≤ b * Λ + (d + b * d) * Λ ^ 2 * (u - s) at hx
  have hΛinv : Λ * (u - s) = 1 := by rw [hlen]; field_simp
  have hm := mul_le_mul_of_nonneg_left hx hΛpos.le
  have heqL : Λ * ((u - s) * f1 x u + b * f0 x u) = f1 x u + Λ * b * f0 x u := by
    calc
      _ = (Λ * (u - s)) * f1 x u + Λ * b * f0 x u := by ring
      _ = _ := by rw [hΛinv, one_mul]
  have heqR : Λ * (b * Λ + (d + b * d) * Λ ^ 2 * (u - s)) = (b + d + b * d) * Λ ^ 2 := by
    calc
      _ = b * Λ ^ 2 + (d + b * d) * Λ ^ 2 * (Λ * (u - s)) := by ring
      _ = _ := by rw [hΛinv]; ring
  rw [heqL, heqR] at hm
  have hn : 0 ≤ Λ * b * f0 x u :=
    mul_nonneg (mul_nonneg hΛpos.le hb0) (c.normSq_nonneg g Hc x u)
  have hcoeff : b + d + b * d ≤ 4 * b ^ 2 := by dsimp only [b]; nlinarith only [hd0, sq_nonneg d]
  have hfinal := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Λ)
  change f1 x u ≤ 4 * b ^ 2 * Λ ^ 2
  linarith only [hm, hn, hfinal]

theorem curvatureDerivative_bernstein_bound_of_curvatureSq_le_div
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (C K : ℝ) (hC : B.C ≤ C) (hK : 1 ≤ K) (hlen : u - s ≤ 1)
    (hk : ∀ x t, t ∈ Ioc s u → c.curvatureSq B.family.metric x t ≤ K / (t - s))
    (hDR : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 5
      (totalNabla0SFun 4 (B.family.connection t) (B.family.rm04 t) (c.lift x t)) ≤ C ^ 2)
    (hDDRic : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 4
      (totalNabla0SFun 3 (B.family.connection t)
        (covStep (B.family.metric t) 2 (B.family.ricci t)) (c.lift x t)) ≤ C ^ 2) :
    ∀ x, c.normSq B.family.metric (c.Ds B.family.metric (c.curvatureVector B.family.metric)) x u ≤
      16 * (1 + 64 * (1 + C)) ^ 2 * (K / (u - s)) ^ 2 := by
  let τ := u - s
  let Λ := 2 * K / τ
  let v := u - 1 / Λ
  have hτ : 0 < τ := sub_pos.mpr hsu
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hΛpos : 0 < Λ := by dsimp only [Λ]; positivity
  have hΛ : 1 ≤ Λ := by
    apply (le_div_iff₀ hτ).mpr
    change 1 * (u - s) ≤ 2 * K
    linarith only [hlen, hK]
  have hΛτ : Λ * τ = 2 * K := by dsimp only [Λ]; field_simp
  have hlength : 1 / Λ ≤ τ / 2 := by
    apply (div_le_iff₀ hΛpos).mpr
    nlinarith only [hΛτ, hK]
  have hv : s < v := by
    dsimp only [v]
    change 1 / Λ ≤ (u - s) / 2 at hlength
    linarith only [hlength, hsu]
  have hvu : v < u := by
    dsimp only [v]
    exact sub_lt_self u (one_div_pos.mpr hΛpos)
  have hI : Icc v u ⊆ Icc s u := Icc_subset_Icc hv.le le_rfl
  have hc' := hc.mono hI (fun t ht => (uniqueDiffOn_Icc hvu t ht).uniqueMDiffWithinAt)
  have hbound : ∀ x t, t ∈ Icc v u → c.curvatureSq B.family.metric x t ≤ Λ := by
    intro x t ht
    have hts : 0 < t - s := sub_pos.mpr (hv.trans_le ht.1)
    refine (hk x t ⟨hv.trans_le ht.1, ht.2⟩).trans ?_
    apply (div_le_div_iff₀ hts hτ).mpr
    have htime : τ ≤ 2 * (t - s) := by
      dsimp only [v, τ] at ht hlength ⊢
      linarith only [ht.1, hlength]
    nlinarith only [mul_le_mul_of_nonneg_left htime hK0]
  have hresult := c.curvatureDerivative_bernstein_bound B hvu (hI.trans hwindow) hc' C Λ hC hΛ
    (by dsimp only [v]; ring) hbound (fun x t ht => hDR x t (hI ht))
    (fun x t ht => hDDRic x t (hI ht))
  intro x
  refine (hresult x).trans_eq ?_
  dsimp only [Λ, τ]
  ring

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
