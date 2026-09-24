import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.BoundaryNormalDerivative
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle

open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

theorem fderiv_norm_sq_saddleBandLevelCurve_neg
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {s τ σ k r u : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r) (hu : u ∈ Ioo (-k) k)
    (hcurve : ∀ v ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ v) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (huV : saddleBandLevelCurve s τ σ u ∈ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r) :
    fderiv ℝ
      (fun p : ℝ × ℝ => ‖G.symm (B (saddleBandLevelCurve s p.1 σ p.2))‖ ^ 2)
      (τ, u) (1, 0) < 0 := by
  obtain ⟨χ, hχsource, hχfun, _⟩ := exists_partialDiffeomorph_saddleBandLevelCurve hs hσ
  have huone : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans hk⟩
  have hχu : (τ, u) ∈ χ.source := by rw [hχsource]; exact ⟨hτ, huone⟩
  let ψ := χ.trans (B.trans G.symm).toPartialDiffeomorph
  have hψsource : (τ, u) ∈ ψ.source := ⟨hχu, mem_univ _⟩
  have hψfun : (ψ : (ℝ × ℝ) → F) =
      fun p => G.symm (B (saddleBandLevelCurve s p.1 σ p.2)) := by
    change (fun p => G.symm (B (χ p))) = _
    rw [hχfun]
  have hface : ∀ᶠ v in 𝓝 u, ‖ψ (τ, v)‖ = r := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    obtain ⟨y, hy, hyeq⟩ := hcurve v hv
    rw [hψfun]
    change ‖G.symm (B (saddleBandLevelCurve s τ σ v))‖ = r
    rw [← hyeq, G.symm_apply_apply]
    simpa only [mem_sphere, dist_zero_right] using hy
  have hχcont := χ.toOpenPartialHomeomorph.continuousAt hχu
  change ContinuousAt χ (τ, u) at hχcont
  have hVpre : ∀ᶠ p in 𝓝 (τ, u), χ p ∈ V :=
    hχcont.eventually (hV.mem_nhds (by simpa only [hχfun] using huV))
  have hside' : ∀ᶠ p in 𝓝 (τ, u), τ ≤ p.1 → ‖ψ p‖ ≤ r := by
    filter_upwards [hVpre, χ.open_source.mem_nhds hχu] with p hpV hpχ hτp
    have hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1 := hχsource ▸ hpχ
    have hheight := saddleBandLevelCurve_height hs hp.1 hσ hp.2 (0 : ℝ)
    have hpball : B (χ p) ∈ G '' closedBall 0 r := by
      apply hside (χ p) hpV
      rw [hχfun]
      change s + τ ≤ (1 - (saddleBandLevelCurve s p.1 σ p.2).1 ^ 2) *
        ((saddleBandLevelCurve s p.1 σ p.2).2 ^ 2 + 2 * s) / 2
      linarith
    obtain ⟨y, hy, hyeq⟩ := hpball
    change ‖G.symm (B (χ p))‖ ≤ r
    rw [← hyeq, G.symm_apply_apply]
    exact mem_closedBall_zero_iff.mp hy
  have hψd := ((ψ.contMDiffOn.contDiffOn.contDiffAt
    (ψ.open_source.mem_nhds hψsource)).differentiableAt (by simp)).hasFDerivAt
  have hψsurj := (Analysis.bijective_fderiv_of_partialDiffeomorph ψ hψsource).surjective
  have hf := Analysis.fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall
    hψd hψsurj hr (d := 0)
    (by simpa only [mem_sphere, dist_zero_right] using hface)
    (by simpa only [mem_closedBall, dist_zero_right] using hside')
  simpa only [sub_zero, hψfun] using hf

theorem exists_neg_fderiv_norm_sq_eq_smul_fderiv_saddle_height
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {s τ σ k r u : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r) (hu : u ∈ Ioo (-k) k)
    (hcurve : ∀ v ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ v) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (huV : saddleBandLevelCurve s τ σ u ∈ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r) :
    let p := B (saddleBandLevelCurve s τ σ u)
    ∃ a : ℝ, a < 0 ∧
      fderiv ℝ (fun x => ‖G.symm x‖ ^ 2) p =
        a • fderiv ℝ (fun x =>
          (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2) p := by
  let p := B (saddleBandLevelCurve s τ σ u)
  let H : F → ℝ := fun x => ‖G.symm x‖ ^ 2
  let q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  obtain ⟨χ, hχsource, hχfun, _⟩ := exists_partialDiffeomorph_saddleBandLevelCurve hs hσ
  have huone : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans hk⟩
  have hχu : (τ, u) ∈ χ.source := by rw [hχsource]; exact ⟨hτ, huone⟩
  let ψ := χ.trans B.toPartialDiffeomorph
  have hψsource : (τ, u) ∈ ψ.source := ⟨hχu, mem_univ _⟩
  have hψfun : (ψ : (ℝ × ℝ) → F) =
      fun z => B (saddleBandLevelCurve s z.1 σ z.2) := by
    change (fun z => B (χ z)) = _
    rw [hχfun]
  have hψp : ψ (τ, u) = p := congrFun hψfun (τ, u)
  have hψd := ((ψ.contMDiffOn.contDiffOn.contDiffAt
    (ψ.open_source.mem_nhds hψsource)).differentiableAt (by simp)).hasFDerivAt
  have hHd : HasFDerivAt H (fderiv ℝ H p) p :=
    ((G.symm.contDiff.differentiable (by simp) p).hasFDerivAt.norm_sq).differentiableAt.hasFDerivAt
  have hqd : HasFDerivAt q (fderiv ℝ q p) p := by
    have hq : ContDiff ℝ ∞ q := by
      exact ((contDiff_const.sub (B.symm.contDiff.fst.pow 2)).mul
        ((B.symm.contDiff.snd.pow 2).add contDiff_const)).div_const 2
    exact (hq.differentiable (by simp) p).hasFDerivAt
  let L := (fderiv ℝ H p).comp (fderiv ℝ ψ (τ, u))
  have hHp : HasFDerivAt H (fderiv ℝ H p) (ψ (τ, u)) := by rwa [hψp]
  have hqp : HasFDerivAt q (fderiv ℝ q p) (ψ (τ, u)) := by rwa [hψp]
  have hLd : HasFDerivAt (H ∘ ψ) L (τ, u) := hHp.comp (τ, u) hψd
  have hface : (fun v => (H ∘ ψ) (τ, v)) =ᶠ[𝓝 u] fun _ => r ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    obtain ⟨y, hy, hyeq⟩ := hcurve v hv
    change ‖G.symm (ψ (τ, v))‖ ^ 2 = r ^ 2
    rw [hψfun]
    change ‖G.symm (B (saddleBandLevelCurve s τ σ v))‖ ^ 2 = r ^ 2
    rw [← hyeq, G.symm_apply_apply]
    congr 1
    simpa only [mem_sphere, dist_zero_right] using hy
  have hin : HasFDerivAt (fun v : ℝ => (τ, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) u :=
    (hasFDerivAt_const τ u).prodMk (hasFDerivAt_id u)
  have hzero (v : ℝ) : L (0, v) = 0 :=
    congrArg (fun A : ℝ →L[ℝ] ℝ => A v)
      (((hLd.comp u hin).congr_of_eventuallyEq hface.symm).unique
        (hasFDerivAt_const (𝕜 := ℝ) (r ^ 2) u))
  have hneg : L (1, 0) < 0 := by
    rw [← hLd.fderiv]
    simpa only [H, Function.comp_def, hψfun] using
      fderiv_norm_sq_saddleBandLevelCurve_neg B G hs hτ hσ hk hr hu hcurve hV huV hside
  have hqeq : q ∘ ψ =ᶠ[𝓝 (τ, u)] fun z => s + z.1 := by
    filter_upwards [χ.open_source.mem_nhds hχu] with z hz
    have hz' : z ∈ Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1 := hχsource ▸ hz
    change (1 - (B.symm (ψ z)).1 ^ 2) * ((B.symm (ψ z)).2 ^ 2 + 2 * s) / 2 = s + z.1
    rw [hψfun]
    simp only [B.symm_apply_apply]
    simpa only [zero_add] using saddleBandLevelCurve_height hs hz'.1 hσ hz'.2 (0 : ℝ)
  have hqder : (fderiv ℝ q p).comp (fderiv ℝ ψ (τ, u)) =
      ContinuousLinearMap.fst ℝ ℝ ℝ := by
    exact (((hqp.comp (τ, u) hψd).congr_of_eventuallyEq hqeq.symm).unique
      (hasFDerivAt_fst.const_add s))
  refine ⟨L (1, 0), hneg, ?_⟩
  change fderiv ℝ H p = L (1, 0) • fderiv ℝ q p
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (Analysis.bijective_fderiv_of_partialDiffeomorph ψ hψsource).surjective v
  have hqw := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A w) hqder
  change (fderiv ℝ q p) ((fderiv ℝ ψ (τ, u)) w) = w.1 at hqw
  change L w = L (1, 0) * (fderiv ℝ q p) ((fderiv ℝ ψ (τ, u)) w)
  rw [hqw]
  have hw : w = w.1 • (1, (0 : ℝ)) + (0, w.2) := by ext <;> simp
  calc
    L w = L (w.1 • (1, (0 : ℝ)) + (0, w.2)) := congrArg L hw
    _ = L (1, 0) * w.1 := by rw [map_add, map_smul, hzero]; simp [mul_comm]

theorem fderiv_saddle_height_radial_neg
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {s τ σ k r u : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r) (hu : u ∈ Ioo (-k) k)
    (hcurve : ∀ v ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ v) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (huV : saddleBandLevelCurve s τ σ u ∈ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r) :
    let p := B (saddleBandLevelCurve s τ σ u)
    fderiv ℝ (fun x =>
      (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2) p
      (fderiv ℝ G (G.symm p) (G.symm p)) < 0 := by
  intro p
  let H : F → ℝ := fun x => ‖G.symm x‖ ^ 2
  let q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  obtain ⟨α, hα, hαeq⟩ := exists_neg_fderiv_norm_sq_eq_smul_fderiv_saddle_height
    B G hs hτ hσ hk hr hu hcurve hV huV hside
  change fderiv ℝ H p = α • fderiv ℝ q p at hαeq
  have hcomp : H ∘ G = fun x : F => ‖x‖ ^ 2 := by
    funext x
    simp only [H, Function.comp_apply, G.symm_apply_apply]
  have hH : ContDiff ℝ ∞ H := G.symm.contDiff.norm_sq ℝ
  have hderiv : (fderiv ℝ H p).comp (fderiv ℝ G (G.symm p)) =
      fderiv ℝ (fun x : F => ‖x‖ ^ 2) (G.symm p) := by
    rw [← hcomp, fderiv_comp _ (hH.differentiable (by simp) _) (G.contDiff.differentiable (by simp) _),
      G.apply_symm_apply]
  have hnorm : ‖G.symm p‖ = r := by
    obtain ⟨x, hx, hxp⟩ := hcurve u hu
    change G x = p at hxp
    rw [← hxp, G.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp hx
  have hpos : 0 < fderiv ℝ H p (fderiv ℝ G (G.symm p) (G.symm p)) := by
    change 0 < ((fderiv ℝ H p).comp (fderiv ℝ G (G.symm p))) (G.symm p)
    rw [hderiv]
    have hd := (hasFDerivAt_id (𝕜 := ℝ) (G.symm p)).norm_sq
    simp only [id_eq] at hd
    rw [hd.fderiv]
    simpa [real_inner_self_eq_norm_sq, hnorm] using mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hr)
  rw [hαeq] at hpos
  change 0 < α * (fderiv ℝ q p (fderiv ℝ G (G.symm p) (G.symm p))) at hpos
  exact (mul_pos_iff.mp hpos).resolve_left (fun h => (not_lt_of_ge hα.le h.1)) |>.2

end DifferentialGeometry.Topology.Morse
