import DifferentialGeometry.Topology.SphereSeparation.OneSaddleBand
import DifferentialGeometry.Topology.SphereSeparation.OneSaddleCutoffStraightening
import DifferentialGeometry.Topology.SphereSeparation.TwoCriticalPoints
import DifferentialGeometry.Topology.Morse.ScalarComposition
import DifferentialGeometry.Topology.Morse.ConstantGerm
import DifferentialGeometry.Topology.Morse.Naturality

open Set Filter Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Topology.SphereSeparation

private theorem regular_height_data_of_saddle_removal
    {f g : SphereTwo → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    {p : SphereTwo}
    (hunique : ∀ x, IsCriticalPointAt (𝓡 2) f x → sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) x).symm y)) (extChartAt (𝓡 2) x x)) = 1 → x = p)
    (ψ : ℝ ≃ₘ[ℝ] ℝ) (hψd : ∀ t, 0 < deriv ψ t)
    (hremoved : ∀ x, IsCriticalPointAt (𝓡 2) g x → x ≠ p ∧ g =ᶠ[𝓝 x] ψ ∘ f) :
    (∀ x, IsCriticalPointAt (𝓡 2) g x → IsNondegenerateCriticalPointAt (𝓡 2) g x) ∧
      InjOn g {x | IsCriticalPointAt (𝓡 2) g x} ∧
      (∀ x, IsCriticalPointAt (𝓡 2) g x → sigNeg (chartHessianAt
        (fun y => g ((extChartAt (𝓡 2) x).symm y)) (extChartAt (𝓡 2) x x)) ≠ 1) := by
  have hφf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (ψ ∘ f) := ψ.contMDiff.comp hf
  have hcrit {x : SphereTwo} (hx : IsCriticalPointAt (𝓡 2) g x) : IsCriticalPointAt (𝓡 2) f x :=
    (isCriticalPointAt_scalar_comp_iff (hf.mdifferentiableAt (by simp))
      (ψ.contDiff.differentiable (by simp) _) (hψd _).ne').mp
        ((isCriticalPointAt_congr_of_eventuallyEq (hremoved x hx).2).mp hx)
  have hess {x : SphereTwo} (hx : IsCriticalPointAt (𝓡 2) g x) :
      sigNeg (chartHessianAt (fun y => g ((extChartAt (𝓡 2) x).symm y)) (extChartAt (𝓡 2) x x)) =
        sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) x).symm y)) (extChartAt (𝓡 2) x x)) := by
    have hh := DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
      (I := 𝓡 2) (f := ψ ∘ f) (g := g) BoundarylessManifold.isInteriorPoint (b := 0)
      (by simpa only [add_zero] using (hremoved x hx).2)
    rw [hh]
    exact sigNeg_chartHessianAt_scalar_comp (hf.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contMDiffAt
      (ψ.contDiff.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt (hcrit hx) (hψd _)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hndφ := (isNondegenerateCriticalPointAt_scalar_comp_iff
      (hf.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contMDiffAt (ψ.contDiff.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt (hψd _).ne').mpr (hnd x (hcrit hx))
    exact (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
      (hφf.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint (b := 0)
      (by simpa only [add_zero] using (hremoved x hx).2)).mpr hndφ
  · intro x hx y hy hxy
    apply hinj (hcrit hx) (hcrit hy)
    apply ψ.injective
    exact (hremoved x hx).2.eq_of_nhds.symm.trans (hxy.trans (hremoved y hy).2.eq_of_nhds)
  · intro x hx hi
    exact (hremoved x hx).1 (hunique x (hcrit hx) ((hess hx).symm.trans hi))

private theorem exists_diffeomorph_image_sphere_of_one_saddle_graph
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range e := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    η, hη, Φ, hΦ, hΦi, hΦ0, hγ, hslices, hcoverage,
    r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
    t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, εcut, hεcut, hεcutt, hεcuth,
    θ, hθ, hθ01, hθ0, hθ1, hθzero, κ, hκin, hκout, hθformula, ν, hν, hνsub,
    H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
    T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
    hrawU, Z, hZ, hZT, hZeq, ρclear, hρclear, hρZ, hρfilledZ,
    ρ, hρ, hrectangle, hmodelRect, hclear, O, hO, g, hg, hgt,
    Wgraph, hWgraph, hWZ, hWO, hactive, hgrapheq,
    Ncollar, hNcollar, hboundaryCollar, hcollarProd, hlowerClearance, hwedge,
    Vside, hVside, hcurveVside, hVsideRect, hside, v₀, hv₀, hv₀t, hwide⟩ :=
    exists_height_preserving_diffeomorph_saddle_cutoff_graph_and_cap_of_one_saddle
      he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  have ht₀pos : 0 < t₀ := (half_pos hδ).trans hτt₀
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, δexp, hδexp, hfamily⟩ :=
    hwide (3 * t₀ / 4) (by constructor <;> linarith)
  obtain ⟨_, _, _, Q, ψ, α, hα, hψd, hψhi, hQheight, hQlow, hQhi,
    hQcylinder, hQcap, hQwhole, hQcapall, hQinj, hQinjS, hQinjWhole, htrace, hfull, _⟩ :=
    hfamily (δexp / 2) ⟨half_pos hδexp, half_lt_self hδexp⟩
  obtain ⟨OQ, hOQ, gQ, hgQ, WQ, hWQ, hKWQ, hWQO, hWQeq, hbottom,
    k, hk, hkd, hbound, Acut, hAcutfst, hAcutgraph, hAcutfixed, hremoved⟩ := hfull
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let Ω : EuclideanThree ≃ₘ[ℝ] EuclideanThree :=
    (((L.toDiffeomorph.trans T).trans Q).trans Acut).trans L.symm.toDiffeomorph
  have hΩheight (x : SphereTwo) : Ω (e x) 2 = (Acut (Q (T (L (e x))))).2 := by
    rfl
  have hcritgerm : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => Ω (e y) 2) x →
      x ≠ β (0, 0) ∧ (fun y => Ω (e y) 2) =ᶠ[𝓝 x] ψ ∘ (fun y => e y 2) := by
    simpa only [hΩheight, L, Function.comp_def] using hremoved
  have hunique : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) x).symm y) 2) (extChartAt (𝓡 2) x x)) = 1 → x = β (0, 0) := by
    obtain ⟨p₀, hp₀⟩ := ncard_eq_one.mp hone
    intro x hx hi
    have hxp : x = p₀ := hp₀.subset ⟨hx, hi⟩
    have hβp : β (0, 0) = p₀ := hp₀.subset ⟨hβcrit, hβindex⟩
    exact hxp.trans hβp.symm
  have heh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  obtain ⟨hnd', hinj', hno⟩ := regular_height_data_of_saddle_removal
    heh hnd hinj hunique ψ hψd hcritgerm
  obtain ⟨F, hF⟩ := exists_diffeomorph_image_sphere_of_no_saddles (he.diffeomorph_comp Ω) hnd' hinj' hno
  refine ⟨F.trans Ω.symm, ?_⟩
  change (Ω.symm ∘ F) '' sphere 0 1 = range e
  rw [image_comp, hF, ← range_comp]
  have heq : (Ω.symm ∘ Ω ∘ e) = e := by funext x; exact Ω.symm_apply_apply (e x)
  exact congrArg range heq

theorem exists_diffeomorph_image_sphere_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1) :
    ∃ F : EuclideanThree ≃ₘ[ℝ] EuclideanThree, F '' sphere 0 1 = range e := by
  obtain ⟨D, p, c, s, hs, hcritD, hndD, hinjD, hconnD, hregular, hp, hindex, hcount,
    h, hh, B, β, hβzero, _, _, _, _, _, _, hβopen, _⟩ :=
    exists_diffeomorph_saddle_band_of_one_saddle he hnd hinj hone
  obtain ⟨A, hAheight, _, U, hU, hrect, hβ, _, hgraphD,
    T, _, _, _, hTheight, _, hstraight, _⟩ := hβopen
  let N : EuclideanThree ≃ₘ[ℝ] EuclideanThree := D.trans (T 1)
  have hNheight (x : SphereTwo) : N (e x) 2 = D (e x) 2 := hTheight 1 (D (e x))
  have hNnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => N (e y) 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => N (e y) 2) x := by
    simpa only [hNheight] using hndD
  have hNinj : InjOn (fun x => N (e x) 2) {x | IsCriticalPointAt (𝓡 2) (fun y => N (e y) 2) x} := by
    simpa only [hNheight] using hinjD
  have hNcount : {x | IsCriticalPointAt (𝓡 2) (fun y => N (e y) 2) x ∧ sigNeg (chartHessianAt
      (fun y => N (e ((extChartAt (𝓡 2) x).symm y)) 2) (extChartAt (𝓡 2) x x)) = 1}.ncard = 1 := by
    simpa only [hNheight] using hcount
  have hNconn : ∀ a : ℝ, IsPreconnected {x | N (e x) 2 < a} := by
    simpa only [hNheight] using hconnD
  have hNgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (N (e (β z))) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
    intro z hz
    change (EuclideanSpace.equivProdLast 2) (T 1 (D (e (β z)))) = _
    rw [hstraight z hz, ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨F, hF⟩ := exists_diffeomorph_image_sphere_of_one_saddle_graph (he.diffeomorph_comp N)
    hNnd hNinj hNcount hNconn B hU
    (hrect ⟨⟨by norm_num, by norm_num⟩, neg_nonpos.mpr hh.le, hh.le⟩)
    hβ hs hNgraph
    (by simpa only [Function.comp_def, hNheight, hβzero] using hp)
    (by simpa only [Function.comp_def, hNheight, hβzero] using hindex)
  refine ⟨F.trans N.symm, ?_⟩
  change (N.symm ∘ F) '' sphere 0 1 = range e
  rw [image_comp, hF, ← range_comp]
  have heq : (N.symm ∘ N ∘ e) = e := by funext x; exact N.symm_apply_apply (e x)
  exact congrArg range heq

end DifferentialGeometry.Topology.SphereSeparation
