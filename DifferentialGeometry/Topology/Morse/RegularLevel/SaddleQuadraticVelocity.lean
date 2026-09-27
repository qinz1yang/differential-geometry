import DifferentialGeometry.Topology.Morse.RegularLevel.SaddleQuadraticFamily
import DifferentialGeometry.Topology.Diffeomorph.SaddleFiberFlow
import DifferentialGeometry.Topology.Diffeomorph.QuadraticFiberFlow

open Set Filter Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

theorem exists_diffeomorph_family_level_transport_saddle_quadratic_velocity
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (hdim : Module.finrank ℝ F = 2)
    {e : M → E × ℝ} (he : ContMDiff I 𝓘(ℝ, E × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s : ℝ} (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (κ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    {d α : ℝ} (hα : α ≠ 0)
    (hnormal : ∀ y ∈ κ.source, e (κ y) = A (y, d + α / 2 * ‖y‖ ^ 2))
    {a b : ℝ} (hcompact : IsCompact ((fun x => (e x).2) ⁻¹' Icc a b))
    (hregular : ∀ x ∈ (fun x => (e x).2) ⁻¹' Icc a b,
      ¬ IsCriticalPointAt I (fun x => (e x).2) x)
    {C₀ C₁ : Set M} (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁)
    (hC₀β : C₀ ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0})
    (hC₁κ : C₁ ⊆ κ '' (κ.source \ {0}))
    {r : ℝ} (hbelow : ∀ x ∈ C₀, (e x).2 < r) (habove : ∀ x ∈ C₁, r < (e x).2) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      Φ a = Diffeomorph.refl I M ∞ ∧
      (∀ t ∈ Icc a b, (Φ t '' {x | (e x).2 = a} = {x | (e x).2 = t}) ∧
        (Φ t '' sublevel (fun x => (e x).2) a = sublevel (fun x => (e x).2) t)) ∧
      ∃ O₀ O₁ : Set M, IsOpen O₀ ∧ IsOpen O₁ ∧ C₀ ⊆ O₀ ∧ C₁ ⊆ O₁ ∧
        O₀ ⊆ (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}) ∩ {x | (e x).2 < r} ∧
        O₁ ⊆ (κ '' (κ.source \ {0})) ∩ {x | r < (e x).2} ∧
        (∀ t x, Φ t x ∈ O₀ → HasDerivAt (fun s => (e (Φ s x)).1)
          (B.saddleFiberVectorField (e (Φ t x)).1) t) ∧
        ∀ t x, (e (Φ t x)).2 = t → Φ t x ∈ O₁ →
          HasDerivAt (fun s => (e (Φ s x)).1)
            (A.quadraticFiberVectorField d (t, (e (Φ t x)).1)) t := by
  have hn (y : E) (hy : y ∈ κ.source) : (e (κ y)).2 = d + α / 2 * ‖y‖ ^ 2 := by
    rw [hnormal y hy, hA]
  obtain ⟨Φ, hΦ, hΦinv, hΦa, htrans, O₀, O₁, hO₀, hO₁, hC₀O, hC₁O, hO₀U, hO₁U,
      hcurve₀, hcurve₁⟩ := exists_diffeomorph_family_level_transport_saddle_quadratic
    hdim he B hU hβ hgraph κ hα hn hcompact hregular hC₀ hC₁ hC₀β hC₁κ hbelow habove
  have hcont (x : M) : Continuous (fun t => Φ t x) :=
    (hΦ.comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have hrev (x : M) : Continuous (fun t => Φ (a - t) x) :=
    (hcont x).comp (continuous_const.sub continuous_id)
  have htarget {x : M} (hx : x ∈ O₁) : x ∈ κ.target := by
    obtain ⟨y, hy, rfl⟩ := (hO₁U hx).1
    exact κ.map_source hy.1
  refine ⟨Φ, hΦ, hΦinv, hΦa, htrans, O₀, O₁, hO₀, hO₁, hC₀O, hC₁O, hO₀U, hO₁U, ?_, ?_⟩
  · intro t x hx
    have hmem : (a - t) ∈ (fun s => Φ (a - s) x) ⁻¹' O₀ := by
      simpa only [mem_preimage, sub_sub_cancel] using hx
    have hd := (hcurve₀ x (a - t) hmem).hasDerivAt
      ((hO₀.preimage (hrev x)).mem_nhds hmem)
    have hds := hd.scomp t ((hasDerivAt_const t a).sub (hasDerivAt_id t))
    have hcoord : HasDerivAt (fun s => B.symm (e (Φ s x)).1)
        (saddleBandVectorField (B.symm (e (Φ t x)).1)) t := by
      simpa only [Function.comp_def, sub_sub_cancel, sub_zero, zero_sub, Prod.smul_mk,
        smul_eq_mul, neg_mul, one_mul, mul_zero, neg_neg, saddleBandVectorField] using hds
    have hD := (B.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hcoord
    simpa only [Function.comp_def, B.apply_symm_apply, Diffeomorph.saddleFiberVectorField] using hD
  · intro t x hheight hx
    let y : ℝ → E := fun s => κ.symm (Φ s x)
    have hmem : (a - t) ∈ (fun s => Φ (a - s) x) ⁻¹' O₁ := by
      simpa only [mem_preimage, sub_sub_cancel] using hx
    have hd := (hcurve₁ x (a - t) hmem).hasDerivAt
      ((hO₁.preimage (hrev x)).mem_nhds hmem)
    have hds := hd.scomp t ((hasDerivAt_const t a).sub (hasDerivAt_id t))
    have hy : HasDerivAt y ((α * ‖y t‖ ^ 2)⁻¹ • y t) t := by
      simpa only [Function.comp_def, sub_sub_cancel, sub_zero, zero_sub, neg_smul,
        one_smul, smul_smul, neg_mul, one_mul, neg_neg, y] using hds
    have hyne : y t ≠ 0 := by
      obtain ⟨z, hz, hzx⟩ := (hO₁U hx).1
      change κ.symm (Φ t x) ≠ 0
      have hκz : κ.symm (κ z) = z := κ.left_inv hz.1
      rw [← hzx, hκz]
      exact fun h => hz.2 (mem_singleton_iff.mpr h)
    have hnormal' : e (Φ t x) = A (y t, d + α / 2 * ‖y t‖ ^ 2) := by
      have h := hnormal (y t) (κ.map_target (htarget hx))
      rw [show κ (y t) = Φ t x from κ.right_inv (htarget hx)] at h
      exact h
    have hqt : d + α / 2 * ‖y t‖ ^ 2 = t := by
      have h := congrArg Prod.snd hnormal'
      rw [hA, hheight] at h
      exact h.symm
    have hq : HasDerivAt (fun s => d + α / 2 * ‖y s‖ ^ 2) (1 : ℝ) t := by
      have h := (((hasStrictFDerivAt_norm_sq (y t)).hasFDerivAt.const_mul (α / 2)).const_add d).comp_hasDerivAt t hy
      apply h.congr_deriv
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
        inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hα, norm_ne_zero_iff.mpr hyne]
      simp only [nsmul_eq_mul]
      field_simp [hα]
      norm_num
    have hD := (A.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (hy.prodMk hq)
    have hDf := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t hD
    have heq : (fun s => (e (Φ s x)).1) =ᶠ[𝓝 t]
        (fun s => (A (y s, d + α / 2 * ‖y s‖ ^ 2)).1) := by
      filter_upwards [(hcont x).continuousAt (hO₁.mem_nhds hx)] with s hs
      have h := hnormal (y s) (κ.map_target (htarget hs))
      rw [show κ (y s) = Φ s x from κ.right_inv (htarget hs)] at h
      exact congrArg Prod.fst h
    have hp : ((e (Φ t x)).1, t) = A (y t, t) := by
      have h := hnormal'
      rw [hqt] at h
      have hp' : ((e (Φ t x)).1, t) = e (Φ t x) := by
        apply Prod.ext
        · rfl
        · exact hheight.symm
      exact hp'.trans h
    apply (hDf.congr_of_eventuallyEq heq).congr_deriv
    unfold Diffeomorph.quadraticFiberVectorField
    rw [hp, A.symm_apply_apply]
    simp only [quadraticLevelVectorField, hqt, ContinuousLinearMap.coe_fst']
    rw [show 2 * (t - d) = α * ‖y t‖ ^ 2 by linarith [hqt]]

end DifferentialGeometry.Topology.Morse
