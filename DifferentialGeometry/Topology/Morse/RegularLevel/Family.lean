import DifferentialGeometry.Topology.Morse.RegularLevel.NoCriticalValues
import DifferentialGeometry.Analysis.ODE.Flow.Complete

open Set Manifold
open scoped ContDiff
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem curveAtDiffeomorph_image_level
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V))
    (hdf : ∀ x ∈ f ⁻¹' Icc a b,
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ∧
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ≤ 0) :
    let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
    curveAtDiffeomorph V hV hc (a - b) '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  let L := levelSetTransportHomeomorph I f hf hab V hV hsupp hdf hrate
  have hL (x : f ⁻¹' {a}) : (L x : M) = curveAtDiffeomorph V hV hc (a - b) x := rfl
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [← hL ⟨x, hx⟩]
    exact (L ⟨x, hx⟩).property
  · intro y hy
    refine ⟨(L.symm ⟨y, hy⟩ : M), (L.symm ⟨y, hy⟩).property, ?_⟩
    rw [← hL, L.apply_symm_apply]

theorem exists_diffeomorph_family_level_transport
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      Φ a = Diffeomorph.refl I M ∞ ∧
      ∀ t ∈ Icc a b, (Φ t '' (f ⁻¹' {a}) = f ⁻¹' {t}) ∧
        (Φ t '' sublevel f a = sublevel f t) := by
  obtain ⟨V, hV, hsupp, hdf, hrate⟩ :=
    exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  let Φ : ℝ → M ≃ₘ⟮I, I⟯ M := fun t => curveAtDiffeomorph V hV hc (a - t)
  have hflow := contMDiff_curveAt V hV hc
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact hflow.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)
  · exact hflow.comp ((contMDiff_const.sub contMDiff_fst).neg.prodMk contMDiff_snd)
  · change curveAtDiffeomorph V hV hc (a - a) = _
    rw [sub_self, curveAtDiffeomorph_zero]
  · intro t ht
    have hdf' : ∀ x ∈ f ⁻¹' Icc a t,
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1 :=
      fun x hx => hdf x ⟨hx.1, hx.2.trans ht.2⟩
    refine ⟨?_, ?_⟩
    · exact curveAtDiffeomorph_image_level hf ht.1 V hV hsupp hdf' hrate
    · exact sublevel_transport_of_stripUnitSpeedVectorField f hf ht.1 V
        (hV.of_le (by norm_num)) hdf' hrate hc

end DifferentialGeometry.Topology.Morse
