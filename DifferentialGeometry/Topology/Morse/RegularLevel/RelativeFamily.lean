import DifferentialGeometry.Topology.Morse.RegularLevel.Family
import DifferentialGeometry.Topology.Morse.RegularLevel.RelativeVectorField

open Set Filter Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_diffeomorph_family_level_transport_relative
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    {ι : Type*} {C U : ι → Set M} (hC : IsCompact (⋃ i, C i))
    (hU : ∀ i, IsOpen (U i)) (hCU : ∀ i, C i ⊆ U i)
    (W : ι → (x : M) → TangentSpace I x)
    (hW : ∀ i, ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W i x⟩ : TangentBundle I M)) (U i))
    (hWdf : ∀ i, ∀ x ∈ U i,
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W i x)) = -1)
    (hagree : ∀ i j, ∀ x ∈ U i ∩ U j, W i x = W j x) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      Φ a = Diffeomorph.refl I M ∞ ∧
      (∀ t ∈ Icc a b, (Φ t '' (f ⁻¹' {a}) = f ⁻¹' {t}) ∧
        (Φ t '' sublevel f a = sublevel f t)) ∧
      ∀ i, ∃ O : Set M, IsOpen O ∧ C i ⊆ O ∧ O ⊆ U i ∧
        ∀ x : M, IsMIntegralCurveOn (fun t => Φ (a - t) x) (W i)
          ((fun t => Φ (a - t) x) ⁻¹' O) := by
  obtain ⟨V, hV, hsupp, hdf, hrate, hVW⟩ :=
    exists_unitSpeedVectorField_eq_nhds_on_union hf hcompact hregular hC hU hCU W hW hWdf hagree
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  let Φ : ℝ → M ≃ₘ⟮I, I⟯ M := fun t => curveAtDiffeomorph V hV hc (a - t)
  have hflow := contMDiff_curveAt V hV hc
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hflow.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)
  · exact hflow.comp ((contMDiff_const.sub contMDiff_fst).neg.prodMk contMDiff_snd)
  · change curveAtDiffeomorph V hV hc (a - a) = _
    rw [sub_self, curveAtDiffeomorph_zero]
  · intro t ht
    have hdf' : ∀ x ∈ f ⁻¹' Icc a t,
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1 :=
      fun x hx => hdf x ⟨hx.1, hx.2.trans ht.2⟩
    exact ⟨curveAtDiffeomorph_image_level hf ht.1 V hV hsupp hdf' hrate,
      sublevel_transport_of_stripUnitSpeedVectorField f hf ht.1 V
        (hV.of_le (by norm_num)) hdf' hrate hc⟩
  · intro i
    obtain ⟨O, hO, hCO, hOVW⟩ := eventually_nhdsSet_iff_exists.mp (hVW i)
    refine ⟨O ∩ U i, hO.inter (hU i), fun x hx => ⟨hCO hx, hCU i hx⟩,
      inter_subset_right, ?_⟩
    intro x
    have heq : (fun t => Φ (a - t) x) = curveAt V hc x := by
      funext t
      change curveAt V hc x (a - (a - t)) = _
      rw [sub_sub_cancel]
    rw [heq]
    intro t ht
    rw [← hOVW (curveAt V hc x t) ht.1]
    exact (curveAt_integralCurve V hc x t).hasMFDerivWithinAt

end DifferentialGeometry.Topology.Morse
