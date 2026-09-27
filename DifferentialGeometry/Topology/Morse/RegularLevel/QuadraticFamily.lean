import DifferentialGeometry.Topology.Morse.RegularLevel.Family
import DifferentialGeometry.Topology.Morse.RegularLevel.QuadraticField
import DifferentialGeometry.Analysis.ODE.QuadraticRadialCurveManifold

open Set Filter Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

theorem exists_diffeomorph_family_level_transport_radial_on_disjoint_charts
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] {ι : Type*} [Finite ι]
    (χ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c α : ι → ℝ} (hα : ∀ i, α i ≠ 0)
    (hnormal : ∀ i, ∀ y ∈ (χ i).source, f (χ i y) = c i + α i / 2 * ‖y‖ ^ 2)
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    {C : ι → Set E} (hC : ∀ i, IsCompact (C i))
    (hCχ : ∀ i, C i ⊆ (χ i).source \ {0})
    (hdisjoint : Pairwise (fun i j => Disjoint
      (χ i '' ((χ i).source \ {0})) (χ j '' ((χ j).source \ {0})))) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M, ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      Φ a = Diffeomorph.refl I M ∞ ∧
      (∀ t ∈ Icc a b, (Φ t '' (f ⁻¹' {a}) = f ⁻¹' {t}) ∧
        (Φ t '' sublevel f a = sublevel f t)) ∧
      ∀ i, ∀ x ∈ C i, ∀ s t : ℝ, s - t ∈ Ioo (-ε i) (ε i) →
        Φ t ((Φ s).symm (χ i x)) = χ i (quadraticRadialCurve (-(α i)⁻¹) x (s - t)) := by
  have hχC (i : ι) : IsCompact (χ i '' C i) :=
    (hC i).image_of_continuousOn ((χ i).contMDiffOn.continuousOn.mono
      (fun _ hx => (hCχ i hx).1))
  obtain ⟨V, hV, hsupp, hdf, hrate, hcoords⟩ :=
    exists_unitSpeedVectorField_radial_nhds_on_disjoint_charts χ hf hα hnormal
      hcompact hregular (isCompact_iUnion hχC) (fun i => image_mono (hCχ i)) hdisjoint
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  have hcoords' (i : ι) : ∀ᶠ z in 𝓝ˢ (χ i '' C i),
      mfderiv I 𝓘(ℝ, E) (χ i).symm z (V z) =
        (-(α i)⁻¹ / ‖(χ i).symm z‖ ^ 2) • (χ i).symm z := by
    filter_upwards [hcoords i] with z hz
    exact hz.2.trans (by congr 1; simp [mul_inv_rev, div_eq_mul_inv, mul_comm])
  choose ε hε hradial using fun i => exists_pos_curveAt_eq_quadraticRadialCurve_on_compact
    (χ i) V (hV.of_le (by norm_num)) hc (-(α i)⁻¹) (hC i) (hCχ i) (hcoords' i)
  let Φ : ℝ → M ≃ₘ⟮I, I⟯ M := fun t => curveAtDiffeomorph V hV hc (a - t)
  have hflow := contMDiff_curveAt V hV hc
  refine ⟨Φ, ε, hε, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i x hx s t hst
    have hcomp : Φ t ((Φ s).symm (χ i x)) = curveAt V hc (χ i x) (s - t) := by
      change curveAtDiffeomorph V hV hc (a - t)
        ((curveAtDiffeomorph V hV hc (a - s)).symm (χ i x)) = _
      rw [curveAtDiffeomorph_symm]
      have hadd := congrArg (fun D : M ≃ₘ⟮I, I⟯ M => D (χ i x))
        (curveAtDiffeomorph_add V hV hc (-(a - s)) (a - t))
      rw [show -(a - s) + (a - t) = s - t by ring] at hadd
      exact hadd.symm
    exact hcomp.trans (hradial i x hx (s - t) hst)

theorem exists_diffeomorph_family_level_transport_radial
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c α : ℝ} (hα : α ≠ 0)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = c + α / 2 * ‖y‖ ^ 2)
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    {C : Set E} (hC : IsCompact C) (hCχ : C ⊆ χ.source \ {0}) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M, ∃ ε : ℝ, 0 < ε ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      Φ a = Diffeomorph.refl I M ∞ ∧
      (∀ t ∈ Icc a b, (Φ t '' (f ⁻¹' {a}) = f ⁻¹' {t}) ∧
        (Φ t '' sublevel f a = sublevel f t)) ∧
      ∀ x ∈ C, ∀ t ∈ Ioo (a - ε) (a + ε),
        Φ t (χ x) = χ (quadraticRadialCurve (-α⁻¹) x (a - t)) := by
  have hdisjoint : Pairwise (fun _ _ : Unit =>
      Disjoint (χ '' (χ.source \ {0})) (χ '' (χ.source \ {0}))) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  obtain ⟨Φ, ε, hε, hΦ, hΦinv, hΦa, htrans, hradial⟩ :=
    exists_diffeomorph_family_level_transport_radial_on_disjoint_charts
      (fun _ : Unit => χ) hf (fun _ => hα) (fun _ => hnormal) hcompact hregular
      (C := fun _ => C) (fun _ => hC) (fun _ => hCχ) hdisjoint
  refine ⟨Φ, ε Unit.unit, hε Unit.unit, hΦ, hΦinv, hΦa, htrans, ?_⟩
  intro x hx t ht
  have h := hradial Unit.unit x hx a t ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [hΦa, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq] using h


end DifferentialGeometry.Topology.Morse
