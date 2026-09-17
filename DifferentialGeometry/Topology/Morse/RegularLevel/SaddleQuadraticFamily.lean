import DifferentialGeometry.Topology.Morse.NormalForm.SaddleField
import DifferentialGeometry.Topology.Morse.RegularLevel.RelativeFamily
import DifferentialGeometry.Topology.Morse.RegularLevel.QuadraticField
import DifferentialGeometry.Analysis.ODE.IntegralCurveNaturality

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem exists_diffeomorph_family_level_transport_saddle_quadratic
    {E P F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (hdim : Module.finrank ℝ F = 2)
    {e : M → E × ℝ} (he : ContMDiff I 𝓘(ℝ, E × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s : ℝ} (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (κ : PartialDiffeomorph 𝓘(ℝ, P) I P M ∞)
    {d α : ℝ} (hα : α ≠ 0)
    (hnormal : ∀ y ∈ κ.source, (e (κ y)).2 = d + α / 2 * ‖y‖ ^ 2)
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
        (∀ x : M, IsIntegralCurveOn (fun t => B.symm (e (Φ (a - t) x)).1)
          (fun _ z => (0, -((1 - z.1 ^ 2) * z.2)⁻¹))
          ((fun t => Φ (a - t) x) ⁻¹' O₀)) ∧
        ∀ x : M, IsIntegralCurveOn (fun t => κ.symm (Φ (a - t) x))
          (fun _ y => -(α * ‖y‖ ^ 2)⁻¹ • y)
          ((fun t => Φ (a - t) x) ⁻¹' O₁) := by
  let _ : FiniteDimensional ℝ F := FiniteDimensional.of_finrank_pos (by omega)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).2) := contDiff_snd.contMDiff.comp he
  obtain ⟨χ, hsource, _, hχ, _, W₀, hW₀, hcoords₀, hdf₀⟩ :=
    exists_unitSpeedVectorField_on_saddle_band hdim he B hU hβ hgraph
  obtain ⟨W₁, hW₁, hcoords₁, hdf₁⟩ := exists_unitSpeedVectorField_on_quadratic_chart
    (f := fun x => (e x).2) κ hα hnormal
  let U₀ := (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}) ∩ {x | (e x).2 < r}
  let U₁ := (κ '' (κ.source \ {0})) ∩ {x | r < (e x).2}
  have hU₀ : IsOpen U₀ := by
    have hmodel : IsOpen {z : ℝ × ℝ | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} :=
      hU.inter (isOpen_ne.preimage (by fun_prop))
    have himage : IsOpen (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}) := by
      rw [← hχ]
      exact χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hmodel
        (fun z hz => hsource.symm ▸ hz.1)
    exact himage.inter (isOpen_lt hf.continuous continuous_const)
  have hU₁ : IsOpen U₁ :=
    (κ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (κ.open_source.sdiff isClosed_singleton) sdiff_subset).inter
        (isOpen_lt continuous_const hf.continuous)
  let C : Bool → Set M := fun i => if i then C₁ else C₀
  let VU : Bool → Set M := fun i => if i then U₁ else U₀
  let W : Bool → (x : M) → TangentSpace I x := fun i => if i then W₁ else W₀
  have hC : IsCompact (⋃ i, C i) := by
    apply isCompact_iUnion
    intro i
    cases i
    · exact hC₀
    · exact hC₁
  have hVU : ∀ i, IsOpen (VU i) := by
    intro i
    cases i
    · exact hU₀
    · exact hU₁
  have hCVU : ∀ i, C i ⊆ VU i := by
    intro i x hx
    cases i
    · exact ⟨hC₀β hx, hbelow x hx⟩
    · exact ⟨hC₁κ hx, habove x hx⟩
  have hW : ∀ i, ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W i x⟩ : TangentBundle I M)) (VU i) := by
    intro i
    cases i
    · exact hW₀.mono inter_subset_left
    · exact hW₁.mono inter_subset_left
  have hWdf : ∀ i, ∀ x ∈ VU i,
      (NormedSpace.fromTangentSpace ((e x).2))
        (mfderiv I 𝓘(ℝ, ℝ) (fun x => (e x).2) x (W i x)) = -1 := by
    intro i x hx
    cases i
    · exact hdf₀ x hx.1
    · exact hdf₁ x hx.1
  have hagree : ∀ i j, ∀ x ∈ VU i ∩ VU j, W i x = W j x := by
    intro i j x hx
    cases i <;> cases j
    · rfl
    · have h0 : (e x).2 < r := hx.1.2
      have h1 : r < (e x).2 := hx.2.2
      exact False.elim (lt_asymm h0 h1)
    · have h0 : (e x).2 < r := hx.2.2
      have h1 : r < (e x).2 := hx.1.2
      exact False.elim (lt_asymm h0 h1)
    · rfl
  obtain ⟨Φ, hΦ, hΦinv, hΦa, htrans, hlocal⟩ :=
    exists_diffeomorph_family_level_transport_relative
      hf hcompact hregular hC hVU hCVU W hW hWdf hagree
  obtain ⟨O₀, hO₀, hC₀O, hO₀U, hcurve₀⟩ := hlocal false
  obtain ⟨O₁, hO₁, hC₁O, hO₁U, hcurve₁⟩ := hlocal true
  refine ⟨Φ, hΦ, hΦinv, hΦa, htrans, O₀, O₁, hO₀, hO₁, hC₀O, hC₁O,
    hO₀U, hO₁U, ?_, ?_⟩
  · intro x
    have hG : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => B.symm (e x).1) :=
      B.symm.contMDiff.comp (contDiff_fst.contMDiff.comp he)
    apply isMIntegralCurveOn_iff_isIntegralCurveOn.mp
    exact (hcurve₀ x).map (fun t _ => hG.mdifferentiable (by simp) _)
      (fun t ht => hcoords₀ _ (hO₀U ht).1)
  · intro x
    apply isMIntegralCurveOn_iff_isIntegralCurveOn.mp
    apply (hcurve₁ x).map
    · intro t ht
      obtain ⟨y, hy, hyx⟩ := (hO₁U ht).1
      have hy' : κ y ∈ κ.target := κ.map_source hy.1
      rw [hyx] at hy'
      exact κ.symm.mdifferentiableAt (by simp) hy'
    · intro t ht
      exact hcoords₁ _ (hO₁U ht).1

end DifferentialGeometry.Topology.Morse
