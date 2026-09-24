import DifferentialGeometry.Topology.Diffeomorph.HeightReparametrization
import DifferentialGeometry.Topology.Morse.ScalarComposition

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

theorem exists_compact_isotopy_height_compression
    {E P H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless]
    {e : M → E × ℝ} (he : ContMDiff I 𝓘(ℝ, E × ℝ) 2 e)
    (hK : IsCompact (range e))
    {m l c q ε : ℝ} (hml : m < l) (hlc : l < c) (hcq : c < q) (hε : 0 < ε) :
    ∃ d ∈ Ioo l c, d < l + ε ∧ m < l - (d - l) / 2 ∧ d + (d - l) / 2 < q ∧
      ∃ a ∈ Ioo l d, ∃ b ∈ Ioo c q,
        ∃ φ : ℝ → ℝ ≃ₘ[ℝ] ℝ,
          (∀ t y, 0 < deriv (φ t) y) ∧ φ 1 c = d ∧
          ∃ D : ℝ → (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
            ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => D z.1 z.2) ∧
            ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (D z.1).symm z.2) ∧
            D 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
            (∀ t z, (D t z).1 = z.1) ∧
            (∀ t, EqOn (D t) id {z | z.2 ∉ Ioo a b} ∧
              EqOn (D t).symm id {z | z.2 ∉ Ioo a b}) ∧
            (∀ t ∈ Icc (0 : ℝ) 1,
              (∀ x, (D t (e x)).2 = φ t (e x).2) ∧
              (∀ x, IsCriticalPointAt I (fun y => (D t (e y)).2) x ↔
                IsCriticalPointAt I (fun y => (e y).2) x) ∧
              (∀ x, IsNondegenerateCriticalPointAt I (fun y => (D t (e y)).2) x ↔
                IsNondegenerateCriticalPointAt I (fun y => (e y).2) x) ∧
              ∀ x, IsCriticalPointAt I (fun y => (e y).2) x →
                sigNeg (chartHessianAt (fun z => (D t (e ((extChartAt I x).symm z))).2)
                  (extChartAt I x x)) =
                sigNeg (chartHessianAt (fun z => (e ((extChartAt I x).symm z)).2)
                  (extChartAt I x x))) ∧
            ∃ S : Set (E × ℝ), IsCompact S ∧ ∀ t,
              EqOn (D t) id Sᶜ ∧ EqOn (D t).symm id Sᶜ := by
  let δ := min (ε / 2) (min ((c - l) / 2) (min (l - m) ((q - l) / 3)))
  have hδ : 0 < δ := lt_min (half_pos hε) (lt_min (half_pos (sub_pos.mpr hlc))
    (lt_min (sub_pos.mpr hml) (div_pos (sub_pos.mpr (hlc.trans hcq)) (by norm_num))))
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδc : δ ≤ (c - l) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδm : δ ≤ l - m := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ (q - l) / 3 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let d := l + δ
  have hld : l < d := by dsimp [d]; linarith
  have hdc : d < c := by dsimp [d]; linarith
  obtain ⟨a, hla, had⟩ := exists_between hld
  obtain ⟨b, hcb, hbq⟩ := exists_between hcq
  obtain ⟨φ, _, _, _, hφc, hφder, _, V, _, hKV, D, hD, hDi, hD0,
      htrack, hfirst, hfixed, hsupport⟩ :=
    Diffeomorph.exists_compact_isotopy_height_reparametrization hK
      (show c ∈ Ioo a b from ⟨had.trans hdc, hcb⟩)
      (show d ∈ Ioo a b from ⟨had, hdc.trans hcb⟩)
  refine ⟨d, ⟨hld, hdc⟩, ?_, ?_, ?_, a, ⟨hla, had⟩, b, ⟨hcb, hbq⟩,
    φ, hφder, hφc, D, hD, hDi, hD0, hfirst, hfixed, ?_, hsupport⟩
  · dsimp [d]
    linarith
  · dsimp [d]
    linarith
  · dsimp [d]
    linarith
  · intro t ht
    let f : M → ℝ := fun x => (e x).2
    have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
      (ContinuousLinearMap.snd ℝ E ℝ).contMDiff.comp he
    have hfun : (fun x => (D t (e x)).2) = φ t ∘ f := by
      funext x
      exact congrArg Prod.snd (htrack t ht (e x) (hKV (mem_range_self x)))
    refine ⟨fun x => congrFun hfun x, ?_, ?_, ?_⟩
    · intro x
      rw [hfun]
      exact isCriticalPointAt_scalar_comp_iff
        (hf.contMDiffAt.mdifferentiableAt (by norm_num))
        ((φ t).contDiff.differentiable (by simp) (f x)) (hφder t (f x)).ne'
    · intro x
      rw [hfun]
      exact isNondegenerateCriticalPointAt_scalar_comp_iff hf.contMDiffAt
        ((φ t).contDiff.of_le
          (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (hφder t (f x)).ne'
    · intro x hx
      have heq : (fun z => (D t (e ((extChartAt I x).symm z))).2) =
          fun z => φ t (f ((extChartAt I x).symm z)) := by
        funext z
        exact congrFun hfun _
      rw [heq]
      exact sigNeg_chartHessianAt_scalar_comp hf.contMDiffAt
        ((φ t).contDiff.of_le
          (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
        hx (hφder t (f x))

end DifferentialGeometry.Topology.Morse
