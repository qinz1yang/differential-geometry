/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SaddleMinimumCoordinates
import DifferentialGeometry.Topology.Manifold.LevelChartTransition

noncomputable section
open Set Filter Function Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

private def planeProductCoordinates :
    Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toEquiv := Equiv.refl _
  contMDiff_toFun := contMDiff_fst.prodMk_space contMDiff_snd
  contMDiff_invFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_end_straightenings {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    {p q : M} (hp : IsNondegenerateCriticalPointAt I f p)
    (hq : IsNondegenerateCriticalPointAt I f q)
    (hpindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (hqindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I q).symm y))
      (extChartAt I q q)) = 0) {γ : ℝ → M}
    (hγ : IsDescendingConnection I f v p q γ)
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    {O Oₚ Oq : Set M} (hO : IsOpen O) (hpO : p ∈ O) (hqO : q ∈ O)
    (hγO : range γ ⊆ O) (hOₚ : IsOpen Oₚ) (hpOₚ : p ∈ Oₚ)
    (hOq : IsOpen Oq) (hqOq : q ∈ Oq) :
    ∃ χₚ χq : PartialDiffeomorph 𝓘(ℝ, MorseModel 2) I (MorseModel 2) M ∞,
      0 ∈ χₚ.source ∧ χₚ 0 = p ∧ 0 ∈ χq.source ∧ χq 0 = q ∧
      (∀ z ∈ χₚ.source, f (χₚ z) = f p + (z 1 ^ 2 - z 0 ^ 2) / 2) ∧
      (∀ z ∈ χq.source, f (χq z) = f q + (z 0 ^ 2 + z 1 ^ 2) / 2) ∧
      ∃ ε a b s₀ δ : ℝ, ∃ side : Bool, 0 < ε ∧ a < b ∧ 0 < δ ∧
        ∃ (w : (x : M) → TangentSpace I x)
          (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
          (hwc : HasCompactSupport w), tsupport w ⊆ O ∧
          ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc (s₀ - δ) (s₀ + δ)) ∧ τ s₀ = b - a ∧
            (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), 0 < τ s) ∧
            let F := Diffeomorph.compactSupportFlow w hw hwc
            let A₀ : ℝ → M := fun s => χₚ (saddleLevelPoint ε side s)
            ∃ d : PartialDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (ℝ × ℝ) M ∞,
              (d : ℝ × ℝ → M) = (fun z => F (z.2 * τ z.1) (A₀ z.1)) ∧
              Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1 ⊆ d.source ∧ d.target ⊆ O ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ),
                f (d (s, 0)) = f (γ a) ∧ f (d (s, 1)) = f (γ b)) ∧
              (∀ last : Bool,
                let χ := if last then χq else χₚ
                let x := γ (if last then b else a)
                ∀ t ∈ Icc (0 : ℝ) 1,
                  t • χ.symm x ∈ χ.source ∧ χ (t • χ.symm x) ∈ O) ∧
              (∀ t ∈ Icc (0 : ℝ) 1, d (s₀, t) = γ (t * (b - a) + a)) ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ),
                d (s, 0) ∈ χₚ.target ∧ d (s, 1) ∈ χq.target) ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), ∀ t ∈ Icc (0 : ℝ) (τ s),
                mvfderiv I f (F t (A₀ s)) (v (F t (A₀ s))) < 0 ∧
                HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => F t (A₀ s)) t
                  ((1 : ℝ →L[ℝ] ℝ).smulRight (v (F t (A₀ s))))) ∧
              ∃ W₀ W₁ : Set M, IsOpen W₀ ∧ IsOpen W₁ ∧ Disjoint W₀ W₁ ∧
                W₀ ∪ W₁ ⊆ O ∧ γ a ∈ W₀ ∧ γ b ∈ W₁ ∧
                (∀ x ∈ W₀ ∪ W₁, x ≠ p ∧ x ≠ q) ∧
                ∀ last : Bool,
                  let χ := if last then χq else χₚ
                  let x := γ (if last then b else a)
                  let W := if last then W₁ else W₀
                  ∃ (ℓ₀ : (ℝ × ℝ) →L[ℝ] ℝ) (ℓ₁ : MorseModel 2 →L[ℝ] ℝ)
                    (c e : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞),
                    x ∈ c.source ∧ x ∈ e.source ∧ c.source ⊆ d.target ∩ W ∧
                    e.source ⊆ χ.target ∩ W ∧
                    (∀ y ∈ c.source, (c y).im = f y) ∧
                    (∀ y ∈ e.source, (e y).im = f y) ∧
                    (∀ y, (c y).re = ℓ₀ (d.symm y - d.symm x)) ∧
                    (∀ y, (e y).re = ℓ₁ (χ.symm y - χ.symm x)) ∧
                    ∃ A : ℂ ≃L[ℝ] ℂ,
                      (A : ℂ →L[ℝ] ℂ) = fderiv ℝ (c.symm.trans e) (c x) ∧
                      (∀ z, (A z).im = z.im) ∧
                      ∃ Φ : ℝ → Diffeomorph I I M M ∞,
                        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
                          (fun z : ℝ × M => Φ z.1 z.2) ∧
                        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
                          (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
                        Φ 0 = Diffeomorph.refl I M ∞ ∧
                        (∀ t y, f (Φ t y) = f y) ∧
                        (∀ t, Φ t p = p ∧ Φ t q = q ∧ Φ t x = x) ∧
                        (χ.trans (Φ 1).toPartialDiffeomorph).source = χ.source ∧
                        (∀ t z, f (Φ t (χ z)) = f (χ z)) ∧
                        (∀ᶠ z in 𝓝 (c x),
                          Φ 1 (e.symm (A (z - c x) + e x)) = c.symm z) ∧
                        (∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ c.source ∩ e.source ∧
                          (∀ y ∈ V, A (c y - c x) + e x ∈ e.target ∧
                            Φ 1 (e.symm (A (c y - c x) + e x)) = y) ∧
                          ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
                            ∀ s ∈ Icc (s₀ - η) (s₀ + η),
                              d (s, if last then 1 else 0) ∈ V) ∧
                        ∃ K : Set M, IsCompact K ∧ K ⊆ d.target ∩ χ.target ∩ W ∧
                          ∀ t y, y ∉ K → Φ t y = y ∧ (Φ t).symm y = y := by
  obtain ⟨χₚ, χq, hχₚ0, hχₚp, χq0, hχqq, hpn, hqn,
    R, ε, r, a, b, s₀, δ, side, hR, hε, hr, hab, hδ, hs₀, hJ,
    haheight, hbheight, hAsub, hCsub, hCemb, hCimage,
    w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos, d, hd, hds, hdt,
    hover, hemb, hend, hheight, hrays, hcentral, hfield⟩ :=
    exists_saddle_minimum_flow_coordinates hf hv hp hq hpindex hqindex hγ hunique
      hO hpO hqO hγO hOₚ hpOₚ hOq hqOq
  have hs : s₀ ∈ Icc (s₀ - δ) (s₀ + δ) := ⟨by linarith, by linarith⟩
  have ha : d (s₀, 0) = γ a := by
    simpa only [zero_mul, zero_add] using hcentral 0 (by simp)
  have hb : d (s₀, 1) = γ b := by
    simpa only [one_mul, sub_add_cancel] using hcentral 1 (by simp)
  have horder : f (γ b) < f (γ a) := hγ.strictAnti hf hab
  let m := (f (γ a) + f (γ b)) / 2
  let W₀ := O ∩ f ⁻¹' Ioo m (f p)
  let W₁ := O ∩ f ⁻¹' Ioo (f q) m
  have hW₀ : IsOpen W₀ := hO.inter (isOpen_Ioo.preimage hf.continuous)
  have hW₁ : IsOpen W₁ := hO.inter (isOpen_Ioo.preimage hf.continuous)
  have hWdisj : Disjoint W₀ W₁ := disjoint_left.mpr fun _ hx hy =>
    (not_lt_of_ge hx.2.1.le) hy.2.2
  have hWO : W₀ ∪ W₁ ⊆ O := union_subset (fun _ hx => hx.1) (fun _ hx => hx.1)
  have hga : γ a ∈ W₀ :=
    ⟨hγO (mem_range_self a), by dsimp [m]; linarith, (hγ.value_mem_Ioo hf a).2⟩
  have hgb : γ b ∈ W₁ :=
    ⟨hγO (mem_range_self b), (hγ.value_mem_Ioo hf b).1, by dsimp [m]; linarith⟩
  have hcritical (y : M) (hy : y ∈ W₀ ∪ W₁) : y ≠ p ∧ y ≠ q := by
    have hlo : f q < f y := by
      rcases hy with hy | hy
      · have hbq := (hγ.value_mem_Ioo hf b).1
        have hym := hy.2.1
        dsimp [m] at hym
        linarith
      · exact hy.2.1
    have hhi : f y < f p := by
      rcases hy with hy | hy
      · exact hy.2.2
      · have hap := (hγ.value_mem_Ioo hf a).2
        have hym := hy.2.2
        dsimp [m] at hym
        linarith
    exact ⟨fun h => hhi.ne (congrArg f h), fun h => hlo.ne (congrArg f h).symm⟩
  refine ⟨χₚ, χq, hχₚ0, hχₚp, χq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, fun s hs => ⟨(hover s hs).1.2, (hover s hs).2.2⟩,
    hfield, W₀, W₁, hW₀, hW₁, hWdisj, hWO, hga, hgb, hcritical, ?_⟩
  intro last
  let χ := if last then χq else χₚ
  let x := γ (if last then b else a)
  let W := if last then W₁ else W₀
  have hxW : x ∈ W := by cases last <;> assumption
  have hW : IsOpen W := by cases last <;> assumption
  have hWin : W ⊆ W₀ ∪ W₁ := by
    cases last
    · exact subset_union_left
    · exact subset_union_right
  have hxdt : x ∈ d.target := by
    cases last
    · change γ a ∈ d.target
      rw [← ha]
      exact d.map_source (hds ⟨hs, by simp⟩)
    · change γ b ∈ d.target
      rw [← hb]
      exact d.map_source (hds ⟨hs, by simp⟩)
  have hxχ : x ∈ χ.target := by
    cases last
    · change γ a ∈ χₚ.target
      rw [← ha]
      exact (hover s₀ hs).1.2
    · change γ b ∈ χq.target
      rw [← hb]
      exact (hover s₀ hs).2.2
  have hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro hz
    have hn := hγ.2.2.2 (if last then b else a)
    have hzero : mvfderiv I f x (v x) = 0 :=
      congrArg (fun L : MorseModel 2 →L[ℝ] ℝ => L (v x)) hz
    exact (ne_of_lt hn) hzero
  let c₀ := d.symm.trans planeProductCoordinates.toPartialDiffeomorph
  obtain ⟨ℓ₀, ℓ₁, r₀, r₁, hxc, hxe, hcW, heW, hcf, hef, hcreal, hereal,
    A, hA, hAi, Φ, hΦ, hΦi, hΦ0, hΦf, hΦx, hmatch, K, hK, hKW, hfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_level_preserving_isotopy_in_coordinates
      (by simp) (by simp [MorseModel]) c₀ χ.symm hf ⟨hxdt, mem_univ _⟩ hxχ hreg hW hxW
  let c₁ := c₀.trans r₀
  let e₁ := χ.symm.trans r₁
  obtain ⟨Z, hZmatch, hZ, hZx⟩ := mem_nhds_iff.mp hmatch
  let Z' := (fun z => A (z - c₁ x) + e₁ x) ⁻¹' e₁.target
  have hZ' : IsOpen Z' := e₁.open_target.preimage
    ((A.continuous.comp (continuous_id.sub continuous_const)).add continuous_const)
  have hZ'x : c₁ x ∈ Z' := by
    change A (c₁ x - c₁ x) + e₁ x ∈ e₁.target
    rw [sub_self, map_zero, zero_add]
    exact e₁.map_source hxe
  let V := (c₁.source ∩ c₁ ⁻¹' (Z ∩ Z')) ∩ e₁.source
  have hV : IsOpen V :=
    (c₁.contMDiffOn.continuousOn.isOpen_inter_preimage c₁.open_source (hZ.inter hZ')).inter
      e₁.open_source
  have hxV : x ∈ V := ⟨⟨hxc, hZx, hZ'x⟩, hxe⟩
  have hVeq (y : M) (hy : y ∈ V) :
      A (c₁ y - c₁ x) + e₁ x ∈ e₁.target ∧
        Φ 1 (e₁.symm (A (c₁ y - c₁ x) + e₁ x)) = y :=
    ⟨hy.1.2.2, (hZmatch hy.1.2.1).trans (c₁.left_inv hy.1.1)⟩
  have hcenter : d (s₀, if last then 1 else 0) = x := by cases last <;> assumption
  have hsrc : (s₀, if last then 1 else 0) ∈ d.source := by
    cases last <;> exact hds ⟨hs, by simp⟩
  have hcurve : ContinuousAt (fun s : ℝ => d (s, if last then 1 else 0)) s₀ :=
    (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hsrc)).continuousAt.comp
      (f := fun s : ℝ => (s, if last then 1 else 0))
      (continuousAt_id.prodMk continuousAt_const)
  have hnear : (fun s : ℝ => d (s, if last then 1 else 0)) ⁻¹' V ∈ 𝓝 s₀ :=
    hcurve.preimage_mem_nhds (hV.mem_nhds (hcenter.symm ▸ hxV))
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall (s : ℝ) (hs' : s ∈ Icc (s₀ - min δ (ρ / 2)) (s₀ + min δ (ρ / 2))) :
      d (s, if last then 1 else 0) ∈ V := by
    apply hρV
    rw [Metric.mem_ball, Real.dist_eq]
    have ha : |s - s₀| ≤ min δ (ρ / 2) := abs_le.mpr ⟨by linarith [hs'.1],
      by linarith [hs'.2]⟩
    exact ha.trans_lt ((min_le_right δ (ρ / 2)).trans_lt (by linarith))
  refine ⟨ℓ₀, ℓ₁, c₀.trans r₀, χ.symm.trans r₁, hxc, hxe,
    fun y hy => ⟨(hcW hy).1.1, (hcW hy).2⟩, heW, hcf, hef, hcreal, hereal,
    A, hA, hAi, Φ, hΦ, hΦi, hΦ0, hΦf, ?_, ?_,
    fun t z => hΦf t (χ z), hmatch,
    ⟨V, hV, hxV, fun y hy => ⟨hy.1.1, hy.2⟩, hVeq,
      min δ (ρ / 2), lt_min hδ (by positivity), min_le_left _ _, hsmall⟩, K, hK,
    fun y hy => ⟨⟨(hKW hy).1.1.1, (hKW hy).1.2⟩, (hKW hy).2⟩, hfix⟩
  · intro t
    have hpK : p ∉ K := fun hpK => (hcritical p (hWin (hKW hpK).2)).1 rfl
    have hqK : q ∉ K := fun hqK => (hcritical q (hWin (hKW hqK).2)).2 rfl
    exact ⟨(hfix t p hpK).1, (hfix t q hqK).1, hΦx t⟩
  · ext z
    exact and_iff_left (mem_univ (χ z))

end DifferentialGeometry.Morse
