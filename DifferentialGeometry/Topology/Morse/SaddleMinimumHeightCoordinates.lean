/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SaddleMinimumEndTransitions
import DifferentialGeometry.Topology.Manifold.StripHeightCoordinates

/-! Unified height coordinates for an actual saddle to minimum strip and its end collars. -/

open Set Filter Function Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_height_coordinates {f : M → ℝ}
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
              ∃ κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞,
                d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1) ⊆ κ.source ∧
                κ.source ⊆ d.target ∧
                (∀ x ∈ κ.source, κ x = ((d.symm x).1, f x)) ∧
                (∀ z ∈ κ.target, (d.symm (κ.symm z)).1 = z.1 ∧ f (κ.symm z) = z.2) ∧
                (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), ∀ t ∈ Icc (0 : ℝ) 1,
                  κ (d (s, t)) = (s, f (d (s, t)))) ∧
                κ '' (d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1)) =
                  Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)) ∧
                κ.symm '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a))) =
                  d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1) ∧
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
  obtain ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield, hends⟩ :=
    exists_saddle_minimum_end_straightenings hf hv hp hq hpindex hqindex hγ hunique
      hO hpO hqO hγO hOₚ hpOₚ hOq hqOq
  let F := Diffeomorph.compactSupportFlow w hw hwc
  let A₀ : ℝ → M := fun s => χₚ (saddleLevelPoint ε side s)
  let J := Icc (s₀ - δ) (s₀ + δ)
  let B := J ×ˢ Icc (0 : ℝ) 1
  have hnegative (s : ℝ) (hs : s ∈ J) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (fun u => f (d (s, u))) t < 0 := by
    have htτ : t * τ s ∈ Icc (0 : ℝ) (τ s) :=
      ⟨mul_nonneg ht.1 (hτpos s hs).le, mul_le_of_le_one_left (hτpos s hs).le ht.2⟩
    have hvelocity := (hfield s hs (t * τ s) htτ).2
    have hrate := (hfield s hs (t * τ s) htτ).1
    have hder : HasDerivAt (fun u => f (F u (A₀ s)))
        (mvfderiv I f (F (t * τ s) (A₀ s)) (v (F (t * τ s) (A₀ s)))) (t * τ s) := by
      have hfm : HasMFDerivAt I 𝓘(ℝ, ℝ) f (F (t * τ s) (A₀ s))
          (mfderiv I 𝓘(ℝ, ℝ) f (F (t * τ s) (A₀ s))) :=
        (hf.mdifferentiableAt (by simp)).hasMFDerivAt
      have hh : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u => f (F u (A₀ s))) (t * τ s)
          ((mfderiv I 𝓘(ℝ, ℝ) f (F (t * τ s) (A₀ s))).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (F (t * τ s) (A₀ s))))) :=
        hfm.comp (t * τ s) hvelocity
      have hfr : HasFDerivAt (fun u => f (F u (A₀ s)))
          ((mvfderiv I f (F (t * τ s) (A₀ s))).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (F (t * τ s) (A₀ s))))) (t * τ s) :=
        hh.hasFDerivAt
      have hr := hfr.hasDerivAt
      change HasDerivAt (fun u => f (F u (A₀ s)))
        ((mvfderiv I f (F (t * τ s) (A₀ s)))
          ((1 : ℝ) • v (F (t * τ s) (A₀ s)))) (t * τ s) at hr
      simpa only [one_smul] using hr
    have hscaled := hder.comp t ((hasDerivAt_id t).mul_const (τ s))
    have hactual : HasDerivAt (fun u => f (d (s, u)))
        (mvfderiv I f (F (t * τ s) (A₀ s)) (v (F (t * τ s) (A₀ s))) * τ s) t := by
      simpa only [hd, Function.comp_def, id_eq, one_mul] using hscaled
    rw [hactual.deriv]
    exact mul_neg_of_neg_of_pos hrate (hτpos s hs)
  obtain ⟨κ, hκs, hκt, hκ, hκi, hκd, hκimage⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_height_chart_of_compact_strip
      d hf isCompact_Icc zero_le_one hds hnegative
  have himage : κ '' (d '' B) = J ×ˢ Icc (f (γ b)) (f (γ a)) := by
    rw [hκimage]
    ext z
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, by rwa [(hheight z.1 hz).1, (hheight z.1 hz).2] at h⟩
    · rintro ⟨hz, h⟩
      exact ⟨hz, by rwa [(hheight z.1 hz).1, (hheight z.1 hz).2]⟩
  have hinverse : κ.symm '' (J ×ˢ Icc (f (γ b)) (f (γ a))) = d '' B := by
    rw [← himage]
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      have hl : κ.symm (κ y) = y := κ.left_inv (hκs hy)
      exact hl.symm ▸ hy
    · intro hx
      exact ⟨κ x, mem_image_of_mem κ hx, κ.left_inv (hκs hx)⟩
  exact ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield,
    κ, hκs, hκt, hκ, hκi, fun s hs t ht => hκd (s, t) ⟨hs, ht⟩,
    himage, hinverse, hends⟩

end DifferentialGeometry.Morse
