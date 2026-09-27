/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SaddleMinimumHeightCoordinates
import DifferentialGeometry.Topology.Manifold.CommonLevelCoordinates

open Set Filter Function Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_aligned_coordinates {f : M → ℝ}
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
                ∃ D : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
                  (∀ z, (D z).im = z.im) ∧
                  let c := κ.trans Complex.equivRealProdCLM.symm.toDiffeomorph.toPartialDiffeomorph
                  let C := c.trans D.toPartialDiffeomorph
                  C.source = κ.source ∧
                  (∀ y ∈ C.source, (C y).im = f y) ∧
                  C '' (d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1)) =
                    D '' (Complex.equivRealProdCLM.symm ''
                      (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)))) ∧
                  ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
                    (Icc (s₀ - η) (s₀ + η) ×ˢ Icc (0 : ℝ) 1 ⊆ d.source) ∧
                    κ '' (d '' (Icc (s₀ - η) (s₀ + η) ×ˢ Icc (0 : ℝ) 1)) =
                      Icc (s₀ - η) (s₀ + η) ×ˢ Icc (f (γ b)) (f (γ a)) ∧
                    C '' (d '' (Icc (s₀ - η) (s₀ + η) ×ˢ Icc (0 : ℝ) 1)) =
                      D '' (Complex.equivRealProdCLM.symm ''
                        (Icc (s₀ - η) (s₀ + η) ×ˢ Icc (f (γ b)) (f (γ a)))) ∧
                  ∀ last : Bool,
                    let χ := if last then χq else χₚ
                    let x := γ (if last then b else a)
                    let W := if last then W₁ else W₀
                    ∃ (ℓ : MorseModel 2 →L[ℝ] ℝ)
                      (e : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞)
                      (R : ℂ ≃L[ℝ] ℂ) (Φ : ℝ → Diffeomorph I I M M ∞),
                      x ∈ e.source ∧ e.source ⊆ χ.target ∩ W ∧
                      (∀ y ∈ e.source, (e y).im = f y) ∧
                      (∀ y, (e y).re = ℓ (χ.symm y - χ.symm x)) ∧
                      (∀ z, (R z).im = z.im) ∧
                      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
                      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
                      Φ 0 = Diffeomorph.refl I M ∞ ∧
                      (∀ t y, f (Φ t y) = f y) ∧
                      (∀ t, Φ t p = p ∧ Φ t q = q ∧ Φ t x = x) ∧
                      (χ.trans (Φ 1).toPartialDiffeomorph).source = χ.source ∧
                      (∀ t z, f (Φ t (χ z)) = f (χ z)) ∧
                      (∃ V : Set M, IsOpen V ∧ x ∈ V ∧
                        V ⊆ C.source ∩ χ.target ∩ W ∧
                        (∀ y ∈ V, (Φ 1).symm y ∈ e.source ∧
                          R (e ((Φ 1).symm y)) = C y) ∧
                        ∀ s ∈ Icc (s₀ - η) (s₀ + η), d (s, if last then 1 else 0) ∈ V) ∧
                      ∃ K : Set M, IsCompact K ∧ K ⊆ d.target ∩ χ.target ∩ W ∧
                        ∀ t y, y ∉ K → Φ t y = y ∧ (Φ t).symm y = y := by
  classical
  obtain ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield,
    κ, hκs, hκt, hκ, hκi, hκd, hκimage, hκinverse,
    W₀, W₁, hW₀, hW₁, hWdisj, hWO, hga, hgb, hcritical, hends⟩ :=
    exists_saddle_minimum_height_coordinates hf hv hp hq hpindex hqindex hγ hunique
      hO hpO hqO hγO hOₚ hpOₚ hOq hqOq
  let χ (i : Bool) := if i then χq else χₚ
  let x (i : Bool) := γ (if i then b else a)
  let W (i : Bool) := if i then W₁ else W₀
  have he_exists (i : Bool) : ∃ (ℓ : MorseModel 2 →L[ℝ] ℝ)
      (e : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞),
      x i ∈ e.source ∧ e.source ⊆ (χ i).target ∩ W i ∧
        (∀ y ∈ e.source, (e y).im = f y) ∧
        ∀ y, (e y).re = ℓ ((χ i).symm y - (χ i).symm (x i)) := by
    obtain ⟨_, ℓ, _, e, _, hxe, _, heW, _, hef, _, hel, _⟩ := hends i
    exact ⟨ℓ, e, hxe, heW, hef, hel⟩
  choose ℓ e hxe heW hef hel using he_exists
  let c := κ.trans Complex.equivRealProdCLM.symm.toDiffeomorph.toPartialDiffeomorph
  have hcs : c.source = κ.source := by
    ext y
    exact and_iff_left (mem_univ (κ y))
  have hcf (y : M) (hy : y ∈ c.source) : (c y).im = f y :=
    congrArg Prod.snd (hκ y (hcs ▸ hy))
  have hs₀ : s₀ ∈ Icc (s₀ - δ) (s₀ + δ) := ⟨by linarith, by linarith⟩
  have hpoint (i : Bool) : d (s₀, if i then 1 else 0) = x i := by
    cases i
    · change d (s₀, 0) = γ a
      simpa only [zero_mul, zero_add] using hcentral 0 (by simp)
    · change d (s₀, 1) = γ b
      simpa only [one_mul, sub_add_cancel] using hcentral 1 (by simp)
  have hxc (i : Bool) : x i ∈ c.source := by
    rw [hcs]
    exact hκs ⟨(s₀, if i then 1 else 0), ⟨hs₀, by cases i <;> simp⟩, hpoint i⟩
  have hW (i : Bool) : IsOpen (W i) := by cases i <;> assumption
  have hxW (i : Bool) : x i ∈ W i := by cases i <;> assumption
  obtain ⟨D, hDi, hCsource, hCends⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_common_level_coordinates
      c e hcf hef x hxc hxe (hγ.strictAnti hf hab) W hW hxW
  let C := c.trans D.toPartialDiffeomorph
  have hCs : C.source = κ.source := hCsource.trans hcs
  have hCf (y : M) (hy : y ∈ C.source) : (C y).im = f y :=
    (hDi (c y)).trans (hcf y (hCsource ▸ hy))
  have hCimage : C '' (d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1)) =
      D '' (Complex.equivRealProdCLM.symm ''
        (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)))) := by
    change (fun y => D (Complex.equivRealProdCLM.symm (κ y))) '' _ = _
    rw [← hκimage]
    simp only [image_image]
  have haux (i : Bool) :
      ∃ (ℓ : MorseModel 2 →L[ℝ] ℝ)
        (e : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞)
        (R : ℂ ≃L[ℝ] ℂ) (Φ : ℝ → Diffeomorph I I M M ∞),
        (x i) ∈ e.source ∧ e.source ⊆ (χ i).target ∩ (W i) ∧
        (∀ y ∈ e.source, (e y).im = f y) ∧
        (∀ y, (e y).re = ℓ ((χ i).symm y - (χ i).symm (x i))) ∧
        (∀ z, (R z).im = z.im) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t y, f (Φ t y) = f y) ∧
        (∀ t, Φ t p = p ∧ Φ t q = q ∧ Φ t (x i) = (x i)) ∧
        ((χ i).trans (Φ 1).toPartialDiffeomorph).source = (χ i).source ∧
        (∀ t z, f (Φ t ((χ i) z)) = f ((χ i) z)) ∧
        (∃ V : Set M, IsOpen V ∧ (x i) ∈ V ∧
          V ⊆ C.source ∩ (χ i).target ∩ (W i) ∧
          (∀ y ∈ V, (Φ 1).symm y ∈ e.source ∧
            R (e ((Φ 1).symm y)) = C y) ∧
          ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
            ∀ s ∈ Icc (s₀ - η) (s₀ + η), d (s, if i then 1 else 0) ∈ V) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ d.target ∩ (χ i).target ∩ (W i) ∧
          ∀ t y, y ∉ K → Φ t y = y ∧ (Φ t).symm y = y := by
    obtain ⟨R, Φ, hRi, hΦ, hΦi, hΦ0, hΦf, hΦx,
      ⟨V, hV, hxV, hVs, hmatch⟩, K, hK, hKs, hfix⟩ := hCends i
    have hWin : W i ⊆ W₀ ∪ W₁ := by
      cases i
      · exact subset_union_left
      · exact subset_union_right
    have hKout : K ⊆ d.target ∩ (χ i).target ∩ W i := by
      intro y hy
      have hs := hKs hy
      exact ⟨⟨hκt (hcs ▸ hs.1.1), (heW i hs.1.2).1⟩, hs.2⟩
    have hsrc : (s₀, if i then 1 else 0) ∈ d.source := by
      apply hds
      exact ⟨hs₀, by cases i <;> simp⟩
    have hcurve : ContinuousAt (fun s : ℝ => d (s, if i then 1 else 0)) s₀ :=
      (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hsrc)).continuousAt.comp
        (f := fun s : ℝ => (s, if i then 1 else 0))
        (continuousAt_id.prodMk continuousAt_const)
    have hnear : (fun s : ℝ => d (s, if i then 1 else 0)) ⁻¹' V ∈ 𝓝 s₀ :=
      hcurve.preimage_mem_nhds (hV.mem_nhds ((hpoint i).symm ▸ hxV))
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hnear
    have hsmall (s : ℝ) (hs : s ∈ Icc (s₀ - min δ (ρ / 2)) (s₀ + min δ (ρ / 2))) :
        d (s, if i then 1 else 0) ∈ V := by
      apply hρV
      rw [Metric.mem_ball, Real.dist_eq]
      have ha : |s - s₀| ≤ min δ (ρ / 2) := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact ha.trans_lt ((min_le_right δ (ρ / 2)).trans_lt (by linarith))
    refine ⟨ℓ i, e i, R, Φ, hxe i, heW i, hef i, hel i, hRi, hΦ, hΦi, hΦ0, hΦf, ?_, ?_,
      fun t z => hΦf t (χ i z), ⟨V, hV, hxV, ?_, hmatch,
        min δ (ρ / 2), lt_min hδ (by positivity), min_le_left _ _, hsmall⟩,
      K, hK, hKout, hfix⟩
    · intro t
      have hpK : p ∉ K := fun hpK => (hcritical p (hWin (hKout hpK).2)).1 rfl
      have hqK : q ∉ K := fun hqK => (hcritical q (hWin (hKout hqK).2)).2 rfl
      exact ⟨(hfix t p hpK).1, (hfix t q hqK).1, hΦx t⟩
    · ext z
      exact and_iff_left (mem_univ (χ i z))
    · intro y hy
      have hs := hVs hy
      exact ⟨⟨hCsource.symm ▸ hs.1.1, (heW i hs.1.2).1⟩, hs.2⟩
  choose ℓ' e' R Φ hx' he' hf' hl' hR hΦ hΦi hΦ0 hΦf hΦfix hΦsource hΦnormal
    collar K hK hKs hfix using haux
  choose V hV hxV hVs hmatch η hη hηδ hsmall using collar
  let η₀ := min (η false) (η true)
  have hη₀ : 0 < η₀ := lt_min (hη false) (hη true)
  have hηle (i : Bool) : η₀ ≤ η i := by
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hηδ₀ : η₀ ≤ δ := (hηle false).trans (hηδ false)
  have hsub {s : ℝ} (hs : s ∈ Icc (s₀ - η₀) (s₀ + η₀)) :
      s ∈ Icc (s₀ - δ) (s₀ + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsubend (i : Bool) {s : ℝ} (hs : s ∈ Icc (s₀ - η₀) (s₀ + η₀)) :
      s ∈ Icc (s₀ - η i) (s₀ + η i) :=
    ⟨by linarith [hs.1, hηle i], by linarith [hs.2, hηle i]⟩
  have hκsmall : κ '' (d '' (Icc (s₀ - η₀) (s₀ + η₀) ×ˢ Icc (0 : ℝ) 1)) =
      Icc (s₀ - η₀) (s₀ + η₀) ×ˢ Icc (f (γ b)) (f (γ a)) := by
    ext z
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, heq⟩
      have hb : z ∈ Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)) :=
        hκimage ▸ ⟨d t, ⟨t, ⟨hsub ht.1, ht.2⟩, rfl⟩, heq⟩
      have he₁ := congrArg Prod.fst ((hκd t.1 (hsub ht.1) t.2 ht.2).symm.trans heq)
      exact ⟨he₁ ▸ ht.1, hb.2⟩
    · intro hz
      have hb : z ∈ κ '' (d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1)) :=
        hκimage.symm ▸ ⟨hsub hz.1, hz.2⟩
      obtain ⟨y, ⟨t, ht, rfl⟩, heq⟩ := hb
      have he₁ := congrArg Prod.fst ((hκd t.1 ht.1 t.2 ht.2).symm.trans heq)
      exact ⟨d t, ⟨t, ⟨he₁.symm ▸ hz.1, ht.2⟩, rfl⟩, heq⟩
  have hCsmall : C '' (d '' (Icc (s₀ - η₀) (s₀ + η₀) ×ˢ Icc (0 : ℝ) 1)) =
      D '' (Complex.equivRealProdCLM.symm ''
        (Icc (s₀ - η₀) (s₀ + η₀) ×ˢ Icc (f (γ b)) (f (γ a)))) := by
    change (fun y => D (Complex.equivRealProdCLM.symm (κ y))) '' _ = _
    rw [← hκsmall]
    simp only [image_image]
  refine ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield,
    κ, hκs, hκt, hκ, hκi, hκd, hκimage, hκinverse,
    W₀, W₁, hW₀, hW₁, hWdisj, hWO, hga, hgb, hcritical,
    D, hDi, hCs, hCf, hCimage, η₀, hη₀, hηδ₀,
    fun z hz => hds ⟨hsub hz.1, hz.2⟩, hκsmall, hCsmall, ?_⟩
  intro i
  exact ⟨ℓ' i, e' i, R i, Φ i, hx' i, he' i, hf' i, hl' i, hR i, hΦ i, hΦi i,
    hΦ0 i, hΦf i, hΦfix i, hΦsource i, hΦnormal i,
    ⟨V i, hV i, hxV i, hVs i, hmatch i, fun s hs => hsmall i s (hsubend i hs)⟩,
    K i, hK i, hKs i, hfix i⟩

end DifferentialGeometry.Morse
