/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SaddleMinimumAlignedCoordinates
import DifferentialGeometry.Topology.Morse.TwoEndedChart

open Set Filter Function Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_common_coordinates {f : M → ℝ}
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
                  ∃ Ξ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞,
                    Ξ.source ⊆ O ∧ p ∈ Ξ.source ∧ q ∈ Ξ.source ∧
                    d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1) ⊆ Ξ.source ∧
                    Ξ '' (d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1)) =
                      D '' (Complex.equivRealProdCLM.symm ''
                        (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)))) ∧
                    (∃ U : Set M, IsOpen U ∧
                      d '' (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1) ⊆ U ∧
                      U ⊆ Ξ.source ∩ C.source ∧ EqOn Ξ C U) ∧
                    ∃ θ : ℝ, 0 < θ ∧ θ ≤ η ∧
                    ∀ last : Bool,
                      let χ := if last then χq else χₚ
                      let x := γ (if last then b else a)
                      let W := if last then W₁ else W₀
                      ∃ (Φ : ℝ → Diffeomorph I I M M ∞)
                        (E : Diffeomorph 𝓘(ℝ, MorseModel 2) 𝓘(ℝ, ℂ) (MorseModel 2) ℂ ∞)
                        (U : Set M),
                        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
                        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
                        Φ 0 = Diffeomorph.refl I M ∞ ∧ (∀ t y, f (Φ t y) = f y) ∧
                        (∀ t, Φ t p = p ∧ Φ t q = q ∧ Φ t x = x) ∧
                        let χ' := χ.trans (Φ 1).toPartialDiffeomorph
                        χ'.source = χ.source ∧ χ'.symm x = χ.symm x ∧
                        IsOpen U ∧ (if last then q else p) ∈ U ∧
                        U ⊆ Ξ.source ∩ χ'.target ∧
                        (∀ y ∈ U, Ξ y = E (χ'.symm y)) ∧
                        Ξ (if last then q else p) = E 0 ∧
                        Ξ '' U = E '' (χ'.symm '' U) ∧
                        (∀ t ∈ Icc (0 : ℝ) 1, χ' (t • χ.symm x) ∈ U) ∧
                        (∀ s ∈ Icc (s₀ - θ) (s₀ + θ), d (s, if last then 1 else 0) ∈ U) ∧
                        (∀ z ∈ χ.source, χ' z ∈ U →
                          Ξ (χ' z) = E z ∧ Ξ.symm (E z) = χ' z) ∧
                        (∀ z ∈ χ.source, f (χ' z) =
                          if last then f q + (z 0 ^ 2 + z 1 ^ 2) / 2
                          else f p + (z 1 ^ 2 - z 0 ^ 2) / 2) ∧
                        ∃ K : Set M, IsCompact K ∧ K ⊆ d.target ∩ χ.target ∩ W ∧
                          ∀ t y, y ∉ K → Φ t y = y ∧ (Φ t).symm y = y := by
  classical
  obtain ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield,
    κ, hκs, hκt, hκ, hκi, hκd, hκimage, hκinverse,
    W₀, W₁, hW₀, hW₁, hWdisj, hWO, hga, hgb, hcritical,
    D, hDi, hCs, hCf, hCimage, η, hη, hηδ, hηs, hκsmall, hCsmall, hends⟩ :=
    exists_saddle_minimum_aligned_coordinates hf hv hp hq hpindex hqindex hγ hunique
      hO hpO hqO hγO hOₚ hpOₚ hOq hqOq
  let C := (κ.trans Complex.equivRealProdCLM.symm.toDiffeomorph.toPartialDiffeomorph).trans
    D.toPartialDiffeomorph
  let χ (i : Bool) := if i then χq else χₚ
  let x (i : Bool) := γ (if i then b else a)
  let critical (i : Bool) := if i then q else p
  choose ell e R Φ hxe heW hef hell hR hΦ hΦi hΦ0 hΦf hΦfix hΦsource
    hΦnormal collar L hL hLs hfix using hends
  let χ' (i : Bool) := (χ i).trans (Φ i 1).toPartialDiffeomorph
  let z (i : Bool) := (χ i).symm (x i)
  have hxχ (i : Bool) : x i ∈ (χ i).target := (heW i (hxe i)).1
  have hzχ (i : Bool) : z i ∈ (χ i).source := (χ i).map_target (hxχ i)
  have hχz (i : Bool) : χ i (z i) = x i := (χ i).right_inv (hxχ i)
  have hzχ' (i : Bool) : z i ∈ (χ' i).source := (hΦsource i).symm ▸ hzχ i
  have hχ'z (i : Bool) : χ' i (z i) = x i := by
    change Φ i 1 (χ i (z i)) = x i
    rw [hχz]
    exact (hΦfix i 1).2.2
  have hχ'0 (i : Bool) : χ' i 0 = critical i := by
    cases i
    · change Φ false 1 (χₚ 0) = p
      rw [hχₚp]
      exact (hΦfix false 1).1
    · change Φ true 1 (χq 0) = q
      rw [hχqq]
      exact (hΦfix true 1).2.1
  have hχ0s (i : Bool) : (0 : MorseModel 2) ∈ (χ i).source := by
    cases i <;> assumption
  have hΦO (i : Bool) (t : ℝ) (y : M) (hy : y ∈ O) : Φ i t y ∈ O := by
    by_contra hn
    have hnL : Φ i t y ∉ L i := fun hm => hn (hdt (hLs i hm).1.1)
    have he : Φ i t y = y := (Φ i t).injective (hfix i t (Φ i t y) hnL).1
    exact hn (he.symm ▸ hy)
  have hradial (i : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      t • z i ∈ (χ' i).source ∧ χ' i (t • z i) ∈ O := by
    have hh := hrays i t ht
    exact ⟨(hΦsource i).symm ▸ hh.1, hΦO i 1 _ hh.2⟩
  have hnormal (i : Bool) (u : MorseModel 2) (hu : u ∈ (χ' i).source) :
      f (χ' i u) = f (critical i) +
        (if i then u 0 ^ 2 + u 1 ^ 2 else u 1 ^ 2 - u 0 ^ 2) / 2 := by
    change f (Φ i 1 (χ i u)) = _
    rw [hΦf]
    cases i
    · exact hpn u (hΦsource false ▸ hu)
    · exact hqn u (hΦsource true ▸ hu)
  have hquad (i : Bool) (t : ℝ) (ht : t • z i ∈ (χ' i).source) :
      f (χ' i (t • z i)) = f (critical i) + t ^ 2 * (f (x i) - f (critical i)) := by
    have hzval : f (x i) = f (critical i) +
        (if i then z i 0 ^ 2 + z i 1 ^ 2 else z i 1 ^ 2 - z i 0 ^ 2) / 2 :=
      (congrArg f (hχ'z i)).symm.trans (hnormal i (z i) (hzχ' i))
    rw [hnormal i _ ht, hzval]
    cases i <;> simp only [Bool.false_eq_true, if_false, if_true,
      Pi.smul_apply, smul_eq_mul] <;> ring
  let B := Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1
  let K := d '' B
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
    (d.contMDiffOn.continuousOn.mono hds)
  have hKC : K ⊆ C.source := fun _ hy => hCs.symm ▸ hκs hy
  have hKO : K ⊆ O := by
    rintro y ⟨u, hu, rfl⟩
    exact hdt (d.map_source (hds hu))
  have hs₀ : s₀ ∈ Icc (s₀ - δ) (s₀ + δ) := ⟨by linarith, by linarith⟩
  have hpoint (i : Bool) : d (s₀, if i then 1 else 0) = x i := by
    cases i
    · change d (s₀, 0) = γ a
      simpa only [zero_mul, zero_add] using hcentral 0 (by simp)
    · change d (s₀, 1) = γ b
      simpa only [one_mul, sub_add_cancel] using hcentral 1 (by simp)
  have hxK (i : Bool) : χ' i (z i) ∈ K :=
    ⟨(s₀, if i then 1 else 0), ⟨hs₀, by cases i <;> simp⟩,
      (hpoint i).trans (hχ'z i).symm⟩
  have hKf (y : M) (hy : y ∈ K) : f y ∈ Icc (f (x true)) (f (x false)) := by
    change f y ∈ Icc (f (γ b)) (f (γ a))
    have hh : κ y ∈ Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)) :=
      hκimage ▸ mem_image_of_mem κ hy
    have hi : (κ y).2 = f y := congrArg Prod.snd (hκ y (hκs hy))
    simpa only [hi] using hh.2
  obtain ⟨E, Ξ, hΞs, hΞO, hΞcrit, hreg, hnew⟩ :=
    exists_chart_containing_two_radial_ends χ' C z hK hKC hxK hCf
      (fun i => f (critical i)) (fun i => f (x i))
      (hγ.value_mem_Ioo hf b).1 (hγ.strictAnti hf hab) (hγ.value_mem_Ioo hf a).2
      hquad hKf hO hKO hradial
  obtain ⟨Vreg, hVreg, hKreg, hregsub, hregmatch⟩ := hreg
  choose V hV hRV hVs hVc hImage using hnew
  have hcritV (i : Bool) : critical i ∈ V i :=
    hRV i ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa only [zero_smul] using hχ'0 i⟩
  have hxV (i : Bool) : x i ∈ V i :=
    hRV i ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa only [one_smul] using hχ'z i⟩
  have hwidth (i : Bool) : ∃ r : ℝ, 0 < r ∧ r ≤ η ∧
      ∀ s ∈ Icc (s₀ - r) (s₀ + r), d (s, if i then 1 else 0) ∈ V i := by
    have hsrc : (s₀, if i then 1 else 0) ∈ d.source :=
      hds ⟨hs₀, by cases i <;> simp⟩
    have hcurve : ContinuousAt (fun s : ℝ => d (s, if i then 1 else 0)) s₀ :=
      (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hsrc)).continuousAt.comp
        (f := fun s : ℝ => (s, if i then 1 else 0))
        (continuousAt_id.prodMk continuousAt_const)
    have hnear : (fun s : ℝ => d (s, if i then 1 else 0)) ⁻¹' V i ∈ 𝓝 s₀ :=
      hcurve.preimage_mem_nhds ((hV i).mem_nhds ((hpoint i).symm ▸ hxV i))
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨min η (ρ / 2), lt_min hη (by positivity), min_le_left _ _, ?_⟩
    intro s hs
    apply hρV
    rw [Metric.mem_ball, Real.dist_eq]
    have ha : |s - s₀| ≤ min η (ρ / 2) := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact ha.trans_lt ((min_le_right η (ρ / 2)).trans_lt (by linarith))
  choose width hwpos hwη hwrow using hwidth
  let θ := min (width false) (width true)
  have hθ : 0 < θ := lt_min (hwpos false) (hwpos true)
  have hθle (i : Bool) : θ ≤ width i := by
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hθrow (i : Bool) (s : ℝ) (hs : s ∈ Icc (s₀ - θ) (s₀ + θ)) :
      d (s, if i then 1 else 0) ∈ V i :=
    hwrow i s ⟨by linarith [hs.1, hθle i], by linarith [hs.2, hθle i]⟩
  have hwhole : K ⊆ Ξ.source := fun _ hy => hΞs (Or.inl (Or.inl hy))
  have hΞimage : Ξ '' K = D '' (Complex.equivRealProdCLM.symm ''
      (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (f (γ b)) (f (γ a)))) :=
    (image_congr (fun y hy => hregmatch (hKreg hy))).trans hCimage
  have hp0 : χ' false 0 = p := hχ'0 false
  have hq0 : χ' true 0 = q := hχ'0 true
  have hpΞ : p ∈ Ξ.source := hp0 ▸ (hΞcrit false).1
  have hqΞ : q ∈ Ξ.source := hq0 ▸ (hΞcrit true).1
  refine ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    ε, a, b, s₀, δ, side, hε, hab, hδ, w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos,
    d, hd, hds, hdt, hheight, hrays, hcentral, hover, hfield,
    κ, hκs, hκt, hκ, hκi, hκd, hκimage, hκinverse,
    W₀, W₁, hW₀, hW₁, hWdisj, hWO, hga, hgb, hcritical,
    D, hDi, hCs, hCf, hCimage, η, hη, hηδ, hηs, hκsmall, hCsmall,
    Ξ, hΞO, hpΞ, hqΞ,
    hwhole, hΞimage, ⟨Vreg, hVreg, hKreg, hregsub, hregmatch⟩,
    θ, hθ, (hθle false).trans (hwη false), ?_⟩
  intro i
  have hzinv : (χ' i).symm (x i) = z i :=
    (congrArg (χ' i).symm (hχ'z i)).symm.trans ((χ' i).left_inv (hzχ' i))
  have hcritinv : (χ' i).symm (critical i) = 0 :=
    (congrArg (χ' i).symm (hχ'0 i)).symm.trans
      ((χ' i).left_inv ((hΦsource i).symm ▸ hχ0s i))
  refine ⟨Φ i, E i, V i, hΦ i, hΦi i, hΦ0 i, hΦf i, hΦfix i,
    hΦsource i, hzinv, hV i, hcritV i, hVs i, hVc i,
    (hVc i _ (hcritV i)).trans (congrArg (E i) hcritinv), ?_,
    fun t ht => hRV i ⟨t, ht, rfl⟩, hθrow i, ?_, ?_, L i, hL i, hLs i, hfix i⟩
  · rw [image_image]
    exact image_congr (hVc i)
  · intro u hu huV
    have hu' : u ∈ (χ' i).source := (hΦsource i).symm ▸ hu
    have he : Ξ (χ' i u) = E i u :=
      (hVc i _ huV).trans (congrArg (E i) ((χ' i).left_inv hu'))
    exact ⟨he, (congrArg Ξ.symm he).symm.trans (Ξ.left_inv (hVs i huV).1)⟩
  · intro u hu
    have hn := hnormal i u ((hΦsource i).symm ▸ hu)
    cases i <;> exact hn

end DifferentialGeometry.Morse
