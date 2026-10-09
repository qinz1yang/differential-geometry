import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.FibreRoot
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.FibreApproximation

/-!
# Smooth replacement of a compact two-sided `C^k` hypersurface (W-SUB, T)

Blueprint LFR47 (`master207A.tex:28975`; "choose a compatible smooth structure on the compact
`C^{m-1}` base", A:28994), design risk R7, external review of the finite soul §8, disposition D8
(weak output). Input: a compact `C^n` manifold `S` (`1 ≤ n`, `n = k - 1` for a `C^k`
hypersurface) and a two-sided `C^n` tube `Φ : S × (-ε, ε) → M` into a smooth boundaryless manifold
of dimension `d + 1` (a `PartialDiffeomorph`, e.g. the calibrated normal tube of the soul).

`exists_smooth_hypersurface_two_sided`: for every `0 < δ ≤ ε` there is a compact smooth embedded
slice `Ŝ ⊆ Φ (S × (-δ, δ))` of `M` with a `C^n` diffeomorphism `β : Ŝ ≃ S` given by the normal
projection `x ↦ (Φ.symm x).1`; `Ŝ` is the graph `s ↦ Φ (s, h s)` of a `C^n` function with
`|h| < δ`.

Route (review §8): the defining function `g = (Φ.symm ·).2` (the signed normal height) is
approximated by a globally smooth `f` with `|f - g| < η` and `f - g` `η`-Lipschitz along the fibres
on the compact buffer `Φ (S × [-δ/2, δ/2])` (A, `exists_smooth_approx_fibre_lipschitz`), with
`η = min (δ/4) (1/2)`; then `f` has fibre slope `≥ 1 - η > 0` and opposite signs at the heights
`∓δ/4`, and the fibre-root kernel K2 (`exists_fibreRoot_hypersurface`) applies on `Φ (S × (-δ/2, δ/2))`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

/-- A two-point slope bound `c (v - u) ≤ F v - F u` on an open set bounds the derivative below. -/
theorem le_deriv_of_slope_le {F : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {c : ℝ}
    (hslope : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → c * (v - u) ≤ F v - F u) {t : ℝ} (ht : t ∈ s)
    (hd : DifferentiableAt ℝ F t) : c ≤ deriv F t := by
  have hmono : MonotoneOn (fun u => F u - c * u) s := by
    intro u hu v hv huv
    have := hslope u hu v hv huv
    change F u - c * u ≤ F v - c * v
    nlinarith
  have hG : HasDerivAt (fun u => F u - c * u) (deriv F t - c * 1) t :=
    hd.hasDerivAt.sub ((hasDerivAt_id t).const_mul c)
  have h0 := hmono.derivWithin_nonneg (x := t)
  rw [derivWithin_of_isOpen hs ht, hG.deriv] at h0
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [CompleteSpace ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [CompactSpace S]

/-- **T: smooth replacement of a compact two-sided `C^k` hypersurface.** -/
theorem exists_smooth_hypersurface_two_sided {d : ℕ} (hdim : Module.finrank ℝ E = d + 1)
    {n : ℕ} (hn : 1 ≤ n)
    (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (S × ℝ) M n) {ε δ : ℝ} (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hsrc : univ ×ˢ Ioo (-ε) ε ⊆ Φ.source) :
    ∃ Ŝ : Set M, ∃ hŜ : IsEmbeddedSlice I d Ŝ, IsCompact Ŝ ∧ Ŝ ⊆ Φ '' (univ ×ˢ Ioo (-δ) δ) ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS Ŝ S n, (∀ x, β x = (Φ.symm x).1) ∧
        ∃ h : S → ℝ, ContMDiff IS 𝓘(ℝ, ℝ) n h ∧ (∀ s, |h s| < δ) ∧
          ∀ s, (β.symm s : M) = Φ (s, h s) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  set a := δ / 2 with ha
  set b := δ / 4 with hb
  set η := min (δ / 4) (1 / 2) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hηb : η ≤ b := min_le_left _ _
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hIoo : Ioo (-a) a ⊆ Ioo (-ε) ε := Ioo_subset_Ioo (by linarith) (by linarith)
  have hIcc : Icc (-a) a ⊆ Ioo (-ε) ε := Icc_subset_Ioo (by linarith) (by linarith)
  have hmem : ∀ s, ∀ t ∈ Ioo (-ε) ε, (s, t) ∈ Φ.source := fun s t ht => hsrc ⟨mem_univ _, ht⟩
  -- the defining function: the normal height
  let g : M → ℝ := fun x => (Φ.symm x).2
  have hg : ContMDiffOn I 𝓘(ℝ, ℝ) 1 g Φ.target :=
    contMDiff_snd.comp_contMDiffOn (Φ.contMDiffOn_invFun.of_le hn1)
  have hgΦ : ∀ s, ∀ t ∈ Ioo (-ε) ε, g (Φ (s, t)) = t := by
    intro s t ht
    have hl : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (s, t)) = (s, t) := Φ.left_inv (hmem s t ht)
    change (Φ.symm.toPartialEquiv (Φ.toPartialEquiv (s, t))).2 = t
    rw [hl]
  have hΦ1 : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) I 1 Φ (univ ×ˢ Ioo (-ε) ε) :=
    (Φ.contMDiffOn_toFun.of_le hn1).mono hsrc
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_approx_fibre_lipschitz Φ.open_target hg
    (a := a) (by linarith) hΦ1 (fun s t ht => Φ.map_source (hmem s t (hIcc ht))) hηpos
  -- fibre slope and end signs
  have hfΦ : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1 (fun p => f (Φ p)) (univ ×ˢ Ioo (-ε) ε) :=
    (hf.of_le (by exact_mod_cast le_top)).comp_contMDiffOn hΦ1
  have hderiv : ∀ s, ∀ t ∈ Ioo (-a) a, 0 < deriv (fun τ => f (Φ (s, τ))) t := by
    intro s t ht
    have hslope : ∀ u ∈ Ioo (-a) a, ∀ v ∈ Ioo (-a) a, u ≤ v →
        (1 - η) * (v - u) ≤ f (Φ (s, v)) - f (Φ (s, u)) := by
      intro u hu v hv huv
      have h := hf1 s u (Ioo_subset_Icc_self hu) v (Ioo_subset_Icc_self hv)
      rw [hgΦ s u (hIoo hu), hgΦ s v (hIoo hv), abs_of_nonneg (sub_nonneg.mpr huv)] at h
      have h' := (abs_le.mp h).1
      nlinarith
    have hd := differentiableAt_fibre hfΦ s (hIoo ht)
    have := le_deriv_of_slope_le isOpen_Ioo hslope ht hd
    linarith
  have hb' : b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
  have hnb' : -b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
  have hneg : ∀ s, f (Φ (s, -b)) < 0 := by
    intro s
    have h := hf0 s (-b) hnb'
    rw [hgΦ s (-b) (hIcc hnb')] at h
    have := (abs_lt.mp h).2
    linarith
  have hpos : ∀ s, 0 < f (Φ (s, b)) := by
    intro s
    have h := hf0 s b hb'
    rw [hgΦ s b (hIcc hb')] at h
    have := (abs_lt.mp h).1
    linarith
  obtain ⟨hŜ, hc, hsub, hrest⟩ := exists_fibreRoot_hypersurface hdim hn Φ (a := a) (b := b)
    (by positivity) (by linarith) (fun p hp => hsrc ⟨mem_univ _, hIoo hp.2⟩) hf.contMDiffOn hneg
    hpos hderiv
  refine ⟨fibreZeroSet Φ a f, hŜ, hc, hsub.trans (image_mono (prod_mono subset_rfl
    (Ioo_subset_Ioo (by linarith) (by linarith)))), ?_⟩
  intro _
  obtain ⟨β, hβ, h, hh, hhb, hβs⟩ := hrest
  refine ⟨β, hβ, h, hh, fun s => abs_lt.mpr ⟨?_, ?_⟩, hβs⟩
  · linarith [(hhb s).1]
  · linarith [(hhb s).2]

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
