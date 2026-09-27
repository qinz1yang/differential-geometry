import DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCutoffProjection
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE (saddleBandCurve quadraticRadialCurve)

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem disjoint_negative_saddle_projection_reference_cylinder_and_cap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (G : F ≃ₘ[ℝ] F)
    (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {ψ : ℝ → ℝ} (hψ : StrictMono ψ) {s τ δ σ h k ρ r v₀ ℓ b : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hτδ : τ < δ) (hσ : σ ^ 2 = 1)
    (hh1 : h < 1) (hkh : k < h) (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hbaseb : ℓ + τ < b) (hψb : ψ b = b) (hQheight : ∀ z, (Q z).2 = ψ z.2)
    {Ucap : Set (F × ℝ)} (hcap : ∀ z ∈ Ucap, b ≤ (Q z).2)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ a < τ, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆ (G '' closedBall 0 r)ᶜ)
    {R : Set (ℝ × ℝ)} {θ : ℝ × ℝ → ℝ}
    (hwidth : ∀ z ∈ R, |z.1| ≤ k) (hbottom : ∀ z ∈ R, -v₀ ≤ σ * z.2)
    (hmodel : ∀ z ∈ R,
      T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) =
        (B (saddleBandCurve z (θ (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z.1) *
          (τ - ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))),
          ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))
    (htransBottom : ∀ z ∈ R,
      -v₀ ≤ σ * (B.symm (T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1).2)
    (htransEnergy : ∀ z ∈ R,
      (1 - (B.symm (T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1).1 ^ 2) *
      ((B.symm (T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1).2 ^ 2 + 2 * s) / 2 ≤ s + τ)
    {K : Set (F × ℝ)}
    (hRK : (fun z : ℝ × ℝ => T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))) '' R ⊆ K)
    (hproj : InjOn (fun q : F × ℝ => (Q q).1) K) :
    Disjoint
      ((fun z : ℝ × ℝ => (Q (T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))).1) ''
        {z ∈ R | σ * z.2 ≤ 0})
      ((fun q : F × ℝ => (Q q).1) ''
        (K ∩ (((G '' sphere 0 r) ×ˢ univ) ∪ Ucap))) := by
  let q := fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
  let f := fun z : ℝ × ℝ => T (B z, ℓ + q z)
  let g := fun z : ℝ × ℝ => B.symm (f z).1
  have hg (z : ℝ × ℝ) (hz : z ∈ R) :
      g z = saddleBandCurve z (θ (q z, z.1) * (τ - q z)) := by
    dsimp only [g, f]
    rw [hmodel z hz]
    exact B.symm_apply_apply _
  have hgwidth (z : ℝ × ℝ) (hz : z ∈ R) : (g z).1 = z.1 := by rw [hg z hz]; rfl
  have hcontact := saddle_lower_band_inter_cap_circle_subset B G hs hτ hτδ hσ hh1 hkh hv₀ hv₀τ
    hupper hclear (K := g '' R)
    (by rintro _ ⟨z, hz, rfl⟩; rw [hgwidth z hz]; exact hwidth z hz)
    (by rintro _ ⟨z, hz, rfl⟩; exact htransBottom z hz)
    (by rintro _ ⟨z, hz, rfl⟩; exact htransEnergy z hz)
  apply disjoint_left.mpr
  rintro y ⟨z, ⟨hz, hzneg⟩, rfl⟩ ⟨w, ⟨hwK, hw⟩, heq⟩
  have hwf : w = f z := hproj hwK (hRK (mem_image_of_mem _ hz)) heq
  subst w
  have htime : (f z).2 = ℓ + q z := by dsimp only [f]; rw [hmodel z hz]
  have hnegative : σ * (g z).2 ≤ 0 := by
    rw [hg z hz]
    change σ * (Real.sqrt _ * z.2) ≤ 0
    rw [mul_left_comm]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hzneg
  rcases hw with hw | hw
  · have hgc : B (g z) ∈ G '' sphere 0 r := by
      simpa only [g, B.apply_symm_apply] using hw.1
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := hcontact ⟨⟨g z, ⟨z, hz, rfl⟩, rfl⟩, hgc⟩
    have hgu := B.injective heq
    have hunit : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hrad : 0 < 2 * (τ + s * u ^ 2) / (1 - u ^ 2) :=
      div_pos (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u))))
        (by nlinarith [hunit.1, hunit.2])
    rw [← hgu] at hnegative
    change σ * (σ * Real.sqrt _) ≤ 0 at hnegative
    rw [← mul_assoc, ← pow_two, hσ, one_mul] at hnegative
    exact (not_le_of_gt (Real.sqrt_pos.mpr hrad)) hnegative
  · have hsq : z.2 ^ 2 ≤ v₀ ^ 2 := by
      have hsquare : (σ * z.2) ^ 2 = z.2 ^ 2 := by rw [mul_pow, hσ, one_mul]
      have hlo := hbottom z hz
      nlinarith
    have hp := mul_nonneg (sq_nonneg z.1)
      (add_nonneg (sq_nonneg z.2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs))
    have hq : q z < τ := by dsimp only [q]; nlinarith
    have hfb : (f z).2 < b := by rw [htime]; linarith
    have hbψ := hcap (f z) hw
    rw [hQheight, ← hψb] at hbψ
    exact (hψ hfb).not_ge hbψ

private theorem exists_isImage_negative_saddle_lens
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, F) (ℝ × ℝ) F ∞)
    {s σ a j k v₀ : ℝ} (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hk1 : k < 1)
    (hv₀ : 0 < v₀) (hv₀j : v₀ ^ 2 / 2 < j) {N : Set F} (hN : IsClosed N) :
    let q := fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R := {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let Y := χ '' R ∪ N
    R ⊆ χ.source →
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    Disjoint (χ '' {z ∈ R | σ * z.2 ≤ 0}) N →
    ∃ c : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, F) (ℝ × ℝ) F ∞,
      (fun z : ℝ × ℝ => (q z, z.1)) '' {z ∈ R | σ * z.2 = -v₀} ⊆ c.source ∧
      χ '' {z ∈ R | σ * z.2 = -v₀} ⊆ c.target ∧
      (c : (ℝ × ℝ) → F) = (fun p => χ (Morse.saddleBandLevelCurve s p.1 (-σ) p.2)) ∧
      (c.symm : F → ℝ × ℝ) = (fun y => (q (χ.symm y), (χ.symm y).1)) ∧
      c.target ⊆ χ.target ∧
      c.toOpenPartialHomeomorph.IsImage
        {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2} Y := by
  intro q R Y hR hside hsep
  obtain ⟨n, hnsource, hntarget, hn, hni⟩ :=
    Morse.exists_partialDiffeomorph_saddle_band_negative_half_strip (s := s) hσ
  have hnleft (p : ℝ × ℝ) (hp : p ∈ n.source) : n.symm (n p) = p := n.left_inv hp
  have hnright (z : ℝ × ℝ) (hz : z ∈ n.target) : n (n.symm z) = z := n.right_inv hz
  let Φ := n.trans χ
  let U := (Φ.source ∩ Φ ⁻¹' Nᶜ) ∩ {p : ℝ × ℝ | |p.2| < k ∧ p.1 < j}
  have hU : IsOpen U :=
    (Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hN.isOpen_compl).inter
      ((isOpen_lt continuous_snd.abs continuous_const).inter (isOpen_lt continuous_fst continuous_const))
  let c := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ U hU
  have hcfun : (c : (ℝ × ℝ) → F) = fun p => χ (Morse.saddleBandLevelCurve s p.1 (-σ) p.2) := by
    change (fun p => χ (n p)) = _
    rw [hn]
  have hcfull (p : ℝ × ℝ) : c p = χ (n p) := rfl
  have hcinv : (c.symm : F → ℝ × ℝ) = fun y => (q (χ.symm y), (χ.symm y).1) := by
    change (fun y => n.symm (χ.symm y)) = _
    rw [hni]
  have hncoords (p : ℝ × ℝ) (hp : p ∈ n.source) : q (n p) = p.1 ∧ (n p).1 = p.2 := by
    have he := hnleft p hp
    rw [hni] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hedge (z : ℝ × ℝ) (hz : z ∈ R) (hzedge : σ * z.2 = -v₀) :
      (q z, z.1) ∈ c.source := by
    have hw : |z.1| < k := lt_of_le_of_ne hz.1 (by
      intro he
      have hp := hside z hz he
      rw [hzedge] at hp
      linarith)
    have hznt : z ∈ n.target := by
      rw [hntarget]
      exact ⟨abs_lt.mp (hw.trans hk1), by rw [hzedge]; linarith⟩
    have hnp : n.symm z ∈ n.source := n.map_target hznt
    have hnpχ : n (n.symm z) ∈ χ.source := by rw [hnright z hznt]; exact hR hz
    have hpΦ : n.symm z ∈ Φ.source := ⟨hnp, hnpχ⟩
    have hnot : Φ (n.symm z) ∉ N := by
      change χ (n (n.symm z)) ∉ N
      rw [hnright z hznt]
      exact fun hnN => disjoint_left.mp hsep ⟨z, ⟨hz, by rw [hzedge]; linarith⟩, rfl⟩ hnN
    have hqj : q z < j := by
      have hsquare : z.2 ^ 2 = v₀ ^ 2 := by
        have he := congrArg (fun x : ℝ => x ^ 2) hzedge
        simpa only [mul_pow, hσ, one_mul, neg_sq] using he
      have hp := mul_nonneg (sq_nonneg z.1)
        (add_nonneg (sq_nonneg z.2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs))
      dsimp only [q]
      nlinarith
    have hpU : n.symm z ∈ U := by
      refine ⟨⟨hpΦ, hnot⟩, ?_⟩
      rw [hni]
      exact ⟨hw, hqj⟩
    have hpC : n.symm z ∈ c.source := ⟨hpΦ, hpU⟩
    simpa only [hni] using hpC
  refine ⟨c, ?_, ?_, hcfun, hcinv, ?_, ?_⟩
  · rintro _ ⟨z, ⟨hz, he⟩, rfl⟩
    exact hedge z hz he
  · rintro _ ⟨z, ⟨hz, he⟩, rfl⟩
    have hc := c.map_source (hedge z hz he)
    have hznt : z ∈ n.target := by
      rw [hntarget]
      exact ⟨abs_lt.mp (hz.1.trans_lt hk1), by rw [he]; linarith⟩
    have hcval : c (q z, z.1) = χ z := by
      rw [hcfull, ← show n.symm z = (q z, z.1) by rw [hni], hnright z hznt]
    rwa [hcval] at hc
  · exact fun y hy => hy.1.1
  · intro p hp
    change c p ∈ Y ↔ a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2
    have hpΦ : p ∈ Φ.source := hp.1
    have hpU : p ∈ U := hp.2
    have hpn : p ∈ n.source := hpΦ.1
    have hpχ : n p ∈ χ.source := hpΦ.2
    have hznegative : σ * (n p).2 < 0 := by
      have ht := n.map_source hpn
      rw [hntarget] at ht
      exact ht.2
    have hzunit : (n p).1 ∈ Ioo (-1 : ℝ) 1 := by
      have ht := n.map_source hpn
      rw [hntarget] at ht
      exact ht.1
    have hcoords := hncoords p hpn
    have hmem : c p ∈ Y ↔ n p ∈ R := by
      rw [hcfull]
      constructor
      · rintro (⟨z, hz, heq⟩ | hnN)
        · exact χ.toPartialEquiv.injOn (hR hz) hpχ heq ▸ hz
        · exact (hpU.1.2 hnN).elim
      · intro hz
        exact Or.inl ⟨n p, hz, rfl⟩
    rw [hmem]
    change (|((n p).1)| ≤ k ∧ -v₀ ≤ σ * (n p).2 ∧ a ≤ q (n p) ∧ q (n p) ≤ j) ↔ _
    rw [Morse.saddle_band_negative_side_iff_height_le (s := s) hσ hzunit hznegative hv₀.le]
    change (|(n p).1| ≤ k ∧ q (n p) ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * (n p).1 ^ 2 ∧
      a ≤ q (n p) ∧ q (n p) ≤ j) ↔ _
    rw [hcoords.1, hcoords.2]
    exact ⟨fun h => ⟨h.2.2.1, h.2.1⟩,
      fun h => ⟨hpU.2.1.le, h.2, h.1, hpU.2.2.le⟩⟩

private theorem exists_isImage_actual_negative_saddle_lens
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : M → F × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) {ψ : ℝ → ℝ} (hψ : StrictMono ψ)
    {s τ δ σ h k ρ r v₀ ℓ a j b m : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hτδ : τ < δ) (hσ : σ ^ 2 = 1)
    (hh1 : h < 1) (hkh : k < h) (hv₀ : 0 < v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hv₀j : v₀ ^ 2 / 2 < j) (hbaseb : ℓ + τ < b)
    (hTheight : ∀ z, (T z).2 = z.2) (hψb : ψ b = b) (hQheight : ∀ z, (Q z).2 = ψ z.2)
    {Ucap : Set (F × ℝ)}
    (hQcap : Q '' Ucap = {z : F × ℝ | b ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2})
    {C : Set F} (hC : C ⊆ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ t < τ, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t}) ⊆ (G '' closedBall 0 r)ᶜ)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hgraph : ∀ z ∈ U, e (β z) =
      (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))
    {θ : ℝ × ℝ → ℝ}
    {OQ : Set F} (hOQ : IsOpen OQ) {gQ : F → ℝ} (hgQ : ContDiffOn ℝ ∞ gQ OQ)
    {WQ : Set (F × ℝ)} (hWQ : IsOpen WQ) (hWQO : WQ ⊆ {p | p.1 ∈ OQ})
    (hWQeq : WQ ∩ Q '' range (T ∘ e) = WQ ∩ {p | p.2 = gQ p.1}) :
    let q := fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R := {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let f := fun z : ℝ × ℝ => T (B z, ℓ + q z)
    let K := f '' R ∪ ((C ×ˢ Icc (ℓ + a) (ℓ + j)) ∪ ((G '' sphere 0 r) ×ˢ Icc (ℓ + j) b) ∪ Ucap)
    let P := fun z => (Q (f z)).1
    let Y := (fun p : F × ℝ => (Q p).1) '' K
    IsCompact K → R ⊆ U → Q '' K ⊆ WQ →
    InjOn (fun p : F × ℝ => (Q p).1) K →
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    (∀ z ∈ R, f z = (B (saddleBandCurve z (θ (q z, z.1) * (τ - q z))), ℓ + q z)) →
    (∀ z ∈ R, -v₀ ≤ σ * (B.symm (f z).1).2) →
    (∀ z ∈ R, (1 - (B.symm (f z).1).1 ^ 2) * ((B.symm (f z).1).2 ^ 2 + 2 * s) / 2 ≤ s + τ) →
    ∃ c : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, F) (ℝ × ℝ) F ∞,
      (fun z : ℝ × ℝ => (q z, z.1)) '' {z ∈ R | σ * z.2 = -v₀} ⊆ c.source ∧
      P '' {z ∈ R | σ * z.2 = -v₀} ⊆ c.target ∧
      (c : (ℝ × ℝ) → F) = (fun p => P (saddleBandLevelCurve s p.1 (-σ) p.2)) ∧
      (∀ p ∈ c.source, gQ (c p) = ψ (ℓ + p.1)) ∧
      c.toOpenPartialHomeomorph.IsImage
        {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2} Y := by
  intro q R f K P Y hK hRU hKW hproj hside hmodel hbottom henergy
  have hraw (z : ℝ × ℝ) (hz : z ∈ U) : f z ∈ range (T ∘ e) := by
    refine ⟨β z, ?_⟩
    change T (e (β z)) = f z
    rw [hgraph z hz]
  have hq : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ℓ + q z) := by dsimp only [q]; fun_prop
  have hrawgraph (z : ℝ × ℝ) (hz : z ∈ U) (hzw : Q (f z) ∈ WQ) :
      (Q (f z)).2 = gQ (Q (f z)).1 :=
    (hWQeq.subset ⟨hzw, mem_image_of_mem Q (hraw z hz)⟩).2
  obtain ⟨χ, hχsource, hχ, hχinv⟩ :=
    DifferentialGeometry.Topology.exists_partialDiffeomorph_projection_of_graph_neighborhood B (T.trans Q) hq hU hOQ hgQ hWQ hWQO hrawgraph
  have hχP : (χ : (ℝ × ℝ) → F) = P := by
    funext z
    rw [hχ]
    rfl
  have hRχ : R ⊆ χ.source := by
    rw [hχsource]
    exact fun z hz => ⟨hRU hz, hKW (mem_image_of_mem Q (Or.inl (mem_image_of_mem f hz)))⟩
  let N₀ : Set (F × ℝ) := K ∩ (((G '' sphere 0 r) ×ˢ univ) ∪ Ucap)
  let N := (fun p : F × ℝ => (Q p).1) '' N₀
  have hcapClosed : IsClosed Ucap := by
    have hc : IsClosed {z : F × ℝ | b ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} :=
      (isClosed_le continuous_const continuous_snd).inter
        (isClosed_eq continuous_snd (by fun_prop))
    rw [← hQcap] at hc
    have hp := hc.preimage Q.continuous
    have hQi : Function.Injective (Q : F × ℝ → F × ℝ) := Q.injective
    rwa [preimage_image_eq Ucap hQi] at hp
  have hN : IsClosed N :=
    ((hK.inter_right (((G.toHomeomorph.isClosedMap _ isClosed_sphere).prod isClosed_univ).union hcapClosed)).image
      Q.continuous.fst).isClosed
  have hsepP := disjoint_negative_saddle_projection_reference_cylinder_and_cap B G T Q hψ hs hτ hτδ hσ
    hh1 hkh hv₀.le hv₀τ hbaseb hψb hQheight
    (fun z hz => (hQcap.subset (mem_image_of_mem Q hz)).1) hupper hclear
    (fun z hz => hz.1) (fun z hz => hz.2.1) hmodel hbottom henergy
    (show f '' R ⊆ K from subset_union_left) hproj
  have hsep : Disjoint (χ '' {z ∈ R | σ * z.2 ≤ 0}) N := by
    simpa only [hχP, N, N₀, P, f, q] using hsepP
  have hY : χ '' R ∪ N = Y := by
    apply subset_antisymm
    · rintro y (⟨z, hz, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨f z, Or.inl (mem_image_of_mem f hz), (congrFun hχP z).symm⟩
      · exact ⟨w, hw.1, rfl⟩
    · rintro y ⟨w, hw, rfl⟩
      rcases hw with ⟨z, hz, rfl⟩ | hw
      · exact Or.inl ⟨z, hz, congrFun hχP z⟩
      · apply Or.inr
        refine ⟨w, ⟨Or.inr hw, ?_⟩, rfl⟩
        rcases hw with (hw | hw) | hw
        · exact Or.inl ⟨hC hw.1, mem_univ _⟩
        · exact Or.inl ⟨hw.1, mem_univ _⟩
        · exact Or.inr hw
  obtain ⟨c, hsource, htarget, hc, hci, hctarget, hImage⟩ :=
    exists_isImage_negative_saddle_lens χ hs hσ (hkh.trans hh1) hv₀ hv₀j hN hRχ hside hsep
  refine ⟨c, hsource, ?_, ?_, ?_, hY ▸ hImage⟩
  · simpa only [hχP] using htarget
  · simpa only [hχP] using hc
  · intro p hp
    have hcp : c p ∈ χ.target := hctarget (c.map_source hp)
    have hzp : χ.symm (c p) ∈ χ.source := χ.map_target hcp
    have hzin := hzp
    rw [hχsource] at hzin
    have hright : χ (χ.symm (c p)) = c p := χ.right_inv hcp
    have hrightP : P (χ.symm (c p)) = c p := by rwa [hχP] at hright
    have hleft : c.symm (c p) = p := c.left_inv hp
    rw [hci] at hleft
    have htime : q (χ.symm (c p)) = p.1 := congrArg Prod.fst hleft
    have hg := hrawgraph (χ.symm (c p)) hzin.1 hzin.2
    change (Q (f (χ.symm (c p)))).2 = gQ (P (χ.symm (c p))) at hg
    rw [hrightP, hQheight] at hg
    dsimp only [f] at hg
    rw [hTheight, htime] at hg
    exact hg.symm

theorem exists_partialDiffeomorph_saddle_cutoff_negative_edge
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : M → F × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) {ψ : ℝ → ℝ} (hψ : StrictMono ψ)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {θ : ℝ × ℝ → ℝ} {V : Set (ℝ × (ℝ × ℝ))}
    {c s h ε d τ δ j σ ρ r v₀ b m : ℝ}
    (hs : 0 ≤ s) (hh : 0 < h) (hh1 : h < 1) (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hτδ : τ < δ) (hτd : τ < d) (hj : j ∈ Ioo (τ / 2) τ)
    (hσ : σ ^ 2 = 1) (hv₀ : 0 < v₀) (hv₀τ : v₀ ^ 2 / 2 < τ / 4)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hTheight : ∀ q, (T q).2 = q.2) (hθle : ∀ q, θ q ≤ 1)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ a < τ, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆ (G '' closedBall 0 r)ᶜ)
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hVreg : ∀ q ∈ V, θ (q.1, q.2.1) * (τ - q.1) = 0 ∨
      (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (τ - q.1)) / q.2.2 ^ 2))
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), c + s + q.1))
    (hbaseb : c + s + τ < b) (hψb : ψ b = b) (hQheight : ∀ z, (Q z).2 = ψ z.2)
    {Ucap : Set (F × ℝ)}
    (hQcap : Q '' Ucap = {z : F × ℝ | b ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2})
    {OQ : Set F} (hOQ : IsOpen OQ) {gQ : F → ℝ} (hgQ : ContDiffOn ℝ ∞ gQ OQ)
    {WQ : Set (F × ℝ)} (hWQ : IsOpen WQ) (hWQO : WQ ⊆ {p | p.1 ∈ OQ})
    (hWQeq : WQ ∩ Q '' range (T ∘ e) = WQ ∩ {p | p.2 = gQ p.1}) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc (-ε / 2) j
    let K := ((fun p : F × ℝ => (p.1, c + s + p.2)) '' S) ∪
      ((G '' sphere 0 r) ×ˢ Icc (c + s + j) b ∪ Ucap)
    let P := fun z : ℝ × ℝ => (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
    IsCompact K → R ⊆ U → Q '' K ⊆ WQ →
    InjOn (fun p : F × ℝ => (Q p).1) K →
    (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) →
    (∀ p ∈ J '' R, -v₀ ≤ σ * p.1.2) →
    ∃ χ : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, F) (ℝ × ℝ) F ∞,
      (fun z : ℝ × ℝ => ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)) ''
        {z ∈ R | σ * z.2 = -v₀} ⊆ χ.source ∧
      P '' {z ∈ R | σ * z.2 = -v₀} ⊆ χ.target ∧
      (χ : (ℝ × ℝ) → F) = (fun p => P (saddleBandLevelCurve s p.1 (-σ) p.2)) ∧
      (∀ p ∈ χ.source, gQ (χ p) = ψ (c + s + p.1)) ∧
      χ.toOpenPartialHomeomorph.IsImage
        {p : ℝ × ℝ | -ε / 2 ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2}
        ((fun p : F × ℝ => (Q p).1) '' K) := by
  intro R J C S K P hK hRU hKW hproj hside hpoints
  let q := fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
  let f := fun z : ℝ × ℝ => T (B z, c + s + q z)
  have htime (z : ℝ × ℝ) : c + s + q z = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
    dsimp only [q]
    ring
  have hJf (z : ℝ × ℝ) : (B (J z).1, c + s + (J z).2) = f z := by
    dsimp only [f]
    rw [htime]
    apply Prod.ext
    · exact B.apply_symm_apply _
    · rw [hTheight]
  have hKraw : K = f '' R ∪ ((C ×ˢ Icc (c + s + (-ε / 2)) (c + s + j)) ∪
      ((G '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪ Ucap) := by
    have hshiftRaw : (fun p : F × ℝ => (p.1, c + s + p.2)) ''
        ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) = f '' R := by
      rw [image_image, image_image]
      congr 1
      funext z
      exact hJf z
    have hshiftWall : (fun p : F × ℝ => (p.1, c + s + p.2)) ''
        (C ×ˢ Icc (-ε / 2) j) = C ×ˢ Icc (c + s + (-ε / 2)) (c + s + j) := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz.1, by dsimp only; linarith only [hz.2.1], by dsimp only; linarith only [hz.2.2]⟩
      · intro hp
        refine ⟨(p.1, p.2 - (c + s)), ⟨hp.1, ?_, ?_⟩, ?_⟩
        · linarith only [hp.2.1]
        · linarith only [hp.2.2]
        · apply Prod.ext
          · rfl
          · dsimp only
            ring
    dsimp only [K, S]
    rw [image_union, hshiftRaw, hshiftWall]
    ext p
    simp only [mem_union]
    tauto
  have hgraph' (z : ℝ × ℝ) (hz : z ∈ U) : e (β z) = (B z, c + s + q z) := by
    rw [htime]
    exact hgraph z hz
  have hmodel (z : ℝ × ℝ) (hz : z ∈ R) :
      f z = (B (saddleBandCurve z (θ (q z, z.1) * (τ - q z))), c + s + q z) := by
    exact hTmodel (q z, z) (hKV ⟨⟨by dsimp only [q]; linarith only [hz.2.2.1, hε],
      hz.2.2.2.trans (hj.2.trans hτd).le⟩, hz.1.trans (by linarith only [hh]), by dsimp only [q]; ring⟩)
  have hcertificate := saddle_cutoff_half_band_coordinates_and_height B T hh.le hε
    (hj.2.trans hτd).le hj.2.le hθle hKV hVreg hTmodel (v₀ := v₀) (σ := σ)
  have hbottom (z : ℝ × ℝ) (hz : z ∈ R) : -v₀ ≤ σ * (B.symm (f z).1).2 := by
    dsimp only [f]
    rw [htime]
    exact hpoints (J z) ⟨z, hz, rfl⟩
  have henergy (z : ℝ × ℝ) (hz : z ∈ R) :
      (1 - (B.symm (f z).1).1 ^ 2) * ((B.symm (f z).1).2 ^ 2 + 2 * s) / 2 ≤ s + τ := by
    dsimp only [f]
    rw [htime]
    exact (hcertificate z hz).2
  have hlens := exists_isImage_actual_negative_saddle_lens e B G T Q hψ hs hτ hτδ hσ hh1
    (k := 5 * h / 8) (by linarith only [hh]) hv₀ (by nlinarith only [hv₀τ, hτ])
    (by linarith only [hv₀τ, hj.1, hτ]) hbaseb hTheight hψb hQheight hQcap
    (C := C) sdiff_subset hupper hclear hU hgraph' hOQ hgQ hWQ hWQO hWQeq
    (hKraw ▸ hK) hRU (hKraw ▸ hKW) (hKraw ▸ hproj) hside hmodel hbottom henergy
  rw [hKraw]
  simpa only [P, R, f, htime, q] using hlens

private theorem fderiv_ne_zero_on_negative_saddle_source_graph
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : M → F × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hTheight : ∀ q, (T q).2 = q.2) (hQheight : ∀ q, (Q q).2 = ψ q.2)
    (hψ : ∀ t, 0 < deriv ψ t)
    {O : Set F} (hO : IsOpen O) {g : F → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (F × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    (hWeq : W ∩ Q '' range (T ∘ e) = W ∩ {p | p.2 = g p.1})
    {z : ℝ × ℝ} (hzU : z ∈ U)
    (hzW : Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∈ W)
    (hzlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s < 0) :
    fderiv ℝ g (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1 ≠ 0 := by
  let γ : ℝ → F × ℝ := fun u => Q (T (B (u, z.2), c + (1 - u ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
  have hγz : γ z.1 = Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) := rfl
  have hγ : ContDiff ℝ ∞ γ := by
    dsimp only [γ]
    apply Q.contDiff.comp
    apply T.contDiff.comp
    exact (B.contDiff.comp (contDiff_id.prodMk contDiff_const)).prodMk (by fun_prop)
  have hγW : ∀ᶠ u in 𝓝 z.1, γ u ∈ W :=
    hγ.continuous.continuousAt.preimage_mem_nhds (hW.mem_nhds hzW)
  have hrawU : ∀ᶠ u in 𝓝 z.1, (u, z.2) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hzU)
  have heq : ∀ᶠ u in 𝓝 z.1, (γ u).2 = g (γ u).1 := by
    filter_upwards [hγW, hrawU] with u huW huU
    apply (hWeq.subset ⟨huW, ?_⟩).2
    refine ⟨T (e (β (u, z.2))), ⟨β (u, z.2), rfl⟩, ?_⟩
    dsimp only [γ]
    rw [hgraph (u, z.2) huU]
  have htime : (fun u => (γ u).2) =
      (fun u => ψ (c + (1 - u ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) := by
    funext u
    dsimp only [γ]
    rw [hQheight, hTheight]
  have hdu : HasDerivAt (fun u : ℝ => c + (1 - u ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
      (-z.1 * (z.2 ^ 2 + 2 * s)) z.1 := by
    convert (((((hasDerivAt_id z.1).pow 2).const_sub 1).mul_const
      (z.2 ^ 2 + 2 * s)).div_const 2).const_add c using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hderiv := (ψ.contDiff.differentiable (by simp) _).hasDerivAt.comp z.1 hdu
  have hneg : z.1 ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), sub_zero, one_mul] at hzlevel
    nlinarith [sq_nonneg z.2]
  have hv : deriv (fun u => (γ u).2) z.1 ≠ 0 := by
    rw [htime]
    exact hderiv.deriv ▸ mul_ne_zero (hψ _).ne' (mul_ne_zero (neg_ne_zero.mpr hneg) (by positivity))
  intro hzero
  have hgd := hg.differentiableOn (by simp) _ (hWO hzW) |>.differentiableAt (hO.mem_nhds (hWO hzW))
  have hd := hgd.hasFDerivAt.comp_hasDerivAt z.1
    (hγ.differentiable (by simp) z.1).fst.hasDerivAt
  rw [hzero, zero_apply] at hd
  exact hv ((hd.congr_of_eventuallyEq heq).deriv)

private theorem fderiv_ne_zero_on_reference_wall_graph
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (hQheight : ∀ q, (Q q).2 = ψ q.2) (hψ : ∀ t, 0 < deriv ψ t)
    {S : Set (F × ℝ)} {C : Set F} {a d : ℝ} (hwall : C ×ˢ Ioo a d ⊆ S)
    {O : Set F} (hO : IsOpen O) {g : F → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (F × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    (hWeq : W ∩ Q '' S = W ∩ {p | p.2 = g p.1})
    {y : F} (hy : y ∈ C) {t : ℝ} (ht : t ∈ Ioo a d) (hyt : Q (y, t) ∈ W) :
    fderiv ℝ g (Q (y, t)).1 ≠ 0 := by
  let γ : ℝ → F × ℝ := fun u => Q (y, u)
  have hγ : ContDiff ℝ ∞ γ := Q.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hγW : ∀ᶠ u in 𝓝 t, γ u ∈ W :=
    hγ.continuous.continuousAt.preimage_mem_nhds (hW.mem_nhds hyt)
  have heq : ∀ᶠ u in 𝓝 t, (γ u).2 = g (γ u).1 := by
    filter_upwards [hγW, isOpen_Ioo.mem_nhds ht] with u huW hu
    exact (hWeq.subset ⟨huW, mem_image_of_mem Q (hwall ⟨hy, hu⟩)⟩).2
  have htime : (fun u => (γ u).2) = ψ := by funext u; exact hQheight (y, u)
  intro hzero
  have hgd := hg.differentiableOn (by simp) _ (hWO hyt) |>.differentiableAt (hO.mem_nhds (hWO hyt))
  have hd := hgd.hasFDerivAt.comp_hasDerivAt t (hγ.differentiable (by simp) t).fst.hasDerivAt
  rw [hzero, zero_apply] at hd
  have hv := (hd.congr_of_eventuallyEq heq).deriv
  rw [htime] at hv
  exact (hψ t).ne' hv


theorem fderiv_ne_zero_on_saddle_cutoff_bottom_boundary
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : M → F × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c s h ε d τ j σ v₀ : ℝ}
    (hs : 0 < s) (hh : 0 ≤ h) (hε : 0 < ε) (hd : 0 ≤ d) (haj : -ε / 2 ≤ j)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hTheight : ∀ q, (T q).2 = q.2) (hQheight : ∀ q, (Q q).2 = ψ q.2)
    (hψ : ∀ t, 0 < deriv ψ t)
    {Cref : Set F}
    (hwall : (Cref \ B '' (Morse.saddleBandLevelCurve s τ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
      Icc (c + s - ε) (c + s + d) ⊆ range (T ∘ e))
    {O : Set F} (hO : IsOpen O) {g : F → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (F × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    (hWeq : W ∩ Q '' range (T ∘ e) = W ∩ {p | p.2 = g p.1})
    (Ucap : Set (F × ℝ)) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let C := Cref \ B '' (Morse.saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc (-ε / 2) j
    let K := ((fun p : F × ℝ => (p.1, c + s + p.2)) '' S) ∪ Ucap
    let P := fun z : ℝ × ℝ => (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
    let Bottom := P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
      (fun y => (Q (y, c + s + (-ε / 2))).1) '' C
    R ⊆ U → Q '' K ⊆ W →
    ∀ x ∈ Bottom, g x = ψ (c + s + (-ε / 2)) ∧ fderiv ℝ g x ≠ 0 := by
  intro R J C S K P Bottom hRU hKW
  have hCsub : C ⊆ Cref \ B '' (Morse.saddleBandLevelCurve s τ σ '' Ioo (-(h / 2)) (h / 2)) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
    exact hy.2 ⟨_, ⟨u, ⟨by linarith only [hu.1, hh], by linarith only [hu.2, hh]⟩, rfl⟩, heq⟩
  have hwallOpen : C ×ˢ Ioo (c + s - ε) (c + s + d) ⊆ range (T ∘ e) :=
    fun _ hz => hwall ⟨hCsub hz.1, hz.2.1.le, hz.2.2.le⟩
  have hbottomtime : c + s + (-ε / 2) ∈ Ioo (c + s - ε) (c + s + d) := by
    constructor <;> linarith only [hε, hd]
  rintro x (⟨z, ⟨hz, hza⟩, rfl⟩ | ⟨y, hy, rfl⟩)
  · have hpK : T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∈ K := by
      refine Or.inl ⟨(B (J z).1, (J z).2), Or.inl ⟨J z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      apply Prod.ext
      · exact B.apply_symm_apply _
      · rw [hTheight]
        dsimp only [J]
        ring
    have hpW := hKW (mem_image_of_mem Q hpK)
    have hprange : T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∈ range (T ∘ e) := by
      refine ⟨β z, ?_⟩
      change T (e (β z)) = _
      rw [hgraph z (hRU hz)]
    constructor
    · have heq := (hWeq.subset ⟨hpW, mem_image_of_mem Q hprange⟩).2
      change _ = g (P z) at heq
      rw [hQheight, hTheight] at heq
      rw [← heq]
      congr 1
      linarith only [hza]
    · exact fderiv_ne_zero_on_negative_saddle_source_graph e B T Q ψ hU hs hgraph
        hTheight hQheight hψ hO hg hW hWO hWeq (hRU hz) hpW (by linarith only [hza, hε])
  · have hpK : (y, c + s + (-ε / 2)) ∈ K :=
      Or.inl ⟨(y, -ε / 2), Or.inr ⟨hy, le_rfl, haj⟩, rfl⟩
    have hpW := hKW (mem_image_of_mem Q hpK)
    constructor
    · have heq := (hWeq.subset ⟨hpW, mem_image_of_mem Q (hwallOpen ⟨hy, hbottomtime⟩)⟩).2
      change (Q (y, c + s + (-ε / 2))).2 = g (Q (y, c + s + (-ε / 2))).1 at heq
      rw [hQheight] at heq
      exact heq.symm
    · exact fderiv_ne_zero_on_reference_wall_graph Q ψ hQheight hψ hwallOpen
        hO hg hW hWO hWeq hy hbottomtime hpW

end DifferentialGeometry.Topology.SphereSeparation
