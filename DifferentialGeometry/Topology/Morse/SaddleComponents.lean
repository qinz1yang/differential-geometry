import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.LeftInverse
import DifferentialGeometry.Topology.Connected.ComponentIn
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import Mathlib.Analysis.Convex.Topology

open Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem exists_saddle_sectors_subset_connectedComponentIn
    {M : Type*} [TopologicalSpace M] (χ : OpenPartialHomeomorph (ℝ × ℝ) M)
    (hzero : (0, 0) ∈ χ.source) {f : M → ℝ} {c : ℝ}
    (hmodel : ∀ z ∈ χ.source, f (χ z) = c + (z.2 ^ 2 - z.1 ^ 2) / 2)
    {p q : M}
    (hp : χ (0, 0) ∈ closure (connectedComponentIn {x | c < f x} p))
    (hq : χ (0, 0) ∈ closure (connectedComponentIn {x | c < f x} q))
    (hne : connectedComponentIn {x | c < f x} p ≠ connectedComponentIn {x | c < f x} q) :
    ∃ r > 0, ball (0 : ℝ × ℝ) r ⊆ χ.source ∧
      ((χ '' (ball 0 r ∩ {z | |z.1| < z.2}) ⊆ connectedComponentIn {x | c < f x} p ∧
        χ '' (ball 0 r ∩ {z | |z.1| < -z.2}) ⊆ connectedComponentIn {x | c < f x} q) ∨
      (χ '' (ball 0 r ∩ {z | |z.1| < z.2}) ⊆ connectedComponentIn {x | c < f x} q ∧
        χ '' (ball 0 r ∩ {z | |z.1| < -z.2}) ⊆ connectedComponentIn {x | c < f x} p)) := by
  obtain ⟨r, hr, hrχ⟩ := Metric.isOpen_iff.mp χ.open_source (0, 0) hzero
  have hcone (σ : ℝ) : Convex ℝ {z : ℝ × ℝ | |z.1| < σ * z.2} := by
    have h₁ : Convex ℝ {z : ℝ × ℝ | z.1 - σ * z.2 < 0} :=
      convex_halfSpace_lt ⟨fun _ _ => by simp; ring, fun _ _ => by simp; ring⟩ 0
    have h₂ : Convex ℝ {z : ℝ × ℝ | -z.1 - σ * z.2 < 0} :=
      convex_halfSpace_lt ⟨fun _ _ => by simp; ring, fun _ _ => by simp; ring⟩ 0
    convert h₁.inter h₂ using 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, abs_lt]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hcpos : IsPreconnected (χ '' (ball 0 r ∩ {z : ℝ × ℝ | |z.1| < z.2})) := by
    apply ((convex_ball (0 : ℝ × ℝ) r).inter (by simpa using hcone 1)).isPreconnected.image
    exact χ.continuousOn.mono (inter_subset_left.trans hrχ)
  have hcneg : IsPreconnected (χ '' (ball 0 r ∩ {z : ℝ × ℝ | |z.1| < -z.2})) := by
    apply ((convex_ball (0 : ℝ × ℝ) r).inter (by simpa using hcone (-1))).isPreconnected.image
    exact χ.continuousOn.mono (inter_subset_left.trans hrχ)
  have hN : χ '' ball (0 : ℝ × ℝ) r ∈ 𝓝 (χ (0, 0)) :=
    ((χ.isOpen_image_iff_of_subset_source hrχ).mpr isOpen_ball).mem_nhds
      (mem_image_of_mem χ (mem_ball_self hr))
  have hsplit (z : ℝ × ℝ) : z.1 ^ 2 < z.2 ^ 2 ↔ |z.1| < z.2 ∨ |z.1| < -z.2 := by
    rw [← sq_abs z.1, ← sq_abs z.2, sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)]
    exact lt_abs
  have hcover : (χ '' ball (0 : ℝ × ℝ) r) ∩ {x | c < f x} =
      χ '' (ball 0 r ∩ {z | |z.1| < z.2}) ∪ χ '' (ball 0 r ∩ {z | |z.1| < -z.2}) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxf⟩
      rw [mem_ofPred_eq, hmodel z (hrχ hz)] at hxf
      have hsq : z.1 ^ 2 < z.2 ^ 2 := by linarith
      rcases (hsplit z).mp hsq with hpos | hneg
      · exact Or.inl ⟨z, ⟨hz, hpos⟩, rfl⟩
      · exact Or.inr ⟨z, ⟨hz, hneg⟩, rfl⟩
    · rintro (⟨z, ⟨hz, hsign⟩, rfl⟩ | ⟨z, ⟨hz, hsign⟩, rfl⟩)
      · refine ⟨⟨z, hz, rfl⟩, ?_⟩
        rw [mem_ofPred_eq, hmodel z (hrχ hz)]
        have hsq := (hsplit z).mpr (Or.inl hsign)
        linarith
      · refine ⟨⟨z, hz, rfl⟩, ?_⟩
        rw [mem_ofPred_eq, hmodel z (hrχ hz)]
        have hsq := (hsplit z).mpr (Or.inr hsign)
        linarith
  exact ⟨r, hr, hrχ,
    hcpos.subset_connectedComponentIn_pair_of_mem_closure hcneg hN hcover hp hq hne⟩

theorem exists_saddle_band_sectors_subset_connectedComponentIn
    {M : Type*} [TopologicalSpace M] (χ : OpenPartialHomeomorph (ℝ × ℝ) M)
    (hzero : (0, 0) ∈ χ.source) {f : M → ℝ} {c s : ℝ} (hs : 0 < s)
    (hmodel : ∀ z ∈ χ.source, f (χ z) = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {p q : M}
    (hp : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} p))
    (hq : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} q))
    (hne : connectedComponentIn {x | c + s < f x} p ≠ connectedComponentIn {x | c + s < f x} q) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (0, 0) ∈ V ∧ V ⊆ χ.source ∧
      ((χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ 0 < z.2} ⊆ connectedComponentIn {x | c + s < f x} p ∧
        χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ z.2 < 0} ⊆ connectedComponentIn {x | c + s < f x} q) ∨
      (χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ 0 < z.2} ⊆ connectedComponentIn {x | c + s < f x} q ∧
        χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ z.2 < 0} ⊆
          connectedComponentIn {x | c + s < f x} p)) := by
  let F : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := (saddleBandChart hs).trans
    (((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toDiffeomorph)
  have hF (z : ℝ × ℝ) : F z = (Real.sqrt (z.2 ^ 2 + 2 * s) * z.1, z.2) := by
    rfl
  have hFzero : F (0, 0) = (0, 0) := by simp only [hF, mul_zero]
  have hFsymmzero : F.symm (0, 0) = (0, 0) := by
    apply F.injective
    change F (F.symm (0, 0)) = F (0, 0)
    rw [F.apply_symm_apply, hFzero]
  let ψ := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans χ
  have hψ (w : ℝ × ℝ) : ψ w = χ (F.symm w) := rfl
  have hψsource : ψ.source = F.symm ⁻¹' χ.source := by
    simp only [ψ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Homeomorph.toOpenPartialHomeomorph_apply, univ_inter]
    rfl
  have hψzero : ψ (0, 0) = χ (0, 0) := by rw [hψ, hFsymmzero]
  have hmodelF (z : ℝ × ℝ) (hz : z ∈ χ.source) :
      f (χ z) = c + s + ((F z).2 ^ 2 - (F z).1 ^ 2) / 2 := by
    rw [hmodel z hz, hF, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hmodelψ (w : ℝ × ℝ) (hw : w ∈ ψ.source) :
      f (ψ w) = c + s + (w.2 ^ 2 - w.1 ^ 2) / 2 := by
    rw [hψ, hmodelF (F.symm w) (by simpa only [hψsource, mem_preimage] using hw),
      F.apply_symm_apply]
  obtain ⟨r, hr, hrψ, hparts⟩ := exists_saddle_sectors_subset_connectedComponentIn ψ
    (by rw [hψsource]; change F.symm (0, 0) ∈ χ.source; rw [hFsymmzero]; exact hzero) hmodelψ
    (hψzero.symm ▸ hp) (hψzero.symm ▸ hq) hne
  let V := F ⁻¹' ball (0 : ℝ × ℝ) r
  have hV : IsOpen V := isOpen_ball.preimage F.continuous
  have hVzero : (0, 0) ∈ V := by change F (0, 0) ∈ ball 0 r; rw [hFzero]; exact mem_ball_self hr
  have hVχ : V ⊆ χ.source := by
    intro z hz
    have hm := hrψ hz
    rw [hψsource] at hm
    simpa only [mem_preimage, F.symm_apply_apply] using hm
  have hpos : χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ 0 < z.2} ⊆
      ψ '' (ball 0 r ∩ {w | |w.1| < w.2}) := by
    rintro x ⟨z, ⟨hz, hzf, hzpos⟩, rfl⟩
    have hsq : (F z).1 ^ 2 < (F z).2 ^ 2 := by rw [hmodelF z (hVχ hz)] at hzf; linarith
    have hpos : 0 < (F z).2 := by simpa only [hF] using hzpos
    refine ⟨F z, ⟨hz, ?_⟩, ?_⟩
    · change |(F z).1| < (F z).2
      rw [← sq_lt_sq₀ (abs_nonneg _) hpos.le, sq_abs]
      exact hsq
    · rw [hψ, F.symm_apply_apply]
  have hneg : χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ z.2 < 0} ⊆
      ψ '' (ball 0 r ∩ {w | |w.1| < -w.2}) := by
    rintro x ⟨z, ⟨hz, hzf, hzneg⟩, rfl⟩
    have hsq : (F z).1 ^ 2 < (F z).2 ^ 2 := by rw [hmodelF z (hVχ hz)] at hzf; linarith
    have hneg : 0 < -(F z).2 := by simpa only [hF, neg_pos] using hzneg
    refine ⟨F z, ⟨hz, ?_⟩, ?_⟩
    · change |(F z).1| < -(F z).2
      rw [← sq_lt_sq₀ (abs_nonneg _) hneg.le, sq_abs, neg_sq]
      exact hsq
    · rw [hψ, F.symm_apply_apply]
  refine ⟨V, hV, hVzero, hVχ, ?_⟩
  rcases hparts with hparts | hparts
  · exact Or.inl ⟨hpos.trans hparts.1, hneg.trans hparts.2⟩
  · exact Or.inr ⟨hpos.trans hparts.1, hneg.trans hparts.2⟩

theorem exists_saddleBandLevelCurve_subset_connectedComponentIn
    {M : Type*} [TopologicalSpace M] (χ : OpenPartialHomeomorph (ℝ × ℝ) M)
    (hzero : (0, 0) ∈ χ.source) {f : M → ℝ} {c s : ℝ} (hs : 0 < s)
    (hmodel : ∀ z ∈ χ.source, f (χ z) = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {p q : M}
    (hp : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} p))
    (hq : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} q))
    (hne : connectedComponentIn {x | c + s < f x} p ≠ connectedComponentIn {x | c + s < f x} q) :
    ∃ δ k : ℝ, 0 < δ ∧ 0 < k ∧ k < 1 ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ t ∈ Ioo (0 : ℝ) δ,
        saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ χ.source ∧
        saddleBandLevelCurve s t (-σ) '' Icc (-k) k ⊆ χ.source ∧
        χ '' (saddleBandLevelCurve s t σ '' Icc (-k) k) ⊆ connectedComponentIn {x | c + s < f x} p ∧
        χ '' (saddleBandLevelCurve s t (-σ) '' Icc (-k) k) ⊆
          connectedComponentIn {x | c + s < f x} q := by
  obtain ⟨V, hV, hVzero, hVχ, hparts⟩ :=
    exists_saddle_band_sectors_subset_connectedComponentIn χ hzero hs hmodel hp hq hne
  obtain ⟨δ, k, hδ, hk, hkone, hsmall⟩ := exists_saddleBandLevelCurve_subset_open s hV hVzero
  have hcoord {t σ u : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ)
      (hσ : σ ∈ ({-1, 1} : Set ℝ)) (hu : u ∈ Icc (-k) k) :
      saddleBandLevelCurve s t σ u ∈ V ∧ c + s < f (χ (saddleBandLevelCurve s t σ u)) ∧
        0 < σ * (saddleBandLevelCurve s t σ u).2 := by
    have huone : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans_lt hkone⟩
    have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσne : σ ≠ 0 := by intro h; rw [h] at hσsq; norm_num at hσsq
    have hzV := hsmall t ⟨ht.1.le, ht.2.le⟩ σ hσ ⟨u, hu, rfl⟩
    have hheight := saddleBandLevelCurve_height hs.le ht.1 hσsq huone c
    have hregular := saddleBandLevelCurve_regular hs.le ht.1 hσne huone
    have hnonneg : 0 ≤ σ * (saddleBandLevelCurve s t σ u).2 := by
      simp only [saddleBandLevelCurve, ← mul_assoc, ← pow_two, hσsq, one_mul]
      exact Real.sqrt_nonneg _
    refine ⟨hzV, ?_, ?_⟩
    · rw [hmodel _ (hVχ hzV), hheight]
      exact lt_add_of_pos_right (c + s) ht.1
    · exact lt_of_le_of_ne hnonneg (mul_ne_zero hσne (mul_ne_zero_iff.mp hregular).2).symm
  have hsub {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ) (σ : ℝ) (hσ : σ ∈ ({-1, 1} : Set ℝ)) :
      saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ χ.source := by
    rintro z ⟨u, hu, rfl⟩
    exact hVχ (hcoord ht hσ hu).1
  have hpos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ) :
      χ '' (saddleBandLevelCurve s t 1 '' Icc (-k) k) ⊆
        χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ 0 < z.2} := by
    apply image_mono
    rintro z ⟨u, hu, rfl⟩
    simpa only [mem_ofPred_eq, one_mul] using hcoord ht (by simp : (1 : ℝ) ∈ ({-1, 1} : Set ℝ)) hu
  have hneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ) :
      χ '' (saddleBandLevelCurve s t (-1) '' Icc (-k) k) ⊆
        χ '' {z | z ∈ V ∧ c + s < f (χ z) ∧ z.2 < 0} := by
    apply image_mono
    rintro z ⟨u, hu, rfl⟩
    simpa only [mem_ofPred_eq, neg_one_mul, neg_pos] using
      hcoord ht (by simp : (-1 : ℝ) ∈ ({-1, 1} : Set ℝ)) hu
  refine ⟨δ, k, hδ, hk, hkone, ?_⟩
  rcases hparts with hparts | hparts
  · refine ⟨1, by simp, ?_⟩
    intro t ht
    exact ⟨hsub ht 1 (by simp), hsub ht (-1) (by simp),
      (hpos ht).trans hparts.1, (hneg ht).trans hparts.2⟩
  · refine ⟨-1, by simp, ?_⟩
    intro t ht
    simpa only [neg_neg] using And.intro (hsub ht (-1) (by simp))
      ⟨hsub ht 1 (by simp), (hneg ht).trans hparts.2, (hpos ht).trans hparts.1⟩

theorem exists_saddleBandLevelCurve_subset_closure_connectedComponentIn
    {M : Type*} [TopologicalSpace M] (χ : OpenPartialHomeomorph (ℝ × ℝ) M)
    (hzero : (0, 0) ∈ χ.source) {f : M → ℝ} {c s b : ℝ} (hs : 0 < s) (hb : c + s < b)
    (hmodel : ∀ z ∈ χ.source, f (χ z) = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {p q : M}
    (hp : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} p))
    (hq : χ (0, 0) ∈ closure (connectedComponentIn {x | c + s < f x} q))
    (hne : connectedComponentIn {x | c + s < f x} p ≠ connectedComponentIn {x | c + s < f x} q)
    (hcover : ∀ a ∈ Ioo (c + s) b, {x | a < f x} =
      connectedComponentIn {x | a < f x} p ∪ connectedComponentIn {x | a < f x} q) :
    ∃ δ k : ℝ, 0 < δ ∧ c + s + δ ≤ b ∧ 0 < k ∧ k < 1 ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ t ∈ Ioo (0 : ℝ) δ,
        saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ χ.source ∧
        saddleBandLevelCurve s t (-σ) '' Icc (-k) k ⊆ χ.source ∧
        χ '' (saddleBandLevelCurve s t σ '' Icc (-k) k) ⊆
          closure (connectedComponentIn {x | c + s + t < f x} p) ∧
        χ '' (saddleBandLevelCurve s t (-σ) '' Icc (-k) k) ⊆
          closure (connectedComponentIn {x | c + s + t < f x} q) := by
  obtain ⟨δ₀, k, hδ₀, hk, hkone, σ, hσ, hcurves⟩ :=
    exists_saddleBandLevelCurve_subset_connectedComponentIn χ hzero hs hmodel hp hq hne
  let δ := min δ₀ (b - (c + s))
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr hb)
  have hδbound : c + s + δ ≤ b := by dsimp [δ]; linarith [min_le_right δ₀ (b - (c + s))]
  have ht₀ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ) : t ∈ Ioo (0 : ℝ) δ₀ :=
    ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hlimit (ε : ℝ) (hε : ε ^ 2 = 1) {p' q' : M}
      (hne' : connectedComponentIn {x | c + s < f x} p' ≠ connectedComponentIn {x | c + s < f x} q')
      (htrack : ∀ v ∈ Ioo (0 : ℝ) δ₀,
        saddleBandLevelCurve s v ε '' Icc (-k) k ⊆ χ.source ∧
        χ '' (saddleBandLevelCurve s v ε '' Icc (-k) k) ⊆ connectedComponentIn {x | c + s < f x} p')
      {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) δ)
      (hcover' : {x | c + s + t < f x} = connectedComponentIn {x | c + s + t < f x} p' ∪
        connectedComponentIn {x | c + s + t < f x} q') :
      χ '' (saddleBandLevelCurve s t ε '' Icc (-k) k) ⊆
        closure (connectedComponentIn {x | c + s + t < f x} p') := by
    rintro x ⟨z, ⟨u, hu, rfl⟩, rfl⟩
    have huone : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans_lt hkone⟩
    have hcurve : Continuous (fun v => saddleBandLevelCurve s v ε u) := by
      unfold saddleBandLevelCurve
      fun_prop
    have hc : ContinuousAt (fun v => χ (saddleBandLevelCurve s v ε u)) t :=
      (χ.continuousAt ((htrack t (ht₀ ht)).1 ⟨u, hu, rfl⟩)).comp
        (f := fun v => saddleBandLevelCurve s v ε u) (x := t) hcurve.continuousAt
    apply hc.continuousWithinAt.mem_closure (s := Ioo t δ)
      (by rw [closure_Ioo ht.2.ne]; exact ⟨le_rfl, ht.2.le⟩)
    intro v hv
    have hv₀ : v ∈ Ioo (0 : ℝ) δ₀ := ht₀ ⟨ht.1.trans hv.1, hv.2⟩
    have hvχ := (htrack v hv₀).1 ⟨u, hu, rfl⟩
    have hvcomp := (htrack v hv₀).2 ⟨saddleBandLevelCurve s v ε u, ⟨u, hu, rfl⟩, rfl⟩
    have hvf : c + s + t < f (χ (saddleBandLevelCurve s v ε u)) := by
      rw [hmodel _ hvχ, saddleBandLevelCurve_height hs.le hv₀.1 hε huone c]
      linarith [hv.1]
    rcases hcover'.subset hvf with hleft | hright
    · exact hleft
    · have hright' : χ (saddleBandLevelCurve s v ε u) ∈ connectedComponentIn {x | c + s < f x} q' :=
        connectedComponentIn_mono q'
          (fun y hy => lt_trans (lt_add_of_pos_right (c + s) ht.1) hy) hright
      exact False.elim
        (hne' ((connectedComponentIn_eq hvcomp).trans (connectedComponentIn_eq hright').symm))
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨δ, k, hδ, hδbound, hk, hkone, σ, hσ, ?_⟩
  intro t ht
  have hcovert := hcover (c + s + t) ⟨lt_add_of_pos_right (c + s) ht.1, by linarith [ht.2]⟩
  refine ⟨(hcurves t (ht₀ ht)).1, (hcurves t (ht₀ ht)).2.1, ?_, ?_⟩
  · exact hlimit σ hσsq hne (fun v hv => ⟨(hcurves v hv).1, (hcurves v hv).2.2.1⟩) ht hcovert
  · apply hlimit (-σ) (by simpa only [neg_sq] using hσsq) (Ne.symm hne)
      (fun v hv => ⟨(hcurves v hv).2.1, (hcurves v hv).2.2.2⟩) ht
    exact hcovert.trans (union_comm _ _)

theorem exists_saddleBandLevelCurve_subset_closure_connectedComponentIn_of_graph
    {E P H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    (hdim : Module.finrank ℝ E = 2) (e : M → P × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] P)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    (hefst : ∀ z ∈ U, ContMDiffAt I 𝓘(ℝ, P) ∞ (fun x => (e x).1) (β z))
    {c s b : ℝ} (hs : 0 < s) (hb : c + s < b)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {p q : M}
    (hp : β (0, 0) ∈ closure (connectedComponentIn {x | c + s < (e x).2} p))
    (hq : β (0, 0) ∈ closure (connectedComponentIn {x | c + s < (e x).2} q))
    (hne : connectedComponentIn {x | c + s < (e x).2} p ≠
      connectedComponentIn {x | c + s < (e x).2} q)
    (hcover : ∀ a ∈ Ioo (c + s) b, {x | a < (e x).2} =
      connectedComponentIn {x | a < (e x).2} p ∪ connectedComponentIn {x | a < (e x).2} q) :
    ∃ δ k : ℝ, 0 < δ ∧ c + s + δ ≤ b ∧ 0 < k ∧ k < 1 ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ t ∈ Ioo (0 : ℝ) δ,
        saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ U ∧
        saddleBandLevelCurve s t (-σ) '' Icc (-k) k ⊆ U ∧
        β '' (saddleBandLevelCurve s t σ '' Icc (-k) k) ⊆
          closure (connectedComponentIn {x | c + s + t < (e x).2} p) ∧
        β '' (saddleBandLevelCurve s t (-σ) '' Icc (-k) k) ⊆
          closure (connectedComponentIn {x | c + s + t < (e x).2} q) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  let G : M → ℝ × ℝ := fun x => B.symm (e x).1
  have hleft : LeftInvOn G β U := by
    intro z hz
    change B.symm (e (β z)).1 = z
    rw [hgraph z hz]
    exact B.symm_apply_apply z
  obtain ⟨χ, hsource, _, hχ, _⟩ := hleft.exists_partialDiffeomorph hU hβ
    (fun z hz => B.symm.contMDiff.contMDiffAt.comp (β z) (hefst z hz))
    (by simp [Module.finrank_prod, hdim])
  have hχcoe : (χ.toOpenPartialHomeomorph : (ℝ × ℝ) → M) = β := hχ
  have hχzero : (0, 0) ∈ χ.toOpenPartialHomeomorph.source := by
    change (0, 0) ∈ χ.source
    rwa [hsource]
  have hmodel (z : ℝ × ℝ) (hz : z ∈ χ.toOpenPartialHomeomorph.source) :
      (e (χ.toOpenPartialHomeomorph z)).2 = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
    have hzχ : z ∈ χ.source := hz
    rw [hsource] at hzχ
    rw [hχcoe, hgraph z hzχ]
  obtain ⟨δ, k, hδ, hδb, hk, hkone, σ, hσ, hcurves⟩ :=
    exists_saddleBandLevelCurve_subset_closure_connectedComponentIn χ.toOpenPartialHomeomorph
      hχzero hs hb hmodel (by simpa only [hχcoe] using hp)
      (by simpa only [hχcoe] using hq) hne hcover
  refine ⟨δ, k, hδ, hδb, hk, hkone, σ, hσ, ?_⟩
  intro t ht
  have h := hcurves t ht
  change _ ⊆ χ.source ∧ _ ⊆ χ.source ∧ _ ∧ _ at h
  simpa only [hsource, hχcoe] using h

end DifferentialGeometry.Topology.Morse
