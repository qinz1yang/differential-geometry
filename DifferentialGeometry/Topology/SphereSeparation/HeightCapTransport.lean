import DifferentialGeometry.Topology.SphereSeparation.HeightCap
import DifferentialGeometry.Topology.SphereSeparation.HeightStraightening
import DifferentialGeometry.Topology.Diffeomorph.Translation
import DifferentialGeometry.Topology.Morse.RegularLevel.QuadraticFamily

open Set Metric Manifold
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_height_transport_radial_at_extrema {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {p q : SphereTwo}
    (hp : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hq : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) q)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2)
    (hmax : ∀ x, x ≠ q → e x 2 < e q 2) (hpq : p ≠ q)
    (hcrit : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p ∨ x = q) :
    ∃ r : ℝ, 0 < r ∧ e p 2 + r ^ 2 / 2 < e q 2 - r ^ 2 / 2 ∧
      ∃ χ₀ χ₁ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ A₀ A₁ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          χ₀.source = ball 0 (2 * r) ∧ χ₁.source = ball 0 (2 * r) ∧
          χ₀ 0 = p ∧ χ₁ 0 = q ∧
          (∀ z, A₀ z 2 = z 2) ∧ (∀ z, A₁ z 2 = z 2) ∧
          (∀ y ∈ χ₀.source,
            e (χ₀ y) 2 = e p 2 + 1 / 2 * ‖y‖ ^ 2 ∧
            A₀ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) = e (χ₀ y)) ∧
          (∀ y ∈ χ₁.source,
            e (χ₁ y) 2 = e q 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
            A₁ ((EuclideanSpace.equivProdLast 2).symm (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ₁ y)) ∧
          χ₀ '' closedBall 0 r = {x | e x 2 ≤ e p 2 + r ^ 2 / 2} ∧
          χ₁ '' closedBall 0 r = {x | e q 2 - r ^ 2 / 2 ≤ e x 2} ∧
          χ₀ '' sphere 0 r = {x | e x 2 = e p 2 + r ^ 2 / 2} ∧
          χ₁ '' sphere 0 r = {x | e x 2 = e q 2 - r ^ 2 / 2} ∧
          ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo, ∃ ε : ℝ, 0 < ε ∧
            ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun z : ℝ × SphereTwo => Φ z.1 z.2) ∧
            ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun z : ℝ × SphereTwo => (Φ z.1).symm z.2) ∧
            Φ (e p 2 + r ^ 2 / 2) = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
            (∀ t ∈ Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2),
              Φ t '' {x | e x 2 = e p 2 + r ^ 2 / 2} = {x | e x 2 = t}) ∧
            (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) r, ∀ s t : ℝ,
              s - t ∈ Ioo (-ε) ε →
              Φ t ((Φ s).symm (χ₀ x)) = χ₀ (quadraticRadialCurve (-1) x (s - t))) ∧
            (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) r, ∀ s t : ℝ,
              s - t ∈ Ioo (-ε) ε →
              Φ t ((Φ s).symm (χ₁ x)) = χ₁ (quadraticRadialCurve 1 x (s - t))) := by
  have hgap : 0 < e q 2 - e p 2 := sub_pos.mpr (hmin q hpq.symm)
  obtain ⟨R₀, hR₀, κ₀, A₀, hR₀s, hκ₀0, hA₀, hn₀, hl₀⟩ :=
    exists_global_height_preserving_minimum_cap he hp hmin
  obtain ⟨R₁, hR₁, κ₁, A₁, hR₁s, hκ₁0, hA₁, hn₁, hl₁⟩ :=
    exists_global_height_preserving_maximum_cap he hq hmax
  let r := min (R₀ / 4) (min (R₁ / 4) (Real.sqrt (e q 2 - e p 2) / 4))
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hr₀ : 2 * r < R₀ := by
    have h : r ≤ R₀ / 4 := min_le_left _ _
    linarith
  have hr₁ : 2 * r < R₁ := by
    have h : r ≤ R₁ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hrsqrt : r ≤ Real.sqrt (e q 2 - e p 2) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hrgap : 4 * r ^ 2 < e q 2 - e p 2 := by
    have hs := Real.sq_sqrt hgap.le
    have hspos := Real.sqrt_pos.mpr hgap
    nlinarith [sq_nonneg (Real.sqrt (e q 2 - e p 2) - 4 * r)]
  have hab : e p 2 + r ^ 2 / 2 < e q 2 - r ^ 2 / 2 := by nlinarith [sq_nonneg r]
  let χ₀ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict κ₀
    (ball 0 (2 * r)) isOpen_ball
  let χ₁ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict κ₁
    (ball 0 (2 * r)) isOpen_ball
  have hs₀ : χ₀.source = ball 0 (2 * r) :=
    inter_eq_right.mpr
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hr₀.le)).trans hR₀s)
  have hs₁ : χ₁.source = ball 0 (2 * r) :=
    inter_eq_right.mpr
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hr₁.le)).trans hR₁s)
  have hnormal₀ (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ χ₀.source) :
      e (χ₀ y) 2 = e p 2 + 1 / 2 * ‖y‖ ^ 2 ∧
      A₀ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) = e (χ₀ y) :=
    hn₀ y hy.1
  have hnormal₁ (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ χ₁.source) :
      e (χ₁ y) 2 = e q 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
      A₁ ((EuclideanSpace.equivProdLast 2).symm (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ₁ y) :=
    hn₁ y hy.1
  have hdis : Disjoint (χ₀ '' (χ₀.source \ {0})) (χ₁ '' (χ₁.source \ {0})) := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have hybound : ‖y‖ < 2 * r := by simpa only [hs₀, mem_ball, dist_zero_right] using hy.1
    have hzbound : ‖z‖ < 2 * r := by simpa only [hs₁, mem_ball, dist_zero_right] using hz.1
    have hyform := (hnormal₀ y hy.1).1
    have hzform := (hnormal₁ z hz.1).1
    rw [heq] at hzform
    have hy2 := (sq_lt_sq₀ (norm_nonneg y) (by positivity : 0 ≤ 2 * r)).mpr hybound
    have hz2 := (sq_lt_sq₀ (norm_nonneg z) (by positivity : 0 ≤ 2 * r)).mpr hzbound
    nlinarith
  let χ : Bool → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞ :=
    fun i => if i then χ₁ else χ₀
  let c : Bool → ℝ := fun i => if i then e q 2 else e p 2
  let α : Bool → ℝ := fun i => if i then -1 else 1
  have hα (i : Bool) : α i ≠ 0 := by cases i <;> norm_num [α]
  have hnormal (i : Bool) (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ (χ i).source) :
      e (χ i y) 2 = c i + α i / 2 * ‖y‖ ^ 2 := by
    cases i
    · exact (hnormal₀ y hy).1
    · exact (hnormal₁ y hy).1
  have hCχ (i : Bool) : sphere (0 : EuclideanSpace ℝ (Fin 2)) r ⊆ (χ i).source \ {0} := by
    intro x hx
    have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
    have hball : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (2 * r) := by
      rw [mem_ball, dist_zero_right, hxn]
      linarith
    refine ⟨?_, ?_⟩
    · cases i
      · exact hs₀.symm ▸ hball
      · exact hs₁.symm ▸ hball
    · intro hx0
      have hzero : x = 0 := hx0
      rw [hzero, norm_zero] at hxn
      linarith
  have hpair : Pairwise (fun i j => Disjoint
      (χ i '' ((χ i).source \ {0})) (χ j '' ((χ j).source \ {0}))) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hregular (x : SphereTwo)
      (hx : e x 2 ∈ Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2)) :
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x := by
    intro hxcrit
    rcases hcrit x hxcrit with rfl | rfl <;> nlinarith [sq_pos_of_pos hr, hx.1, hx.2]
  obtain ⟨Φ, ε, hε, hΦ, hΦinv, hΦa, hlevels, hradial⟩ :=
    exists_diffeomorph_family_level_transport_radial_on_disjoint_charts χ hf hα hnormal
      (isClosed_Icc.preimage hf.continuous).isCompact hregular
      (C := fun _ => sphere 0 r) (fun _ => isCompact_sphere 0 r) hCχ hpair
  refine ⟨r, hr, hab, χ₀, χ₁, A₀, A₁, hs₀, hs₁, hκ₀0, hκ₁0, hA₀, hA₁,
    hnormal₀, hnormal₁, ?_, ?_, ?_, ?_, Φ, min (ε false) (ε true), lt_min (hε false) (hε true),
    hΦ, hΦinv, hΦa, fun t ht => (hlevels t ht).1, ?_, ?_⟩
  · change κ₀ '' closedBall 0 r = _
    simpa only [show (1 : ℝ) / 2 * r ^ 2 = r ^ 2 / 2 by ring] using
      (hl₀ r hr.le (by linarith)).1
  · change κ₁ '' closedBall 0 r = _
    simpa only [show e q 2 + (-1) / 2 * r ^ 2 = e q 2 - r ^ 2 / 2 by ring] using
      (hl₁ r hr.le (by linarith)).1
  · change κ₀ '' sphere 0 r = _
    simpa only [show (1 : ℝ) / 2 * r ^ 2 = r ^ 2 / 2 by ring] using
      (hl₀ r hr.le (by linarith)).2
  · change κ₁ '' sphere 0 r = _
    simpa only [show e q 2 + (-1) / 2 * r ^ 2 = e q 2 - r ^ 2 / 2 by ring] using
      (hl₁ r hr.le (by linarith)).2
  · intro x hx s t hst
    have hst' : s - t ∈ Ioo (-ε false) (ε false) :=
      ⟨(neg_le_neg (min_le_left _ _)).trans_lt hst.1, hst.2.trans_le (min_le_left _ _)⟩
    simpa only [χ, α, Bool.false_eq_true, ↓reduceIte, inv_one] using hradial false x hx s t hst'
  · intro x hx s t hst
    have hst' : s - t ∈ Ioo (-ε true) (ε true) :=
      ⟨(neg_le_neg (min_le_right _ _)).trans_lt hst.1, hst.2.trans_le (min_le_right _ _)⟩
    simpa only [χ, α, ↓reduceIte, inv_neg, inv_one, neg_neg] using hradial true x hx s t hst'

theorem exists_isotopy_height_transport_of_regular_slab
    {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {a b s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hr : ∀ x, e x 2 ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) :
    ∃ H : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
      (∀ u, H u '' range e = range e) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
        H u ((EuclideanSpace.equivProdLast 2).symm (x, s)) 2 = s + u * (t - s)) ∧
      ∃ J : Set EuclideanThree, IsCompact J ∧ J ⊆ {z | z 2 ∈ Ioo a b} ∧ ∀ u : ℝ,
        EqOn (H u) id Jᶜ ∧ EqOn (H u).symm id Jᶜ := by
  obtain ⟨D, hDh, hDs, hlevels, _⟩ :=
    exists_height_preserving_regular_slab_diffeomorph_at he ⟨hs.1.le, hs.2.le⟩ hr
      isOpen_univ (subset_univ _)
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let Φ := L.symm.toDiffeomorph.trans D
  have hΦh (z : EuclideanSpace ℝ (Fin 2) × ℝ) : Φ z 2 = z.2 :=
    (hDh _).trans (EuclideanSpace.equivProdLast_symm_last 2 _)
  have hΦs (x : EuclideanSpace ℝ (Fin 2)) : Φ (x, s) = L.symm (x, s) :=
    hDs _ (EuclideanSpace.equivProdLast_symm_last 2 _)
  let S := Φ ⁻¹' range e
  let C := (fun x => L.symm (x, s)) ⁻¹' range e
  have hprod : S ∩ (univ ×ˢ Ioo a b) = C ×ˢ Ioo a b := by
    have hiff (z : EuclideanSpace ℝ (Fin 2) × ℝ) (hz : z.2 ∈ Ioo a b) :
        z ∈ S ↔ z.1 ∈ C := by
      exact Set.ext_iff.mp (preimage_height_section_eq D.injective hDh
        (hlevels z.2 ⟨hz.1.le, hz.2.le⟩)) z.1
    ext z
    constructor
    · rintro ⟨hzS, _, hz⟩
      exact ⟨(hiff z hz).mp hzS, hz⟩
    · rintro ⟨hzC, hz⟩
      exact ⟨(hiff z hz).mpr hzC, mem_univ _, hz⟩
  obtain ⟨G, hG, hGi, hG0, hmove, _, hGS, J, hJ, hJU, hfix⟩ :=
    Diffeomorph.exists_isotopy_vertical_translation_preserving_set hK hprod
      (isOpen_univ.prod isOpen_Ioo) (subset_refl _) s t (by
        rintro z ⟨_, hz⟩
        refine ⟨mem_univ _, ?_⟩
        exact (ordConnected_Ioo.uIcc_subset hs ht) hz)
  let H := fun u => Φ.symm.trans ((G u).trans Φ)
  have hΦS : Φ '' S = range e := by
    exact Φ.surjective.image_preimage (range e)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, Φ '' J, hJ.image Φ.contMDiff.continuous, ?_, ?_⟩
  · exact Φ.contMDiff.contDiff.comp
      (hG.comp (contDiff_fst.prodMk (Φ.symm.contMDiff.contDiff.comp contDiff_snd)))
  · exact Φ.contMDiff.contDiff.comp
      (hGi.comp (contDiff_fst.prodMk (Φ.symm.contMDiff.contDiff.comp contDiff_snd)))
  · apply Diffeomorph.ext
    intro z
    change Φ (G 0 (Φ.symm z)) = z
    rw [hG0]
    exact Φ.apply_symm_apply z
  · intro u
    have hmap : H u ∘ Φ = Φ ∘ G u := by
      funext z
      change Φ (G u (Φ.symm (Φ z))) = Φ (G u z)
      rw [Φ.symm_apply_apply]
    rw [← hΦS, ← image_comp, hmap, image_comp, hGS]
  · intro u hu x hx
    have hinv : Φ.symm (L.symm (x, s)) = (x, s) := by
      rw [← hΦs, Φ.symm_apply_apply]
    change Φ (G u (Φ.symm (L.symm (x, s)))) 2 = s + u * (t - s)
    rw [hinv, hmove u hu x hx, hΦh]
  · rintro _ ⟨z, hz, rfl⟩
    change Φ z 2 ∈ Ioo a b
    rw [hΦh]
    exact (hJU hz).2
  · intro u
    constructor
    · intro z hz
      have hinv : Φ.symm z ∉ J := fun h => hz ⟨Φ.symm z, h, Φ.apply_symm_apply z⟩
      change Φ (G u (Φ.symm z)) = z
      rw [(hfix u).1 hinv]
      exact Φ.apply_symm_apply z
    · intro z hz
      have hinv : Φ.symm z ∉ J := fun h => hz ⟨Φ.symm z, h, Φ.apply_symm_apply z⟩
      change Φ ((G u).symm (Φ.symm z)) = z
      rw [(hfix u).2 hinv]
      exact Φ.apply_symm_apply z

end DifferentialGeometry.Topology.SphereSeparation
