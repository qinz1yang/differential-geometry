import DifferentialGeometry.Topology.SphereSeparation.HeightCapComponent
import DifferentialGeometry.Topology.SphereSeparation.HeightLevel
import DifferentialGeometry.Topology.Morse.RegularLevel.SaddleQuadraticVelocity
import DifferentialGeometry.Topology.Embedding.SaddleQuadraticIsotopy
import DifferentialGeometry.Topology.LevelSet.QuadraticGraph
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Embedding.LinearEquiv

open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_height_level_isotopy_saddle_cap_normal_form
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p : SphereTwo} (hnd : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hmax : IsLocalMax (fun x => e x 2) p)
    (B₀ : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : ℝ × ℝ → SphereTwo} {Uβ : Set (ℝ × ℝ)}
    (hUβ : IsOpen Uβ) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β Uβ)
    {c₀ s : ℝ} (hgraphβ : ∀ z ∈ Uβ,
      EuclideanSpace.equivProdLast 2 (e (β z)) =
        (B₀ z, c₀ + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {a : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKUβ : K ⊆ Uβ)
    (hKreg : ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0)
    (hKlevel : ∀ z ∈ K, c₀ + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = a)
    (ha : a < e p 2)
    (hregular : ∀ x, e x 2 ∈ Ico a (e p 2) →
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) :
    ∃ r : ℝ, 0 < r ∧ a < e p 2 - r ^ 2 / 2 ∧
      ∃ A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
        (∀ z, (A z).2 = z.2) ∧
        (∃ R τ : ℝ, r < R ∧ 0 < τ ∧ r ^ 2 / 2 < τ ∧
          ((closedBall 0 R ×ˢ closedBall (e p 2) τ) ∩
              range (fun x => A.symm (EuclideanSpace.equivProdLast 2 (e x)))) =
            (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) ''
            connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
          (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (Φ z.1).symm z.2) ∧
          Φ a = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ ∧
          (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
            Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
              {x | e x 2 = a}) =
              (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) ∧
          (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
            ((fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ∩
                ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) =
              (fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r) ∧
          (∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧ ∀ t : ℝ,
            EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
          (∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧
            ∀ t ∈ Icc (a - δ₀) (a + δ₀), ∀ z ∈ cthickening ε K,
              Φ t (B₀ z) = B₀ (saddleBandCurve z (t - a))) ∧
          ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, r < R ∧
            ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - δ) (e p 2 - r ^ 2 / 2 + δ),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm (A (x, e p 2 - r ^ 2 / 2)).1) =
                  (A (quadraticLevelScaling (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1 := by
  obtain ⟨R₀, hR₀, τ, hτ, χ, B, hsource, hχ0, hB, hnormal, hgraph, hcap⟩ :=
    exists_global_height_preserving_local_maximum_cap he hnd hmax
  let c := e p 2
  let r := min (R₀ / 4) (min (Real.sqrt τ / 2) (Real.sqrt (c - a) / 4))
  have hca : 0 < c - a := sub_pos.mpr ha
  have hr : 0 < r := lt_min (by positivity)
    (lt_min (half_pos (Real.sqrt_pos.mpr hτ)) (by positivity : 0 < Real.sqrt (c - a) / 4))
  have hrR : r ≤ R₀ / 4 := min_le_left _ _
  have hrτ : r ≤ Real.sqrt τ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ Real.sqrt (c - a) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hrτsq : r ^ 2 ≤ τ / 4 := by
    have hsq := (sq_le_sq₀ hr.le (by positivity : 0 ≤ Real.sqrt τ / 2)).mpr hrτ
    nlinarith [Real.sq_sqrt hτ.le]
  have hrasq : r ^ 2 ≤ (c - a) / 16 := by
    have hsq := (sq_le_sq₀ hr.le (by positivity : 0 ≤ Real.sqrt (c - a) / 4)).mpr hra
    nlinarith [Real.sq_sqrt hca.le]
  let b := c - r ^ 2 / 2
  have hab : a < b := by dsimp [b]; nlinarith
  have hbc : b < c := by dsimp [b]; nlinarith [sq_pos_of_pos hr]
  let δ := r ^ 2 / 32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ = r ^ 2 / 32 := rfl
  have hbcδ : b + δ < c := by dsimp [b]; nlinarith [sq_pos_of_pos hr]
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let A := L.symm.toDiffeomorph.trans (B.trans L.toDiffeomorph)
  have hA (z : EuclideanSpace ℝ (Fin 2) × ℝ) : (A z).2 = z.2 :=
    (hB (L.symm z)).trans (EuclideanSpace.equivProdLast_symm_last 2 z)
  have hn (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ χ.source) :
      L (e (χ y)) = A (y, c + (-1) / 2 * ‖y‖ ^ 2) :=
    congrArg L (hnormal y hy).2.symm
  have hAinv (x : SphereTwo) : A.symm (L (e x)) = L (B.symm (e x)) := by
    change L (B.symm (L.symm (L (e x)))) = _
    rw [L.symm_apply_apply]
  have hnormalbox : ((closedBall 0 R₀ ×ˢ closedBall c τ) ∩
      range (fun x => A.symm (L (e x)))) =
        (fun y => (y, c + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R₀ := by
    simpa only [hAinv] using hgraph
  have hrR₀ : r < R₀ := by linarith
  have hrτ₀ : r ^ 2 / 2 < τ := by linarith
  let C : Set (EuclideanSpace ℝ (Fin 2)) := closedBall 0 (2 * r) \ ball 0 (r / 2)
  have hC : IsCompact C := (isCompact_closedBall 0 (2 * r)).diff isOpen_ball
  have hCχ : C ⊆ χ.source \ {0} := by
    intro x hx
    refine ⟨hsource ((closedBall_subset_closedBall (by linarith : 2 * r ≤ R₀)) hx.1), ?_⟩
    rintro rfl
    exact hx.2 (mem_ball_self (half_pos hr))
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hstrip : IsCompact ((fun x => e x 2) ⁻¹' Icc a b) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  have hreg (x : SphereTwo) (hx : e x 2 ∈ Icc a b) :
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x :=
    hregular x ⟨hx.1, hx.2.trans_lt hbc⟩
  have hC₀ : IsCompact (β '' K) := hK.image_of_continuousOn
    (hβ.continuousOn.mono hKUβ)
  have hC₁ : IsCompact (χ '' C) := hC.image_of_continuousOn
    (χ.contMDiffOn.continuousOn.mono (fun _ hx => (hCχ hx).1))
  have hβlevel (z : ℝ × ℝ) (hz : z ∈ K) : e (β z) 2 = a :=
    (congrArg Prod.snd (hgraphβ z (hKUβ hz))).trans (hKlevel z hz)
  obtain ⟨F, hF, _, hFa, hFlevels, O₀, O₁, hO₀, hO₁, hC₀O, hC₁O,
      hO₀U, hO₁U, hv₀, hv₁⟩ :=
    exists_diffeomorph_family_level_transport_saddle_quadratic_velocity
      (e := fun x => L (e x)) (a := a) (b := b) (r := (a + c) / 2)
      (by simp) (L.contDiff.contMDiff.comp he.contMDiff)
      B₀ hUβ hβ hgraphβ χ A hA (by norm_num : (-1 : ℝ) ≠ 0) hn hstrip hreg
      hC₀ hC₁
      (by rintro x ⟨z, hz, rfl⟩; exact ⟨z, ⟨hKUβ hz, hKreg z hz⟩, rfl⟩)
      (image_mono hCχ)
      (by rintro x ⟨z, hz, rfl⟩; change e (β z) 2 < (a + c) / 2; rw [hβlevel z hz]; linarith)
      (by
        rintro x ⟨z, hz, rfl⟩
        rw [hn z (hCχ hz).1, hA]
        have hnorm := mem_closedBall_zero_iff.mp hz.1
        have hnormsq := (sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ 2 * r)).mpr hnorm
        nlinarith)
  have hra (x : SphereTwo) (hx : e x 2 = a) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0 :=
    hregular x ⟨hx.ge, hx ▸ ha⟩
  obtain ⟨Cs, Ms, hinc, _, _, _⟩ := exists_height_level_manifold he a hra
  let _ := Cs
  let _ := Ms
  let T := {x : SphereTwo // e x 2 = a}
  let : CompactSpace T := isCompact_iff_compactSpace.mp
    (isClosed_eq hf.continuous continuous_const).isCompact
  let G : ℝ × T → EuclideanSpace ℝ (Fin 2) × ℝ := fun z => L (e (F z.1 z.2.val))
  let J : ℝ × T → EuclideanSpace ℝ (Fin 2) := fun z => (G z).1
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MorseModel 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ G :=
    L.contDiff.contMDiff.comp (he.contMDiff.comp (hF.comp (contMDiff_fst.prodMk
      (hinc.contMDiff.comp contMDiff_snd))))
  have hJ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MorseModel 1)) (𝓡 2) ∞ J :=
    contDiff_fst.contMDiff.comp hG
  have hGemb (t : ℝ) : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun x => G (t, x)) := by
    have hD := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (F t).isLocalDiffeomorph (F t).injective
    exact (he.comp (hD.comp hinc (by simp)) (by simp)).continuousLinearEquiv_comp L
  have hheight (t : ℝ) (ht : t ∈ Icc a b) (x : T) : (G (t, x)).2 = t :=
    (hFlevels t ht).1.subset ⟨x.val, x.property, rfl⟩
  have hJemb (t : ℝ) (ht : t ∈ Icc a b) :
      IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) (𝓡 2) ∞ (fun x => J (t, x)) :=
    (hGemb t).fst_of_snd_eq_const (by simp) (hheight t ht)
  let U : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    {z | z.1 ∈ Ioo (b - 2 * δ) (b + 2 * δ) ∧
      (A.symm (z.2, z.1)).1 ∈ ball 0 (2 * r)}
  have hU : IsOpen U := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_ball.preimage (A.symm.contMDiff.continuous.comp
      (continuous_snd.prodMk continuous_fst)).fst)
  have hUc (z : ℝ × EuclideanSpace ℝ (Fin 2)) (hz : z ∈ U) : z.1 ≠ c := by
    have hz' := hz.1.2
    dsimp [b] at hz'
    nlinarith [sq_pos_of_pos hr]
  have hJU (t : ℝ) (ht : t ∈ Icc a b) (x : T) (hx : (t, J (t, x)) ∈ U) :
      F t x.val ∈ χ '' C := by
    let y := (A.symm (J (t, x), t)).1
    have hy : y ∈ ball 0 (2 * r) := hx.2
    have hcoord : A.symm (G (t, x)) = (y, t) := by
      have hGJ : G (t, x) = (J (t, x), t) := Prod.ext rfl (hheight t ht x)
      rw [hGJ]
      refine Prod.ext ?_ ?_
      · rfl
      change (A.symm (J (t, x), t)).2 = t
      rw [← hA (A.symm (J (t, x), t)), A.apply_symm_apply]
    have hcoord' : L (B.symm (e (F t x.val))) = (y, t) :=
      (hAinv (F t x.val)).symm.trans hcoord
    have hytarget : (y, t) ∈
        (closedBall 0 R₀ ×ˢ closedBall c τ) ∩
          range (fun x => L (B.symm (e x))) := by
      refine ⟨⟨?_, ?_⟩, ⟨F t x.val, hcoord'⟩⟩
      · exact (closedBall_subset_closedBall (by linarith : 2 * r ≤ R₀))
          (ball_subset_closedBall hy)
      · rw [mem_closedBall, Real.dist_eq, abs_le]
        have htlo := hx.1.1
        have hthi := hx.1.2
        dsimp [b] at htlo hthi
        constructor <;> nlinarith
    obtain ⟨w, hw, hwyt⟩ := hgraph.subset hytarget
    have hwy : w = y := congrArg Prod.fst hwyt
    subst w
    have hqyt : c + (-1) / 2 * ‖y‖ ^ 2 = t := congrArg Prod.snd hwyt
    have hysource : y ∈ χ.source := hsource hw
    have hχy : χ y = F t x.val := by
      apply he.isEmbedding.injective
      apply L.injective
      rw [hn y hysource, hqyt, ← hcoord]
      exact A.apply_symm_apply _
    refine ⟨y, ⟨ball_subset_closedBall hy, ?_⟩, hχy⟩
    rw [mem_ball_zero_iff]
    intro hsmall
    have hsq := (sq_lt_sq₀ (norm_nonneg y) (half_pos hr).le).mpr hsmall
    have htupper := hx.1.2
    dsimp [b] at htupper
    nlinarith
  have hvJ (t : ℝ) (ht : t ∈ Icc a b) (x : T) (hx : (t, J (t, x)) ∈ U) :
      HasDerivWithinAt (fun s => J (s, x))
        (A.quadraticFiberVectorField c (t, J (t, x))) (Icc a b) t :=
    (hv₁ t x.val (hheight t ht x) (hC₁O (hJU t ht x hx))).hasDerivWithinAt
  have hKU (t : ℝ) (ht : t ∈ Icc (b - δ) (b + δ))
      (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ closedBall 0 (3 * r / 2)) :
      (t, (A (quadraticLevelScaling b c x t, t)).1) ∈ U := by
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hpair : ((A (quadraticLevelScaling b c x t, t)).1, t) =
        A (quadraticLevelScaling b c x t, t) :=
      Prod.ext rfl (hA (quadraticLevelScaling b c x t, t)).symm
    rw [hpair, A.symm_apply_apply, mem_ball_zero_iff]
    have hpos : 0 < (t - c) / (b - c) :=
      div_pos_of_neg_of_neg (by dsimp [b] at ht; nlinarith [ht.2, sq_pos_of_pos hr])
        (sub_neg.mpr hbc)
    have hratio : (t - c) / (b - c) < 3 / 2 := by
      rw [div_lt_iff_of_neg (sub_neg.mpr hbc)]
      dsimp [b] at *
      nlinarith [ht.1, sq_pos_of_pos hr]
    have hnorm : ‖x‖ ^ 2 ≤ (3 * r / 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) (by positivity)).mpr (mem_closedBall_zero_iff.mp hx)
    have hscale := norm_sq_quadraticLevelScaling b c x hpos.le
    have hbound := mul_le_mul_of_nonneg_left hnorm hpos.le
    have hbound' := mul_lt_mul_of_pos_right hratio (sq_pos_of_pos (by positivity : 0 < 3 * r / 2))
    apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * r)).mp
    nlinarith
  have hLe : Topology.IsInducing (fun x => L (e x)) :=
    L.toHomeomorph.isEmbedding.isInducing.comp he.isEmbedding.isInducing
  obtain ⟨V₀, hV₀, hpreV₀⟩ := hLe.isOpen_iff.mp hO₀
  let U₀ : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    {z | (z.2, z.1) ∈ V₀ ∧
      (1 - (B₀.symm z.2).1 ^ 2) * (B₀.symm z.2).2 ≠ 0 ∧ z.1 < (a + c) / 2}
  have hU₀ : IsOpen U₀ :=
    (hV₀.preimage (continuous_snd.prodMk continuous_fst)).inter
      ((isOpen_ne_fun ((continuous_const.sub
        ((B₀.symm.continuous.comp continuous_snd).fst.pow 2)).mul
          (B₀.symm.continuous.comp continuous_snd).snd) continuous_const).inter
            (isOpen_Iio.preimage continuous_fst))
  have hKU₀ (z : ℝ × ℝ) (hz : z ∈ K) : (a, B₀ z) ∈ U₀ := by
    refine ⟨?_, ?_, by linarith⟩
    · have hx : β z ∈ (fun x => L (e x)) ⁻¹' V₀ :=
        hpreV₀.symm ▸ hC₀O (mem_image_of_mem _ hz)
      change L (e (β z)) ∈ V₀ at hx
      rw [hgraphβ z (hKUβ hz), hKlevel z hz] at hx
      exact hx
    · simpa only [B₀.symm_apply_apply] using hKreg z hz
  have hvJ₀ (t : ℝ) (ht : t ∈ Icc a b) (x : T) (hx : (t, J (t, x)) ∈ U₀) :
      HasDerivWithinAt (fun s => J (s, x))
        (B₀.saddleFiberVectorField (J (t, x))) (Icc a b) t := by
    apply (hv₀ t x.val ?_).hasDerivWithinAt
    rw [← hpreV₀]
    change G (t, x) ∈ V₀
    have hGJ : G (t, x) = (J (t, x), t) := Prod.ext rfl (hheight t ht x)
    rw [hGJ]
    exact hx.1
  have hdisj : Disjoint U₀ U := by
    rw [disjoint_left]
    intro z hz₀ hz₁
    have hlo := hz₁.1.1
    have hhi := hz₀.2.2
    dsimp [b] at hlo
    nlinarith
  obtain ⟨Φ, hΦ, hΦinv, hΦa, hΦJ, hΦsaddle, hΦcap, hsupport⟩ :=
    exists_contDiff_compact_ambient_isotopy_eqOn_saddle_quadratic_models hab hδ
      (by
        intro t ht
        exact div_pos_of_neg_of_neg (sub_neg.mpr (ht.2.trans_lt hbcδ)) (sub_neg.mpr hbc))
      hJ.contMDiffOn hJemb B₀ A hA hU₀ hU hdisj (fun _ hz => hz.2.1) hUc
      hvJ₀ hvJ hK hKU₀ (isCompact_closedBall 0 (3 * r / 2)) hKU
  have hrange (t : ℝ) (ht : t ∈ Icc a b) :
      range (fun x : T => J (t, x)) =
        (fun x => (L (e x)).1) '' {x | e x 2 = t} := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨F t x.val, (hFlevels t ht).1.subset ⟨x.val, x.property, rfl⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := (hFlevels t ht).1.symm.subset hx
      exact ⟨⟨y, hy⟩, congrArg (fun z => (L (e z)).1) hyx⟩
  have hlevels (t : ℝ) (ht : t ∈ Icc a b) :
      Φ t '' ((fun x => (L (e x)).1) '' {x | e x 2 = a}) =
        (fun x => (L (e x)).1) '' {x | e x 2 = t} := by
    rw [← hrange a ⟨le_rfl, hab.le⟩, ← range_comp]
    exact (congrArg range (funext (hΦJ t ht))).trans (hrange t ht)
  have hbase : ((fun y => (A (y, b)).1) '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) ∩
      ((fun x => (L (e x)).1) '' {x | e x 2 = b}) =
        (fun y => (A (y, b)).1) '' sphere 0 r := by
    have heqb : c + (-1 : ℝ) / 2 * r ^ 2 = b := by dsimp [b]; ring
    have hbτ : c + (-1 : ℝ) / 2 * r ^ 2 ∈ closedBall c τ := by
      rw [mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> nlinarith only [hrτsq, hτ, sq_nonneg r]
    have hh := Equiv.image_closedBall_inter_image_level_eq_of_quadratic_graph
      (fun x => L (e x)) A.toEquiv hA (by norm_num : (-1 : ℝ) ≠ 0)
      hr.le hrR₀.le hbτ hnormalbox
    simpa only [heqb, Diffeomorph.coe_toEquiv, L, EuclideanSpace.equivProdLast_snd,
      show (Fin.last 2 : Fin 3) = 2 by decide] using hh
  have hseparation (t : ℝ) (ht : t ∈ Icc a b) :
      ((fun y => Φ t ((Φ b).symm (A (y, b)).1)) '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) ∩
          ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
        (fun y => Φ t ((Φ b).symm (A (y, b)).1)) '' sphere 0 r := by
    let Q : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)) := (Φ b).symm.trans (Φ t)
    have hpre : (Φ b).symm '' ((fun x => (L (e x)).1) '' {x | e x 2 = b}) =
        (fun x => (L (e x)).1) '' {x | e x 2 = a} := by
      rw [← hlevels b ⟨hab.le, le_rfl⟩, image_image]
      simp only [(Φ b).symm_apply_apply, image_id']
    have hQlevel : Q '' ((fun x => (L (e x)).1) '' {x | e x 2 = b}) =
        (fun x => (L (e x)).1) '' {x | e x 2 = t} := by
      change ((Φ t) ∘ (Φ b).symm) '' _ = _
      rw [image_comp, hpre, hlevels t ht]
    have hQbase := congrArg (Q '' ·) hbase
    rw [image_inter (show Function.Injective (fun x => Q x) from Q.injective),
      hQlevel, image_image, image_image] at hQbase
    exact hQbase
  refine ⟨r, hr, hab, A, hA, ⟨R₀, τ, hrR₀, hτ, hrτ₀, hnormalbox⟩, ?_, Φ, hΦ, hΦinv, hΦa, hlevels, hseparation, hsupport, hΦsaddle,
    δ, hδ, 3 * r / 2, by linarith, hΦcap⟩
  · have hcut : c + (-1) / 2 * r ^ 2 = c - r ^ 2 / 2 := by ring
    have hcapr := (hcap r hr.le (by linarith)).1
    rw [hcut] at hcapr
    rw [← hcapr, image_image]
    apply image_congr
    intro y hy
    exact hn y (hsource ((closedBall_subset_closedBall (by linarith : r ≤ R₀)) hy))

theorem exists_height_level_isotopy_eqOn_saddle_and_local_maximum_neighborhoods
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p : SphereTwo} (hnd : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hmax : IsLocalMax (fun x => e x 2) p)
    (B₀ : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : ℝ × ℝ → SphereTwo} {Uβ : Set (ℝ × ℝ)}
    (hUβ : IsOpen Uβ) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β Uβ)
    {c₀ s : ℝ} (hgraphβ : ∀ z ∈ Uβ,
      EuclideanSpace.equivProdLast 2 (e (β z)) =
        (B₀ z, c₀ + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {a : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKUβ : K ⊆ Uβ)
    (hKreg : ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0)
    (hKlevel : ∀ z ∈ K, c₀ + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = a)
    (ha : a < e p 2)
    (hregular : ∀ x, e x 2 ∈ Ico a (e p 2) →
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) :
    ∃ r : ℝ, 0 < r ∧ a < e p 2 - r ^ 2 / 2 ∧
      ∃ A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
        (∀ z, (A z).2 = z.2) ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) ''
            connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
          (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (Φ z.1).symm z.2) ∧
          Φ a = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ ∧
          (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
            Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
              {x | e x 2 = a}) =
              (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) ∧
          (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
            ((fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ∩
                ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) =
              (fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r) ∧
          (∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧ ∀ t : ℝ,
            EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
          (∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧
            ∀ t ∈ Icc (a - δ₀) (a + δ₀), ∀ z ∈ cthickening ε K,
              Φ t (B₀ z) = B₀ (saddleBandCurve z (t - a))) ∧
          ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, r < R ∧
            ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - δ) (e p 2 - r ^ 2 / 2 + δ),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm (A (x, e p 2 - r ^ 2 / 2)).1) =
                  (A (quadraticLevelScaling (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1 := by
  obtain ⟨r, hr, hab, A, hA, _, hcap, Φ, hΦ, hΦinv, hΦa, hlevels, hseparation,
      hsupport, hsaddle, hmodel⟩ :=
    exists_height_level_isotopy_saddle_cap_normal_form he hnd hmax B₀ hUβ hβ hgraphβ
      hK hKUβ hKreg hKlevel ha hregular
  exact ⟨r, hr, hab, A, hA, hcap, Φ, hΦ, hΦinv, hΦa, hlevels, hseparation,
    hsupport, hsaddle, hmodel⟩

end DifferentialGeometry.Topology.SphereSeparation
