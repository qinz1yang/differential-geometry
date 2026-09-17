import DifferentialGeometry.Topology.Embedding.CylinderCap
import DifferentialGeometry.Topology.Diffeomorph.Translation
import Mathlib.Topology.Order.IntermediateValue

open Set Metric
open scoped ContDiff Manifold

namespace Diffeomorph

private theorem image_union_inter_zero_of_vertical_motion
    {E : Type*} [NormedAddCommGroup E]
    {A K : Set (E × ℝ)} {R ε d σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hd : 0 < d)
    (Φ : (E × ℝ) ≃ₜ (E × ℝ)) (hfst : ∀ p, (Φ p).1 = p.1)
    (hfix : EqOn Φ id (ball (0 : E) R ×ˢ Ioo (-ε) ε)ᶜ)
    (hzero : ∀ x ∈ sphere (0 : E) 1, Φ (x, 0) = (x, σ * d))
    (hA : ∀ p ∈ A ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε), ‖p.1‖ = 1 ∧ 0 < σ * p.2)
    (hK : ∀ p ∈ K, 0 < σ * (Φ p).2) :
    Φ '' (A ∪ K) ∩ (univ ×ˢ ({0} : Set ℝ)) = A ∩ (univ ×ˢ ({0} : Set ℝ)) := by
  have hmono (x : E) : StrictMono (fun t : ℝ => (Φ (x, t)).2) := by
    have hc : Continuous (fun t : ℝ => (Φ (x, t)).2) :=
      Φ.continuous.snd.comp (continuous_const.prodMk continuous_id)
    have hi : Function.Injective (fun t : ℝ => (Φ (x, t)).2) := by
      intro t u htu
      exact congrArg Prod.snd (Φ.injective (Prod.ext
        ((hfst (x, t)).trans (hfst (x, u)).symm) htu))
    rcases hc.strictMono_of_inj hi with hm | hm
    · exact hm
    · have h₀ : Φ (x, ε) = (x, ε) := hfix (fun h => (lt_irrefl ε) h.2.2)
      have h₁ : Φ (x, ε + 1) = (x, ε + 1) := hfix (fun h => by linarith [h.2.2])
      have hh : (Φ (x, ε + 1)).2 < (Φ (x, ε)).2 := hm (by linarith : ε < ε + 1)
      rw [h₀, h₁] at hh
      linarith
  have hpositive {p : E × ℝ} (hp : p ∈ A ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε)) :
      0 < σ * (Φ p).2 := by
    obtain ⟨hn, ht⟩ := hA p hp
    have hbase := hzero p.1 (mem_sphere_zero_iff_norm.mpr hn)
    rcases hσ with rfl | rfl
    · have hp0 : 0 < p.2 := by simpa only [one_mul] using ht
      have hh : (Φ (p.1, 0)).2 < (Φ p).2 := hmono p.1 hp0
      rw [hbase] at hh
      simp only [one_mul] at hh ⊢
      exact hd.trans hh
    · have hp0 : p.2 < 0 := by nlinarith
      have hh : (Φ p).2 < (Φ (p.1, 0)).2 := hmono p.1 hp0
      rw [hbase] at hh
      simp only [neg_one_mul] at hh ⊢
      linarith
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    have hp0 : (Φ q).2 = 0 := hp.2
    rcases hq with hq | hq
    · by_cases hqU : q ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε
      · have hh := hpositive ⟨hq, hqU⟩
        rw [hp0, mul_zero] at hh
        exact hh.false.elim
      · exact ⟨(hfix hqU).symm ▸ hq, hp⟩
    · have hh := hK q hq
      rw [hp0, mul_zero] at hh
      exact hh.false.elim
  · rintro ⟨hpA, hp⟩
    have hp0 : p.2 = 0 := hp.2
    have hpU : p ∉ ball (0 : E) R ×ˢ Ioo (-ε) ε := by
      intro hpU
      have hh := (hA p ⟨hpA, hpU⟩).2
      rw [hp0, mul_zero] at hh
      exact hh.false
    exact ⟨⟨p, Or.inl hpA, hfix hpU⟩, hp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_isotopy_cylinderCap_translation
    {S : Set (E × ℝ)} {R ε a d σ : ℝ}
    (hR : 1 < R) (ha : 0 ≤ a) (had : a < d) (hdε : d < ε)
    (hσ : σ = 1 ∨ σ = -1)
    (hS : S ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε) = sphere (0 : E) 1 ×ˢ Ioo (-ε) ε) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ t z, (H t z).1 = z.1) ∧ (∀ t, H t '' S = S) ∧
      (∀ x ∈ closedBall (0 : E) 1,
        0 < σ * (H 1 (EuclideanGeometry.cylinderCap (σ * a) x)).2) ∧
      (∀ A : Set (E × ℝ), A ⊆ S →
        (∀ p ∈ A ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε), 0 < σ * p.2) →
        H 1 '' (A ∪ EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : E) 1) ∩
          (univ ×ˢ ({0} : Set ℝ)) = A ∩ (univ ×ˢ ({0} : Set ℝ))) ∧
      ∃ U : Set (E × ℝ), IsOpen U ∧
        EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : E) 1 ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, H t p = (p.1, p.2 + t * (σ * d))) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ J ⊆ ball (0 : E) R ×ˢ Ioo (-ε) ε ∧
        ∀ t : ℝ, EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  let r := (R + 1) / 2
  let δ := (ε - d) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hdδ : d + δ < ε := by dsimp [δ]; linarith
  have haδ : a + δ < ε := by linarith
  have hr : 1 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let K : Set (E × ℝ) := closedBall 0 r ×ˢ {z : ℝ | -a - δ ≤ σ * z ∧ σ * z ≤ δ}
  let U : Set (E × ℝ) := ball 0 r ×ˢ {z : ℝ | -a - δ < σ * z ∧ σ * z < δ}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : E) r).prod
    rcases hσ with rfl | rfl
    · simp only [one_mul]
      change IsCompact (Icc (-a - δ) δ)
      exact isCompact_Icc
    · have heq : {z : ℝ | -a - δ ≤ -1 * z ∧ -1 * z ≤ δ} = Icc (-δ) (a + δ) := by
        ext z
        simp only [mem_ofPred_eq, mem_Icc, neg_one_mul]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
      rw [heq]
      exact isCompact_Icc
  have hU : IsOpen U := isOpen_ball.prod
    ((isOpen_lt continuous_const (continuous_const.mul continuous_id)).inter
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const))
  have hUK : U ⊆ K := prod_mono ball_subset_closedBall (fun _ h => ⟨h.1.le, h.2.le⟩)
  have hcapU : EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : E) 1 ⊆ U := by
    rintro p ⟨x, hx, rfl⟩
    refine ⟨mem_ball_zero_iff.mpr
      ((EuclideanGeometry.norm_cylinderCap_fst_le_one (σ * a) x).trans_lt hr), ?_⟩
    have hcap := EuclideanGeometry.cylinderCap_snd_mem_Icc ha
      (mem_closedBall_zero_iff.mp hx)
    change -a - δ < σ * (EuclideanGeometry.cylinderCap (σ * a) x).2 ∧
      σ * (EuclideanGeometry.cylinderCap (σ * a) x).2 < δ
    rw [EuclideanGeometry.cylinderCap_snd] at hcap ⊢
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hcap.1, hcap.2]
  have hSc : S ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε) =
      (sphere (0 : E) 1 ∩ ball (0 : E) R) ×ˢ Ioo (-ε) ε := by
    rw [inter_eq_left.mpr (sphere_subset_ball hR)]
    exact hS
  have htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K,
      (p.1, p.2 + t * (σ * d)) ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε := by
    intro t ht p hp
    refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.1).trans_lt hrR), ?_⟩
    have hz : -a - δ ≤ σ * p.2 ∧ σ * p.2 ≤ δ := hp.2
    rcases hσ with rfl | rfl <;> constructor <;>
      nlinarith [hz.1, hz.2, mul_nonneg ht.1 (ha.trans had.le),
        mul_le_mul_of_nonneg_right ht.2 (ha.trans had.le)]
  obtain ⟨H, hH, hHi, hH0, hmove, hfst, hHS, J, hJ, hJU, hfix⟩ :=
    exists_isotopy_vertical_translation_of_local_product hK hSc
      (isOpen_ball.prod isOpen_Ioo) (subset_refl _) (σ * d) htrace
  have hpositive (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      0 < σ * (H 1 (EuclideanGeometry.cylinderCap (σ * a) x)).2 := by
    rw [hmove 1 ⟨zero_le_one, le_rfl⟩ _ (hUK (hcapU ⟨x, hx, rfl⟩))]
    simp only [EuclideanGeometry.cylinderCap_snd, one_mul]
    rcases hσ with rfl | rfl <;>
      nlinarith [mul_nonneg ha (sq_nonneg ‖x‖)]
  refine ⟨H, hH, hHi, hH0, hfst, hHS, hpositive, ?_, U, hU, hcapU,
    fun t ht p hp => hmove t ht p (hUK hp), J, hJ, hJU, hfix⟩
  intro A hAS hA
  apply image_union_inter_zero_of_vertical_motion hσ (ha.trans_lt had)
    (H 1).toHomeomorph (hfst 1) (fun p hp => (hfix 1).1 (fun h => hp (hJU h)))
  · intro x hx
    have heq := EuclideanGeometry.cylinderCap_of_norm_eq_one (σ * a)
      (mem_sphere_zero_iff_norm.mp hx)
    have hxU := hUK (hcapU ⟨x, sphere_subset_closedBall hx, rfl⟩)
    rw [heq] at hxU
    change H 1 (x, 0) = (x, σ * d)
    simpa only [one_mul, zero_add] using hmove 1 ⟨zero_le_one, le_rfl⟩ (x, 0) hxU
  · intro p hp
    exact ⟨mem_sphere_zero_iff_norm.mp ((hS.subset ⟨hAS hp.1, hp.2⟩).1), hA p hp⟩
  · rintro p ⟨x, hx, rfl⟩
    exact hpositive x hx

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isotopy_cylinderCap_translation_in_chart
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) {S : Set F} {R ε a d σ c : ℝ}
    (hR : 1 < R) (ha : 0 ≤ a) (had : a < d) (hdε : d < ε)
    (hσ : σ = 1 ∨ σ = -1) (h : F → ℝ) (hheight : ∀ p, h (Ψ p) = c + p.2)
    (hS : Ψ ⁻¹' S ∩ (ball (0 : E) R ×ˢ Ioo (-ε) ε) =
      sphere (0 : E) 1 ×ˢ Ioo (-ε) ε) :
    ∃ H : ℝ → (F ≃ₘ[ℝ] F),
      ContDiff ℝ ∞ (fun z : ℝ × F => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × F => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, F) F ∞ ∧
      (∀ t, H t '' S = S) ∧
      (∀ x ∈ closedBall (0 : E) 1,
        0 < σ * (h (H 1 (Ψ (EuclideanGeometry.cylinderCap (σ * a) x))) - c)) ∧
      (∀ A : Set F, A ⊆ S →
        (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ A → 0 < σ * p.2) →
        H 1 '' (A ∪ Ψ '' (EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : E) 1)) ∩
          {z | h z = c} = A ∩ {z | h z = c}) ∧
      ∃ U : Set (E × ℝ), IsOpen U ∧
        EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : E) 1 ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, H t (Ψ p) = Ψ (p.1, p.2 + t * (σ * d))) ∧
      ∃ J : Set F, IsCompact J ∧ J ⊆ Ψ '' (ball (0 : E) R ×ˢ Ioo (-ε) ε) ∧
        ∀ t : ℝ, EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨G, hG, hGi, hG0, _, hGS, hpositive, hlevel, U, hU, hcapU, hmove,
    J, hJ, hJU, hfix⟩ := exists_isotopy_cylinderCap_translation hR ha had hdε hσ hS
  let H := fun t => Ψ.symm.trans ((G t).trans Ψ)
  have hconj (t : ℝ) : H t ∘ Ψ = Ψ ∘ G t := by
    funext p
    change Ψ (G t (Ψ.symm (Ψ p))) = Ψ (G t p)
    rw [Ψ.symm_apply_apply]
  have hΨinj : Function.Injective (Ψ : E × ℝ → F) := Ψ.injective
  have hSimage : Ψ '' (Ψ ⁻¹' S) = S := Ψ.surjective.image_preimage S
  have hzero : Ψ '' (univ ×ˢ ({0} : Set ℝ)) = {z | h z = c} := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change h (Ψ p) = c
      rw [hheight, show p.2 = 0 from hp.2, add_zero]
    · intro hz
      refine ⟨Ψ.symm z, ⟨mem_univ _, ?_⟩, Ψ.apply_symm_apply z⟩
      have hh := hheight (Ψ.symm z)
      rw [Ψ.apply_symm_apply] at hh
      change (Ψ.symm z).2 = 0
      change h z = c at hz
      linarith
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, U, hU, hcapU, ?_,
    Ψ '' J, hJ.image Ψ.contMDiff.continuous, image_mono hJU, ?_⟩
  · exact Ψ.contMDiff.contDiff.comp
      (hG.comp (contDiff_fst.prodMk (Ψ.symm.contMDiff.contDiff.comp contDiff_snd)))
  · exact Ψ.contMDiff.contDiff.comp
      (hGi.comp (contDiff_fst.prodMk (Ψ.symm.contMDiff.contDiff.comp contDiff_snd)))
  · apply Diffeomorph.ext
    intro z
    change Ψ (G 0 (Ψ.symm z)) = z
    rw [hG0]
    exact Ψ.apply_symm_apply z
  · intro t
    rw [← hSimage, ← image_comp, hconj, image_comp, hGS]
  · intro x hx
    have hpoint := congrFun (hconj 1) (EuclideanGeometry.cylinderCap (σ * a) x)
    change H 1 (Ψ (EuclideanGeometry.cylinderCap (σ * a) x)) =
      Ψ (G 1 (EuclideanGeometry.cylinderCap (σ * a) x)) at hpoint
    rw [hpoint, hheight, add_sub_cancel_left]
    exact hpositive x hx
  · intro A hAS hA
    have hAimage : Ψ '' (Ψ ⁻¹' A) = A := Ψ.surjective.image_preimage A
    have hzeroA := hlevel (Ψ ⁻¹' A) (preimage_mono hAS)
      (fun p hp => hA p hp.2 hp.1)
    rw [← hAimage, ← image_union, ← image_comp, hconj, image_comp,
      ← hzero, ← image_inter hΨinj, hzeroA, image_inter hΨinj, hAimage]
  · intro t ht p hp
    exact (congrFun (hconj t) p).trans (congrArg Ψ (hmove t ht p hp))
  · intro t
    constructor
    · intro z hz
      have hinv : Ψ.symm z ∉ J := fun hh => hz ⟨Ψ.symm z, hh, Ψ.apply_symm_apply z⟩
      change Ψ (G t (Ψ.symm z)) = z
      rw [(hfix t).1 hinv]
      exact Ψ.apply_symm_apply z
    · intro z hz
      have hinv : Ψ.symm z ∉ J := fun hh => hz ⟨Ψ.symm z, hh, Ψ.apply_symm_apply z⟩
      change Ψ ((G t).symm (Ψ.symm z)) = z
      rw [(hfix t).2 hinv]
      exact Ψ.apply_symm_apply z


end Diffeomorph
