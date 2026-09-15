import DifferentialGeometry.Topology.Diffeomorph.DisjointSupport
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import Mathlib.Topology.Homeomorph.Lemmas
import DifferentialGeometry.External.Schoenflies.Plane
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Pi

section
open scoped ContDiff Manifold

namespace Schoenflies

private theorem smooth_corner_profile_bounds {ε r : ℝ} (hε : 0 < ε) (hεr : ε ≤ r)
    {d : ℝ} (hd : d = 0 ∨ d = 1) {x : ℝ} (hx : |x| ≤ r) :
    0 ≤ d * Real.smoothMax ε x 0 ∧ d * Real.smoothMax ε x 0 ≤ 2 * r := by
  have hr : 0 < r := hε.trans_le hεr
  rcases hd with rfl | rfl
  · simp only [zero_mul]
    exact ⟨le_refl 0, by positivity⟩
  · simp only [one_mul]
    refine ⟨(le_max_right x 0).trans (Real.smoothMax.max_le hε x 0), ?_⟩
    have hm : max x 0 ≤ r := max_le (abs_le.mp hx).2 hr.le
    linarith [Real.smoothMax.le_max_add hε x 0]

private theorem exists_isotopy_between_smooth_corner_profiles_in_disk
    {ε₀ ε₁ R d : ℝ} (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hR : 3 * max ε₀ ε₁ < R) (hd : d = 0 ∨ d = 1) :
    ∃ H : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : ℝ × ℝ), (H t p).1 = p.1) ∧
      (∀ x : ℝ, H 1 (x, d * Real.smoothMax ε₀ x 0) =
        (x, d * Real.smoothMax ε₁ x 0)) ∧
      (∀ s : Set ℝ,
        H 1 '' {p : ℝ × ℝ | p.1 ∈ s ∧ d * Real.smoothMax ε₀ p.1 0 ≤ p.2} =
          {p : ℝ × ℝ | p.1 ∈ s ∧ d * Real.smoothMax ε₁ p.1 0 ≤ p.2}) ∧
      (∀ s : Set ℝ,
        H 1 '' {p : ℝ × ℝ | p.1 ∈ s ∧ d * Real.smoothMax ε₀ p.1 0 < p.2} =
          {p : ℝ × ℝ | p.1 ∈ s ∧ d * Real.smoothMax ε₁ p.1 0 < p.2}) ∧
      ∃ C : Set (ℝ × ℝ), IsCompact C ∧
        C ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} ∧ ∀ t : ℝ,
          Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ := by
  let r := max ε₀ ε₁
  let g : ℝ × ℝ → ℝ := fun p =>
    (1 - p.1) * (d * Real.smoothMax ε₀ p.2 0) +
      p.1 * (d * Real.smoothMax ε₁ p.2 0)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_const.sub contDiff_fst).mul (contDiff_const.mul
      ((Real.smoothMax.contDiff ε₀).comp (contDiff_snd.prodMk contDiff_const)))).add
      (contDiff_fst.mul (contDiff_const.mul
        ((Real.smoothMax.contDiff ε₁).comp (contDiff_snd.prodMk contDiff_const))))
  have hr : 0 < r := hε₀.trans_le (le_max_left _ _)
  have hrR : 3 * r < R := hR
  have hfixed : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∉ Metric.closedBall (0 : ℝ) r, g (t, x) = g (0, x) := by
    intro t ht x hx
    have hxr : r ≤ |x| := (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx)).le
    have he₀ := Real.smoothMax.eq_max_of_le hε₀
      (show ε₀ ≤ |x - 0| by simpa only [sub_zero] using (le_max_left ε₀ ε₁).trans hxr)
    have he₁ := Real.smoothMax.eq_max_of_le hε₁
      (show ε₁ ≤ |x - 0| by simpa only [sub_zero] using (le_max_right ε₀ ε₁).trans hxr)
    dsimp only [g]
    rw [he₀, he₁]
    ring
  have hO : IsOpen {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} :=
    isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  have htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : ℝ) r,
      (x, g (t, x)) ∈ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} := by
    intro t ht x hx
    have hxr : |x| ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx
    have h₀ := smooth_corner_profile_bounds hε₀ (le_max_left ε₀ ε₁) hd hxr
    have h₁ := smooth_corner_profile_bounds hε₁ (le_max_right ε₀ ε₁) hd hxr
    have hnonneg : 0 ≤ g (t, x) :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) h₀.1) (mul_nonneg ht.1 h₁.1)
    have hbound : g (t, x) ≤ 2 * r := by
      have hleft := mul_le_mul_of_nonneg_left h₀.2 (sub_nonneg.mpr ht.2)
      have hright := mul_le_mul_of_nonneg_left h₁.2 ht.1
      dsimp only [g]
      nlinarith
    change x ^ 2 + g (t, x) ^ 2 < R ^ 2
    have hx₂ : x ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr.le).mpr hxr
    have hg₂ : g (t, x) ^ 2 ≤ (2 * r) ^ 2 := by
      exact (sq_le_sq₀ hnonneg (by positivity)).mpr hbound
    have hRpos : 0 < R := by linarith
    have hr₂ : (3 * r) ^ 2 < R ^ 2 :=
      (sq_lt_sq₀ (by positivity) hRpos.le).mpr hrR
    nlinarith [sq_nonneg r]
  obtain ⟨H, hH, hi, hzero, hfst, hgraph, hepi, hstrict, C, hC, hCO, hfix⟩ :=
    Diffeomorph.exists_isotopy_graphOn_endpoints_in_open hg
      (isCompact_closedBall (0 : ℝ) r) hfixed hO htrace
  refine ⟨H, hH, hi, hzero, hfst, ?_, ?_, ?_, C, hC, hCO, hfix⟩
  · simpa only [g, sub_zero, one_mul, zero_mul, zero_add, sub_self, add_zero] using hgraph
  · simpa only [g, sub_zero, one_mul, zero_mul, zero_add, sub_self, add_zero] using hepi
  · simpa only [g, sub_zero, one_mul, zero_mul, zero_add, sub_self, add_zero] using hstrict

end Schoenflies

end

section
open scoped ContDiff Manifold

namespace Schoenflies

private theorem image_lower_sides_of_image_upper_sides
    {E : Type*} [TopologicalSpace E] (e : (E × ℝ) ≃ₜ (E × ℝ)) {f g : E → ℝ}
    (hweak : e '' {p : E × ℝ | f p.1 ≤ p.2} = {p : E × ℝ | g p.1 ≤ p.2})
    (hstrict : e '' {p : E × ℝ | f p.1 < p.2} = {p : E × ℝ | g p.1 < p.2}) :
    e '' {p : E × ℝ | p.2 ≤ f p.1} = {p : E × ℝ | p.2 ≤ g p.1} ∧
      e '' {p : E × ℝ | p.2 < f p.1} = {p : E × ℝ | p.2 < g p.1} := by
  have hc : {p : E × ℝ | p.2 ≤ f p.1} = {p : E × ℝ | f p.1 < p.2}ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  have ho : {p : E × ℝ | p.2 < f p.1} = {p : E × ℝ | f p.1 ≤ p.2}ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  constructor
  · rw [hc, e.image_compl, hstrict]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  · rw [ho, e.image_compl, hweak]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]

end Schoenflies

end

section
open Set

namespace Schoenflies

private theorem image_local_replacement_of_eqOn_compl
    {X : Type*} (e : X ≃ X) {D N K A B : Set X} (hNK : N ⊆ K)
    (hfix : EqOn e id Nᶜ) (hAB : e '' A = B) :
    e '' ((D \ N) ∪ (K ∩ A)) = (D \ N) ∪ (K ∩ B) := by
  have hout : e '' (D \ N) = D \ N :=
    (hfix.mono (fun _ hp => hp.2)).image_eq_self
  have hc : e '' Kᶜ = Kᶜ := (hfix.mono (compl_subset_compl.mpr hNK)).image_eq_self
  have hK : e '' K = K := by
    apply compl_injective
    rw [← e.image_compl, hc]
  rw [image_union, image_inter e.injective, hout, hK, hAB]

private theorem image_local_replacement_sides_of_eqOn_compl
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X) {D N K A B : Set X}
    (hNK : N ⊆ K) (hfix : EqOn e id Nᶜ) (hAB : e '' A = B) :
    e '' ((D \ N) ∪ (K ∩ A)) = (D \ N) ∪ (K ∩ B) ∧
      e '' interior ((D \ N) ∪ (K ∩ A)) = interior ((D \ N) ∪ (K ∩ B)) ∧
      e '' frontier ((D \ N) ∪ (K ∩ A)) = frontier ((D \ N) ∪ (K ∩ B)) := by
  have h := image_local_replacement_of_eqOn_compl e.toEquiv (D := D) hNK hfix hAB
  exact ⟨h, (e.image_interior _).trans (congrArg interior h),
    (e.image_frontier _).trans (congrArg frontier h)⟩

end Schoenflies

end

section
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_affine_conjugate_isotopy
    (e : Plane ≃ᵃ[ℝ] Plane) (H : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)))
    (hH : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hi : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (H z.1).symm z.2))
    (hzero : H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞)
    {C O : Set (ℝ × ℝ)} (hC : IsCompact C) (hO : IsOpen O) (hCO : C ⊆ O)
    (hfix : ∀ t : ℝ, Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ) :
    let c := fun p : Plane => ((e p) 0, (e p) 1)
    ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t p, c (Φ t p) = H t (c p)) ∧
      (∀ t p, c ((Φ t).symm p) = (H t).symm (c p)) ∧
      (∀ t s, Φ t '' (c ⁻¹' s) = c ⁻¹' (H t '' s)) ∧
      (∀ t s, (Φ t).symm '' (c ⁻¹' s) = c ⁻¹' ((H t).symm '' s)) ∧
      IsOpen (c ⁻¹' O) ∧ IsCompact (c ⁻¹' C) ∧ c ⁻¹' C ⊆ c ⁻¹' O ∧
      ∀ t : ℝ, Set.EqOn (Φ t) id (c ⁻¹' C)ᶜ ∧
        Set.EqOn (Φ t).symm id (c ⁻¹' C)ᶜ := by
  dsimp only
  let a : Plane ≃ₘ[ℝ] Plane :=
    { toEquiv := e.toEquiv
      contMDiff_toFun :=
        (⟨e.toAffineMap, e.toAffineMap.continuous_of_finiteDimensional⟩ :
          Plane →ᴬ[ℝ] Plane).contDiff.contMDiff
      contMDiff_invFun :=
        (⟨e.symm.toAffineMap, e.symm.toAffineMap.continuous_of_finiteDimensional⟩ :
          Plane →ᴬ[ℝ] Plane).contDiff.contMDiff }
  let L : Plane ≃L[ℝ] (ℝ × ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).trans
    (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
  let c : Plane ≃ₘ[ℝ] (ℝ × ℝ) := a.trans L.toDiffeomorph
  have hc (p : Plane) : c p = ((e p) 0, (e p) 1) := rfl
  let Φ : ℝ → (Plane ≃ₘ[ℝ] Plane) := fun t => (c.trans (H t)).trans c.symm
  have hΦ : ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) :=
    c.symm.contDiff.comp (hH.comp (contDiff_fst.prodMk (c.contDiff.comp contDiff_snd)))
  have hΦi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) :=
    c.symm.contDiff.comp (hi.comp (contDiff_fst.prodMk (c.contDiff.comp contDiff_snd)))
  have hforward (t : ℝ) (p : Plane) : c (Φ t p) = H t (c p) :=
    c.apply_symm_apply _
  have hinverse (t : ℝ) (p : Plane) : c ((Φ t).symm p) = (H t).symm (c p) :=
    c.apply_symm_apply _
  have himage (g : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) (s : Set (ℝ × ℝ)) :
      ((c.trans g).trans c.symm) '' (c ⁻¹' s) = c ⁻¹' (g '' s) := by
    calc
      ((c.trans g).trans c.symm) '' (c ⁻¹' s) =
          c.symm '' (g '' (c '' (c ⁻¹' s))) := by
        rw [Set.image_image, Set.image_image]
        rfl
      _ = c.symm '' (g '' s) := by
        rw [show c '' (c ⁻¹' s) = s from c.toEquiv.image_preimage s]
      _ = c ⁻¹' (g '' s) := c.symm_image_eq_preimage _
  have hcompact : IsCompact (c ⁻¹' C) := by
    rw [← c.symm_image_eq_preimage]
    exact hC.image c.symm.continuous
  refine ⟨Φ, hΦ, hΦi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro p
    change c.symm (H 0 (c p)) = p
    rw [hzero]
    exact c.symm_apply_apply p
  · intro t p
    simpa only [hc] using hforward t p
  · intro t p
    exact hinverse t p
  · intro t s
    exact himage (H t) s
  · intro t s
    exact himage (H t).symm s
  · exact hO.preimage c.continuous
  · exact hcompact
  · exact Set.preimage_mono hCO
  · intro t
    constructor
    · intro p hp
      change c.symm (H t (c p)) = p
      rw [(hfix t).1 (show c p ∉ C from hp), id_eq, c.symm_apply_apply]
    · intro p hp
      change c.symm ((H t).symm (c p)) = p
      rw [(hfix t).2 (show c p ∉ C from hp), id_eq, c.symm_apply_apply]

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_isotopy_between_affine_smooth_corner_regions
    (e : Plane ≃ᵃ[ℝ] Plane) {ε₀ ε₁ R d σ : ℝ}
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hR : 3 * max ε₀ ε₁ < R)
    (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1) :
    let F := fun ε p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
    let N := e ⁻¹' ball (0 : Plane) R
    let K := e ⁻¹' closedBall (0 : Plane) R
    ∃ (Φ : ℝ → (Plane ≃ₘ[ℝ] Plane)) (C : Set Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      IsCompact C ∧ C ⊆ N ∧
      (∀ t : ℝ, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' {p | 0 ≤ F ε₀ p} = {p | 0 ≤ F ε₁ p} ∧
      ∀ D : Set Plane,
        Φ 1 '' ((D \ N) ∪ (K ∩ {p | 0 ≤ F ε₀ p})) =
          (D \ N) ∪ (K ∩ {p | 0 ≤ F ε₁ p}) ∧
        Φ 1 '' interior ((D \ N) ∪ (K ∩ {p | 0 ≤ F ε₀ p})) =
          interior ((D \ N) ∪ (K ∩ {p | 0 ≤ F ε₁ p})) ∧
        Φ 1 '' frontier ((D \ N) ∪ (K ∩ {p | 0 ≤ F ε₀ p})) =
          frontier ((D \ N) ∪ (K ∩ {p | 0 ≤ F ε₁ p})) := by
  dsimp only
  let c := fun p : Plane => ((e p) 0, (e p) 1)
  let O := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2}
  have hRpos : 0 < R := by
    have h := hε₀.trans_le (le_max_left ε₀ ε₁)
    linarith
  have hO : IsOpen O :=
    isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  have hball : c ⁻¹' O = e ⁻¹' ball (0 : Plane) R := by
    ext p
    change (e p) 0 ^ 2 + (e p) 1 ^ 2 < R ^ 2 ↔ dist (e p) 0 < R
    rw [dist_zero_right, ← sq_lt_sq₀ (norm_nonneg (e p)) hRpos.le]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  obtain ⟨H, hH, hi, hzero, _, _, hweak, hstrict, B, hB, hBO, hfix⟩ :=
    exists_isotopy_between_smooth_corner_profiles_in_disk hε₀ hε₁ hR hd
  have hw := hweak univ
  have hs := hstrict univ
  simp only [mem_univ, true_and] at hw hs
  have hl := image_lower_sides_of_image_upper_sides (H 1).toHomeomorph
    (f := fun x => d * Real.smoothMax ε₀ x 0)
    (g := fun x => d * Real.smoothMax ε₁ x 0) hw hs
  have hsign : H 1 '' {p : ℝ × ℝ | 0 ≤ σ * (p.2 - d * Real.smoothMax ε₀ p.1 0)} =
      {p : ℝ × ℝ | 0 ≤ σ * (p.2 - d * Real.smoothMax ε₁ p.1 0)} := by
    rcases hσ with rfl | rfl
    · simpa only [Diffeomorph.coe_toHomeomorph, neg_one_mul, neg_nonneg, sub_nonpos]
        using hl.1
    · simpa only [one_mul, sub_nonneg] using hw
  obtain ⟨Φ, hΦ, hΦi, hΦzero, _, _, himage, _, _, hC, hCO, hΦfix⟩ :=
    exists_affine_conjugate_isotopy e H hH hi hzero hB hO hBO hfix
  have htransport : Φ 1 '' {p : Plane |
      0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε₀ ((e p) 0) 0)} =
      {p : Plane | 0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε₁ ((e p) 0) 0)} := by
    simpa only [hsign, preimage_ofPred_eq] using
      himage 1 {p : ℝ × ℝ | 0 ≤ σ * (p.2 - d * Real.smoothMax ε₀ p.1 0)}
  have hCN : c ⁻¹' B ⊆ e ⁻¹' ball (0 : Plane) R := by
    rw [← hball]
    exact hCO
  refine ⟨Φ, c ⁻¹' B, hΦ, hΦi, hΦzero, hC, hCN, hΦfix, htransport, ?_⟩
  intro D
  exact image_local_replacement_sides_of_eqOn_compl (Φ 1).toHomeomorph
    (D := D) (preimage_mono ball_subset_closedBall)
    ((hΦfix 1).1.mono (compl_subset_compl.mpr hCN)) htransport

end Schoenflies

end

section
open Set

namespace Equiv

private theorem image_indexed_replacement_of_local_eq
    {X ι : Type*} (g : X ≃ X) (e : ι → X ≃ X)
    {D : Set X} {N K A B : ι → Set X}
    (hNK : ∀ i, N i ⊆ K i) (hfix : EqOn g id (⋃ i, N i)ᶜ)
    (heq : ∀ i, EqOn g (e i) (K i))
    (hfixe : ∀ i, EqOn (e i) id (N i)ᶜ) (hAB : ∀ i, e i '' A i = B i) :
    g '' ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) =
      (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ B i := by
  have hout : g '' (D \ ⋃ i, N i) = D \ ⋃ i, N i :=
    (hfix.mono (fun _ hp => hp.2)).image_eq_self
  have hlocal (i : ι) : g '' (K i ∩ A i) = K i ∩ B i := by
    have hc : e i '' (K i)ᶜ = (K i)ᶜ :=
      ((hfixe i).mono (compl_subset_compl.mpr (hNK i))).image_eq_self
    have hK : e i '' K i = K i := by
      apply compl_injective
      rw [← (e i).image_compl, hc]
    rw [((heq i).mono inter_subset_left).image_eq, image_inter (e i).injective, hK, hAB]
  rw [image_union, hout, image_iUnion]
  congr 1
  exact iUnion_congr hlocal

end Equiv

namespace Homeomorph

private theorem image_indexed_replacement_sides_of_local_eq
    {X ι : Type*} [TopologicalSpace X] (g : X ≃ₜ X) (e : ι → X ≃ₜ X)
    {D : Set X} {N K A B : ι → Set X}
    (hNK : ∀ i, N i ⊆ K i) (hfix : EqOn g id (⋃ i, N i)ᶜ)
    (heq : ∀ i, EqOn g (e i) (K i))
    (hfixe : ∀ i, EqOn (e i) id (N i)ᶜ) (hAB : ∀ i, e i '' A i = B i) :
    g '' ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) =
        (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ B i ∧
      g '' interior ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) =
        interior ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ B i) ∧
      g '' frontier ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) =
        frontier ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ B i) := by
  have h := Equiv.image_indexed_replacement_of_local_eq g.toEquiv
    (fun i => (e i).toEquiv) (D := D) hNK hfix heq hfixe hAB
  exact ⟨h, (g.image_interior _).trans (congrArg interior h),
    (g.image_frontier _).trans (congrArg frontier h)⟩

end Homeomorph

end

section
open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

theorem exists_isotopy_between_finite_affine_corner_replacements
    {ι : Type*} [Finite ι] (e : ι → Plane ≃ᵃ[ℝ] Plane)
    (ε₀ ε₁ R d σ : ι → ℝ)
    (hε₀ : ∀ i, 0 < ε₀ i) (hε₁ : ∀ i, 0 < ε₁ i)
    (hR : ∀ i, 3 * max (ε₀ i) (ε₁ i) < R i)
    (hd : ∀ i, d i = 0 ∨ d i = 1) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hdisj : Pairwise fun i j => Disjoint
      (e i ⁻¹' closedBall (0 : Plane) (R i)) (e j ⁻¹' closedBall (0 : Plane) (R j))) :
    let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
    let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
    let F := fun ε i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
    ∃ (Φ : ℝ → (Plane ≃ₘ[ℝ] Plane)) (C : Set Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      IsCompact C ∧ C ⊆ ⋃ i, N i ∧
      (∀ t : ℝ, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      ∀ D : Set Plane,
        Φ 1 '' ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₀ i p}) =
            (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₁ i p} ∧
          Φ 1 '' interior ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₀ i p}) =
            interior ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₁ i p}) ∧
          Φ 1 '' frontier ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₀ i p}) =
            frontier ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ F ε₁ i p}) := by
  classical
  dsimp only
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  have hNK (i : ι) : N i ⊆ K i := preimage_mono ball_subset_closedBall
  choose H C hH hi hzero hC hCN hfix himage _ using fun i =>
    exists_isotopy_between_affine_smooth_corner_regions (e i)
      (hε₀ i) (hε₁ i) (hR i) (hd i) (hσ i)
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hcompact, hΦfix, hΦeq⟩ :=
    Diffeomorph.exists_isotopy_of_finite_disjoint_compact_support C K H hC
      (fun i => (hCN i).trans (hNK i)) hH hi hzero hdisj (fun i t => (hfix i t).1)
  have hCNall : (⋃ i, C i) ⊆ ⋃ i, N i := iUnion_mono hCN
  refine ⟨Φ, ⋃ i, C i, hΦ, hΦi, hΦzero, hcompact, hCNall, hΦfix, ?_⟩
  intro D
  exact Homeomorph.image_indexed_replacement_sides_of_local_eq (Φ 1).toHomeomorph
    (fun i => (H i 1).toHomeomorph) (D := D) hNK
    (((hΦfix 1).1).mono (compl_subset_compl.mpr hCNall))
    (fun i => (hΦeq i 1).1)
    (fun i => ((hfix i 1).1).mono (compl_subset_compl.mpr (hCN i))) himage

end Schoenflies

end
