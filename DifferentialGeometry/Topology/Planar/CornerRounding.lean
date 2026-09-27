import DifferentialGeometry.Topology.Diffeomorph.CompactIsotopyComposition
import DifferentialGeometry.Topology.Diffeomorph.LevelTransport
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Calculus.Deriv.Basic
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

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem norm_le_three_mul_of_corner_strip {ε : ℝ} (hε : 0 < ε)
    {p : Plane} (hx : |p 0| ≤ ε) (hy : 0 ≤ p 1) (hyε : p 1 ≤ 2 * ε) :
    ‖p‖ ≤ 3 * ε := by
  have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  have hxx := mul_nonneg (sub_nonneg.mpr hx₂) (by linarith : 0 ≤ ε + p 0)
  have hyy := mul_nonneg (sub_nonneg.mpr hyε)
    (by linarith : 0 ≤ 2 * ε + p 1)
  apply (sq_le_sq₀ (norm_nonneg p) (by positivity : 0 ≤ 3 * ε)).mp
  nlinarith

theorem smooth_corner_signs_eq_outside_ball {ε d σ : ℝ} (hε : 0 < ε)
    (hd : d = 0 ∨ d = 1) {p : Plane}
    (hp : 3 * ε < ‖p‖) :
    (0 ≤ σ * (p 1 - d * Real.smoothMax ε (p 0) 0) ↔
      0 ≤ σ * (p 1 - d * max (p 0) 0)) ∧
    (0 < σ * (p 1 - d * Real.smoothMax ε (p 0) 0) ↔
      0 < σ * (p 1 - d * max (p 0) 0)) ∧
    (p 1 = d * Real.smoothMax ε (p 0) 0 ↔ p 1 = d * max (p 0) 0) := by
  rcases hd with rfl | rfl
  · simp only [zero_mul, iff_self, and_self]
  by_cases hx : ε ≤ |p 0|
  · rw [Real.smoothMax.eq_max_of_le (x := p 0) (y := 0) hε
      (by simpa only [sub_zero] using hx)]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  have hxε : |p 0| ≤ ε := (lt_of_not_ge hx).le
  have hmax₀ : 0 ≤ max (p 0) 0 := le_max_right _ _
  have hmaxε : max (p 0) 0 ≤ ε := max_le (abs_le.mp hxε).2 hε.le
  have hμ₀ : 0 ≤ Real.smoothMax ε (p 0) 0 :=
    hmax₀.trans (Real.smoothMax.max_le hε _ _)
  have hμε : Real.smoothMax ε (p 0) 0 ≤ 2 * ε := by
    linarith [Real.smoothMax.le_max_add hε (p 0) 0]
  have hy : p 1 < 0 ∨ 2 * ε < p 1 := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hp) (norm_le_three_mul_of_corner_strip hε hxε h.1 h.2)
  rcases hy with hy | hy
  · have hμ : p 1 - Real.smoothMax ε (p 0) 0 < 0 := by linarith
    have hm : p 1 - max (p 0) 0 < 0 := by linarith
    simp only [one_mul, mul_nonneg_iff, mul_pos_iff]
    simp only [hμ.le, hm.le, not_le_of_gt hμ, not_le_of_gt hm, hμ, hm,
      not_lt_of_ge hμ.le, not_lt_of_ge hm.le, and_true, and_false, false_or]
    exact ⟨trivial, trivial, iff_of_false (by linarith) (by linarith)⟩
  · have hμ : 0 < p 1 - Real.smoothMax ε (p 0) 0 := by linarith
    have hm : 0 < p 1 - max (p 0) 0 := by linarith
    simp only [one_mul, mul_nonneg_iff, mul_pos_iff]
    simp only [hμ.le, hm.le, not_le_of_gt hμ, not_le_of_gt hm, hμ, hm,
      not_lt_of_ge hμ.le, not_lt_of_ge hm.le, and_true, and_false, or_false]
    exact ⟨trivial, trivial, iff_of_false (by linarith) (by linarith)⟩

end Schoenflies

end

section

open Set
open scoped ContDiff

namespace Schoenflies

private theorem affine_smooth_corner_fderiv_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E →ᴬ[ℝ] ℝ) (ε : ℝ) {v : E}
    (hg : 0 < g.contLinear v) (hgf : 0 < g.contLinear v - f.contLinear v) (p : E) :
    0 < fderiv ℝ (fun q => g q - Real.smoothMax ε (f q) 0) p v := by
  have hf : HasFDerivAt f f.contLinear p := by
    rw [f.decomp]
    exact f.contLinear.hasFDerivAt.add_const (f 0)
  have hg' : HasFDerivAt g g.contLinear p := by
    rw [g.decomp]
    exact g.contLinear.hasFDerivAt.add_const (g 0)
  have hs : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothMax ε x 0) :=
    (Real.smoothMax.contDiff ε).comp (contDiff_id.prodMk contDiff_const)
  have hd := ((hs.differentiable (by simp)).differentiableAt (x := f p)).hasDerivAt
  have hcomp := hd.comp_hasFDerivAt p hf
  have hderiv := (hg'.sub hcomp).fderiv
  change fderiv ℝ (fun q => g q - Real.smoothMax ε (f q) 0) p = _ at hderiv
  rw [hderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  let α := deriv (fun x => Real.smoothMax ε x 0) (f p)
  obtain ⟨hα₀, hα₁⟩ := Real.smoothMax.deriv_left_mem_Icc ε (f p) 0
  change 0 < g.contLinear v - α * f.contLinear v
  by_cases hα : α = 1
  · rw [hα, one_mul]
    exact hgf
  · have hlt : α < 1 := lt_of_le_of_ne hα₁ hα
    have hpos := mul_pos (sub_pos.mpr hlt) hg
    have hnonneg := mul_nonneg hα₀ hgf.le
    nlinarith

private theorem affine_smooth_corner_interpolation_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ g₀ f₁ g₁ : E →ᴬ[ℝ] ℝ) (ε₀ ε₁ : ℝ) {v : E}
    (hg₀ : 0 < g₀.contLinear v) (hgf₀ : 0 < g₀.contLinear v - f₀.contLinear v)
    (hg₁ : 0 < g₁.contLinear v) (hgf₁ : 0 < g₁.contLinear v - f₁.contLinear v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : E) :
    fderiv ℝ (fun q => (1 - t) * (g₀ q - Real.smoothMax ε₀ (f₀ q) 0) +
      t * (g₁ q - Real.smoothMax ε₁ (f₁ q) 0)) p ≠ 0 := by
  let A := fun q => g₀ q - Real.smoothMax ε₀ (f₀ q) 0
  let B := fun q => g₁ q - Real.smoothMax ε₁ (f₁ q) 0
  have hA : ContDiff ℝ ∞ A := g₀.contDiff.sub
    ((Real.smoothMax.contDiff ε₀).comp (f₀.contDiff.prodMk contDiff_const))
  have hB : ContDiff ℝ ∞ B := g₁.contDiff.sub
    ((Real.smoothMax.contDiff ε₁).comp (f₁.contDiff.prodMk contDiff_const))
  have hdA := (hA.differentiable (by simp)).differentiableAt (x := p)
  have hdB := (hB.differentiable (by simp)).differentiableAt (x := p)
  have hderiv := ((hdA.hasFDerivAt.const_mul (1 - t)).add
    (hdB.hasFDerivAt.const_mul t)).fderiv
  have hposA := affine_smooth_corner_fderiv_pos f₀ g₀ ε₀ hg₀ hgf₀ p
  have hposB := affine_smooth_corner_fderiv_pos f₁ g₁ ε₁ hg₁ hgf₁ p
  intro hz
  have hvalue := congrArg (fun L : E →L[ℝ] ℝ => L v) (hz.symm.trans hderiv)
  simp only [zero_apply, add_apply,
    smul_apply, smul_eq_mul] at hvalue
  by_cases htone : t = 1
  · simp only [htone, sub_self, zero_mul, one_mul, zero_add] at hvalue
    exact (ne_of_gt hposB) hvalue.symm
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 htone
    have hpositive := mul_pos (sub_pos.mpr hlt) hposA
    have hnonnegative := mul_nonneg ht.1 hposB.le
    linarith

end Schoenflies

end

section

open Set
open scoped ContDiff

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise (cartesianX cartesianY)

private theorem normalized_corner_common_direction
    (e : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r : ℝ}
    (ha : e a = Plane.mk (-1) 0) (hb : e b = Plane.mk r r) (hc : e c = 0) :
    e.linear ((a - c) + (b - c)) = Plane.mk (r - 1) r := by
  have hv (q : Plane) : e.linear (q - c) = e q - e c :=
    e.toAffineMap.linearMap_vsub q c
  rw [map_add, hv, hv, ha, hb, hc, sub_zero, sub_zero]
  ext i
  fin_cases i <;> simp [PiLp.add_apply, Plane.mk]
  ring

private theorem normalized_affine_corner_interpolation_regular
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    (ε₀ ε₁ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : Plane) :
    fderiv ℝ (fun q =>
      (1 - t) * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0) +
        t * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0)) p ≠ 0 := by
  let v := (a - c) + (b - c)
  let f₀ : Plane →ᴬ[ℝ] ℝ :=
    ⟨cartesianX.comp e₀.toAffineMap,
      (cartesianX.comp e₀.toAffineMap).continuous_of_finiteDimensional⟩
  let g₀ : Plane →ᴬ[ℝ] ℝ :=
    ⟨cartesianY.comp e₀.toAffineMap,
      (cartesianY.comp e₀.toAffineMap).continuous_of_finiteDimensional⟩
  let f₁ : Plane →ᴬ[ℝ] ℝ :=
    ⟨cartesianX.comp e₁.toAffineMap,
      (cartesianX.comp e₁.toAffineMap).continuous_of_finiteDimensional⟩
  let g₁ : Plane →ᴬ[ℝ] ℝ :=
    ⟨cartesianY.comp e₁.toAffineMap,
      (cartesianY.comp e₁.toAffineMap).continuous_of_finiteDimensional⟩
  have hv₀ : e₀.linear v = Plane.mk (r₀ - 1) r₀ :=
    normalized_corner_common_direction e₀ ha₀ hb₀ hc₀
  have hv₁ : e₁.linear v = Plane.mk (r₁ - 1) r₁ :=
    normalized_corner_common_direction e₁ ha₁ hb₁ hc₁
  have hf₀ : f₀.contLinear v = r₀ - 1 := by
    change (e₀.linear v) 0 = r₀ - 1
    rw [hv₀]
    rfl
  have hg₀ : g₀.contLinear v = r₀ := by
    change (e₀.linear v) 1 = r₀
    rw [hv₀]
    rfl
  have hf₁ : f₁.contLinear v = r₁ - 1 := by
    change (e₁.linear v) 0 = r₁ - 1
    rw [hv₁]
    rfl
  have hg₁ : g₁.contLinear v = r₁ := by
    change (e₁.linear v) 1 = r₁
    rw [hv₁]
    rfl
  exact affine_smooth_corner_interpolation_regular f₀ g₀ f₁ g₁ ε₀ ε₁
    (hg₀.symm ▸ hr₀) (by rw [hg₀, hf₀]; linarith)
    (hg₁.symm ▸ hr₁) (by rw [hg₁, hf₁]; linarith) ht p

private theorem normalized_signed_corner_interpolation_regular
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ σ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hσ : σ = -1 ∨ σ = 1)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    (ε₀ ε₁ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : Plane) :
    fderiv ℝ (fun q =>
      (1 - t) * (σ * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0)) +
        t * (σ * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0))) p ≠ 0 := by
  let G := fun q => (1 - t) * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0) +
    t * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0)
  have hreg : fderiv ℝ G p ≠ 0 :=
    normalized_affine_corner_interpolation_regular e₀ e₁ hr₀ hr₁ ha₀ hb₀ hc₀
      ha₁ hb₁ hc₁ ε₀ ε₁ ht p
  have hdiff : DifferentiableAt ℝ G p := by
    by_contra h
    exact hreg (fderiv_zero_of_not_differentiableAt h)
  have hσne : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have heq : (fun q =>
      (1 - t) * (σ * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0)) +
        t * (σ * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0))) =
      fun q => σ * G q := by
    funext q
    dsimp only [G]
    ring
  rw [heq, fderiv_const_mul hdiff]
  exact smul_ne_zero hσne hreg

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem normalized_corner_sign_eq_of_local_region_eq
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ σ₀ σ₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hσ₀ : σ₀ = -1 ∨ σ₀ = 1)
    (hσ₁ : σ₁ = -1 ∨ σ₁ = 1)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    {D U₀ U₁ : Set Plane} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hcU₀ : c ∈ U₀) (hcU₁ : c ∈ U₁)
    (hside₀ : ∀ q ∈ U₀, q ∈ D ↔ 0 ≤ σ₀ * ((e₀ q) 1 - max ((e₀ q) 0) 0))
    (hside₁ : ∀ q ∈ U₁, q ∈ D ↔ 0 ≤ σ₁ * ((e₁ q) 1 - max ((e₁ q) 0) 0)) :
    σ₀ = σ₁ := by
  let v := (a - c) + (b - c)
  have hv₀ : e₀.linear v = Plane.mk (r₀ - 1) r₀ :=
    normalized_corner_common_direction e₀ ha₀ hb₀ hc₀
  have hv₁ : e₁.linear v = Plane.mk (r₁ - 1) r₁ :=
    normalized_corner_common_direction e₁ ha₁ hb₁ hc₁
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (hU₀.inter hU₁) c ⟨hcU₀, hcU₁⟩
  let t := ρ / (2 * (‖v‖ + 1))
  have ht : 0 < t := by dsimp only [t]; positivity
  have htρ : t * ‖v‖ < ρ := by
    have hden : 0 < 2 * (‖v‖ + 1) := by positivity
    calc
      t * ‖v‖ < t * (2 * (‖v‖ + 1)) :=
        mul_lt_mul_of_pos_left (by linarith [norm_nonneg v]) ht
      _ = ρ := div_mul_cancel₀ ρ hden.ne'
  let q := c + t • v
  have hq : q ∈ U₀ ∩ U₁ := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    change ‖c + t • v - c‖ < ρ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htρ
  have he (e : Plane ≃ᵃ[ℝ] Plane) (r : ℝ)
      (hc : e c = 0) (hv : e.linear v = Plane.mk (r - 1) r) :
      e q = t • Plane.mk (r - 1) r := by
    change e (c + t • v) = _
    rw [add_comm c (t • v)]
    change e (t • v +ᵥ c) = _
    rw [e.map_vadd, map_smul, hv, hc]
    exact add_zero _
  have hG (e : Plane ≃ᵃ[ℝ] Plane) (r : ℝ) (hr : 0 < r)
      (hc : e c = 0) (hv : e.linear v = Plane.mk (r - 1) r) :
      0 < (e q) 1 - max ((e q) 0) 0 := by
    rw [he e r hc hv]
    change 0 < t * r - max (t * (r - 1)) 0
    rw [sub_pos, max_lt_iff]
    constructor
    · nlinarith
    · exact mul_pos ht hr
  have hG₀ := hG e₀ r₀ hr₀ hc₀ hv₀
  have hG₁ := hG e₁ r₁ hr₁ hc₁ hv₁
  have hs := (hside₀ q hq.1).symm.trans (hside₁ q hq.2)
  rcases hσ₀ with rfl | rfl
  · rcases hσ₁ with rfl | rfl
    · rfl
    · have hh := hs.mpr (by simpa only [one_mul] using hG₁.le)
      simp only [neg_one_mul] at hh
      linarith
  · rcases hσ₁ with rfl | rfl
    · have hh := hs.mp (by simpa only [one_mul] using hG₀.le)
      simp only [neg_one_mul] at hh
      linarith
    · rfl


end Schoenflies

end

section

namespace Schoenflies

private theorem normalized_corner_face_coordinates
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ : ℝ}
    (hr₀ : r₀ ≠ 0)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    (p : Plane) :
    (e₁ p) 1 = (r₁ / r₀) * (e₀ p) 1 ∧
      (e₁ p) 1 - (e₁ p) 0 = (e₀ p) 1 - (e₀ p) 0 := by
  have hv₀ (q : Plane) : e₀.linear (q - c) = e₀ q - e₀ c :=
    e₀.toAffineMap.linearMap_vsub q c
  have hv₁ (q : Plane) : e₁.linear (q - c) = e₁ q - e₁ c :=
    e₁.toAffineMap.linearMap_vsub q c
  have hva₀ : e₀.linear (a - c) = Plane.mk (-1) 0 := by
    rw [hv₀, ha₀, hc₀, sub_zero]
  have hvb₀ : e₀.linear (b - c) = Plane.mk r₀ r₀ := by
    rw [hv₀, hb₀, hc₀, sub_zero]
  have hva₁ : e₁.linear (a - c) = Plane.mk (-1) 0 := by
    rw [hv₁, ha₁, hc₁, sub_zero]
  have hvb₁ : e₁.linear (b - c) = Plane.mk r₁ r₁ := by
    rw [hv₁, hb₁, hc₁, sub_zero]
  let x := (e₀ p) 0
  let y := (e₀ p) 1
  let v := (y - x) • (a - c) + (y / r₀) • (b - c)
  have hev : e₀.linear v = e₀ p := by
    dsimp only [v]
    rw [map_add, map_smul, map_smul, hva₀, hvb₀]
    ext i
    fin_cases i
    · change (y - x) * (-1) + (y / r₀) * r₀ = x
      rw [div_mul_cancel₀ _ hr₀]
      ring
    · change (y - x) * 0 + (y / r₀) * r₀ = y
      rw [mul_zero, zero_add, div_mul_cancel₀ _ hr₀]
  have hv : v = p - c := e₀.linear.injective (by rwa [hv₀, hc₀, sub_zero])
  have he : e₁ p = (y - x) • Plane.mk (-1) 0 + (y / r₀) • Plane.mk r₁ r₁ := by
    calc
      e₁ p = e₁.linear (p - c) := by rw [hv₁, hc₁, sub_zero]
      _ = e₁.linear v := congrArg e₁.linear hv.symm
      _ = _ := by dsimp only [v]; rw [map_add, map_smul, map_smul, hva₁, hvb₁]
  constructor
  · rw [he]
    change (y - x) * 0 + (y / r₀) * r₁ = (r₁ / r₀) * y
    ring
  · rw [he]
    change ((y - x) * 0 + (y / r₀) * r₁) -
      ((y - x) * (-1) + (y / r₀) * r₁) = y - x
    ring

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem smooth_corner_locally_proportional_of_face_coordinates
    {X : Type*} [TopologicalSpace X] (f₀ g₀ f₁ g₁ : X → ℝ)
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) {ε₀ ε₁ κ : ℝ}
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hκ : 0 < κ) (σ : ℝ)
    (hg : ∀ q, g₁ q = κ * g₀ q)
    (hface : ∀ q, g₁ q - f₁ q = g₀ q - f₀ q)
    {W : Set X} (hW : IsOpen W) {p : X} (hpW : p ∈ W)
    (hp : g₀ p = max (f₀ p) 0) (hx₀ : ε₀ < |f₀ p|) (hx₁ : ε₁ < |f₁ p|) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧
      EqOn (fun q => σ * (g₁ q - Real.smoothMax ε₁ (f₁ q) 0))
        (fun q => ρ * (σ * (g₀ q - Real.smoothMax ε₀ (f₀ q) 0))) N := by
  have hlow {ε x : ℝ} (hε : 0 < ε) (hx : x < -ε) : Real.smoothMax ε x 0 = 0 := by
    have hxneg : x < 0 := by linarith
    rw [Real.smoothMax.eq_max_of_le hε (by rw [sub_zero, abs_of_neg hxneg]; linarith),
      max_eq_right hxneg.le]
  have hhigh {ε x : ℝ} (hε : 0 < ε) (hx : ε < x) : Real.smoothMax ε x 0 = x := by
    have hxpos : 0 < x := hε.trans hx
    rw [Real.smoothMax.eq_max_of_le hε (by rw [sub_zero, abs_of_pos hxpos]; exact hx.le),
      max_eq_left hxpos.le]
  by_cases hneg : f₀ p < 0
  · have hg₀ : g₀ p = 0 := hp.trans (max_eq_right hneg.le)
    have hfp : f₁ p = f₀ p := by
      have h := hface p
      rw [hg p, hg₀, mul_zero] at h
      linarith
    have hx₀' : f₀ p < -ε₀ := by rw [abs_of_neg hneg] at hx₀; linarith
    have hx₁' : f₁ p < -ε₁ := by
      rw [hfp, abs_of_neg hneg] at hx₁
      rw [hfp]
      linarith
    refine ⟨κ, hκ, W ∩ {q | f₀ q < -ε₀ ∧ f₁ q < -ε₁},
      hW.inter ((isOpen_lt hf₀ continuous_const).inter (isOpen_lt hf₁ continuous_const)),
      ⟨hpW, hx₀', hx₁'⟩, inter_subset_left, ?_⟩
    intro q hq
    change σ * (g₁ q - Real.smoothMax ε₁ (f₁ q) 0) =
      κ * (σ * (g₀ q - Real.smoothMax ε₀ (f₀ q) 0))
    rw [hlow hε₀ hq.2.1, hlow hε₁ hq.2.2, sub_zero, sub_zero, hg q]
    ring
  · have hnonneg : 0 ≤ f₀ p := le_of_not_gt hneg
    have hx₀' : ε₀ < f₀ p := by rwa [abs_of_nonneg hnonneg] at hx₀
    have hpos : 0 < f₀ p := hε₀.trans hx₀'
    have hg₀ : g₀ p = f₀ p := hp.trans (max_eq_left hnonneg)
    have hfp : f₁ p = κ * f₀ p := by
      have h := hface p
      rw [hg p, hg₀] at h
      linarith
    have hpos₁ : 0 < f₁ p := by rw [hfp]; exact mul_pos hκ hpos
    have hx₁' : ε₁ < f₁ p := by rwa [abs_of_pos hpos₁] at hx₁
    refine ⟨1, zero_lt_one, W ∩ {q | ε₀ < f₀ q ∧ ε₁ < f₁ q},
      hW.inter ((isOpen_lt continuous_const hf₀).inter (isOpen_lt continuous_const hf₁)),
      ⟨hpW, hx₀', hx₁'⟩, inter_subset_left, ?_⟩
    intro q hq
    change σ * (g₁ q - Real.smoothMax ε₁ (f₁ q) 0) =
      1 * (σ * (g₀ q - Real.smoothMax ε₀ (f₀ q) 0))
    rw [hhigh hε₀ hq.2.1, hhigh hε₁ hq.2.2, hface q, one_mul]

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem normalized_corner_profiles_locally_proportional
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ ε₀ ε₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (σ : ℝ)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    {W : Set Plane} (hW : IsOpen W) {p : Plane} (hpW : p ∈ W)
    (hp : (e₀ p) 1 = max ((e₀ p) 0) 0)
    (hx₀ : ε₀ < |(e₀ p) 0|) (hx₁ : ε₁ < |(e₁ p) 0|) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧
      EqOn (fun q => σ * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0))
        (fun q => ρ * (σ * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0))) N := by
  have hfaces := normalized_corner_face_coordinates e₀ e₁ hr₀.ne'
    ha₀ hb₀ hc₀ ha₁ hb₁ hc₁
  exact smooth_corner_locally_proportional_of_face_coordinates
    (fun q => (e₀ q) 0) (fun q => (e₀ q) 1)
    (fun q => (e₁ q) 0) (fun q => (e₁ q) 1)
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0).comp
      e₀.toAffineMap.continuous_of_finiteDimensional)
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0).comp
      e₁.toAffineMap.continuous_of_finiteDimensional)
    hε₀ hε₁ (div_pos hr₁ hr₀) σ (fun q => (hfaces q).1) (fun q => (hfaces q).2)
    hW hpW hp hx₀ hx₁

end Schoenflies

end

section

open Set

namespace Schoenflies

private theorem corner_raw_signs_of_face_coordinates
    {x₀ y₀ x₁ y₁ κ : ℝ} (hκ : 0 < κ)
    (hy : y₁ = κ * y₀) (hd : y₁ - x₁ = y₀ - x₀) :
    (0 ≤ y₀ - max x₀ 0 ↔ 0 ≤ y₁ - max x₁ 0) ∧
      (0 < y₀ - max x₀ 0 ↔ 0 < y₁ - max x₁ 0) := by
  have hle : x₁ ≤ y₁ ↔ x₀ ≤ y₀ := by
    calc
      x₁ ≤ y₁ ↔ 0 ≤ y₁ - x₁ := sub_nonneg.symm
      _ ↔ 0 ≤ y₀ - x₀ := by rw [hd]
      _ ↔ x₀ ≤ y₀ := sub_nonneg
  have hlt : x₁ < y₁ ↔ x₀ < y₀ := by
    calc
      x₁ < y₁ ↔ 0 < y₁ - x₁ := sub_pos.symm
      _ ↔ 0 < y₀ - x₀ := by rw [hd]
      _ ↔ x₀ < y₀ := sub_pos
  constructor
  · simp only [sub_nonneg, max_le_iff, hle]
    rw [hy, mul_nonneg_iff_of_pos_left hκ]
  · simp only [sub_pos, max_lt_iff, hlt]
    rw [hy, mul_pos_iff_of_pos_left hκ]

private theorem same_sign_interpolation_zero {A B t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hle : 0 ≤ A ↔ 0 ≤ B) (hlt : 0 < A ↔ 0 < B)
    (hz : (1 - t) * A + t * B = 0) : A = 0 ∧ B = 0 := by
  rcases lt_trichotomy A 0 with hA | hA | hA
  · have hB : B < 0 := lt_of_not_ge fun h => (not_le_of_gt hA) (hle.mpr h)
    have h := (convex_Iio (𝕜 := ℝ) (0 : ℝ)) hA hB
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    change (1 - t) * A + t * B < 0 at h
    rw [hz] at h
    exact False.elim (lt_irrefl _ h)
  · have hB₀ : 0 ≤ B := hle.mp hA.ge
    have hB₁ : B ≤ 0 := le_of_not_gt fun h => (ne_of_gt (hlt.mpr h)) hA
    exact ⟨hA, le_antisymm hB₁ hB₀⟩
  · have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) hA (hlt.mp hA)
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    change 0 < (1 - t) * A + t * B at h
    rw [hz] at h
    exact False.elim (lt_irrefl _ h)

private theorem raw_corner_zero_avoids_strip {ε : ℝ} (hε : 0 < ε) {p : Plane}
    (hp : p 1 = max (p 0) 0) (hn : 3 * ε < ‖p‖) : ε < |p 0| := by
  by_contra hx
  have hx' : |p 0| ≤ ε := le_of_not_gt hx
  have hmax₀ : 0 ≤ max (p 0) 0 := le_max_right _ _
  have hmaxε : max (p 0) 0 ≤ ε := max_le ((le_abs_self _).trans hx') hε.le
  have hy₀ : 0 ≤ p 1 := by rw [hp]; exact hmax₀
  have hyε : p 1 ≤ 2 * ε := by rw [hp]; linarith
  exact (not_le_of_gt hn) (norm_le_three_mul_of_corner_strip hε hx' hy₀ hyε)

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem normalized_corner_interpolation_locally_proportional_outside_balls
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ ε₀ ε₁ σ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hσ : σ ≠ 0)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    {W : Set Plane} (hW : IsOpen W) {p : Plane} (hpW : p ∈ W)
    (hp₀ : 3 * ε₀ < ‖e₀ p‖) (hp₁ : 3 * ε₁ < ‖e₁ p‖)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : (1 - t) * (σ * ((e₀ p) 1 - Real.smoothMax ε₀ ((e₀ p) 0) 0)) +
      t * (σ * ((e₁ p) 1 - Real.smoothMax ε₁ ((e₁ p) 0) 0)) = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧
      EqOn (fun q => σ * ((e₁ q) 1 - Real.smoothMax ε₁ ((e₁ q) 0) 0))
        (fun q => ρ * (σ * ((e₀ q) 1 - Real.smoothMax ε₀ ((e₀ q) 0) 0))) N := by
  let A := (e₀ p) 1 - Real.smoothMax ε₀ ((e₀ p) 0) 0
  let B := (e₁ p) 1 - Real.smoothMax ε₁ ((e₁ p) 0) 0
  have hz' : (1 - t) * A + t * B = 0 := by
    have hm : σ * ((1 - t) * A + t * B) = 0 := by
      calc
        σ * ((1 - t) * A + t * B) = (1 - t) * (σ * A) + t * (σ * B) := by ring
        _ = 0 := hz
    exact (mul_eq_zero.mp hm).resolve_left hσ
  have hs₀ := smooth_corner_signs_eq_outside_ball (d := 1) (σ := 1) hε₀
    (Or.inr rfl) hp₀
  have hs₁ := smooth_corner_signs_eq_outside_ball (d := 1) (σ := 1) hε₁
    (Or.inr rfl) hp₁
  simp only [one_mul] at hs₀ hs₁
  have hfaces := normalized_corner_face_coordinates e₀ e₁ hr₀.ne'
    ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ p
  have hraw := corner_raw_signs_of_face_coordinates (div_pos hr₁ hr₀) hfaces.1 hfaces.2
  have hle : 0 ≤ A ↔ 0 ≤ B := hs₀.1.trans (hraw.1.trans hs₁.1.symm)
  have hlt : 0 < A ↔ 0 < B := hs₀.2.1.trans (hraw.2.trans hs₁.2.1.symm)
  obtain ⟨hA, hB⟩ := same_sign_interpolation_zero ht hle hlt hz'
  have hboundary₀ : (e₀ p) 1 = max ((e₀ p) 0) 0 :=
    hs₀.2.2.mp (sub_eq_zero.mp hA)
  have hboundary₁ : (e₁ p) 1 = max ((e₁ p) 0) 0 :=
    hs₁.2.2.mp (sub_eq_zero.mp hB)
  exact normalized_corner_profiles_locally_proportional e₀ e₁ hr₀ hr₁ hε₀ hε₁ σ
    ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hW hpW hboundary₀
    (raw_corner_zero_avoids_strip hε₀ hboundary₀ hp₀)
    (raw_corner_zero_avoids_strip hε₁ hboundary₁ hp₁)

end Schoenflies

end

section

open Set Metric
open scoped ContDiff

namespace Schoenflies

private theorem affine_closed_ball_preimage_subset_of_isOpen
    {W : Set Plane} (hW : IsOpen W) (e : Plane ≃ᵃ[ℝ] Plane) {c : Plane}
    (hcW : c ∈ W) (hc : e c = 0) :
    ∃ R : ℝ, 0 < R ∧ e ⁻¹' closedBall (0 : Plane) R ⊆ W := by
  have hmem : e.symm ⁻¹' W ∈ nhds (0 : Plane) := by
    have hc' : e.symm 0 ∈ W := by rw [← hc, e.symm_apply_apply]; exact hcW
    exact (hW.preimage e.symm.toAffineMap.continuous_of_finiteDimensional).mem_nhds hc'
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  exact ⟨R, hR, fun p hp => by simpa only [Set.mem_preimage, e.symm_apply_apply] using hsub hp⟩

private theorem isCompact_affine_closed_ball_preimage (e : Plane ≃ᵃ[ℝ] Plane) (r : ℝ) :
    IsCompact (e ⁻¹' closedBall (0 : Plane) r) := by
  have heq : e ⁻¹' closedBall (0 : Plane) r = e.symm '' closedBall (0 : Plane) r := by
    ext p
    exact ⟨fun hp => ⟨e p, hp, e.symm_apply_apply p⟩,
      fun ⟨q, hq, hp⟩ => by simpa only [← hp, Set.mem_preimage, e.apply_symm_apply] using hq⟩
  rw [heq]
  exact (isCompact_closedBall (0 : Plane) r).image e.symm.toAffineMap.continuous_of_finiteDimensional

private theorem exists_normalized_corner_interpolation_compact_core
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ σ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hσ : σ = -1 ∨ σ = 1)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    {W : Set Plane} (hW : IsOpen W) (hcW : c ∈ W) :
    ∃ η₀ η₁ : ℝ, 0 < η₀ ∧ 0 < η₁ ∧
      ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ η₀ → 0 < ε₁ → ε₁ ≤ η₁ →
        let A := fun p => σ * ((e₀ p) 1 - Real.smoothMax ε₀ ((e₀ p) 0) 0)
        let B := fun p => σ * ((e₁ p) 1 - Real.smoothMax ε₁ ((e₁ p) 0) 0)
        let J := (e₀ ⁻¹' closedBall (0 : Plane) (3 * ε₀)) ∪
          (e₁ ⁻¹' closedBall (0 : Plane) (3 * ε₁))
        IsCompact J ∧ c ∈ interior J ∧ J ⊆ W ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ p,
            fderiv ℝ (fun q => (1 - t) * A q + t * B q) p ≠ 0) ∧
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ W,
            (1 - t) * A p + t * B p = 0 → p ∉ J →
              ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧
                EqOn B (fun q => ρ * A q) N := by
  obtain ⟨R₀, hR₀, hK₀⟩ := affine_closed_ball_preimage_subset_of_isOpen hW e₀ hcW hc₀
  obtain ⟨R₁, hR₁, hK₁⟩ := affine_closed_ball_preimage_subset_of_isOpen hW e₁ hcW hc₁
  refine ⟨R₀ / 4, R₁ / 4, by positivity, by positivity, ?_⟩
  intro ε₀ ε₁ hε₀ hε₀R hε₁ hε₁R
  dsimp only
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have h₀R : 3 * ε₀ ≤ R₀ := by linarith only [hε₀R, hR₀]
  have h₁R : 3 * ε₁ ≤ R₁ := by linarith only [hε₁R, hR₁]
  have hJ : IsCompact ((e₀ ⁻¹' closedBall (0 : Plane) (3 * ε₀)) ∪
      (e₁ ⁻¹' closedBall (0 : Plane) (3 * ε₁))) :=
    (isCompact_affine_closed_ball_preimage e₀ (3 * ε₀)).union
      (isCompact_affine_closed_ball_preimage e₁ (3 * ε₁))
  have hN₀K : e₀ ⁻¹' ball (0 : Plane) (3 * ε₀) ⊆
      e₀ ⁻¹' closedBall (0 : Plane) (3 * ε₀) :=
    Set.preimage_mono (f := e₀)
      (ball_subset_closedBall (x := (0 : Plane)) (ε := 3 * ε₀))
  have hN₀ : IsOpen (e₀ ⁻¹' ball (0 : Plane) (3 * ε₀)) :=
    (isOpen_ball : IsOpen (ball (0 : Plane) (3 * ε₀))).preimage
      (show Continuous (e₀ : Plane → Plane) from
        e₀.toAffineMap.continuous_of_finiteDimensional)
  refine ⟨hJ, ?_, ?_, ?_, ?_⟩
  · apply mem_interior.mpr
    refine ⟨e₀ ⁻¹' ball (0 : Plane) (3 * ε₀), ?_, ?_, ?_⟩
    · intro p hp
      exact Or.inl (hN₀K hp)
    · exact hN₀
    · change e₀ c ∈ ball (0 : Plane) (3 * ε₀)
      rw [hc₀]
      exact mem_ball_self (by positivity)
  · intro p hp
    rcases hp with hp | hp
    · exact hK₀ ((Set.preimage_mono (f := e₀) (closedBall_subset_closedBall h₀R)) hp)
    · exact hK₁ ((Set.preimage_mono (f := e₁) (closedBall_subset_closedBall h₁R)) hp)
  · intro t ht p
    exact normalized_signed_corner_interpolation_regular e₀ e₁ hr₀ hr₁ hσ
      ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ ε₀ ε₁ ht p
  · intro t ht p hpW hz hpJ
    have hp₀ : 3 * ε₀ < ‖e₀ p‖ := by
      apply lt_of_not_ge
      intro hn
      exact hpJ (Or.inl (mem_closedBall_zero_iff.mpr hn))
    have hp₁ : 3 * ε₁ < ‖e₁ p‖ := by
      apply lt_of_not_ge
      intro hn
      exact hpJ (Or.inr (mem_closedBall_zero_iff.mpr hn))
    exact normalized_corner_interpolation_locally_proportional_outside_balls
      e₀ e₁ hr₀ hr₁ hε₀ hε₁ hσne ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hW hpW hp₀ hp₁ ht hz

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise (cartesianX cartesianY)

private theorem exists_isotopy_between_normalized_corner_profiles
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ σ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hσ : σ = -1 ∨ σ = 1)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ r₀) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ r₁) (hc₁ : e₁ c = 0)
    {W : Set Plane} (hW : IsOpen W) (hcW : c ∈ W) :
    ∃ η₀ η₁ : ℝ, 0 < η₀ ∧ 0 < η₁ ∧
      ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ η₀ → 0 < ε₁ → ε₁ ≤ η₁ →
        let A := fun p => σ * ((e₀ p) 1 - Real.smoothMax ε₀ ((e₀ p) 0) 0)
        let B := fun p => σ * ((e₁ p) 1 - Real.smoothMax ε₁ ((e₁ p) 0) 0)
        ∃ (K : Set Plane) (H : ℝ → Plane ≃ₘ[ℝ] Plane),
          IsCompact K ∧ c ∈ interior K ∧ K ⊆ W ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
          H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ ∧
            (∀ p, H t p ∈ W ↔ p ∈ W) ∧ (∀ p, (H t).symm p ∈ W ↔ p ∈ W)) ∧
          (∀ p ∈ W, (A p = 0 ↔ B (H 1 p) = 0) ∧
            (A p < 0 ↔ B (H 1 p) < 0) ∧ (A p ≤ 0 ↔ B (H 1 p) ≤ 0)) ∧
          ∀ p ∈ W, (B p = 0 ↔ A ((H 1).symm p) = 0) ∧
            (B p < 0 ↔ A ((H 1).symm p) < 0) ∧
              (B p ≤ 0 ↔ A ((H 1).symm p) ≤ 0) := by
  have hsmooth (e : Plane ≃ᵃ[ℝ] Plane) (ε : ℝ) :
      ContDiff ℝ ∞ (fun p => σ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0)) := by
    let f : Plane →ᴬ[ℝ] ℝ := ⟨cartesianX.comp e.toAffineMap,
      (cartesianX.comp e.toAffineMap).continuous_of_finiteDimensional⟩
    let g : Plane →ᴬ[ℝ] ℝ := ⟨cartesianY.comp e.toAffineMap,
      (cartesianY.comp e.toAffineMap).continuous_of_finiteDimensional⟩
    exact contDiff_const.mul (g.contDiff.sub
      ((Real.smoothMax.contDiff ε).comp (f.contDiff.prodMk contDiff_const)))
  obtain ⟨η₀, η₁, hη₀, hη₁, hcore⟩ :=
    exists_normalized_corner_interpolation_compact_core e₀ e₁ hr₀ hr₁ hσ
      ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hW hcW
  refine ⟨η₀, η₁, hη₀, hη₁, ?_⟩
  intro ε₀ ε₁ hε₀ hε₀η hε₁ hε₁η
  obtain ⟨hJ, hcJ, hJW, hreg, hprop⟩ := hcore ε₀ ε₁ hε₀ hε₀η hε₁ hε₁η
  obtain ⟨K, H, hK, hJK, hKW, hH, hHi, hH₀, hs, hf, hb⟩ :=
    Diffeomorph.exists_isotopy_level_and_sublevels_of_proportional_interpolation
      (hsmooth e₀ ε₀) (hsmooth e₁ ε₁) hW hJ hJW
      (fun t ht p _ _ => hreg t ht p) hprop
  exact ⟨K, H, hK, hJK (interior_subset hcJ), hKW, hH, hHi, hH₀, hs, hf, hb⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_isotopy_between_native_corner_profiles
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ d₀ d₁ σ₀ σ₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hd₀ : d₀ = 0 ∨ d₀ = 1) (hd₁ : d₁ = 0 ∨ d₁ = 1)
    (hstraight : d₀ = 0 ↔ d₁ = 0)
    (hσ₀ : σ₀ = -1 ∨ σ₀ = 1) (hσ₁ : σ₁ = -1 ∨ σ₁ = 1)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ (d₀ * r₀))
    (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ (d₁ * r₁))
    (hc₁ : e₁ c = 0)
    {D U₀ U₁ : Set Plane} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hcU₀ : c ∈ U₀) (hcU₁ : c ∈ U₁)
    (hside₀ : ∀ q ∈ U₀, q ∈ D ↔ 0 ≤ σ₀ * ((e₀ q) 1 - d₀ * max ((e₀ q) 0) 0))
    (hside₁ : ∀ q ∈ U₁, q ∈ D ↔ 0 ≤ σ₁ * ((e₁ q) 1 - d₁ * max ((e₁ q) 0) 0)) :
    let W := U₀ ∩ U₁
    ∃ η₀ η₁ : ℝ, 0 < η₀ ∧ 0 < η₁ ∧
      ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ η₀ → 0 < ε₁ → ε₁ ≤ η₁ →
        ∃ (C : Set Plane) (H : ℝ → Plane ≃ₘ[ℝ] Plane), IsCompact C ∧ C ⊆ W ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
          H 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          (∀ t, EqOn (H t) id Cᶜ ∧ EqOn (H t).symm id Cᶜ ∧
            (∀ p, H t p ∈ W ↔ p ∈ W) ∧ (∀ p, (H t).symm p ∈ W ↔ p ∈ W)) ∧
          ∀ p ∈ W,
            (0 ≤ σ₀ * ((e₀ p) 1 - d₀ * Real.smoothMax ε₀ ((e₀ p) 0) 0) ↔
              0 ≤ σ₁ * ((e₁ (H 1 p)) 1 - d₁ * Real.smoothMax ε₁ ((e₁ (H 1 p)) 0) 0)) := by
  dsimp only
  by_cases hdzero : d₀ = 0
  · have hd₁zero : d₁ = 0 := hstraight.mp hdzero
    refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro ε₀ ε₁ _ _ _ _
    refine ⟨∅, fun _ => Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞,
      isCompact_empty, empty_subset _, contDiff_snd, contDiff_snd, rfl, ?_, ?_⟩
    · exact fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · intro p hp
      have h₀ := hside₀ p hp.1
      have h₁ := hside₁ p hp.2
      simp only [hdzero, hd₁zero, zero_mul, sub_zero] at h₀ h₁ ⊢
      exact h₀.symm.trans h₁
  · have hd₀one : d₀ = 1 := hd₀.resolve_left hdzero
    have hd₁one : d₁ = 1 := hd₁.resolve_left fun h => hdzero (hstraight.mpr h)
    have hb₀' : e₀ b = Plane.mk r₀ r₀ := by simpa only [hd₀one, one_mul] using hb₀
    have hb₁' : e₁ b = Plane.mk r₁ r₁ := by simpa only [hd₁one, one_mul] using hb₁
    have hside₀' : ∀ q ∈ U₀, q ∈ D ↔ 0 ≤ σ₀ * ((e₀ q) 1 - max ((e₀ q) 0) 0) := by
      simpa only [hd₀one, one_mul] using hside₀
    have hside₁' : ∀ q ∈ U₁, q ∈ D ↔ 0 ≤ σ₁ * ((e₁ q) 1 - max ((e₁ q) 0) 0) := by
      simpa only [hd₁one, one_mul] using hside₁
    have hσeq := normalized_corner_sign_eq_of_local_region_eq e₀ e₁ hr₀ hr₁ hσ₀ hσ₁
      ha₀ hb₀' hc₀ ha₁ hb₁' hc₁ hU₀ hU₁ hcU₀ hcU₁ hside₀' hside₁'
    obtain ⟨η₀, η₁, hη₀, hη₁, h⟩ := exists_isotopy_between_normalized_corner_profiles
      e₀ e₁ hr₀ hr₁ hσ₀ ha₀ hb₀' hc₀ ha₁ hb₁' hc₁ (hU₀.inter hU₁) ⟨hcU₀, hcU₁⟩
    refine ⟨η₀, η₁, hη₀, hη₁, ?_⟩
    intro ε₀ ε₁ hε₀ hε₀η hε₁ hε₁η
    obtain ⟨C, H, hC, _, hCW, hH, hHi, hH₀, hs, hf, _⟩ :=
      h ε₀ ε₁ hε₀ hε₀η hε₁ hε₁η
    refine ⟨C, H, hC, hCW, hH, hHi, hH₀, hs, ?_⟩
    intro p hp
    simpa only [hd₀one, hd₁one, one_mul, ← hσeq, not_lt] using
      not_congr (hf p hp).2.1

end Schoenflies

end

section

open Set Metric

namespace Schoenflies

private theorem mem_indexed_replacement_iff_of_disjoint_neighborhoods
    {X ι : Type*} {D : Set X} {U N K A : ι → Set X}
    (hNK : ∀ i, N i ⊆ K i) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (heq : ∀ i, ∀ p ∈ U i \ N i, p ∈ A i ↔ p ∈ D)
    (i : ι) {p : X} (hp : p ∈ U i) :
    p ∈ ((D \ ⋃ j, N j) ∪ ⋃ j, K j ∩ A j) ↔ p ∈ A i := by
  have houtside (j : ι) (hji : j ≠ i) (hpj : p ∈ U j) : False :=
    Set.disjoint_left.mp (hdisj hji) hpj hp
  constructor
  · rintro (⟨hpD, hpN⟩ | hpK)
    · exact (heq i p ⟨hp, fun h => hpN (Set.mem_iUnion.mpr ⟨i, h⟩)⟩).mpr hpD
    · obtain ⟨j, hpj, hpa⟩ := Set.mem_iUnion.mp hpK
      by_cases hji : j = i
      · exact hji ▸ hpa
      · exact False.elim (houtside j hji (hKU j hpj))
  · intro hpA
    by_cases hpN : p ∈ N i
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hNK i hpN, hpA⟩)
    · refine Or.inl ⟨(heq i p ⟨hp, hpN⟩).mp hpA, ?_⟩
      intro hpall
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpall
      by_cases hji : j = i
      · exact hpN (hji ▸ hpj)
      · exact houtside j hji (hKU j (hNK j hpj))

private theorem affine_corner_replacement_local_profile
    {ι : Type*} (e : ι → Plane ≃ᵃ[ℝ] Plane) (ε R d σ : ι → ℝ)
    {D : Set Plane} {U : ι → Set Plane}
    (hε : ∀ i, 0 < ε i) (hεR : ∀ i, 3 * ε i < R i)
    (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hside : ∀ i, ∀ p ∈ U i, p ∈ D ↔
      0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) :
    ∀ i, ∀ p ∈ U i,
      p ∈ ((D \ ⋃ j, e j ⁻¹' ball (0 : Plane) (R j)) ∪
        ⋃ j, (e j ⁻¹' closedBall (0 : Plane) (R j)) ∩
          {q | 0 ≤ σ j * ((e j q) 1 - d j * Real.smoothMax (ε j) ((e j q) 0) 0)}) ↔
        0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0) := by
  intro i p hp
  refine mem_indexed_replacement_iff_of_disjoint_neighborhoods
    (fun j => Set.preimage_mono (f := e j)
      (ball_subset_closedBall (x := (0 : Plane)) (ε := R j))) hKU hdisj ?_ i hp
  intro j q hq
  have hqR : R j ≤ ‖e j q‖ := by
    apply le_of_not_gt
    intro hn
    exact hq.2 (mem_ball_zero_iff.mpr hn)
  exact (smooth_corner_signs_eq_outside_ball (σ := σ j) (hε j) (hd j)
    ((hεR j).trans_le hqR)).1.trans (hside j q hq.1).symm

end Schoenflies

end

section

open Set Metric
open scoped Topology

namespace Schoenflies

private theorem mem_indexed_replacement_iff_of_local_agreement
    {X ι : Type*} {D : Set X} {N K A : ι → Set X}
    (hNK : ∀ i, N i ⊆ K i) {p : X}
    (heq : ∀ i, p ∈ K i → (p ∈ A i ↔ p ∈ D)) :
    p ∈ ((D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i) ↔ p ∈ D := by
  constructor
  · rintro (⟨hpD, _⟩ | h)
    · exact hpD
    · obtain ⟨i, hKi, hAi⟩ := mem_iUnion.mp h
      exact (heq i hKi).mp hAi
  · intro hpD
    by_cases hpN : p ∈ ⋃ i, N i
    · obtain ⟨i, hNi⟩ := mem_iUnion.mp hpN
      exact Or.inr (mem_iUnion.mpr
        ⟨i, hNK i hNi, (heq i (hNK i hNi)).mpr hpD⟩)
    · exact Or.inl ⟨hpD, hpN⟩


private theorem affine_corner_replacement_eq_outside_small_balls
    {ι : Type*} (e : ι → Plane ≃ᵃ[ℝ] Plane) (ε R d σ : ι → ℝ) {D : Set Plane}
    (hε : ∀ i, 0 < ε i) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hside : ∀ i, ∀ p ∈ e i ⁻¹' closedBall (0 : Plane) (R i),
      p ∈ D ↔ 0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0))
    {p : Plane} (hp : p ∉ ⋃ i, e i ⁻¹' closedBall (0 : Plane) (3 * ε i)) :
    p ∈ ((D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
      ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
        {q | 0 ≤ σ i * ((e i q) 1 - d i * Real.smoothMax (ε i) ((e i q) 0) 0)}) ↔
      p ∈ D := by
  apply mem_indexed_replacement_iff_of_local_agreement
    (fun _ => preimage_mono ball_subset_closedBall)
  intro i hpK
  have hnorm : 3 * ε i < ‖e i p‖ := by
    apply lt_of_not_ge
    intro h
    exact hp (mem_iUnion.mpr ⟨i, mem_closedBall_zero_iff.mpr h⟩)
  exact (smooth_corner_signs_eq_outside_ball (σ := σ i) (hε i) (hd i) hnorm).1.trans
    (hside i p hpK).symm


end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_small_affine_corner_width
    (e : Plane ≃ᵃ[ℝ] Plane) {c : Plane} {W : Set Plane}
    (hc : e c = 0) (hW : IsOpen W) (hcW : c ∈ W)
    {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ ζ ∧
      ∀ ε : ℝ, ε ≤ η → e ⁻¹' closedBall (0 : Plane) (3 * ε) ⊆ W := by
  have hmem : e.symm ⁻¹' W ∈ nhds (0 : Plane) := by
    have hc' : e.symm 0 ∈ W := by rw [← hc, e.symm_apply_apply]; exact hcW
    exact (hW.preimage e.symm.toAffineMap.continuous_of_finiteDimensional).mem_nhds hc'
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hRW : e ⁻¹' closedBall (0 : Plane) R ⊆ W :=
    fun p hp => by simpa only [Set.mem_preimage, e.symm_apply_apply] using hsub hp
  let η := min δ (min ζ (R / 4))
  have hη : 0 < η := lt_min hδ (lt_min hζ (div_pos hR (by norm_num)))
  refine ⟨η, hη, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro ε hε
  have hεR : ε ≤ R / 4 := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 3 * ε ≤ R := by linarith only [hεR, hR]
  exact (preimage_mono (closedBall_subset_closedBall hsmall)).trans hRW

private theorem exists_isotopy_between_finite_native_corner_replacements
    {ι : Type*} [Finite ι] (e : Fin 2 → ι → Plane ≃ᵃ[ℝ] Plane)
    (a b c : ι → Plane) (U : Fin 2 → ι → Set Plane)
    (r d σ δ R : Fin 2 → ι → ℝ) {D : Set Plane}
    (hnorm : ∀ k i, 0 < r k i ∧ e k i (a i) = Plane.mk (-1) 0 ∧
      e k i (b i) = Plane.mk (r k i) (d k i * r k i) ∧ e k i (c i) = 0)
    (hU : ∀ k i, IsOpen (U k i) ∧ c i ∈ U k i)
    (hd : ∀ k i, d k i = 0 ∨ d k i = 1)
    (hstraight : ∀ i, d 0 i = 0 ↔ d 1 i = 0)
    (hσ : ∀ k i, σ k i = -1 ∨ σ k i = 1)
    (hδ : ∀ k i, 0 < δ k i ∧ 3 * δ k i < R k i)
    (hKU : ∀ k i, e k i ⁻¹' closedBall (0 : Plane) (R k i) ⊆ U k i)
    (hdisj : ∀ k, Pairwise fun i j => Disjoint (U k i) (U k j))
    (hside : ∀ k i, ∀ p ∈ U k i, p ∈ D ↔
      0 ≤ σ k i * ((e k i p) 1 - d k i * max ((e k i p) 0) 0)) :
    ∃ η : Fin 2 → ι → ℝ,
      (∀ k i, 0 < η k i ∧ η k i ≤ δ k i ∧
        e k i ⁻¹' closedBall (0 : Plane) (3 * η k i) ⊆ U 0 i ∩ U 1 i) ∧
      ∀ ε : Fin 2 → ι → ℝ, (∀ k i, 0 < ε k i ∧ ε k i ≤ η k i) →
        let D' := fun k => (D \ ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
          ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
            {p | 0 ≤ σ k i * ((e k i p) 1 -
              d k i * Real.smoothMax (ε k i) ((e k i p) 0) 0)}
        ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
          ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
          Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
          IsCompact C ∧ C ⊆ ⋃ i, U 0 i ∩ U 1 i ∧
          (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
          Φ 1 '' D' 0 = D' 1 ∧ Φ 1 '' interior (D' 0) = interior (D' 1) ∧
          Φ 1 '' frontier (D' 0) = frontier (D' 1) := by
  classical
  let W := fun i => U 0 i ∩ U 1 i
  have hlocal (i : ι) := exists_isotopy_between_native_corner_profiles (e 0 i) (e 1 i)
    (hnorm 0 i).1 (hnorm 1 i).1 (hd 0 i) (hd 1 i) (hstraight i) (hσ 0 i) (hσ 1 i)
    (hnorm 0 i).2.1 (hnorm 0 i).2.2.1 (hnorm 0 i).2.2.2
    (hnorm 1 i).2.1 (hnorm 1 i).2.2.1 (hnorm 1 i).2.2.2
    (hU 0 i).1 (hU 1 i).1 (hU 0 i).2 (hU 1 i).2 (hside 0 i) (hside 1 i)
  choose ζ₀ ζ₁ hζ₀ hζ₁ hlocal using hlocal
  let ζ : Fin 2 → ι → ℝ := ![ζ₀, ζ₁]
  have hζ (k : Fin 2) (i : ι) : 0 < ζ k i := by
    fin_cases k
    · exact hζ₀ i
    · exact hζ₁ i
  have hsmall (k : Fin 2) (i : ι) := exists_small_affine_corner_width (e k i)
    (hnorm k i).2.2.2 ((hU 0 i).1.inter (hU 1 i).1)
    ⟨(hU 0 i).2, (hU 1 i).2⟩ (hδ k i).1 (hζ k i)
  choose η hη hηδ hηζ hηW using hsmall
  refine ⟨η, fun k i => ⟨hη k i, hηδ k i, hηW k i (η k i) le_rfl⟩, ?_⟩
  intro ε hε
  let D' := fun k => (D \ ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
    ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
      {p | 0 ≤ σ k i * ((e k i p) 1 - d k i * Real.smoothMax (ε k i) ((e k i p) 0) 0)}
  have hεR (k : Fin 2) (i : ι) : 3 * ε k i < R k i :=
    (mul_le_mul_of_nonneg_left ((hε k i).2.trans (hηδ k i))
      (by norm_num : (0 : ℝ) ≤ 3)).trans_lt (hδ k i).2
  have hprofile (k : Fin 2) := affine_corner_replacement_local_profile
    (e k) (ε k) (R k) (d k) (σ k) (fun i => (hε k i).1) (hεR k)
    (hd k) (hKU k) (hdisj k) (hside k)
  have hout (k : Fin 2) (p : Plane) (hp : p ∉ ⋃ i, W i) : p ∈ D' k ↔ p ∈ D := by
    apply affine_corner_replacement_eq_outside_small_balls
      (e k) (ε k) (R k) (d k) (σ k) (fun i => (hε k i).1) (hd k)
      (fun i q hq => hside k i q (hKU k i hq))
    intro hpJ
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hpJ
    exact hp (mem_iUnion.mpr ⟨i, hηW k i (ε k i) (hε k i).2 hpi⟩)
  have hisotopy (i : ι) := hlocal i (ε 0 i) (ε 1 i)
    (hε 0 i).1 ((hε 0 i).2.trans (hηζ 0 i))
    (hε 1 i).1 ((hε 1 i).2.trans (hηζ 1 i))
  choose C H hC hCW hH hi hzero hfix hmember using hisotopy
  have hWdisj : Pairwise fun i j => Disjoint (W i) (W j) := by
    intro i j hij
    exact (hdisj 0 hij).mono inter_subset_left inter_subset_left
  have htransport (i : ι) (p : Plane) (hp : p ∈ W i) :
      H i 1 p ∈ D' 1 ↔ p ∈ D' 0 := by
    have hpH : H i 1 p ∈ W i := ((hfix i 1).2.2.1 p).mpr hp
    exact (hprofile 1 i (H i 1 p) hpH.2).trans
      ((hmember i p hp).symm.trans (hprofile 0 i p hp.1).symm)
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hcompact, hΦfix, _, himage⟩ :=
    Diffeomorph.exists_isotopy_image_of_finite_local_transport C W H hC hCW hH hi hzero
      hWdisj (fun i t => (hfix i t).1) htransport
      (fun p hp => (hout 0 p hp).trans (hout 1 p hp).symm)
  exact ⟨Φ, ⋃ i, C i, hΦ, hΦi, hΦzero, hcompact, iUnion_mono hCW, hΦfix, himage⟩

end Schoenflies

end

section

namespace Set

private theorem union_subset_iUnion_union_of_subsets
    {X ι : Type*} {C₀ C C₁ : Set X} (U₀ U₁ : ι → Set X)
    (h₀ : C₀ ⊆ ⋃ i, U₀ i) (h : C ⊆ ⋃ i, U₀ i ∩ U₁ i) (h₁ : C₁ ⊆ ⋃ i, U₁ i) :
    (C₀ ∪ C) ∪ C₁ ⊆ ⋃ i, U₀ i ∪ U₁ i := by
  refine union_subset (union_subset ?_ ?_) ?_
  · exact h₀.trans (iUnion_mono fun _ => subset_union_left)
  · exact h.trans (iUnion_mono fun _ => inter_subset_left.trans subset_union_left)
  · exact h₁.trans (iUnion_mono fun _ => subset_union_right)

end Set

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_isotopy_between_finite_affine_corner_replacements_in_neighborhoods
    {ι : Type*} [Finite ι] (e : ι → Plane ≃ᵃ[ℝ] Plane) (U : ι → Set Plane)
    (ε₀ ε₁ R d σ : ι → ℝ) (D : Set Plane)
    (hε₀ : ∀ i, 0 < ε₀ i) (hε₁ : ∀ i, 0 < ε₁ i)
    (hR : ∀ i, 3 * max (ε₀ i) (ε₁ i) < R i)
    (hd : ∀ i, d i = 0 ∨ d i = 1) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j)) :
    let A := fun ε => (D \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
      ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
        {p | 0 ≤ σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)}
    ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧ IsCompact C ∧ C ⊆ ⋃ i, U i ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' A ε₀ = A ε₁ ∧ Φ 1 '' interior (A ε₀) = interior (A ε₁) ∧
      Φ 1 '' frontier (A ε₀) = frontier (A ε₁) := by
  have hKdisj : Pairwise fun i j => Disjoint
      (e i ⁻¹' closedBall (0 : Plane) (R i)) (e j ⁻¹' closedBall (0 : Plane) (R j)) :=
    fun i j hij => (hdisj hij).mono (hKU i) (hKU j)
  have hNU (i : ι) : e i ⁻¹' ball (0 : Plane) (R i) ⊆ U i :=
    (Set.preimage_mono (f := e i)
      (ball_subset_closedBall (x := (0 : Plane)) (ε := R i))).trans (hKU i)
  obtain ⟨Φ, C, hΦ, hi, hz, hC, hCN, hfix, himage⟩ :=
    exists_isotopy_between_finite_affine_corner_replacements
      e ε₀ ε₁ R d σ hε₀ hε₁ hR hd hσ hKdisj
  exact ⟨Φ, C, hΦ, hi, hz, hC, hCN.trans (iUnion_mono hNU), hfix, himage D⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem exists_isotopy_between_native_roundings_of_admissible_widths
    {ι : Type*} [Finite ι] (e : Fin 2 → ι → Plane ≃ᵃ[ℝ] Plane)
    (a b c : ι → Plane) (U : Fin 2 → ι → Set Plane)
    (r d σ δ R : Fin 2 → ι → ℝ) {D : Set Plane}
    (hnorm : ∀ k i, 0 < r k i ∧ e k i (a i) = Plane.mk (-1) 0 ∧
      e k i (b i) = Plane.mk (r k i) (d k i * r k i) ∧ e k i (c i) = 0)
    (hU : ∀ k i, IsOpen (U k i) ∧ c i ∈ U k i)
    (hd : ∀ k i, d k i = 0 ∨ d k i = 1)
    (hstraight : ∀ i, d 0 i = 0 ↔ d 1 i = 0)
    (hσ : ∀ k i, σ k i = -1 ∨ σ k i = 1)
    (hδ : ∀ k i, 0 < δ k i ∧ 3 * δ k i < R k i)
    (hKU : ∀ k i, e k i ⁻¹' closedBall (0 : Plane) (R k i) ⊆ U k i)
    (hdisj : ∀ k, Pairwise fun i j => Disjoint (U k i) (U k j))
    (hside : ∀ k i, ∀ p ∈ U k i, p ∈ D ↔
      0 ≤ σ k i * ((e k i p) 1 - d k i * max ((e k i p) 0) 0))
    (ε : Fin 2 → ι → ℝ) (hε : ∀ k i, 0 < ε k i ∧ ε k i ≤ δ k i) :
    let D' := fun k => (D \ ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
      ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
        {p | 0 ≤ σ k i * ((e k i p) 1 -
          d k i * Real.smoothMax (ε k i) ((e k i p) 0) 0)}
    ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      IsCompact C ∧ C ⊆ ⋃ i, U 0 i ∪ U 1 i ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' D' 0 = D' 1 ∧ Φ 1 '' interior (D' 0) = interior (D' 1) ∧
      Φ 1 '' frontier (D' 0) = frontier (D' 1) := by
  obtain ⟨η, hη, hcompare⟩ := exists_isotopy_between_finite_native_corner_replacements
    e a b c U r d σ δ R hnorm hU hd hstraight hσ hδ hKU hdisj hside
  obtain ⟨H, C, hH, hi, hz, hC, hCW, hfix, himage, _, _⟩ :=
    hcompare η (fun k i => ⟨(hη k i).1, le_rfl⟩)
  let A := fun (k : Fin 2) (ν : ι → ℝ) =>
    (D \ ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
      ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
        {p | 0 ≤ σ k i * ((e k i p) 1 - d k i * Real.smoothMax (ν i) ((e k i p) 0) 0)}
  have hR (k : Fin 2) (i : ι) : 3 * max (ε k i) (η k i) < R k i :=
    (mul_le_mul_of_nonneg_left (max_le (hε k i).2 (hη k i).2.1)
      (by norm_num : (0 : ℝ) ≤ 3)).trans_lt (hδ k i).2
  obtain ⟨H₀, C₀, hH₀, hi₀, hz₀, hC₀, hC₀U, hfix₀, himage₀, _, _⟩ :=
    exists_isotopy_between_finite_affine_corner_replacements_in_neighborhoods
      (e 0) (U 0) (ε 0) (η 0) (R 0) (d 0) (σ 0) D
      (fun i => (hε 0 i).1) (fun i => (hη 0 i).1) (hR 0)
      (hd 0) (hσ 0) (hKU 0) (hdisj 0)
  obtain ⟨H₁, C₁, hH₁, hi₁, hz₁, hC₁, hC₁U, hfix₁, himage₁, _, _⟩ :=
    exists_isotopy_between_finite_affine_corner_replacements_in_neighborhoods
      (e 1) (U 1) (η 1) (ε 1) (R 1) (d 1) (σ 1) D
      (fun i => (hη 1 i).1) (fun i => (hε 1 i).1)
      (fun i => by simpa only [max_comm] using hR 1 i)
      (hd 1) (hσ 1) (hKU 1) (hdisj 1)
  have hsupport : (C₀ ∪ C) ∪ C₁ ⊆ ⋃ i, U 0 i ∪ U 1 i :=
    Set.union_subset_iUnion_union_of_subsets (U 0) (U 1) hC₀U hCW hC₁U
  have himage₀' : H₀ 1 '' A 0 (ε 0) = A 0 (η 0) := himage₀
  have himage₁' : H₁ 1 '' A 1 (η 1) = A 1 (ε 1) := himage₁
  have himage' : H 1 '' A 0 (η 0) = A 1 (η 1) := himage
  obtain ⟨G, _, hG, hGi, hGz, hGC, hGfix, hGimage, _, _⟩ :=
    Diffeomorph.exists_compact_isotopy_image_trans H₀ H
      hH₀ hi₀ hz₀ hC₀ hfix₀ hH hi hz hC hfix himage₀' himage'
  obtain ⟨Φ, _, hΦ, hΦi, hΦz, hΦC, hΦfix, hregion, hinterior, hfrontier⟩ :=
    Diffeomorph.exists_compact_isotopy_image_trans G H₁
      hG hGi hGz hGC hGfix hH₁ hi₁ hz₁ hC₁ hfix₁ hGimage himage₁'
  exact ⟨Φ, (C₀ ∪ C) ∪ C₁, hΦ, hΦi, hΦz, hΦC, hsupport, hΦfix,
    hregion, hinterior, hfrontier⟩

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem normalized_corner_straight_of_straight
    (e₀ e₁ : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {r₀ r₁ d : ℝ} (hr₁ : r₁ ≠ 0)
    (ha₀ : e₀ a = Plane.mk (-1) 0) (hb₀ : e₀ b = Plane.mk r₀ 0) (hc₀ : e₀ c = 0)
    (ha₁ : e₁ a = Plane.mk (-1) 0) (hb₁ : e₁ b = Plane.mk r₁ (d * r₁))
    (hc₁ : e₁ c = 0) : d = 0 := by
  have hv₀ (q : Plane) : e₀.linear (q - c) = e₀ q - e₀ c :=
    e₀.toAffineMap.linearMap_vsub q c
  have hv₁ (q : Plane) : e₁.linear (q - c) = e₁ q - e₁ c :=
    e₁.toAffineMap.linearMap_vsub q c
  have hline : b - c = (-r₀) • (a - c) := by
    apply e₀.linear.injective
    rw [map_smul, hv₀, hv₀, ha₀, hb₀, hc₀, sub_zero, sub_zero]
    ext i
    fin_cases i <;> simp [Plane.mk]
  have he : e₁ b = (-r₀) • Plane.mk (-1) 0 := by
    calc
      e₁ b = e₁.linear (b - c) := by rw [hv₁, hc₁, sub_zero]
      _ = (-r₀) • Plane.mk (-1) 0 := by rw [hline, map_smul, hv₁, ha₁, hc₁, sub_zero]
  have hy := congrArg (fun q : Plane => q 1) (hb₁.symm.trans he)
  change d * r₁ = (-r₀) * 0 at hy
  exact (mul_eq_zero.mp (hy.trans (mul_zero _))).resolve_right hr₁

theorem exists_isotopy_between_normalized_corner_replacements
    {ι : Type*} [Finite ι] (e : Fin 2 → ι → Plane ≃ᵃ[ℝ] Plane)
    (a b c : ι → Plane) (U : Fin 2 → ι → Set Plane)
    (r d σ ε R : Fin 2 → ι → ℝ) {D : Set Plane}
    (hnorm : ∀ k i, 0 < r k i ∧ e k i (a i) = Plane.mk (-1) 0 ∧
      e k i (b i) = Plane.mk (r k i) (d k i * r k i) ∧ e k i (c i) = 0)
    (hU : ∀ k i, IsOpen (U k i))
    (hd : ∀ k i, d k i = 0 ∨ d k i = 1)
    (hσ : ∀ k i, σ k i = -1 ∨ σ k i = 1)
    (hε : ∀ k i, 0 < ε k i) (hR : ∀ k i, 3 * ε k i < R k i)
    (hKU : ∀ k i, e k i ⁻¹' closedBall (0 : Plane) (R k i) ⊆ U k i)
    (hdisj : ∀ k, Pairwise fun i j => Disjoint (U k i) (U k j))
    (hside : ∀ k i, ∀ p ∈ U k i, p ∈ D ↔
      0 ≤ σ k i * ((e k i p) 1 - d k i * max ((e k i p) 0) 0)) :
    let D' := fun k => (D \ ⋃ i, e k i ⁻¹' ball (0 : Plane) (R k i)) ∪
      ⋃ i, (e k i ⁻¹' closedBall (0 : Plane) (R k i)) ∩
        {p | 0 ≤ σ k i * ((e k i p) 1 -
          d k i * Real.smoothMax (ε k i) ((e k i p) 0) 0)}
    ∃ (Φ : ℝ → Plane ≃ₘ[ℝ] Plane) (C : Set Plane),
      ContDiff ℝ ∞ (fun z : ℝ × Plane => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × Plane => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      IsCompact C ∧ C ⊆ ⋃ i, U 0 i ∪ U 1 i ∧
      (∀ t, EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ) ∧
      Φ 1 '' D' 0 = D' 1 ∧ Φ 1 '' interior (D' 0) = interior (D' 1) ∧
      Φ 1 '' frontier (D' 0) = frontier (D' 1) := by
  have hstraight (i : ι) : d 0 i = 0 ↔ d 1 i = 0 := by
    constructor
    · intro h
      have hb : e 0 i (b i) = Plane.mk (r 0 i) 0 := by
        simpa only [h, zero_mul] using (hnorm 0 i).2.2.1
      exact normalized_corner_straight_of_straight (e 0 i) (e 1 i) (r₀ := r 0 i)
        (hnorm 1 i).1.ne' (hnorm 0 i).2.1 hb (hnorm 0 i).2.2.2
        (hnorm 1 i).2.1 (hnorm 1 i).2.2.1 (hnorm 1 i).2.2.2
    · intro h
      have hb : e 1 i (b i) = Plane.mk (r 1 i) 0 := by
        simpa only [h, zero_mul] using (hnorm 1 i).2.2.1
      exact normalized_corner_straight_of_straight (e 1 i) (e 0 i) (r₀ := r 1 i)
        (hnorm 0 i).1.ne' (hnorm 1 i).2.1 hb (hnorm 1 i).2.2.2
        (hnorm 0 i).2.1 (hnorm 0 i).2.2.1 (hnorm 0 i).2.2.2
  have hcU (k : Fin 2) (i : ι) : c i ∈ U k i := by
    apply hKU k i
    change e k i (c i) ∈ closedBall (0 : Plane) (R k i)
    rw [(hnorm k i).2.2.2]
    exact mem_closedBall_self ((mul_pos (by norm_num) (hε k i)).trans (hR k i)).le
  exact exists_isotopy_between_native_roundings_of_admissible_widths e a b c U r d σ ε R
    hnorm (fun k i => ⟨hU k i, hcU k i⟩) hd hstraight hσ
    (fun k i => ⟨hε k i, hR k i⟩) hKU hdisj hside ε (fun k i => ⟨hε k i, le_rfl⟩)

end Schoenflies

end
