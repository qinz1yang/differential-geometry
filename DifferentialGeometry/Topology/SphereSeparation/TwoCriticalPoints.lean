import DifferentialGeometry.Topology.SphereSeparation.HeightDiskFamily
import DifferentialGeometry.Topology.Diffeomorph.QuadraticCaps
import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapCollar
import DifferentialGeometry.Topology.Handle.QuadraticCapsule
import DifferentialGeometry.Topology.Morse.SurfaceEulerCharacteristic

open Set Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Handle

namespace DifferentialGeometry.Topology.SphereSeparation

open Schoenflies (Plane)

private theorem exists_diffeomorph_image_sphere_of_nondegenerate_extrema
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p q : SphereTwo}
    (hp : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hq : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) q)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2)
    (hmax : ∀ x, x ≠ q → e x 2 < e q 2) (hpq : p ≠ q)
    (hcrit : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p ∨ x = q) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range e := by
  obtain ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁, C, hC,
      δ, hδ, hδhalf, hrad, G, hG, hGi, hlevels, η, hη, _, _, V, hV, hVr, h₀, h₁⟩ :=
    exists_height_disk_family_eqOn_extremum_neighborhoods he hp hq hmin hmax hpq hcrit
  obtain ⟨ηF, hηF, F, hF, hFside, _, hFgraph, _⟩ :=
    Diffeomorph.exists_diffeomorph_quadratic_cap_eqOn_radial_collar
      (c := e q 2) C hr hδ hδhalf hC
      (fun x hx s hs => (hrad x hx s hs).1) (fun x hx s hs => (hrad x hx s hs).2)
  obtain ⟨ε, τ, hε, hεr, hεh, hτ, hτmin, _, hτgap, hR₀, hR₁⟩ :=
    exists_quadraticCapsule_cap_intervals hr hab (lt_min hη hηF)
  let c₀ := e p 2
  let c₁ := e q 2
  let a := c₀ + r ^ 2 / 2
  let b := c₁ - r ^ 2 / 2
  let R : ℝ → ℝ := fun t =>
    quadraticCapsuleRadius ε (2 * r) ((c₁ - c₀) / 2) (t - (c₀ + c₁) / 2)
  have hshift (t : ℝ) : t ∈ Ioo c₀ c₁ →
      t - (c₀ + c₁) / 2 ∈ Ioo (-((c₁ - c₀) / 2)) ((c₁ - c₀) / 2) := by
    intro ht
    constructor <;> linarith [ht.1, ht.2]
  have hR : ContDiffOn ℝ ∞ R (Ioo c₀ c₁) :=
    (contDiffOn_quadraticCapsuleRadius hε hεr hεh).comp
      (contDiff_id.sub contDiff_const).contDiffOn hshift
  have hRpos : ∀ t ∈ Ioo c₀ c₁, 0 < R t := fun t ht =>
    quadraticCapsuleRadius_pos hε hεr hεh (hshift t ht)
  have hRnonneg : ∀ t, 0 ≤ R t := fun _ => Real.sqrt_nonneg _
  obtain ⟨Q, hQball, hQsphere⟩ :=
    exists_diffeomorph_quadraticCapsule_eq_radius 2 hε hεr hεh ((c₀ + c₁) / 2)
  have hleft : (c₀ + c₁) / 2 - (c₁ - c₀) / 2 = c₀ := by ring
  have hright : (c₀ + c₁) / 2 + (c₁ - c₀) / 2 = c₁ := by ring
  rw [hleft, hright] at hQball hQsphere
  have hQ : ∀ z ∈ closedBall (0 : EuclideanThree) 1,
      (Q z).2 ∈ Icc c₀ c₁ ∧ ‖(Q z).1‖ ≤ R (Q z).2 := by
    intro z hz
    exact hQball.subset (mem_image_of_mem Q hz)
  obtain ⟨D, hD₀, hDmid, hD₁⟩ :=
    Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap_charts
      Q A₀ A₁ F C G hA₀ hA₁ hG hGi hr zero_lt_one (a := a) (b := b) rfl rfl
      hτ (hτmin.trans (min_le_left _ _)) (by dsimp [a, b, c₀, c₁]; linarith)
      hR hRpos hR₀ hR₁ hQ hV hVr h₀ h₁
      (fun z hz => hF z (hz.trans (hτmin.trans (min_le_right _ _)))) hFside
  have hca : c₀ < a := by dsimp [a]; nlinarith [sq_pos_of_pos hr]
  have hbc : b < c₁ := by dsimp [b]; nlinarith [sq_pos_of_pos hr]
  have hDs := Function.image_eq_union_of_quadratic_cap_formulas Q D (sphere 0 1)
    A₀ A₁ F (fun t => G t) C R hr hab.le hQsphere
    (fun t _ => hRnonneg t) (fun t ht => hRpos t ⟨hca.trans ht.1, ht.2.trans hbc⟩)
    (fun t ht => hR₀ t ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht => hR₁ t ⟨by linarith [ht.1], ht.2⟩) hC hFgraph
    (fun z hz ht => hD₀ z (sphere_subset_closedBall hz) (by dsimp [a, c₀]; linarith))
    (fun z hz ht => hDmid z (sphere_subset_closedBall hz) ht)
    (fun z hz ht => hD₁ z (sphere_subset_closedBall hz) (by dsimp [b, c₁]; linarith))
  let S := (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2).toDiffeomorph
  let f : SphereTwo → Plane × ℝ := S ∘ e
  have hfheight (x : SphereTwo) : (f x).2 = e x 2 := by
    exact EuclideanSpace.equivProdLast_snd 2 (e x)
  have hmiddle : (fun z : Plane × ℝ => (G z.2 z.1, z.2)) ''
      (sphere 0 r ×ˢ Ioo a b) = f '' {x | (f x).2 ∈ Ioo a b} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      obtain ⟨x, hx, heq⟩ := (hlevels t ⟨ht.1.le, ht.2.le⟩).subset ⟨y, hy, rfl⟩
      have hxt : (f x).2 = t := (hfheight x).trans hx
      exact ⟨x, by change (f x).2 ∈ Ioo a b; rw [hxt]; exact ht, Prod.ext heq hxt⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, heq⟩ := (hlevels (f x).2 ⟨hx.1.le, hx.2.le⟩).symm.subset
        ⟨x, (hfheight x).symm, rfl⟩
      exact ⟨(y, (f x).2), ⟨hy, hx⟩, Prod.ext heq rfl⟩
  have hcap₀' : f '' {x | (f x).2 ≤ a} =
      (fun x => A₀ (x, c₀ + ‖x‖ ^ 2 / 2)) '' closedBall 0 r := by
    simp only [hfheight]
    change (EuclideanSpace.equivProdLast 2 ∘ e) '' _ = _
    simpa only [one_div, inv_mul_eq_div] using hcap₀
  have hcap₁' : f '' {x | b ≤ (f x).2} =
      (fun x => A₁ (x, c₁ - ‖x‖ ^ 2 / 2)) '' closedBall 0 r := by
    simp only [hfheight]
    change (EuclideanSpace.equivProdLast 2 ∘ e) '' _ = _
    simpa only [neg_div, one_div, neg_mul, inv_mul_eq_div, ← sub_eq_add_neg] using hcap₁
  have hDrange : D '' sphere 0 1 = range f := by
    rw [hDs, ← hcap₀', ← hcap₁', hmiddle, ← image_union, ← image_union]
    have hcover : {x | (f x).2 ≤ a} ∪ {x | (f x).2 ∈ Ioo a b} ∪
        {x | b ≤ (f x).2} = univ := by
      ext x
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      by_cases hlo : (f x).2 ≤ a
      · exact Or.inl (Or.inl hlo)
      · by_cases hhi : b ≤ (f x).2
        · exact Or.inr hhi
        · exact Or.inl (Or.inr ⟨lt_of_not_ge hlo, lt_of_not_ge hhi⟩)
    rw [hcover, image_univ]
  refine ⟨D.trans S.symm, ?_⟩
  change (S.symm ∘ D) '' sphere 0 1 = range e
  rw [image_comp, hDrange, show f = S ∘ e from rfl, range_comp]
  exact S.symm_image_image (range e)


theorem exists_diffeomorph_image_sphere_of_ncard_criticalPoints_eq_two
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hcard : {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}.ncard = 2) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range e := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  let : Infinite SphereTwo := by
    let p : SphereTwo := ⟨EuclideanSpace.single 0 1, by simp⟩
    exact Infinite.of_injective (f := (stereographic' 2 p).symm)
      ((stereographic' 2 p).symm.isOpenEmbedding (by simp)).injective
  have hinj := injOn_criticalPoints_of_ncard_eq_two hf.continuous hcard
  obtain ⟨p, q, hpq, hset, hb, hp, hq⟩ :=
    exists_min_max_of_ncard_criticalPoints_eq_two hf.continuous hinj hcard
  have hpc : IsCriticalPointAt (𝓡 2) (fun y => e y 2) p := by
    change p ∈ {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}
    rw [hset]
    exact mem_insert p {q}
  have hqc : IsCriticalPointAt (𝓡 2) (fun y => e y 2) q := by
    change q ∈ {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}
    rw [hset]
    exact mem_insert_of_mem p (mem_singleton q)
  refine exists_diffeomorph_image_sphere_of_nondegenerate_extrema he (hnd p hpc) (hnd q hqc)
    (fun x hx => lt_of_le_of_ne (hb x).1 (fun h => hx ((hp x).mp h.symm)))
    (fun x hx => lt_of_le_of_ne (hb x).2 (fun h => hx ((hq x).mp h)))
    (fun h => hpq.ne (congrArg (fun x => e x 2) h)) ?_
  intro x hx
  have hmem : x ∈ ({p, q} : Set SphereTwo) := hset.subset hx
  simpa only [mem_insert_iff, mem_singleton_iff] using hmem

theorem exists_diffeomorph_image_sphere_of_no_saddles
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x})
    (hno : ∀ p, IsCriticalPointAt (𝓡 2) (fun y => e y 2) p → sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) ≠ 1) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range e := by
  apply exists_diffeomorph_image_sphere_of_ncard_criticalPoints_eq_two he hnd
  exact ncard_criticalPoints_sphere_two_of_no_saddles
    ((EuclideanSpace.proj 2).contMDiff.comp he.contMDiff) hnd hinj hno

end DifferentialGeometry.Topology.SphereSeparation
