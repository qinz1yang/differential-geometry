import DifferentialGeometry.Topology.Diffeomorph.IsotopyInterpolation
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.SphereSeparation.HeightCapRegion
import DifferentialGeometry.Topology.SphereSeparation.HeightCapSaddleIsotopy
import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapExtension

open Set Metric Manifold
open Schoenflies (Plane)
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_diffeomorph_heightCapRegion
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : M → E × ℝ) (G : ℝ → E ≃ₘ[ℝ] E)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    {a b c r R R₀ τ δ : ℝ} (hab : a ≤ b) (hb : b = c - r ^ 2 / 2)
    (hr : 0 < r) (hrR : r < R) (hrR₀ : r ≤ R₀) (hrτ : r ^ 2 / 2 ≤ τ) (hδ : 0 < δ)
    (hmodel : ∀ t ∈ Icc (b - δ) (b + δ), ∀ x ∈ closedBall (0 : E) R,
      G t x = (A (quadraticLevelScaling b c x t, t)).1)
    (hgraph : (closedBall 0 R₀ ×ˢ closedBall c τ) ∩ range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀)
    (hlevels : ∀ t ∈ Icc a b,
      (G t '' closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' sphere 0 r) :
    ∃ D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), (∀ p, (D p).2 = p.2) ∧
      (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (G t x, t)) ∧
      (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : E) ρ, D (x, t) = A (x, t)) ∧
      D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
        heightCapRegion (fun t => G t) A a b c r ∧
      heightCapRegion (fun t => G t) A a b c r ∩ range f =
        D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} := by
  have hbc : b < c := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  obtain ⟨D, hD, hlo, ρ, hrρ, hhi⟩ :=
    Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap G hG hGi A hA hbc hδ hr.le hrR hmodel
  have hhi' (t : ℝ) (ht : b ≤ t) (x : E) (hx : x ∈ closedBall 0 r) : D (x, t) = A (x, t) :=
    hhi t ht x (closedBall_subset_ball hrρ hx)
  refine ⟨D, hD, hlo, ⟨ρ, hrρ, hhi⟩, ?_, ?_⟩
  · exact Function.image_paraboloid_cap_eq_union D A (fun t x => (G t x, t)) hr hab hb hlo hhi'
  · have hinter := heightCapRegion_inter_range f (fun t => G t) A.toEquiv
      hb hr.le hrR₀ hrτ hgraph hlevels
    simp only [Diffeomorph.coe_toEquiv] at hinter
    exact hinter.trans (Function.image_paraboloid_graph_eq_union D A
      (fun t x => (G t x, t)) hr hab hb hlo hhi').symm

theorem exists_diffeomorph_heightCapRegion_of_image_closedBall_eq
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : M → E × ℝ) (G H : ℝ → E ≃ₘ[ℝ] E)
    (hH : ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2))
    (hHi : ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2))
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    {a b c r R R₀ τ δ : ℝ} (hab : a ≤ b) (hb : b = c - r ^ 2 / 2)
    (hr : 0 < r) (hrR : r < R) (hrR₀ : r ≤ R₀) (hrτ : r ^ 2 / 2 ≤ τ) (hδ : 0 < δ)
    (hmodel : ∀ t ∈ Icc (b - δ) (b + δ), ∀ x ∈ closedBall (0 : E) R,
      G t x = (A (quadraticLevelScaling b c x t, t)).1)
    (hgraph : (closedBall 0 R₀ ×ˢ closedBall c τ) ∩ range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀)
    (hlevels : ∀ t ∈ Icc a b,
      (G t '' closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' sphere 0 r)
    (himages : ∀ t ∈ Icc a b, H t '' closedBall 0 r = G t '' closedBall 0 r)
    (hupper : ∀ t ∈ Icc (b - δ) (b + δ), EqOn (H t) (G t) (closedBall 0 R)) :
    ∃ D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), (∀ p, (D p).2 = p.2) ∧
      (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (H t x, t)) ∧
      (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : E) ρ, D (x, t) = A (x, t)) ∧
      D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
        heightCapRegion (fun t => G t) A a b c r ∧
      heightCapRegion (fun t => G t) A a b c r ∩ range f =
        D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} := by
  have hspheres (t : ℝ) (ht : t ∈ Icc a b) : H t '' sphere 0 r = G t '' sphere 0 r := by
    have hh := congrArg frontier (himages t ht)
    change frontier ((H t).toHomeomorph '' closedBall 0 r) =
      frontier ((G t).toHomeomorph '' closedBall 0 r) at hh
    rw [← (H t).toHomeomorph.image_frontier, ← (G t).toHomeomorph.image_frontier,
      frontier_closedBall _ hr.ne'] at hh
    exact hh
  have hcontact (t : ℝ) (ht : t ∈ Icc a b) :
      (H t '' closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        H t '' sphere 0 r := by
    rw [himages t ht, hspheres t ht]
    exact hlevels t ht
  obtain ⟨D, hD, hlo, hhi, hregion, hinter⟩ :=
    exists_diffeomorph_heightCapRegion f H hH hHi A hA hab hb hr hrR hrR₀ hrτ hδ
      (fun t ht x hx => (hupper t ht hx).trans (hmodel t ht x hx)) hgraph hcontact
  have heq := heightCapRegion_eq_of_image_closedBall_eq (A := A) (c := c) himages
  rw [heq] at hregion hinter
  exact ⟨D, hD, hlo, hhi, hregion, hinter⟩

theorem exists_diffeomorph_heightCapRegion_eqOn_of_image_sphere_eq
    {M : Type*} (f : M → Plane × ℝ) (G P : ℝ → Plane ≃ₘ[ℝ] Plane)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × Plane => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (G z.1).symm z.2))
    (hP : ContDiff ℝ ∞ (fun z : ℝ × Plane => P z.1 z.2))
    (hPi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (P z.1).symm z.2))
    (A : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    {a b c r R R₀ τ δ u v t₀ : ℝ}
    (hau : a ≤ u) (hut₀ : u < t₀) (ht₀v : t₀ < v) (hvb : v < b)
    (hb : b = c - r ^ 2 / 2) (hr : 0 < r) (hrR : r < R)
    (hrR₀ : r ≤ R₀) (hrτ : r ^ 2 / 2 ≤ τ) (hδ : 0 < δ)
    (hmodel : ∀ t ∈ Icc (b - δ) (b + δ), ∀ x ∈ closedBall (0 : Plane) R,
      G t x = (A (quadraticLevelScaling b c x t, t)).1)
    (hgraph : (closedBall 0 R₀ ×ˢ closedBall c τ) ∩ range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀)
    (hlevels : ∀ t ∈ Icc a b,
      (G t '' closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' sphere 0 r)
    (hP₀ : P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞)
    (hcircle : ∀ t ∈ Ioo u v, P t '' (G t₀ '' sphere 0 r) = G t '' sphere 0 r) :
    ∃ ε > 0, Ioo (t₀ - ε) (t₀ + ε) ⊆ Ioo a b ∧
      ∃ F : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => F z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (F z.1).symm z.2) ∧
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ x, F t x = P t (G t₀ x)) ∧
        EqOn F G (Ioo u v)ᶜ ∧
        (∀ t, F t '' closedBall 0 r = G t '' closedBall 0 r) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ p, (D p).2 = p.2) ∧
        (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (F t x, t)) ∧
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ x,
          D (quadraticLevelScaling b c x t, t) = (P t (G t₀ x), t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D (x, t) = A (x, t)) ∧
        D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A a b c r ∧
        heightCapRegion (fun t => G t) A a b c r ∩ range f =
          D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} := by
  let Q (t : ℝ) := (G t₀).trans (P t)
  have hQ : ContDiff ℝ ∞ (fun z : ℝ × Plane => Q z.1 z.2) :=
    hP.comp (contDiff_fst.prodMk ((G t₀).contDiff.comp contDiff_snd))
  have hQi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (Q z.1).symm z.2) :=
    (G t₀).symm.contDiff.comp hPi
  have hQ₀ : Q t₀ = G t₀ := by
    ext x : 1
    change P t₀ (G t₀ x) = G t₀ x
    rw [hP₀]
    rfl
  have hQcircle (t : ℝ) (ht : t ∈ Ioo u v) : Q t '' sphere 0 r = G t '' sphere 0 r := by
    change (fun x => P t (G t₀ x)) '' sphere 0 r = _
    rw [← image_image]
    exact hcircle t ht
  have hQdisk (t : ℝ) (ht : t ∈ Ioo u v) :
      Q t '' closedBall 0 r = G t '' closedBall 0 r := by
    exact DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_sphere_eq
      (Q t).toHomeomorph (G t).toHomeomorph 0 0 hr hr (hQcircle t ht)
  obtain ⟨ψ, ε, hε, _, _, hεsub, _, _, F, hF, hFi, _, hFQ, hFout, hFdisk⟩ :=
    Diffeomorph.exists_contDiff_family_eqOn_of_image_eq G Q hG hGi hQ hQi hut₀ ht₀v hQ₀ hQdisk
  have hεab : Ioo (t₀ - ε) (t₀ + ε) ⊆ Ioo a b := by
    intro t ht
    exact ⟨hau.trans_lt (hεsub ht).1, (hεsub ht).2.trans hvb⟩
  let δ₁ := min δ ((b - v) / 2)
  have hδ₁ : 0 < δ₁ := lt_min hδ (half_pos (sub_pos.mpr hvb))
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  have hδ₁v : δ₁ ≤ (b - v) / 2 := min_le_right _ _
  have hupper (t : ℝ) (ht : t ∈ Icc (b - δ₁) (b + δ₁)) : F t = G t := by
    apply hFout
    intro htuv
    linarith [ht.1, htuv.2]
  have hmodel₁ (t : ℝ) (ht : t ∈ Icc (b - δ₁) (b + δ₁))
      (x : Plane) (hx : x ∈ closedBall 0 R) :
      G t x = (A (quadraticLevelScaling b c x t, t)).1 :=
    hmodel t ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx
  obtain ⟨D, hD, hlo, hhi, hregion, hinter⟩ :=
    exists_diffeomorph_heightCapRegion_of_image_closedBall_eq f G F hF hFi A hA
      (hau.trans (hut₀.trans (ht₀v.trans hvb)).le) hb hr hrR hrR₀ hrτ hδ₁
      hmodel₁ hgraph hlevels (fun t _ => hFdisk t)
      (fun t ht x _ => congrArg (fun Z : Plane ≃ₘ[ℝ] Plane => Z x) (hupper t ht))
  refine ⟨ε, hε, hεab, F, hF, hFi, ?_, hFout, hFdisk, D, hD, hlo, ?_, hhi,
    hregion, hinter⟩
  · intro t ht x
    exact congrArg (fun Z : Plane ≃ₘ[ℝ] Plane => Z x) (hFQ ht)
  · intro t ht x
    rw [hlo t (hεab ht).2.le x, hFQ ht]
    rfl

theorem exists_height_cap_diffeomorph_and_level_isotopy
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
          (∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, r < R ∧
            ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - δ) (e p 2 - r ^ 2 / 2 + δ),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm (A (x, e p 2 - r ^ 2 / 2)).1) =
                  (A (quadraticLevelScaling (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1) ∧
          let c := e p 2
          let b := c - r ^ 2 / 2
          let G : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
            fun t y => Φ t ((Φ b).symm (A (y, b)).1)
          ∃ D : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
            (∀ z, (D z).2 = z.2) ∧
            (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (G t x, t)) ∧
            (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
              D (x, t) = A (x, t)) ∧
            D '' {z | a ≤ z.2 ∧ z.2 ≤ c - ‖z.1‖ ^ 2 / 2} = heightCapRegion G A a b c r ∧
            heightCapRegion G A a b c r ∩ range (EuclideanSpace.equivProdLast 2 ∘ e) =
              D '' {z | a ≤ z.2 ∧ z.2 = c - ‖z.1‖ ^ 2 / 2} := by
  obtain ⟨r, hr, hab, A, hA, hbox, hcap, Φ, hΦ, hΦi, hΦa, hlevels, hdisks,
      hsupport, hlower, hupper⟩ :=
    exists_height_level_isotopy_saddle_cap_normal_form he hnd hmax B₀ hUβ hβ hgraphβ
      hK hKUβ hKreg hKlevel ha hregular
  refine ⟨r, hr, hab, A, hA, hbox, hcap, Φ, hΦ, hΦi, hΦa, hlevels, hdisks,
    hsupport, hlower, hupper, ?_⟩
  let c := e p 2
  let b := c - r ^ 2 / 2
  let A' : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ),
      (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    { toEquiv := A.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.symm.contMDiff }
  let A_b := A'.restrictFiber hA b
  let G (t : ℝ) := A_b.trans ((Φ b).symm.trans (Φ t))
  have hG : ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => G z.1 z.2) :=
    hΦ.comp (contDiff_fst.prodMk ((Φ b).symm.contDiff.comp (A_b.contDiff.comp contDiff_snd)))
  have hGi : ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (G z.1).symm z.2) :=
    A_b.symm.contDiff.comp ((Φ b).contDiff.comp hΦi)
  obtain ⟨R₀, τ, hrR₀, _, hrτ, hnormal⟩ := hbox
  obtain ⟨δ, hδ, R, hrR, hmodel⟩ := hupper
  have hnormal' : (closedBall 0 R₀ ×ˢ closedBall c τ) ∩
      range (A.symm ∘ (EuclideanSpace.equivProdLast 2 ∘ e)) =
        (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀ := by
    simpa only [Function.comp_def, neg_div, one_div, neg_mul, one_mul,
      sub_eq_add_neg, div_eq_mul_inv, mul_comm] using hnormal
  have hGcoe (t : ℝ) : ⇑(G t) = fun y => Φ t ((Φ b).symm (A (y, b)).1) := rfl
  have hlevels' : ∀ t ∈ Icc a b,
      (G t '' closedBall 0 r) ∩
          ((fun x => ((EuclideanSpace.equivProdLast 2 ∘ e) x).1) ''
            {x | ((EuclideanSpace.equivProdLast 2 ∘ e) x).2 = t}) = G t '' sphere 0 r := by
    simpa only [hGcoe, Function.comp_def, EuclideanSpace.equivProdLast_snd,
      show (Fin.last 2 : Fin 3) = 2 by decide] using hdisks
  exact exists_diffeomorph_heightCapRegion (EuclideanSpace.equivProdLast 2 ∘ e) G hG hGi
    A hA hab.le rfl hr hrR hrR₀.le hrτ.le hδ hmodel hnormal' hlevels'

theorem exists_diffeomorph_eqOn_upper_half_space_of_level_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P F : ℝ → E ≃ₘ[ℝ] E)
    (hP : ContDiff ℝ ∞ (fun z : ℝ × E => P z.1 z.2))
    (hPi : ContDiff ℝ ∞ (fun z : ℝ × E => (P z.1).symm z.2))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ ∞ (fun z : ℝ × E => (F z.1).symm z.2))
    (D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hD : ∀ p, (D p).2 = p.2)
    {b c d ε : ℝ} (hε : 0 < ε) (heq : EqOn P F (Ioo (d - ε) (d + ε)))
    (hmodel : ∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (F t x, t)) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E,
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      EqOn H P (Iio (d + ε)) ∧ EqOn H F (Ioi (d - ε)) ∧
      ∃ D' : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), (∀ p, (D' p).2 = p.2) ∧
        EqOn D' D {p | d - ε < p.2} ∧
        (∀ t ≤ b, ∀ x, D' (quadraticLevelScaling b c x t, t) = (H t x, t)) ∧
        (∀ S ⊆ {p : E × ℝ | d ≤ p.2}, D' '' S = D '' S) ∧
        ∀ t ≤ b, t < d + ε → ∀ x,
          D' (quadraticLevelScaling b c x t, t) = (P t x, t) := by
  obtain ⟨H, hH, hHi, hHP, hHF⟩ :=
    Diffeomorph.exists_contDiff_family_eqOn_Iio_Ioi P F hP hPi hF hFi hε heq
  let Ξ : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => ((F t).symm.trans (H t)).toEquiv)
      contMDiff_toFun :=
        ((hH.comp (contDiff_snd.prodMk
          (hFi.comp (contDiff_snd.prodMk contDiff_fst)))).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hF.comp (contDiff_snd.prodMk
          (hHi.comp (contDiff_snd.prodMk contDiff_fst)))).prodMk contDiff_snd).contMDiff }
  let D' := D.trans Ξ
  have hD' (p : E × ℝ) : D' p = (H p.2 ((F p.2).symm (D p).1), p.2) := by
    change (H (D p).2 ((F (D p).2).symm (D p).1), (D p).2) = _
    rw [hD p]
  have heqD : EqOn D' D {p | d - ε < p.2} := by
    intro p hp
    rw [hD', hHF hp, (F p.2).apply_symm_apply]
    exact Prod.ext rfl (hD p).symm
  have hmodel' (t : ℝ) (ht : t ≤ b) (x : E) :
      D' (quadraticLevelScaling b c x t, t) = (H t x, t) := by
    rw [hD', hmodel t ht]
    simp only [Diffeomorph.symm_apply_apply]
  refine ⟨H, hH, hHi, hHP, hHF, D', (by intro p; rw [hD']),
    heqD, hmodel', ?_, ?_⟩
  · intro S hS
    apply image_congr
    intro p hp
    have hpd : d ≤ p.2 := hS hp
    exact heqD (by change d - ε < p.2; linarith)
  · intro t ht htd x
    rw [hmodel' t ht, hHP htd]

theorem exists_diffeomorph_heightCapRegion_eqOn_lower_family
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : M → E × ℝ) (G P F : ℝ → E ≃ₘ[ℝ] E)
    (hP : ContDiff ℝ ∞ (fun z : ℝ × E => P z.1 z.2))
    (hPi : ContDiff ℝ ∞ (fun z : ℝ × E => (P z.1).symm z.2))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ ∞ (fun z : ℝ × E => (F z.1).symm z.2))
    (A D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hD : ∀ p, (D p).2 = p.2)
    {a b c d r ε : ℝ} (had : a ≤ d) (hdb : d ≤ b)
    (hb : b = c - r ^ 2 / 2) (hr : 0 < r) (hε : 0 < ε)
    (hP₀ : P d = Diffeomorph.refl 𝓘(ℝ, E) E ∞)
    (hFP : ∀ t ∈ Ioo (d - ε) (d + ε), ∀ x, F t x = P t (G d x))
    (hFdisk : ∀ t ∈ Icc d b, F t '' closedBall 0 r = G t '' closedBall 0 r)
    (hlo : ∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (F t x, t))
    (hhi : ∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : E) ρ, D (x, t) = A (x, t))
    (hregion : D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
      heightCapRegion (fun t => G t) A a b c r)
    (hinter : heightCapRegion (fun t => G t) A a b c r ∩ range f =
      D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2}) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E,
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H d = G d ∧
      (∀ t < d + ε, H t = (G d).trans (P t)) ∧
      (∀ t, d - ε < t → H t = F t) ∧
      ∃ D' : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), (∀ p, (D' p).2 = p.2) ∧
        EqOn D' D {p | d - ε < p.2} ∧
        (∀ t ≤ b, ∀ x, D' (quadraticLevelScaling b c x t, t) = (H t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : E) ρ, D' (x, t) = A (x, t)) ∧
        D' '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A d b c r ∧
        heightCapRegion (fun t => G t) A d b c r ∩ range f =
          D' '' {p | d ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} ∧
        ∀ t ≤ b, t < d + ε → ∀ x,
          D' (quadraticLevelScaling b c x t, t) = (P t (G d x), t) := by
  let Q (t : ℝ) := (G d).trans (P t)
  have hQ : ContDiff ℝ ∞ (fun z : ℝ × E => Q z.1 z.2) :=
    hP.comp (contDiff_fst.prodMk ((G d).contDiff.comp contDiff_snd))
  have hQi : ContDiff ℝ ∞ (fun z : ℝ × E => (Q z.1).symm z.2) :=
    (G d).symm.contDiff.comp hPi
  have hQF : EqOn Q F (Ioo (d - ε) (d + ε)) := by
    intro t ht
    ext x : 1
    exact (hFP t ht x).symm
  obtain ⟨H, hH, hHi, hHQ, hHF, D', hD', hD'eq, hD'lo, hD'images, hD'lower⟩ :=
    exists_diffeomorph_eqOn_upper_half_space_of_level_family Q F hQ hQi hF hFi D hD hε hQF hlo
  have hH₀ : H d = G d := by
    rw [hHQ (by change d < d + ε; linarith)]
    ext x : 1
    change P d (G d x) = _
    rw [hP₀]
    rfl
  obtain ⟨ρ, hrρ, hρ⟩ := hhi
  have hD'hi (t : ℝ) (ht : b ≤ t) (x : E) (hx : x ∈ ball 0 ρ) :
      D' (x, t) = A (x, t) := by
    rw [hD'eq (by change d - ε < t; linarith)]
    exact hρ t ht x hx
  have hDhi (t : ℝ) (ht : b ≤ t) (x : E) (hx : x ∈ closedBall 0 r) :
      D (x, t) = A (x, t) := hρ t ht x (closedBall_subset_ball hrρ hx)
  have hraised : D '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
      heightCapRegion (fun t => G t) A d b c r := by
    have hh := Function.image_paraboloid_cap_eq_union D A (fun t x => (F t x, t))
      hr hdb hb hlo hDhi
    exact hh.trans (heightCapRegion_eq_of_image_closedBall_eq hFdisk)
  have hraisedcontact :
      (D '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2}) ∩ range f =
        D '' {p | d ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} := by
    have hcontact :
        (D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2}) ∩ range f =
          D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} := by
      rw [hregion]
      exact hinter
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      obtain ⟨z, hz, hzx⟩ := hcontact.subset ⟨⟨x, ⟨had.trans hx.1, hx.2⟩, rfl⟩, hy⟩
      have heq : z = x := D.injective hzx
      subst z
      exact ⟨x, ⟨hx.1, hz.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩,
        (hcontact.symm.subset ⟨x, ⟨had.trans hx.1, hx.2⟩, rfl⟩).2⟩
  have hcapimages : D' '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
      D '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} :=
    hD'images _ (fun _ hp => hp.1)
  have hgraphimages : D' '' {p | d ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} =
      D '' {p | d ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} :=
    hD'images _ (fun _ hp => hp.1)
  refine ⟨H, hH, hHi, hH₀, hHQ, hHF, D', hD', hD'eq, hD'lo,
    ⟨ρ, hrρ, hD'hi⟩, hcapimages.trans hraised, ?_, hD'lower⟩
  rw [← hraised, hraisedcontact, ← hgraphimages]

theorem exists_diffeomorph_heightCapRegion_lower_family_of_image_sphere_eq
    {M : Type*} (f : M → Plane × ℝ) (G P : ℝ → Plane ≃ₘ[ℝ] Plane)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × Plane => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (G z.1).symm z.2))
    (hP : ContDiff ℝ ∞ (fun z : ℝ × Plane => P z.1 z.2))
    (hPi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (P z.1).symm z.2))
    (A : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    {a b c d r R R₀ τ δ η : ℝ}
    (ha : a ≤ d - η) (hbnd : d + η < b) (hη : 0 < η)
    (hb : b = c - r ^ 2 / 2) (hr : 0 < r) (hrR : r < R)
    (hrR₀ : r ≤ R₀) (hrτ : r ^ 2 / 2 ≤ τ) (hδ : 0 < δ)
    (hmodel : ∀ t ∈ Icc (b - δ) (b + δ), ∀ x ∈ closedBall (0 : Plane) R,
      G t x = (A (quadraticLevelScaling b c x t, t)).1)
    (hgraph : (closedBall 0 R₀ ×ˢ closedBall c τ) ∩ range (A.symm ∘ f) =
      (fun y => (y, c - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀)
    (hlevels : ∀ t ∈ Icc a b,
      (G t '' closedBall 0 r) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) =
        G t '' sphere 0 r)
    (hP₀ : P d = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞)
    (hcircle : ∀ t ∈ Ioo (d - η) (d + η),
      P t '' (G d '' sphere 0 r) = G t '' sphere 0 r) :
    ∃ ε > 0, ε ≤ η ∧ Ioo (d - ε) (d + ε) ⊆ Ioo a b ∧
      ∃ F : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => F z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (F z.1).symm z.2) ∧
        (∀ t ∈ Ioo (d - ε) (d + ε), ∀ x, F t x = P t (G d x)) ∧
        EqOn F G (Ioo (d - η) (d + η))ᶜ ∧
        (∀ t, F t '' closedBall 0 r = G t '' closedBall 0 r) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ p, (D p).2 = p.2) ∧
        (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (F t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D (x, t) = A (x, t)) ∧
        D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A a b c r ∧
        heightCapRegion (fun t => G t) A a b c r ∩ range f =
          D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} ∧
      ∃ H : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
        H d = G d ∧
        (∀ t < d + ε, H t = (G d).trans (P t)) ∧
        (∀ t, d - ε < t → H t = F t) ∧
      ∃ D' : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ p, (D' p).2 = p.2) ∧
        EqOn D' D {p | d - ε < p.2} ∧
        (∀ t ≤ b, ∀ x, D' (quadraticLevelScaling b c x t, t) = (H t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D' (x, t) = A (x, t)) ∧
        D' '' {p | d ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A d b c r ∧
        heightCapRegion (fun t => G t) A d b c r ∩ range f =
          D' '' {p | d ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} ∧
        ∀ t ≤ b, t < d + ε → ∀ x,
          D' (quadraticLevelScaling b c x t, t) = (P t (G d x), t) := by
  obtain ⟨ε₀, hε₀, hε₀sub, F, hF, hFi, hFP, hFout, hFdisk,
      D, hD, hlo, _, hhi, hregion, hinter⟩ :=
    exists_diffeomorph_heightCapRegion_eqOn_of_image_sphere_eq f G P hG hGi hP hPi A hA
      ha (by linarith) (by linarith) hbnd hb hr hrR hrR₀ hrτ hδ
      hmodel hgraph hlevels hP₀ hcircle
  let ε := min ε₀ η
  have hε : 0 < ε := lt_min hε₀ hη
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hεsub : Ioo (d - ε) (d + ε) ⊆ Ioo (d - ε₀) (d + ε₀) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hFP' : ∀ t ∈ Ioo (d - ε) (d + ε), ∀ x, F t x = P t (G d x) :=
    fun t ht => hFP t (hεsub ht)
  obtain ⟨H, hH, hHi, hH₀, hHP, hHF, D', hD', hD'eq, hD'lo,
      hD'hi, hraised, hcontact, hD'lower⟩ :=
    exists_diffeomorph_heightCapRegion_eqOn_lower_family f G P F hP hPi hF hFi A D hD
      (by linarith : a ≤ d) (by linarith : d ≤ b) hb hr hε hP₀ hFP'
      (fun t _ => hFdisk t) hlo hhi hregion hinter
  exact ⟨ε, hε, hεη, hεsub.trans hε₀sub, F, hF, hFi, hFP', hFout, hFdisk,
    D, hD, hlo, hhi, hregion, hinter, H, hH, hHi, hH₀, hHP, hHF,
    D', hD', hD'eq, hD'lo, hD'hi, hraised, hcontact, hD'lower⟩

end DifferentialGeometry.Topology.SphereSeparation
