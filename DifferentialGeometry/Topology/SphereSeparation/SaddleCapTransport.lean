import DifferentialGeometry.Topology.Morse.RegularLevel.CriticalSeparation
import DifferentialGeometry.Topology.Morse.RegularLevel.SaddleTransport
import DifferentialGeometry.Topology.PlanarJordan.SaddleCapSides

open Set Metric Manifold
open scoped ContDiff
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE (saddleBandVectorField)
open Schoenflies (Plane)

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_uniform_box_clearance {M : Type*} [TopologicalSpace M] [CompactSpace M]
    {g : M → ℝ × ℝ} (hg : Continuous g)
    {Φ : ℝ → M → M} (hΦ : Continuous (fun p : ℝ × M => Φ p.1 p.2))
    (hzero : ∀ x, Φ 0 x = x) {h b v Q : ℝ} (hb : h < b) (hQ : v < Q) :
    ∃ ε > 0, ∀ t ∈ Icc (-ε) ε, ∀ x,
      g x ∉ Ioo (-b) b ×ˢ Ioo (-Q) Q →
        g (Φ t x) ∉ Icc (-h) h ×ˢ Icc (-v) v := by
  let K := g ⁻¹' (Ioo (-b) b ×ˢ Ioo (-Q) Q)ᶜ
  have hK : IsCompact K := ((isOpen_Ioo.prod isOpen_Ioo).isClosed_compl.preimage hg).isCompact
  have hsmall : Icc (-h) h ×ˢ Icc (-v) v ⊆ Ioo (-b) b ×ˢ Ioo (-Q) Q := by
    intro z hz
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hgood : IsOpen {p : ℝ × M | g (Φ p.1 p.2) ∉ Icc (-h) h ×ˢ Icc (-v) v} :=
    (isClosed_Icc.prod isClosed_Icc).isOpen_compl.preimage (hg.comp hΦ)
  have hslice : ({0} : Set ℝ) ×ˢ K ⊆ {p : ℝ × M | g (Φ p.1 p.2) ∉ Icc (-h) h ×ˢ Icc (-v) v} := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := ht
    subst t
    change g (Φ 0 x) ∉ Icc (-h) h ×ˢ Icc (-v) v
    rw [hzero]
    exact fun hs => hx (hsmall hs)
  obtain ⟨T, V, hT, _, h0T, hKV, hTV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hgood hslice
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.mp hT 0 (h0T rfl)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht x hx
  apply hTV (a := (t, x))
  refine ⟨hεT ?_, hKV hx⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

private theorem isCompact_and_subset_regular_saddle_band
    {M : Type*} [TopologicalSpace M] {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hβ : ContinuousOn β U) {h b Q d c s : ℝ} (hs : 0 < s)
    (hb : b < 1) (hd : d < s * h ^ 2)
    (hbox : Icc (-b) b ×ˢ Icc (-Q) Q ⊆ U) :
    let C := β '' {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
      h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d}
    IsCompact C ∧ C ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} := by
  let L := {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
    h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d}
  have hsq : IsClosed {z : ℝ × ℝ | h ^ 2 ≤ z.1 ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  have hheight : IsClosed {z : ℝ × ℝ |
      |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d} :=
    isClosed_le (by fun_prop) continuous_const
  have hL : IsCompact L := (isCompact_Icc.prod isCompact_Icc).inter_right (hsq.inter hheight)
  have hLU : L ⊆ U := fun _ hz => hbox hz.1
  refine ⟨hL.image_of_continuousOn (hβ.mono hLU), ?_⟩
  apply image_mono
  intro z hz
  refine ⟨hLU hz, ?_⟩
  have hden : 0 < 1 - z.1 ^ 2 := by
    have hu : -1 < z.1 ∧ z.1 < 1 := by
      constructor <;> linarith [hz.1.1.1, hz.1.1.2]
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < z.1 + 1)]
  intro hn
  have hz2 : z.2 = 0 := (mul_eq_zero.mp hn).resolve_left hden.ne'
  have hbound := (abs_le.mp hz.2.2).1
  rw [hz2] at hbound
  have hmul := mul_le_mul_of_nonneg_left hz.2.1 hs.le
  nlinarith

private theorem saddle_source_complement_subset
    {M : Type*} {e : M → Plane × ℝ} (he : Function.Injective e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (G : Plane ≃ₜ Plane)
    {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} {s τ σ c k R r h b Q d : ℝ}
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r) (hh : 0 ≤ h)
    (hb : b < k) (hQ : Q < R) (hτ : τ ∈ Icc (0 : ℝ) d)
    (hbox : Icc (-b) b ×ˢ Icc (-Q) Q ⊆ U)
    (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hside : ∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
      (B z ∈ interior (G '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
      (B z ∈ G '' closedBall 0 r ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) :
    {x | (e x).2 = c + s + τ ∧ (e x).1 ∈ (G '' sphere 0 r) \
      B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ⊆
      β '' {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
        h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d} ∪
      {x | B.symm (e x).1 ∉ Icc (-b) b ×ˢ Icc (-Q) Q} := by
  intro x hx
  let z := B.symm (e x).1
  by_cases hz : z ∈ Icc (-b) b ×ˢ Icc (-Q) Q
  · left
    have hBz : B z = (e x).1 := B.apply_symm_apply _
    have hzopen : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R := by
      constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    have hκ :=
      DifferentialGeometry.Topology.PlanarJordan.eq_saddleBandLevelCurve_of_mem_image_sphere
      B G hσ hk hr hside hzopen (by simpa only [hBz] using hx.2.1)
    have houtside : z.1 ∉ Ioo (-h) h := by
      intro hin
      exact hx.2.2 ⟨z, ⟨z.1, hin, hκ.symm⟩, hBz⟩
    have hsquare : h ^ 2 ≤ z.1 ^ 2 := by
      by_contra hn
      apply houtside
      constructor <;> nlinarith
    have hheight : c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ := by
      have hd := ((hside z hzopen).2.mp (image_mono sphere_subset_closedBall
        (by simpa only [hBz] using hx.2.1))).1
      have hnot : B z ∉ interior (G '' closedBall 0 r) := by
        rw [← G.image_interior, interior_closedBall _ hr.ne']
        rintro ⟨y, hy, hye⟩
        obtain ⟨w, hw, hwe⟩ := hx.2.1
        have heq := G.injective ((hye.trans hBz).trans hwe.symm)
        subst w
        exact (mem_ball.mp hy).ne (mem_sphere.mp hw)
      have hle : c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ c + s + τ := by
        by_contra hh
        exact hnot ((hside z hzopen).1.mpr
          ⟨lt_of_not_ge hh, ((hside z hzopen).2.mp
            (image_mono sphere_subset_closedBall (by simpa only [hBz] using hx.2.1))).2⟩)
      exact hle.antisymm hd
    refine ⟨z, ⟨hz, hsquare, ?_⟩, ?_⟩
    · rw [hheight, add_sub_cancel_left, abs_of_nonneg hτ.1]
      exact hτ.2
    · apply he
      rw [hgraph z (hbox hz)]
      exact Prod.ext hBz (hheight.trans hx.1.symm)
  · exact Or.inr hz

theorem exists_saddle_closing_arc_transport_inter_rectangle
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ F = 2)
    {e : M → Plane × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, Plane × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s h b k Q R : ℝ} (hs : 0 < s) (hh : 0 < h) (hhb : h < b)
    (hbk : b < k) (hk : k < 1) (hQ : 0 < Q) (hQR : Q < R)
    (hbox : Icc (-b) b ×ˢ Icc (-Q) Q ⊆ U)
    (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hcritical : ∀ x, (e x).2 = c + s → IsCriticalPointAt I (fun x => (e x).2) x →
      B.symm (e x).1 ∈ Ioo (-b) b ×ˢ Ioo (-Q) Q) :
    ∃ d > 0, d < s * h ^ 2 ∧
      let C := β '' {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
        h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d}
      ∃ δ > 0, δ ≤ d ∧ ∃ N P : Set M, IsOpen N ∧
        C ∪ {x | |(e x).2 - (c + s)| ≤ d ∧
          B.symm (e x).1 ∉ Ioo (-b) b ×ˢ Ioo (-Q) Q} ⊆ N ∧ IsOpen P ∧ C ⊆ P ∧
        P ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (-δ) δ, MapsTo (Φ t) P
          (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0})) ∧
        (∀ x ∈ P, IsIntegralCurveOn (fun t => B.symm (e (Φ t x)).1)
          (fun _ => saddleBandVectorField) (Icc (-δ) δ)) ∧
        (∀ x ∈ N, ∀ t ∈ Icc (-δ) δ, (e (Φ t x)).2 = (e x).2 + t) ∧
        (∀ τ ∈ Ioo (0 : ℝ) δ, ∀ σ : ℝ, σ ^ 2 = 1 →
          ∀ (G : Plane ≃ₜ Plane) (r : ℝ), 0 < r →
            (∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
              (B z ∈ interior (G '' closedBall 0 r) ↔
                c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
              (B z ∈ G '' closedBall 0 r ↔
                c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) →
            {x | (e x).2 = c + s + τ ∧ (e x).1 ∈ (G '' sphere 0 r) \
              B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ⊆ N ∧
            (∀ t ∈ Icc (-δ) δ, ∀ x,
              (e x).2 = c + s + τ →
              (e x).1 ∈ (G '' sphere 0 r) \
                B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) →
              B.symm (e (Φ t x)).1 ∈ Icc (-h) h ×ˢ Icc (-(Q / 2)) (Q / 2) →
              B.symm (e (Φ t x)).1 = saddleBandLevelCurve s (τ + t) σ (-h) ∨
                B.symm (e (Φ t x)).1 = saddleBandLevelCurve s (τ + t) σ h) ∧
            (∀ t ∈ Icc (-δ) δ, ∀ x,
              (e x).2 = c + s + τ →
              (e x).1 ∈ (G '' sphere 0 r) \
                B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) →
              B.symm (e (Φ t x)).1 ∉
                Icc (-(h / 2)) (h / 2) ×ˢ Icc (-(Q / 2)) (Q / 2)) ∧
            ∀ t ∈ Icc (-δ) δ, 0 < τ + t →
              B (saddleBandLevelCurve s (τ + t) σ 0) ∉
                (fun x => (e (Φ t x)).1) ''
                  {x | (e x).2 = c + s + τ ∧ (e x).1 ∈ (G '' sphere 0 r) \
                    B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)}) ∧
        ∃ A : ℝ → (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
          ContDiff ℝ ∞ (fun p : ℝ × (Plane × ℝ) => A p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × (Plane × ℝ) => (A p.1).symm p.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, Plane × ℝ) (Plane × ℝ) ∞ ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x, A t (e x) = e (Φ t x) ∧
            (A t).symm (e (Φ t x)) = e x) ∧
          ∃ S : Set (Plane × ℝ), IsCompact S ∧ ∀ t,
            EqOn (A t) id Sᶜ ∧ EqOn (A t).symm id Sᶜ := by
  let g : M → ℝ × ℝ := fun x => B.symm (e x).1
  have hg : Continuous g := B.symm.continuous.comp (continuous_fst.comp he.contMDiff.continuous)
  let V := g ⁻¹' (Ioo (-b) b ×ˢ Ioo (-Q) Q)
  have hV : IsOpen V := (isOpen_Ioo.prod isOpen_Ioo).preimage hg
  obtain ⟨ρ, hρ, hF, hFreg⟩ := exists_pos_regular_strip_sdiff
    ((contDiff_snd.contMDiff.comp he.contMDiff).of_le (by simp)) isCompact_univ hV (c := c + s)
    (fun x _ hx hxc => hcritical x hx hxc)
  let d := min ρ (s * h ^ 2 / 2)
  have hsh : 0 < s * h ^ 2 := mul_pos hs (sq_pos_of_pos hh)
  have hd : 0 < d := lt_min hρ (half_pos hsh)
  have hdρ : d ≤ ρ := min_le_left _ _
  have hdsh : d < s * h ^ 2 := (min_le_right _ _).trans_lt (by linarith)
  let C := β '' {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
    h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d}
  have hC := isCompact_and_subset_regular_saddle_band (c := c)
    hβ.continuousOn hs (hbk.trans hk) hdsh hbox
  obtain ⟨_, _, _, _, _, W, _, _, hdf⟩ :=
    exists_unitSpeedVectorField_on_saddle_band hdim he.contMDiff B hU hβ hgraph
  have hCreg (x : M) (hx : x ∈ C) : ¬ IsCriticalPointAt I (fun x => (e x).2) x := by
    intro hxc
    have hv := hdf x (hC.2 hx)
    change mfderiv I 𝓘(ℝ) (fun x => (e x).2) x = 0 at hxc
    rw [hxc] at hv
    simp at hv
  obtain ⟨ζ, hζ, N, P, hN, hKN, hP, hCP, hPreg, Φ, hΦ, hΦi, hΦ0,
      hheight, hstay, hcurve, A, hA, hAi, hA0, hAe, hsupport⟩ :=
    exists_ambient_isotopy_local_level_transport_saddle hdim he B hU hβ hgraph
      (hC.1.union hF) (fun x hx => hx.elim (hCreg x) (hFreg x))
      isOpen_univ (subset_univ _) hC.1 hC.2
  obtain ⟨ε, hε, hclear⟩ := exists_uniform_box_clearance (Φ := fun t x => Φ t x) hg hΦ.continuous
    (fun x => by simpa using DFunLike.congr_fun hΦ0 x) hhb (show Q / 2 < Q by linarith)
  let δ := min ζ (min ε (min d (min (s * h ^ 2 / 2) (Q ^ 2 / 16))))
  have hδ : 0 < δ := lt_min hζ (lt_min hε (lt_min hd
    (lt_min (half_pos hsh) (div_pos (sq_pos_of_pos hQ) (by norm_num)))))
  have hδζ : δ ≤ ζ := min_le_left _ _
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδd : δ ≤ d := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδsh : δ ≤ s * h ^ 2 / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδQ : δ ≤ Q ^ 2 / 16 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htime : Icc (-δ) δ ⊆ Icc (-ζ) ζ := Icc_subset_Icc (neg_le_neg hδζ) hδζ
  refine ⟨d, hd, hdsh, δ, hδ, hδd, N, P, hN, ?_, hP, hCP, hPreg, Φ, hΦ, hΦi, hΦ0,
    fun t ht => hstay t (htime ht), fun x hx => (hcurve x hx).mono htime,
    fun x hx t ht => (hheight t (htime ht) x hx).2, ?_,
    A, hA, hAi, hA0, fun t ht => hAe t (htime ht), hsupport⟩
  · intro x hx
    apply hKN
    rcases hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr ⟨⟨mem_univ _, ?_⟩, hx.2⟩
      have ha := abs_le.mp hx.1
      change (e x).2 ∈ Icc (c + s - ρ) (c + s + ρ)
      constructor <;> linarith [ha.1, ha.2]
  · intro τ hτ σ hσ G r hr hside
    constructor
    · intro x hx
      apply hKN
      have hsplit :=
        saddle_source_complement_subset he.isEmbedding.injective B G hσ hk hr hh.le hbk hQR
        (show τ ∈ Icc (0 : ℝ) d from ⟨hτ.1.le, hτ.2.le.trans hδd⟩) hbox hgraph hside hx
      rcases hsplit with hxC | hxFar
      · exact Or.inl hxC
      · refine Or.inr ⟨⟨mem_univ _, ?_⟩, ?_⟩
        · change (e x).2 ∈ Icc (c + s - ρ) (c + s + ρ)
          rw [hx.1]
          constructor <;> linarith [hτ.1, hτ.2]
        · intro hlarge
          exact hxFar ⟨⟨hlarge.1.1.le, hlarge.1.2.le⟩, ⟨hlarge.2.1.le, hlarge.2.2.le⟩⟩
    have hbox_contact : ∀ t ∈ Icc (-δ) δ, ∀ x,
        (e x).2 = c + s + τ →
        (e x).1 ∈ (G '' sphere 0 r) \
          B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) →
        g (Φ t x) ∈ Icc (-h) h ×ˢ Icc (-(Q / 2)) (Q / 2) →
        g (Φ t x) = saddleBandLevelCurve s (τ + t) σ (-h) ∨
          g (Φ t x) = saddleBandLevelCurve s (τ + t) σ h := by
      intro t ht x hxheight hxcircle hmem
      have hx := And.intro hxheight hxcircle
      have hsplit :=
        saddle_source_complement_subset he.isEmbedding.injective B G hσ hk hr hh.le hbk hQR
        (show τ ∈ Icc (0 : ℝ) d from ⟨hτ.1.le, hτ.2.le.trans hδd⟩) hbox hgraph hside hx
      rcases hsplit with hxC | hxFar
      · have hxP : x ∈ P := hCP hxC
        obtain ⟨z, hz, hzx⟩ := hxC
        have hreg (v : ℝ) (hv : v ∈ Icc (-δ) δ) :
            (1 - (B.symm (e (Φ v x)).1).1 ^ 2) * (B.symm (e (Φ v x)).1).2 ≠ 0 := by
          obtain ⟨w, hw, hwe⟩ := hstay v (htime hv) hxP
          rw [← hwe, hgraph w hw.1, B.symm_apply_apply]
          exact hw.2
        have hzopen : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R := by
          constructor <;> constructor <;> linarith [hz.1.1.1, hz.1.1.2, hz.1.2.1, hz.1.2.2]
        have hBz : B z = (e x).1 := by rw [← hzx, hgraph z (hbox hz.1)]
        have hzκ :=
          DifferentialGeometry.Topology.PlanarJordan.eq_saddleBandLevelCurve_of_mem_image_sphere
          B G hσ hk hr hside hzopen (by simpa only [hBz] using hx.2.1)
        have htimepos : δ < τ + s * z.1 ^ 2 := by
          have hm := mul_le_mul_of_nonneg_left hz.2.1 hs.le
          linarith [hτ.1]
        have hinit : B.symm (e (Φ 0 x)).1 = saddleBandLevelCurve s τ σ z.1 := by
          rw [hΦ0]
          change B.symm (e x).1 = _
          rw [← hBz, B.symm_apply_apply]
          exact hzκ
        have heq := eq_saddleBandLevelCurve_of_isIntegralCurveOn hδ
          ((hcurve x hxP).mono htime) hreg hinit htimepos hσ
          (show z.1 ∈ Ioo (-1 : ℝ) 1 by
            constructor <;> linarith [hzopen.1.1, hzopen.1.2])
        change B.symm (e (Φ t x)).1 ∈ _ at hmem
        have heqt : B.symm (e (Φ t x)).1 = saddleBandLevelCurve s (τ + t) σ z.1 := heq ht
        rw [heqt] at hmem
        have hu : -h ≤ z.1 ∧ z.1 ≤ h := hmem.1
        have hcases : z.1 = -h ∨ z.1 = h := by
          have hp := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hu.1)
          have hsquare : z.1 ^ 2 = h ^ 2 := by nlinarith [hz.2.1]
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hzpos | hzneg
          · exact Or.inr hzpos
          · exact Or.inl hzneg
        rcases hcases with hzleft | hzright
        · left
          exact heqt.trans (congrArg (saddleBandLevelCurve s (τ + t) σ) hzleft)
        · right
          exact heqt.trans (congrArg (saddleBandLevelCurve s (τ + t) σ) hzright)
      · have hfar : g x ∉ Ioo (-b) b ×ˢ Ioo (-Q) Q := by
          intro hxopen
          exact hxFar ⟨⟨hxopen.1.1.le, hxopen.1.2.le⟩, ⟨hxopen.2.1.le, hxopen.2.2.le⟩⟩
        exact False.elim (hclear t (Icc_subset_Icc (neg_le_neg hδε) hδε ht) x hfar hmem)
    have hcore : ∀ t ∈ Icc (-δ) δ, ∀ x,
        (e x).2 = c + s + τ →
        (e x).1 ∈ (G '' sphere 0 r) \
          B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) →
        g (Φ t x) ∉ Icc (-(h / 2)) (h / 2) ×ˢ Icc (-(Q / 2)) (Q / 2) := by
      intro t ht x hxheight hxcircle hmem
      have hfull : g (Φ t x) ∈ Icc (-h) h ×ˢ Icc (-(Q / 2)) (Q / 2) :=
        ⟨⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩, hmem.2⟩
      rcases hbox_contact t ht x hxheight hxcircle hfull with heq | heq
      · rw [heq] at hmem
        have hm : -(h / 2) ≤ -h := hmem.1.1
        linarith
      · rw [heq] at hmem
        have hm : h ≤ h / 2 := hmem.1.2
        linarith
    refine ⟨hbox_contact, hcore, ?_⟩
    intro t ht hτt hmem
    obtain ⟨x, hx, hxt⟩ := hmem
    change (e (Φ t x)).1 = B (saddleBandLevelCurve s (τ + t) σ 0) at hxt
    apply hcore t ht x hx.1 hx.2
    change B.symm (e (Φ t x)).1 ∈ Icc (-(h / 2)) (h / 2) ×ˢ Icc (-(Q / 2)) (Q / 2)
    rw [hxt, B.symm_apply_apply]
    have hradsq : (Real.sqrt (2 * (τ + t))) ^ 2 = 2 * (τ + t) :=
      Real.sq_sqrt (by positivity)
    have hsigsq : (σ * Real.sqrt (2 * (τ + t))) ^ 2 = 2 * (τ + t) := by
      rw [mul_pow, hσ, one_mul, hradsq]
    suffices 0 ∈ Icc (-(h / 2)) (h / 2) ∧
        σ * Real.sqrt (2 * (τ + t)) ∈ Icc (-(Q / 2)) (Q / 2) by
      simpa only [saddleBandLevelCurve, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
        sub_zero, div_one, mem_prod] using this
    constructor
    · exact ⟨by linarith, by linarith⟩
    · constructor <;> nlinarith [ht.2, hτ.2]

theorem exists_saddle_closing_arc_transport
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ F = 2)
    {e : M → Plane × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, Plane × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s h b k Q R : ℝ} (hs : 0 < s) (hh : 0 < h) (hhb : h < b)
    (hbk : b < k) (hk : k < 1) (hQ : 0 < Q) (hQR : Q < R)
    (hbox : Icc (-b) b ×ˢ Icc (-Q) Q ⊆ U)
    (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hcritical : ∀ x, (e x).2 = c + s → IsCriticalPointAt I (fun x => (e x).2) x →
      B.symm (e x).1 ∈ Ioo (-b) b ×ˢ Ioo (-Q) Q) :
    ∃ d > 0, d < s * h ^ 2 ∧
      let C := β '' {z : ℝ × ℝ | z ∈ Icc (-b) b ×ˢ Icc (-Q) Q ∧
        h ^ 2 ≤ z.1 ^ 2 ∧ |c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s)| ≤ d}
      ∃ δ > 0, δ ≤ d ∧ ∃ N P : Set M, IsOpen N ∧
        C ∪ {x | |(e x).2 - (c + s)| ≤ d ∧
          B.symm (e x).1 ∉ Ioo (-b) b ×ˢ Ioo (-Q) Q} ⊆ N ∧ IsOpen P ∧ C ⊆ P ∧
        P ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (-δ) δ, MapsTo (Φ t) P
          (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0})) ∧
        (∀ x ∈ P, IsIntegralCurveOn (fun t => B.symm (e (Φ t x)).1)
          (fun _ => saddleBandVectorField) (Icc (-δ) δ)) ∧
        (∀ x ∈ N, ∀ t ∈ Icc (-δ) δ, (e (Φ t x)).2 = (e x).2 + t) ∧
        (∀ τ ∈ Ioo (0 : ℝ) δ, ∀ σ : ℝ, σ ^ 2 = 1 →
          ∀ (G : Plane ≃ₜ Plane) (r : ℝ), 0 < r →
            (∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
              (B z ∈ interior (G '' closedBall 0 r) ↔
                c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
              (B z ∈ G '' closedBall 0 r ↔
                c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) →
            {x | (e x).2 = c + s + τ ∧ (e x).1 ∈ (G '' sphere 0 r) \
              B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ⊆ N ∧
            (∀ t ∈ Icc (-δ) δ, ∀ x,
              (e x).2 = c + s + τ →
              (e x).1 ∈ (G '' sphere 0 r) \
                B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) →
              B.symm (e (Φ t x)).1 ∉
                Icc (-(h / 2)) (h / 2) ×ˢ Icc (-(Q / 2)) (Q / 2)) ∧
            ∀ t ∈ Icc (-δ) δ, 0 < τ + t →
              B (saddleBandLevelCurve s (τ + t) σ 0) ∉
                (fun x => (e (Φ t x)).1) ''
                  {x | (e x).2 = c + s + τ ∧ (e x).1 ∈ (G '' sphere 0 r) \
                    B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)}) ∧
        ∃ A : ℝ → (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
          ContDiff ℝ ∞ (fun p : ℝ × (Plane × ℝ) => A p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × (Plane × ℝ) => (A p.1).symm p.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, Plane × ℝ) (Plane × ℝ) ∞ ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x, A t (e x) = e (Φ t x) ∧
            (A t).symm (e (Φ t x)) = e x) ∧
          ∃ S : Set (Plane × ℝ), IsCompact S ∧ ∀ t,
            EqOn (A t) id Sᶜ ∧ EqOn (A t).symm id Sᶜ := by
  obtain ⟨d, hd, hdsh, δ, hδ, hδd, N, P, hN, hKN, hP, hCP, hPreg,
      Φ, hΦ, hΦi, hΦ0, hstay, hcurve, hheight, hav,
      A, hA, hAi, hA0, hAe, hsupport⟩ :=
    exists_saddle_closing_arc_transport_inter_rectangle hdim he B hU hβ hs hh hhb
      hbk hk hQ hQR hbox hgraph hcritical
  refine ⟨d, hd, hdsh, δ, hδ, hδd, N, P, hN, hKN, hP, hCP, hPreg,
    Φ, hΦ, hΦi, hΦ0, hstay, hcurve, hheight, ?_, A, hA, hAi, hA0, hAe, hsupport⟩
  intro τ hτ σ hσ G r hr hside
  have hh := hav τ hτ σ hσ G r hr hside
  exact ⟨hh.1, hh.2.2.1, hh.2.2.2⟩

end DifferentialGeometry.Topology.SphereSeparation
