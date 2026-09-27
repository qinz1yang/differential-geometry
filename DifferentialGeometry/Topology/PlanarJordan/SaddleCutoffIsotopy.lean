import DifferentialGeometry.Topology.PlanarJordan.SaddleIsotopy
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCutoff

open Set Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open Schoenflies (Plane IsCutPair)
open DifferentialGeometry.Analysis.ODE (saddleBandCurve)

namespace DifferentialGeometry.Topology.PlanarJordan

theorem image_circle_eq_of_closing_arc_and_saddle_band_time_change
    (P : Plane ≃ Plane) (B : (ℝ × ℝ) → Plane)
    {s t t₀ σ h : ℝ} (hs : 0 ≤ s) (ht₀ : 0 ≤ t₀) (ht : 0 < t)
    (hσ : σ ^ 2 = 1) (hh1 : h < 1)
    {γ γ₀ : unitInterval → Plane} {C C₀ : Set Plane}
    (hcut : IsCutPair C (B (saddleBandLevelCurve s t σ (-h)))
      (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range γ))
    (hcut₀ : IsCutPair C₀ (B (saddleBandLevelCurve s t₀ σ (-h)))
      (B (saddleBandLevelCurve s t₀ σ h))
      (B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h)) (range γ₀))
    {θ : ℝ → ℝ} (hθ : ∀ u ∈ Icc (-h) h, θ u = 1)
    (hclosing : ∀ u, P.symm (γ u) = γ₀ u)
    (hmodel : ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t →
      P.symm (B z) = B (saddleBandCurve z (θ z.1 * (t₀ - t)))) :
    P '' C₀ = C := by
  have hcoord {u : ℝ} (hu : u ∈ Icc (-h) h) : u ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hselected : P.symm '' (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) =
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) := by
    have hp (u : ℝ) (hu : u ∈ Icc (-h) h) :
        P.symm (B (saddleBandLevelCurve s t σ u)) = B (saddleBandLevelCurve s t₀ σ u) := by
      have hheight : (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) *
          ((saddleBandLevelCurve s t σ u).2 ^ 2 + 2 * s) / 2 = s + t := by
        simpa only [zero_add] using saddleBandLevelCurve_height hs ht hσ (hcoord hu) 0
      rw [hmodel (saddleBandLevelCurve s t σ u) (abs_le.mpr hu) hheight]
      change B (saddleBandCurve (saddleBandLevelCurve s t σ u) (θ u * (t₀ - t))) = _
      rw [hθ u hu, one_mul, saddleBandCurve_saddleBandLevelCurve
        (add_pos_of_pos_of_nonneg ht (mul_nonneg hs (sq_nonneg u)))
        (add_nonneg ht₀ (mul_nonneg hs (sq_nonneg u))) hσ (hcoord hu)]
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, (hp u hu).symm⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hp u hu⟩
  have hforward : P.symm '' C = C₀ := by
    rw [← hcut.union_eq, image_union, hselected]
    rw [show P.symm '' range γ = range γ₀ by
      rw [← range_comp]; congr 1; funext u; exact hclosing u]
    exact hcut₀.union_eq
  rw [← hforward]
  exact P.image_symm_image C


private theorem exists_ambient_isotopy_closing_arc_homotopy_eqOn_integralCurve
    {Γ : ℝ × unitInterval → Plane}
    (hΓ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ Γ)
    (hemb : ∀ t, IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => Γ (t, u)))
    {a b t₀ : ℝ} {U C : Set ((ℝ × ℝ) × Plane)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {W : (ℝ × ℝ) × Plane → Plane} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
      ((r, t), Γ ((1 - r) * t + r * t₀, u)) ∈ U →
      W ((r, t), Γ ((1 - r) * t + r * t₀, u)) =
        deriv (fun q => Γ (q, u)) ((1 - r) * t + r * t₀))
    {Q : Type*} {ζ : Q → ℝ → ℝ × Plane}
    (hζ : ∀ q, ContinuousOn (ζ q) (Icc (0 : ℝ) 1))
    (hζ' : ∀ q, ∀ r ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (ζ q) (0, (t₀ - (ζ q r).1) • W ((r, (ζ q r).1), (ζ q r).2)) (Ici r) r)
    (hζC : ∀ q, ∀ r ∈ Icc (0 : ℝ) 1, ((r, (ζ q r).1), (ζ q r).2) ∈ C) :
    ∃ Φ : ℝ → (ℝ × Plane) ≃ₘ[ℝ] (ℝ × Plane),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × Plane) (ℝ × Plane) ∞ ∧
      (∀ r q, (Φ r q).1 = q.1) ∧
      (∀ r y, Φ r (t₀, y) = (t₀, y)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
        Φ r (t, Γ (t, u)) = (t, Γ ((1 - r) * t + r * t₀, u))) ∧
      (∀ q, ∀ r ∈ Icc (0 : ℝ) 1, Φ r (ζ q 0) = ζ q r) ∧
      ∃ S : Set (ℝ × Plane), IsCompact S ∧
        ∀ r, EqOn (Φ r) id Sᶜ ∧ EqOn (Φ r).symm id Sᶜ := by
  let τ : ℝ × ℝ → ℝ := fun q => (1 - q.1) * q.2 + q.1 * t₀
  have hτ : ContDiff ℝ ∞ τ :=
    ((contDiff_const.sub contDiff_fst).mul contDiff_snd).add (contDiff_fst.mul contDiff_const)
  let e : (ℝ × ℝ) × unitInterval → Plane := fun q => Γ (τ q.1, q.2)
  let v : (ℝ × ℝ) × unitInterval → Plane :=
    fun q => deriv (fun z => Γ (z, q.2)) (τ q.1)
  have he : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ e :=
    hΓ.comp ((hτ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hvelocity : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞
      (fun q : ℝ × unitInterval => deriv (fun z => Γ (z, q.2)) q.1) :=
    fun q => DifferentialGeometry.timeDeriv_smoothAt (hΓ q) (by simp)
  have hv : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ v :=
    hvelocity.comp ((hτ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hve (r t : ℝ) (u : unitInterval) :
      deriv (fun x => e ((x, t), u)) r = (t₀ - t) • v ((r, t), u) := by
    have hg : ContDiff ℝ ∞ (fun z => Γ (z, u)) :=
      (hΓ.comp (contMDiff_id.prodMk contMDiff_const)).contDiff
    have hlinear : HasDerivAt (fun x => (1 - x) * t + x * t₀) (t₀ - t) r := by
      convert (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).mul_const t).add
        ((hasDerivAt_id r).mul_const t₀) using 1 <;> first | rfl | ring
    exact (((hg.differentiable (by simp) (τ (r, t))).hasDerivAt).scomp r hlinear).deriv
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) unitInterval :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) unitInterval)
  let _ : IsManifold (𝓡∂ (0 + 1)) ∞ unitInterval :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ unitInterval)
  obtain ⟨Φ, hΦ, hΦi, hΦ0, hΦp, hΦfix, hΦe, hΦζ, S, hS, _, hΦS⟩ :=
    exists_contDiff_compact_ambient_isotopy_halfspace_parametric_eqOn_integralCurve_of_weighted_velocity
      he (fun q => hemb (τ q)) (k := fun t => t₀ - t) (contDiff_const.sub contDiff_id)
      hv isCompact_Icc (fun r _ t _ u => hve r t u) isOpen_univ
      (fun _ _ _ _ _ => mem_univ _) hU hC
      (fun q hq => ⟨hCU hq, mem_univ _⟩) hW hWe hζ hζ' hζC
  refine ⟨Φ, hΦ, hΦi, hΦ0, hΦp, ?_, ?_, ?_, S, hS, hΦS⟩
  · intro r y
    exact (hΦfix r (t₀, y) (sub_self _)).1
  · intro r hr t ht u
    simpa only [e, τ, sub_zero, one_mul, zero_mul, add_zero] using hΦe r hr t ht u
  · intro q r hr
    simpa only [hΦ0, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq] using hΦζ q r hr

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff_region
    {γ : ℝ × unitInterval → Plane} {δ : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ (Icc (-δ) δ ×ˢ univ))
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h ρ t₀ a b : ℝ}
    (hs : 0 < s) (hσ : σ ^ 2 = 1) (hh : 0 < h) (hh1 : h < 1)
    (hδsh : 4 * δ < s * h ^ 2) (ha : a < 0) (ht₀ : t₀ ∈ Ioo (0 : ℝ) b)
    (hJ : Icc a b ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ u,
      B.symm (γ (t, u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, u)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, u)) = saddleBandLevelCurve s t σ h)
    (hbox : ∀ t ∈ Icc (-δ) δ, ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s t 1 u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    ∃ ε > 0, a < -ε ∧ ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
        (∀ t u, θ (t, u) =
          1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
      ∃ Φ : ℝ → (ℝ × Plane) ≃ₘ[ℝ] (ℝ × Plane),
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => Φ q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × Plane) (ℝ × Plane) ∞ ∧
        (∀ r q, (Φ r q).1 = q.1) ∧
        (∀ r y, Φ r (t₀, y) = (t₀, y)) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
          Φ r (t, γ (t, u)) = (t, γ ((1 - r) * t + r * t₀, u))) ∧
        (∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
          {q | q.1 ∈ Icc (-ε) b ∧ |q.2.1| ≤ h ∧
            s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
            (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
              s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)} ⊆ V ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            Φ r (q.1, B q.2) =
              (q.1, B (saddleBandCurve q.2 (r * (θ (q.1, q.2.1) * (t₀ - q.1)))))) ∧
          ∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            r * (θ (q.1, q.2.1) * (t₀ - q.1)) = 0 ∨
              (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
                0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ *
                  (r * (θ (q.1, q.2.1) * (t₀ - q.1))) / q.2.2 ^ 2)) ∧
        ∃ S : Set (ℝ × Plane), IsCompact S ∧
          ∀ r, EqOn (Φ r) id Sᶜ ∧ EqOn (Φ r).symm id Sᶜ := by
  have ht₀J : t₀ ∈ Icc a b := ⟨(ha.trans ht₀.1).le, ht₀.2.le⟩
  have ht₀δ : t₀ ∈ Ioo (-δ) δ := hJ ht₀J
  have hδ : 0 < δ := ht₀.1.trans ht₀δ.2
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) unitInterval :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) unitInterval)
  let _ : IsManifold (𝓡∂ (0 + 1)) ∞ unitInterval :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ unitInterval)
  obtain ⟨Γ, hΓ, hΓemb, hΓeq⟩ :=
    exists_isSmoothEmbedding_extension_Icc_halfspace (d := 0) (M := unitInterval)
      (show -δ ≤ δ by linarith) hγ hemb
  have hΓpoint (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) : Γ (t, u) = γ (t, u) :=
    hΓeq ⟨ht, mem_univ u⟩
  obtain ⟨ε₀, hε₀, hε₀t, hε₀h, θ, ψ, hθ, hψ, hθ01, hψeq, hθ0, hθ1,
      hθzero, _, κ, hκin, hκout, hθformula, D, hDdom, hDgraph, hDnormalized, hDf, _, _⟩ :=
    exists_partialDiffeomorph_saddle_band_cutoff_profile_superlevel hs hh hh1 ht₀.1
  let ε := min ε₀ (-a / 2)
  have hε : 0 < ε := lt_min hε₀ (by linarith)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have haε : a < -ε := by have := min_le_right ε₀ (-a / 2); dsimp [ε]; linarith
  have hmodelJ : Icc (-ε) b ⊆ Icc a b := fun _ ht => ⟨haε.le.trans ht.1, ht.2⟩
  let τ : ℝ × ℝ → ℝ := fun q => (1 - q.1) * q.2 + q.1 * t₀
  have hτ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc a b) :
      τ (r, t) ∈ Ioo (-δ) δ :=
    (convex_Ioo (-δ) δ) (hJ ht) ht₀δ (sub_nonneg.mpr hr.2) hr.1 (sub_add_cancel 1 r)
  let Ω₀ : Set (ℝ × (ℝ × ℝ)) := {p | (p.1, p.2.1) ∉ tsupport θ ∨
    (1 - p.2.1 ^ 2) * p.2.2 ≠ 0}
  have hΩ₀ : IsOpen Ω₀ := DifferentialGeometry.Analysis.ODE.isOpen_smul_saddleBandVectorField_domain θ
  let j : ((ℝ × ℝ) × Plane) → ℝ × (ℝ × ℝ) := fun p => (p.1.2, B.symm p.2)
  have hj : ContDiff ℝ ∞ j := contDiff_fst.snd.prodMk (B.symm.contDiff.comp contDiff_snd)
  let Ω := j ⁻¹' Ω₀
  have hΩ : IsOpen Ω := hΩ₀.preimage hj.continuous
  let X : (ℝ × ℝ) × Plane → Plane := fun p =>
    θ (p.1.2, (B.symm p.2).1) • B.saddleFiberVectorField p.2
  have hX : ContDiffOn ℝ ∞ X Ω := by
    have hn : ContDiffOn ℝ ∞ (fun p : (ℝ × ℝ) × Plane =>
        θ (p.1.2, (B.symm p.2).1) • DifferentialGeometry.Analysis.ODE.saddleBandVectorField (B.symm p.2)) Ω :=
      (DifferentialGeometry.Analysis.ODE.contDiffOn_smul_saddleBandVectorField hθ).comp
        hj.contDiffOn (fun _ hp => hp)
    have hBD : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × Plane => fderiv ℝ (B : ℝ × ℝ → Plane) (B.symm p.2)) :=
      (B.contDiff.fderiv_right (by simp)).comp (B.symm.contDiff.comp contDiff_snd)
    simpa only [X, Diffeomorph.saddleFiberVectorField, map_smul] using hBD.contDiffOn.clm_apply hn
  obtain ⟨N, hN, hrectangleN, hNΩ, hNΓ⟩ :=
    exists_closing_arc_homotopy_field_neighborhood_of_saddle_rectangle hΓ.continuous B
      hs.le hσ hh hδsh ht₀δ hJ
      (fun t _ => (hΓemb t).isEmbedding.injective) hW hW0 hW1
      (fun u hu => ⟨(hendpoint u hu).1, fun t ht =>
        (hΓpoint t ht u).trans ((hendpoint u hu).2 t ht)⟩)
      (fun t ht => by rw [hΓpoint t ht 0, hΓpoint t ht 1]; exact hends t ht)
      (fun t ht u => by rw [hΓpoint t ht u]; exact hcontact t ht u)
      (fun t u hu => hθ1 t u (Or.inr hu)) hΩ
  let K : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-ε) b ∧ |q.2.1| ≤ h ∧
    s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
        s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)}
  have hbδ : b ∈ Ioo (-δ) δ := hJ ⟨(ha.trans ht₀.1).le.trans ht₀.2.le, le_rfl⟩
  have hupper (t u : ℝ) (ht : t ≤ b) :
      t + (1 - θ (t, u)) * (t₀ - t) ≤ b := by
    have hp := (hθ01 (t, u))
    nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr ht),
      mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr ht₀.2.le)]
  have hQcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2) := by fun_prop
  have hLcont : Continuous (fun q : ℝ × (ℝ × ℝ) => s + q.1) := by fun_prop
  have hUcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)) := by fun_prop
  have hKclosed : IsClosed K := by
    dsimp only [K]
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (continuous_snd.fst.abs) continuous_const).inter
        ((isClosed_le hLcont hQcont).inter (isClosed_le hQcont hUcont)))
  have hK : IsCompact K := by
    apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hKclosed
      (show K ⊆ Icc (-ε) b ×ˢ (Icc (-h) h ×ˢ Icc (-ρ) ρ) from ?_)
    intro q hq
    refine ⟨hq.1, mem_rectangle_of_saddle_band_height_le
      (abs_lt.mp (hq.2.1.trans_lt hh1)) ?_ (hbox b (Ioo_subset_Icc_self hbδ) q.2.1 (abs_le.mp hq.2.1))⟩
    linarith [hq.2.2.2, hupper q.1 q.2.1 hq.1.2]
  let E : Set (ℝ × (ℝ × (ℝ × ℝ))) := {q | ((q.1, q.2.1), q.2.2) ∈ D.source}
  let f : ℝ × (ℝ × (ℝ × ℝ)) → (ℝ × ℝ) × Plane :=
    fun q => ((q.1, q.2.1), B ((D ((q.1, q.2.1), q.2.2)).2))
  have hE : IsOpen E := D.open_source.preimage (by fun_prop)
  have hf : ContinuousOn f E := by
    apply (continuousOn_fst.prodMk continuousOn_snd.fst).prodMk
    exact B.continuous.comp_continuousOn ((D.contMDiffOn.continuousOn.comp
      (show ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) => ((q.1, q.2.1), q.2.2)) E from
        (by fun_prop)) (fun _ hp => hp)).snd)
  have hsource : Icc (0 : ℝ) 1 ×ˢ K ⊆ E := by
    rintro ⟨r, t, z⟩ ⟨hr, ht, hz, hlow, hupp⟩
    exact hDgraph r hr t (by linarith [ht.1]) z hz hlow
  have htrace : MapsTo f (Icc (0 : ℝ) 1 ×ˢ K) N := by
    rintro ⟨r, t, z⟩ ⟨hr, ht, hz, hlow, hupp⟩
    have htε₀ : -ε₀ ≤ t := by linarith [ht.1]
    have hsrc := hDgraph r hr t htε₀ z hz hlow
    have hnorm := hDnormalized r hr t htε₀ z hz hlow
    apply hrectangleN
    refine ⟨?_, ?_⟩
    · change (t, B.symm (B ((D ((r, t), z)).2))) ∈ Ω₀
      rw [B.symm_apply_apply]
      exact hnorm
    · change B.symm (B ((D ((r, t), z)).2)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ
      rw [B.symm_apply_apply]
      have henergy : (1 - (D ((r, t), z)).2.1 ^ 2) *
          ((D ((r, t), z)).2.2 ^ 2 + 2 * s) / 2 =
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 + r * θ (t, z.1) * (t₀ - t) := by
        rw [hDf]
        rcases hDdom _ hsrc with hoff | hreg
        · have hoff' := image_eq_zero_of_notMem_tsupport hoff
          change r * ψ (t, z.1) = 0 at hoff'
          rw [hoff', DifferentialGeometry.Analysis.ODE.saddleBandCurve_zero]
          rw [hψeq] at hoff'
          nlinarith
        · have he := DifferentialGeometry.Analysis.ODE.saddleBandCurve_height
            hreg.1 hreg.2.1 hreg.2.2.le 0 s
          simpa only [zero_add, hψeq, mul_assoc] using he
      have hlevel : (1 - (D ((r, t), z)).2.1 ^ 2) *
          ((D ((r, t), z)).2.2 ^ 2 + 2 * s) / 2 ≤ s + max t₀ (τ (r, t)) := by
        rw [henergy]
        by_cases htt₀ : t ≤ t₀
        · have hnn := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr.2)
            (hθ01 (t, z.1)).1) (sub_nonneg.mpr htt₀)
          have hm := le_max_left t₀ (τ (r, t))
          nlinarith
        · have hone := hθ1 t z.1 (Or.inl (by linarith))
          rw [hone] at hupp ⊢
          have hm := le_max_right t₀ (τ (r, t))
          dsimp only [τ] at hm
          nlinarith
      have hcoord : (D ((r, t), z)).2.1 = z.1 := by rw [hDf]; rfl
      apply mem_rectangle_of_saddle_band_height_le (τ := max t₀ (τ (r, t)))
        (by rw [hcoord]; exact abs_lt.mp (hz.trans_lt hh1))
        hlevel
      rw [hcoord]
      exact hbox (max t₀ (τ (r, t)))
        (Ioo_subset_Icc_self ⟨lt_max_of_lt_left ht₀δ.1,
          max_lt ht₀δ.2 (hτ r hr t (hmodelJ ht)).2⟩) z.1 (abs_le.mp hz)
  obtain ⟨K', hK', hKK', hK'source, hK'trace⟩ :=
    hf.exists_compact_prod_mapsTo hE isCompact_Icc hK hsource hN htrace
  let C := f '' (Icc (0 : ℝ) 1 ×ˢ K')
  have hC : IsCompact C := (isCompact_Icc.prod hK').image_of_continuousOn (hf.mono hK'source)
  have hCN : C ⊆ N := by
    rintro _ ⟨q, hq, rfl⟩
    exact hK'trace hq
  let ζ : K' → ℝ → ℝ × Plane := fun q r => (q.val.1, B ((D ((r, q.val.1), q.val.2)).2))
  have hζ (q : K') : ContinuousOn (ζ q) (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.prodMk
    exact B.continuous.comp_continuousOn ((D.contMDiffOn.continuousOn.comp
      (show ContinuousOn (fun r : ℝ => ((r, q.val.1), q.val.2)) (Icc (0 : ℝ) 1) from
        (by fun_prop)) (fun r hr => hK'source (show (r, q.val) ∈ Icc (0 : ℝ) 1 ×ˢ K' from
          ⟨hr, q.property⟩))).snd)
  have hζ' (q : K') (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
      HasDerivWithinAt (ζ q) (0, (t₀ - (ζ q r).1) • X ((r, (ζ q r).1), (ζ q r).2)) (Ici r) r := by
    have hsrc := hK'source (show (r, q.val) ∈ Icc (0 : ℝ) 1 ×ˢ K' from
      ⟨Ico_subset_Icc_self hr, q.property⟩)
    have hrad : 0 < 1 + 2 * (1 - q.val.2.1 ^ 2)⁻¹ *
        (r * ψ (q.val.1, q.val.2.1)) / q.val.2.2 ^ 2 := by
      rcases hDdom _ hsrc with hoff | hreg
      · have hzero := image_eq_zero_of_notMem_tsupport hoff
        change r * ψ (q.val.1, q.val.2.1) = 0 at hzero
        rw [hzero]
        norm_num
      · exact hreg.2.2
    have hd := (B.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
      (DifferentialGeometry.Analysis.ODE.hasDerivAt_saddleBandCurve_mul_const hrad)
    have hd' : HasDerivAt (ζ q)
        (0, (t₀ - (ζ q r).1) • X ((r, (ζ q r).1), (ζ q r).2)) r := by
      convert (hasDerivAt_const r q.val.1).prodMk hd using 1
      · funext x
        dsimp only [ζ]
        rw [hDf]
        rfl
      · dsimp only [ζ, X]
        rw [hDf, B.symm_apply_apply]
        simp only [Diffeomorph.saddleFiberVectorField, B.symm_apply_apply, map_smul]
        rw [hψeq, smul_smul]
        congr 2
        change (t₀ - q.val.1) * θ (q.val.1, q.val.2.1) = θ (q.val.1, q.val.2.1) * (t₀ - q.val.1)
        ring
    exact hd'.hasDerivWithinAt
  have hζC (q : K') (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ((r, (ζ q r).1), (ζ q r).2) ∈ C :=
    ⟨(r, q.val), ⟨hr, q.property⟩, rfl⟩
  obtain ⟨Φ, hΦ, hΦi, hΦ0, hΦp, hΦfix, hΦΓ, hΦζ, S, hS, hΦS⟩ :=
    exists_ambient_isotopy_closing_arc_homotopy_eqOn_integralCurve hΓ hΓemb hN hC hCN
      (hX.mono hNΩ) hNΓ hζ hζ' hζC
  refine ⟨ε, hε, haε, hεle.trans_lt hε₀t, hεle.trans_lt hε₀h,
    θ, hθ, hθ01, hθ0, hθ1, hθzero, κ, hκin, hκout, hθformula, Φ, hΦ, hΦi, hΦ0, hΦp, hΦfix, ?_,
    ⟨interior K', isOpen_interior, hKK', ?_, ?_⟩, S, hS, hΦS⟩
  · intro r hr t ht u
    have hcur := hΦΓ r hr t ht u
    change Φ r (t, Γ (t, u)) = (t, Γ (τ (r, t), u)) at hcur
    rwa [hΓpoint t (Ioo_subset_Icc_self (hJ ht)) u,
      hΓpoint (τ (r, t)) (Ioo_subset_Icc_self (hτ r hr t ht)) u] at hcur
  · intro r hr q hq
    have hh := hΦζ ⟨q, interior_subset hq⟩ r hr
    dsimp only [ζ] at hh
    rw [hDf, hDf, zero_mul, DifferentialGeometry.Analysis.ODE.saddleBandCurve_zero, hψeq] at hh
    exact hh
  · intro r hr q hq
    have hsourceq := hK'source (show (r, q) ∈ Icc (0 : ℝ) 1 ×ˢ K' from
      ⟨hr, interior_subset hq⟩)
    rcases hDdom _ hsourceq with hoff | hreg
    · left
      have hzero := image_eq_zero_of_notMem_tsupport hoff
      change r * ψ (q.1, q.2.1) = 0 at hzero
      rwa [hψeq] at hzero
    · right
      simpa only [hψeq] using hreg

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff_profile
    {γ : ℝ × unitInterval → Plane} {δ : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ (Icc (-δ) δ ×ˢ univ))
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h ρ t₀ a b : ℝ}
    (hs : 0 < s) (hσ : σ ^ 2 = 1) (hh : 0 < h) (hh1 : h < 1)
    (hδsh : 4 * δ < s * h ^ 2) (ha : a < 0) (ht₀ : t₀ ∈ Ioo (0 : ℝ) b)
    (hJ : Icc a b ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ u,
      B.symm (γ (t, u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, u)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, u)) = saddleBandLevelCurve s t σ h)
    (hbox : ∀ t ∈ Icc (-δ) δ, ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s t 1 u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    ∃ ε > 0, a < -ε ∧ ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
        (∀ t u, θ (t, u) =
          1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
      ∃ Φ : ℝ → (ℝ × Plane) ≃ₘ[ℝ] (ℝ × Plane),
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => Φ q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × Plane) (ℝ × Plane) ∞ ∧
        (∀ r q, (Φ r q).1 = q.1) ∧
        (∀ r y, Φ r (t₀, y) = (t₀, y)) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
          Φ r (t, γ (t, u)) = (t, γ ((1 - r) * t + r * t₀, u))) ∧
        (∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
          {q | q.1 ∈ Icc (-ε) b ∧ |q.2.1| ≤ h ∧
            (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            Φ r (q.1, B q.2) =
              (q.1, B (saddleBandCurve q.2 (r * (θ (q.1, q.2.1) * (t₀ - q.1)))))) ∧
          ∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            r * (θ (q.1, q.2.1) * (t₀ - q.1)) = 0 ∨
              (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
                0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ *
                  (r * (θ (q.1, q.2.1) * (t₀ - q.1))) / q.2.2 ^ 2)) ∧
        ∃ S : Set (ℝ × Plane), IsCompact S ∧
          ∀ r, EqOn (Φ r) id Sᶜ ∧ EqOn (Φ r).symm id Sᶜ := by
  obtain ⟨ε, hε, haε, hεt, hεh, θ, hθ, hθ01, hθ0, hθ1, hθzero,
      κ, hκin, hκout, hprofile, Φ, hΦ, hΦi, hΦ0, hΦp, hΦfix, hΦarc,
      ⟨V, hV, hKV, hmodel, hreg⟩, S, hS, hΦS⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff_region hγ B hs hσ hh hh1 hδsh ha ht₀ hJ
      hemb hW hW0 hW1 hendpoint hends hcontact hbox
  refine ⟨ε, hε, haε, hεt, hεh, θ, hθ, hθ01, hθ0, hθ1, hθzero,
    κ, hκin, hκout, hprofile, Φ, hΦ, hΦi, hΦ0, hΦp, hΦfix, hΦarc,
    ⟨V, hV, ?_, hmodel, hreg⟩, S, hS, hΦS⟩
  intro q hq
  apply hKV
  refine ⟨hq.1, hq.2.1, hq.2.2.ge, ?_⟩
  rw [hq.2.2]
  by_cases ht : q.1 ≤ t₀
  · exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr (hθ01 _).2) (sub_nonneg.mpr ht))
  · rw [hθ1 q.1 q.2.1 (Or.inl (by linarith))]
    simp

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff
    {γ : ℝ × unitInterval → Plane} {δ : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ (Icc (-δ) δ ×ˢ univ))
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h ρ t₀ a b : ℝ}
    (hs : 0 < s) (hσ : σ ^ 2 = 1) (hh : 0 < h) (hh1 : h < 1)
    (hδsh : 4 * δ < s * h ^ 2) (ha : a < 0) (ht₀ : t₀ ∈ Ioo (0 : ℝ) b)
    (hJ : Icc a b ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ u,
      B.symm (γ (t, u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, u)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, u)) = saddleBandLevelCurve s t σ h)
    (hbox : ∀ t ∈ Icc (-δ) δ, ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s t 1 u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    ∃ ε > 0, a < -ε ∧ ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ Φ : ℝ → (ℝ × Plane) ≃ₘ[ℝ] (ℝ × Plane),
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => Φ q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Plane) => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × Plane) (ℝ × Plane) ∞ ∧
        (∀ r q, (Φ r q).1 = q.1) ∧
        (∀ r y, Φ r (t₀, y) = (t₀, y)) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
          Φ r (t, γ (t, u)) = (t, γ ((1 - r) * t + r * t₀, u))) ∧
        (∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
          {q | q.1 ∈ Icc (-ε) b ∧ |q.2.1| ≤ h ∧
            (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            Φ r (q.1, B q.2) =
              (q.1, B (saddleBandCurve q.2 (r * (θ (q.1, q.2.1) * (t₀ - q.1)))))) ∧
          ∀ r ∈ Icc (0 : ℝ) 1, ∀ q ∈ V,
            r * (θ (q.1, q.2.1) * (t₀ - q.1)) = 0 ∨
              (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
                0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ *
                  (r * (θ (q.1, q.2.1) * (t₀ - q.1))) / q.2.2 ^ 2)) ∧
        ∃ S : Set (ℝ × Plane), IsCompact S ∧
          ∀ r, EqOn (Φ r) id Sᶜ ∧ EqOn (Φ r).symm id Sᶜ := by
  obtain ⟨ε, hε, haε, hεt, hεh, θ, hθ, hθ01, hθ0, hθ1, hθzero, _, _, _, _, Φ, hΦ⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff_profile hγ B hs hσ hh hh1 hδsh ha ht₀ hJ
      hemb hW hW0 hW1 hendpoint hends hcontact hbox
  exact ⟨ε, hε, haε, hεt, hεh, θ, hθ, hθ01, hθ0, hθ1, hθzero, Φ, hΦ⟩

end DifferentialGeometry.Topology.PlanarJordan
