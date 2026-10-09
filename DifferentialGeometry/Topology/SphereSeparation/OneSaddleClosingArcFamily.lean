import DifferentialGeometry.Topology.PlanarJordan.SaddleIsotopy
import DifferentialGeometry.Topology.SphereSeparation.OneSaddleCapNormalForm
import DifferentialGeometry.Topology.SphereSeparation.SaddleCapTransport
import DifferentialGeometry.Topology.SphereSeparation.SaddleCapClosingArc
import DifferentialGeometry.Topology.SphereSeparation.HeightSection

open Set Metric Manifold Schoenflies
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.PlanarJordan

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_pos_endpoint_intervals_subset {W : Set unitInterval} (hW : IsOpen W)
    (h0 : (0 : unitInterval) ∈ W) (h1 : (1 : unitInterval) ∈ W) :
    ∃ ε > 0, ∀ u : unitInterval, (u : ℝ) < ε ∨ 1 - ε < (u : ℝ) → u ∈ W := by
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hW 0 h0
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hW 1 h1
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro u hu
  rcases hu with hu | hu
  · apply hball₀
    change dist (u : ℝ) 0 < r₀
    rw [Real.dist_eq, sub_zero, abs_of_nonneg u.property.1]
    exact hu.trans_le (min_le_left _ _)
  · apply hball₁
    change dist (u : ℝ) 1 < r₁
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr u.property.2)]
    linarith [min_le_right r₀ r₁]

private theorem exists_fixed_saddle_endpoint_parameters {s k Q : ℝ} (hs : 0 < s) (hk : 0 < k) (hQ : 0 < Q) :
    ∃ h b d : ℝ, 0 < h ∧ h < b ∧ b < k ∧ b < 1 ∧ 0 < d ∧ d < s * h ^ 2 ∧
      ∀ t ∈ Icc (0 : ℝ) d, ∀ σ ∈ ({-1, 1} : Set ℝ),
        saddleBandLevelCurve s t σ '' Icc (-b) b ⊆ Ioo (-k) k ×ˢ Ioo (-Q) Q := by
  obtain ⟨D, b, hD, hb, hb1, hsub⟩ := exists_saddleBandLevelCurve_subset_open s
    (isOpen_Ioo.prod isOpen_Ioo) (show (0, 0) ∈ Ioo (-k) k ×ˢ Ioo (-Q) Q by
      exact ⟨⟨neg_neg_of_pos hk, hk⟩, ⟨neg_neg_of_pos hQ, hQ⟩⟩)
  have hbk : b < k := (hsub 0 ⟨le_rfl, hD.le⟩ 1 (by simp)
    ⟨b, ⟨by linarith, le_rfl⟩, rfl⟩).1.2
  have hh : 0 < b / 2 := half_pos hb
  have hsquare : 0 < s * (b / 2) ^ 2 := mul_pos hs (sq_pos_of_pos hh)
  refine ⟨b / 2, b, min D (s * (b / 2) ^ 2 / 2), hh, half_lt_self hb, hbk, hb1,
    lt_min hD (half_pos hsquare), (min_le_right _ _).trans_lt (half_lt_self hsquare), ?_⟩
  intro t ht σ hσ
  exact hsub t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ σ hσ

theorem exists_closing_arc_family_and_height_cap_inter_rectangle_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ r : ℝ, 0 < r ∧ c + s + τ < e p 2 - r ^ 2 / 2 ∧
      ∃ Acap : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ z, (Acap z).2 = z.2) ∧
        (∃ R T : ℝ, r < R ∧ 0 < T ∧ r ^ 2 / 2 < T ∧
          (closedBall 0 R ×ˢ closedBall (e p 2) T) ∩ range (fun x => Acap.symm (L (e x))) =
            (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) ∧
        (L ∘ e) '' connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
          (fun y => Acap (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
      ∃ Ψ : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Ψ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Ψ z.1).symm z.2) ∧
        Ψ (c + s + τ) = Diffeomorph.refl (𝓡 2) Plane ∞ ∧
      ∃ Gcap : ℝ → Plane ≃ₘ[ℝ] Plane,
        (∀ t y, Gcap t y = Ψ t ((Ψ (e p 2 - r ^ 2 / 2)).symm
          (Acap (y, e p 2 - r ^ 2 / 2)).1)) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Gcap z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Gcap z.1).symm z.2) ∧
        (∀ t ∈ Icc τ (e p 2 - r ^ 2 / 2 - (c + s)),
          C t = Gcap (c + s + t) '' sphere 0 r) ∧
        (∀ t ∈ Icc (c + s + τ) (e p 2 - r ^ 2 / 2),
          (Gcap t '' closedBall 0 r) ∩ ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
            Gcap t '' sphere 0 r) ∧
        (∃ d : ℝ, 0 < d ∧ ∃ R : ℝ, r < R ∧
          ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - d) (e p 2 - r ^ 2 / 2 + d),
            ∀ x ∈ closedBall (0 : Plane) R,
              Gcap t x = (Acap (DifferentialGeometry.Analysis.ODE.quadraticLevelScaling
                (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1) ∧
      ∃ γ : unitInterval → Plane, ∃ η : unitInterval → SphereTwo,
        IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ γ ∧
        ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
        (∀ u, L (e (η u)) = (γ u, c + s + τ)) ∧
        γ 0 = B (saddleBandLevelCurve s τ σ (-h)) ∧
        γ 1 = B (saddleBandLevelCurve s τ σ h) ∧
        range γ = C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) ∧
        range η = {x | e x 2 = c + s + τ ∧ (L (e x)).1 ∈
          C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      ∃ D : ℝ, 0 < D ∧ 4 * δ < D ∧ D < s * h ^ 2 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set SphereTwo, IsOpen N ∧ range η ⊆ N ∧
        (∀ v ∈ Icc (-D) D, ∀ x ∈ N, e (Φ v x) 2 = e x 2 + v) ∧
        (∀ x ∈ N, e x 2 = c + s + τ → (L (e x)).1 ∈ C τ) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡 2) ∞
          (fun q : ℝ × unitInterval => Φ (q.1 - τ) (η q.2)) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞
          (fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1) ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => (L (e (Φ (t - τ) (η u)))).1) ∧
          (∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
          (L (e (Φ (t - τ) (η 0)))).1 = B (saddleBandLevelCurve s t σ (-h)) ∧
          (L (e (Φ (t - τ) (η 1)))).1 = B (saddleBandLevelCurve s t σ h) ∧
          ∀ u, B.symm (L (e (Φ (t - τ) (η u)))).1 ∉
            Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ) ∧
        (∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ u : unitInterval,
          (u : ℝ) < ε ∨ 1 - ε < (u : ℝ) →
          (B.symm (γ u)).1 ∈ Ioo (-1 : ℝ) 1 ∧
          h ^ 2 ≤ (B.symm (γ u)).1 ^ 2 ∧
          ∀ t ∈ Icc (-δ) δ,
            0 < t + s * (B.symm (γ u)).1 ^ 2 ∧
            (L (e (Φ (t - τ) (η u)))).1 =
              B (saddleBandLevelCurve s t σ (B.symm (γ u)).1)) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => (L (e (Φ (t - τ) (η u)))).1))) ∧
        (∃ A : ℝ → (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => A q.1 q.2) ∧
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => (A q.1).symm q.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, Plane × ℝ) (Plane × ℝ) ∞ ∧
          (∀ v ∈ Icc (-D) D, ∀ x, A v (L (e x)) = L (e (Φ v x)) ∧
            (A v).symm (L (e (Φ v x))) = L (e x)) ∧
          ∃ S : Set (Plane × ℝ), IsCompact S ∧ ∀ v,
            EqOn (A v) id Sᶜ ∧ EqOn (A v).symm id Sᶜ) ∧
        IsCompact ((fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
          (Icc (-δ) δ ×ˢ univ)) ∧
        ∃ V : Set (Plane × ℝ), IsOpen V ∧
          (L ∘ e) '' ((fun q : ℝ × SphereTwo => Φ q.1 q.2) ''
            (Ioo (-D) D ×ˢ (N ∩ {x | e x 2 = c + s + τ}))) = V ∩ range (L ∘ e) ∧
          (fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
            (Icc (-δ) δ ×ˢ univ) ⊆ V ∧
          (∀ t ∈ Icc (-δ) δ, ∀ u,
            B.symm (L (e (Φ (t - τ) (η u)))).1 ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
            B.symm (L (e (Φ (t - τ) (η u)))).1 = saddleBandLevelCurve s t σ (-h) ∨
              B.symm (L (e (Φ (t - τ) (η u)))).1 = saddleBandLevelCurve s t σ h) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 →
            ∀ u ∈ Icc (-h) h,
              saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) ∧
          Icc (-h) h ×ˢ Icc (-ρ) ρ ⊆ U ∧
          ∀ z ∈ Icc (-(2 * h)) (2 * h) ×ˢ Icc (-(2 * ρ)) (2 * ρ),
            ∀ t ∈ Icc (-(2 * δ)) (2 * δ),
              (B z, c + s + t) ∈ range (L ∘ e) ↔
                (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have heL := he.continuousLinearEquiv_comp L
  obtain ⟨p, hpmax, hpnd, hpnotmax, δcap, k, R, hδcap, hδcapp, hk, hkone,
      hR, hkR, hRU, hboxlevel, σ, hσmem, hcapdata⟩ :=
    exists_height_level_isotopy_saddle_cap_normal_form_of_one_saddle
      he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  have hσ : σ ^ 2 = 1 := by
    have hcases : σ = -1 ∨ σ = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hσmem
    rcases hcases with rfl | rfl <;> norm_num
  obtain ⟨h, v, δparam, hh, hhv, hvk, hvone, hδparam, hδparamsh, hparams⟩ :=
    exists_fixed_saddle_endpoint_parameters hs (half_pos hk) (show 0 < R / 4 by positivity)
  have hhb : h < k / 2 := hhv.trans hvk
  have hbox : Icc (-(k / 2)) (k / 2) ×ˢ Icc (-(R / 2)) (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    have hx : |z.1| ≤ k / 2 := abs_le.mpr hz.1
    have hy : |z.2| ≤ R / 2 := abs_le.mpr hz.2
    simpa only [Real.norm_eq_abs] using And.intro (hx.trans (by linarith)) (hy.trans (by linarith))
  have hzeroeq : L (e (β (0, 0))) = (B (0, 0), c + s) := by
    simpa using hgraph (0, 0) hzero
  have hcritical : ∀ x, (L (e x)).2 = c + s →
      IsCriticalPointAt (𝓡 2) (fun y => (L (e y)).2) x →
      B.symm (L (e x)).1 ∈ Ioo (-(k / 2)) (k / 2) ×ˢ Ioo (-(R / 2)) (R / 2) := by
    intro x hx hxc
    have hxe : x = β (0, 0) :=
      hinj hxc hβcrit (hx.trans (congrArg Prod.snd hzeroeq).symm)
    rw [hxe, hzeroeq, B.symm_apply_apply]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨d, hd, hdsh, δflow, hδflow, hδflowd, N, P, hN, hfixedN, hP, hCP, hPreg,
      Φ, hΦ, hΦi, hΦ0, hstay, hcurve, hheight, hav, Aflow, hAflow, hAflowi, hAflow0,
      hAflowe, hAflowsupp⟩ := exists_saddle_closing_arc_transport_inter_rectangle (by simp) heL B hU hβ hs hh hhb
        (show k / 2 < k by linarith) hkone (half_pos hR) (half_lt_self hR) hbox hgraph hcritical
  let δ := min (δflow / 8) (min (δcap / 2) (δparam / 2))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδflowbound : δ ≤ δflow / 8 := min_le_left _ _
  have hδcapbound : δ ≤ δcap / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδparambound : δ ≤ δparam / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let τ := δ / 2
  have hτ : τ ∈ Ioo (0 : ℝ) δcap := ⟨half_pos hδ, by dsimp [τ]; linarith⟩
  have hτflow : τ ∈ Ioo (0 : ℝ) δflow := ⟨half_pos hδ, by dsimp [τ]; linarith⟩
  have hτparam : τ ∈ Icc (0 : ℝ) δparam := ⟨hτ.1.le, by dsimp [τ]; linarith⟩
  obtain ⟨hKp, hKq, hK, hKU, hKreg, hKlevel, hap, hregular,
      r, hr, hab, Acap, hAcap, hnormal, hcap, Ψ, hΨ, hΨi, hΨa, hlevels,
      hcontact, hsupport, hgerm, hcapgerm, hselected, hopp, Vside, hVside,
      hKVside, hVsideU, hinside, hclosed, hrectU, hside, htail⟩ := hcapdata τ hτ
  let Ap : (Plane × ℝ) ≃ₘ⟮𝓘(ℝ, Plane).prod 𝓘(ℝ), 𝓘(ℝ, Plane).prod 𝓘(ℝ)⟯ (Plane × ℝ) :=
    { toEquiv := Acap.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact Acap.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact Acap.symm.contMDiff }
  let G := (Ap.restrictFiber hAcap (e p 2 - r ^ 2 / 2)).trans
    ((Ψ (e p 2 - r ^ 2 / 2)).symm.trans (Ψ (c + s + τ)))
  have hcircle : (fun y => (y, c + s + τ)) '' (G '' sphere 0 r) ⊆ range (L ∘ e) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem := (hcontact (c + s + τ) ⟨le_rfl, hab.le⟩).symm.subset hy
    obtain ⟨x, hx, hxy⟩ := hmem.2
    exact ⟨x, Prod.ext hxy hx⟩
  have hselectedh : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ⊆ G '' sphere 0 r := by
    exact (image_mono (image_mono (Icc_subset_Icc
      (show -k ≤ -h by linarith) (show h ≤ k by linarith)))).trans hselected
  obtain ⟨γ, η, hγ, hη, hηemb, hηeq, hγ0, hγ1, hunion, hinter⟩ :=
    exists_saddleBandLevelCurve_complementary_arc_lift heL B G hs.le hτ.1 hh
      (hhv.trans hvone) hr hselectedh hcircle
  have hηrange := range_lift_eq_sdiff_image_saddleBandLevelCurve heL.isEmbedding.injective
    B.injective hηeq hunion hinter
  have hηsub := hηrange.subset
  have hηN : range η ⊆ N := hηsub.trans (hav τ hτflow σ hσ G.toHomeomorph r hr hside).1
  have hcircleJordan : IsJordanCurve (G '' sphere 0 r) :=
    isJordanCurve_image_sphere G.toHomeomorph 0 hr
  have hcirclepre : G '' sphere 0 r ⊆
      (fun y : Plane => L.symm (y, c + s + τ)) ⁻¹' range e := by
    intro y hy
    obtain ⟨x, hx⟩ := hcircle ⟨y, hy, rfl⟩
    exact ⟨x, L.injective (by simpa using hx)⟩
  obtain ⟨O, hO, hOlevel⟩ := exists_isOpen_inter_height_level_eq_of_isJordanCurve he
    (c + s + τ) (fun x hx => hregular x ⟨hx.ge, hx.trans_lt hap⟩) hcircleJordan hcirclepre
  let N' := N ∩ (fun x => (L (e x)).1) ⁻¹' O
  have hN' : IsOpen N' := hN.inter (hO.preimage (continuous_fst.comp heL.contMDiff.continuous))
  have hηN' : range η ⊆ N' := by
    intro x hx
    refine ⟨hηN hx, ?_⟩
    obtain ⟨u, rfl⟩ := hx
    change ((L ∘ e) (η u)).1 ∈ O
    rw [hηeq]
    exact (hOlevel.symm.subset ((hunion ▸ subset_union_right) (mem_range_self u))).1
  have hwindow : δ + |τ| < δflow := by rw [abs_of_pos hτ.1]; dsimp [τ]; linarith
  have hfamily := contMDiff_and_isSmoothEmbedding_level_arc_transport heL hγ hη Φ hΦ hΦi hΦ0
    hN' hηN' hwindow (fun t ht x hx => hheight x hx.1 t ht) hηeq Aflow
    (fun t ht x => (hAflowe t ht x).1)
  have hκsmall (u : ℝ) (hu : u ∈ Icc (-h) h) :
      saddleBandLevelCurve s τ σ u ∈ Ioo (-(k / 2)) (k / 2) ×ˢ Ioo (-(R / 4)) (R / 4) :=
    hparams τ hτparam σ hσmem ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  have hκbox (u : ℝ) (hu : u ∈ Icc (-h) h) :
      saddleBandLevelCurve s τ σ u ∈ Icc (-(k / 2)) (k / 2) ×ˢ Icc (-(R / 2)) (R / 2) := by
    have ht := hκsmall u hu
    exact ⟨⟨ht.1.1.le, ht.1.2.le⟩, ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩⟩
  have huone (u : ℝ) (hu : u ∈ Icc (-h) h) : u ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hκheight (u : ℝ) (hu : u ∈ Icc (-h) h) :=
    saddleBandLevelCurve_height hs.le hτ.1 hσ (huone u hu) c
  have hendP (u : ℝ) (hu : u = -h ∨ u = h) : β (saddleBandLevelCurve s τ σ u) ∈ P := by
    have hucc : u ∈ Icc (-h) h := by rcases hu with rfl | rfl <;> constructor <;> linarith
    apply hCP
    refine ⟨saddleBandLevelCurve s τ σ u, ⟨hκbox u hucc, ?_, ?_⟩, rfl⟩
    · change h ^ 2 ≤ u ^ 2
      rcases hu with rfl | rfl <;> nlinarith
    · rw [hκheight u hucc]
      have heq : c + s + τ - (c + s) = τ := by ring
      rw [heq, abs_of_pos hτ.1]
      exact hτflow.2.le.trans hδflowd
  have hηend (v : unitInterval) (u : ℝ) (hu : u ∈ Icc (-h) h)
      (hvu : γ v = B (saddleBandLevelCurve s τ σ u)) : η v = β (saddleBandLevelCurve s τ σ u) := by
    apply heL.isEmbedding.injective
    rw [hηeq, hvu]
    change (B (saddleBandLevelCurve s τ σ u), c + s + τ) = L (e (β (saddleBandLevelCurve s τ σ u)))
    rw [hgraph _ (hbox (hκbox u hu)), hκheight u hu]
  have hη0P : η 0 ∈ P := by
    rw [hηend 0 (-h) ⟨le_rfl, by linarith⟩ hγ0]
    exact hendP (-h) (Or.inl rfl)
  have hη1P : η 1 ∈ P := by
    rw [hηend 1 h ⟨by linarith, le_rfl⟩ hγ1]
    exact hendP h (Or.inr rfl)
  have hγsub : range γ ⊆ (G '' sphere 0 r) \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) := by
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    simpa only [hηeq, Diffeomorph.coe_toEquiv] using (hηsub (mem_range_self u)).2
  have hregflow (x : SphereTwo) (hx : x ∈ P) (t : ℝ) (ht : t ∈ Icc (-δflow) δflow) :
      (1 - (B.symm (L (e (Φ t x))).1).1 ^ 2) * (B.symm (L (e (Φ t x))).1).2 ≠ 0 := by
    obtain ⟨z, hz, hzx⟩ := hstay t ht hx
    rw [← hzx, hgraph z hz.1, B.symm_apply_apply]
    exact hz.2
  have hendbig (u : ℝ) (hu : u ∈ Icc (-h) h) :
      saddleBandLevelCurve s τ σ u ∈ Ioo (-k) k ×ˢ Ioo (-R) R := by
    have ht := hκsmall u hu
    constructor <;> constructor <;> linarith [ht.1.1, ht.1.2, ht.2.1, ht.2.2]
  obtain ⟨W, hW, hW0, hW1, hWP, hWcurve⟩ :=
    exists_open_endpoint_saddleBandLevelCurve_transport hη.continuous hγ.contMDiff.continuous
      B.toHomeomorph G.toHomeomorph hs.le hσ hh.le hkone hr hδflow
      (show δflow < τ + s * h ^ 2 by linarith [hτ.1]) hηeq hγ0 hγ1
      (hendbig (-h) ⟨le_rfl, by linarith⟩) (hendbig h ⟨by linarith, le_rfl⟩)
      hside hγsub hP hη0P hη1P (fun t x => Φ t x)
      (fun x => by rw [hΦ0]; rfl) hcurve hregflow
  have htime (t : ℝ) (ht : t ∈ Icc (-δ) δ) : t - τ ∈ Icc (-δflow) δflow := by
    have hτpos := hτ.1
    dsimp [τ] at *
    constructor <;> linarith [ht.1, ht.2]
  have hendpoint (u : unitInterval) (hu : u ∈ W) (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      (L (e (Φ (t - τ) (η u)))).1 = B (saddleBandLevelCurve s t σ (B.symm (γ u)).1) := by
    have hh := (hWcurve u hu).2.2.2 (t - τ) (htime t ht)
    rw [show τ + (t - τ) = t by ring] at hh
    exact hh
  have hendpoint0 (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      (L (e (Φ (t - τ) (η 0)))).1 = B (saddleBandLevelCurve s t σ (-h)) := by
    simpa only [hγ0, B.symm_apply_apply, saddleBandLevelCurve] using hendpoint 0 hW0 t ht
  have hendpoint1 (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      (L (e (Φ (t - τ) (η 1)))).1 = B (saddleBandLevelCurve s t σ h) := by
    simpa only [hγ1, B.symm_apply_apply, saddleBandLevelCurve] using hendpoint 1 hW1 t ht
  have hexclude (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) δ) :
      B (saddleBandLevelCurve s t σ 0) ∉ range (fun u => (L (e (Φ (t - τ) (η u)))).1) := by
    have havt := (hav τ hτflow σ hσ G.toHomeomorph r hr hside).2.2.2 (t - τ)
      (htime t ⟨by linarith [ht.1], ht.2⟩) (by linarith [ht.1])
    have heq : τ + (t - τ) = t := by ring
    rw [heq] at havt
    rintro ⟨u, hu⟩
    exact havt ⟨η u, hηsub (mem_range_self u), hu⟩
  let C (t : ℝ) := (fun x => (L (e x)).1) ''
    (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
  have hCτ : C τ = G '' sphere 0 r := by
    obtain ⟨G', hG', hboundary⟩ := exists_diffeomorph_height_cap_component_level he hr hab.le
      hregular Acap hAcap hcap Ψ hΨ.continuous hΨa hlevels ⟨le_rfl, hab.le⟩
    rw [hG'] at hboundary
    exact hboundary
  have hN'circle (x : SphereTwo) (hx : x ∈ N') (hxlevel : e x 2 = c + s + τ) :
      (L (e x)).1 ∈ C τ := by
    rw [hCτ, ← hOlevel]
    refine ⟨hx.2, ?_⟩
    change L.symm ((L (e x)).1, c + s + τ) ∈ range e
    refine ⟨x, ?_⟩
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl hxlevel
  have hcore (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) :
      B.symm (L (e (Φ (t - τ) (η u)))).1 ∉
        Icc (-(h / 2)) (h / 2) ×ˢ Icc (-(R / 4)) (R / 4) := by
    have havt := (hav τ hτflow σ hσ G.toHomeomorph r hr hside).2.2.1
      (t - τ) (htime t ht) (η u) (hηsub (mem_range_self u)).1 (hηsub (mem_range_self u)).2
    simpa only [Function.comp_apply, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using havt
  have hcontactRect (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval)
      (hmem : B.symm (L (e (Φ (t - τ) (η u)))).1 ∈
        Icc (-h) h ×ˢ Icc (-(R / 4)) (R / 4)) :
      B.symm (L (e (Φ (t - τ) (η u)))).1 = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (L (e (Φ (t - τ) (η u)))).1 = saddleBandLevelCurve s t σ h := by
    have havt := (hav τ hτflow σ hσ G.toHomeomorph r hr hside).2.1
      (t - τ) (htime t ht) (η u) (hηsub (mem_range_self u)).1
      (hηsub (mem_range_self u)).2
      (by simpa only [Function.comp_apply, div_div,
        show (2 : ℝ) * 2 = 4 by norm_num] using hmem)
    simpa only [add_sub_cancel, Function.comp_apply] using havt
  have hrectangle : Icc (-h) h ×ˢ Icc (-(R / 4)) (R / 4) ⊆ U := by
    intro z hz
    apply hbox
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hrectangleLevel (z : ℝ × ℝ)
      (hz : z ∈ Icc (-(2 * h)) (2 * h) ×ˢ Icc (-(2 * (R / 4))) (2 * (R / 4)))
      (t : ℝ) (ht : t ∈ Icc (-(2 * δ)) (2 * δ)) :
      (B z, c + s + t) ∈ range (L ∘ e) ↔
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t := by
    have hzball : z ∈ closedBall (0 : ℝ × ℝ) R := by
      rw [mem_closedBall_zero_iff, norm_prod_le_iff]
      simpa only [Real.norm_eq_abs] using And.intro
        ((abs_le.mpr hz.1).trans (by linarith))
        ((abs_le.mpr hz.2).trans (by linarith))
    have htball : c + s + t ∈ closedBall (c + s) δcap := by
      rw [mem_closedBall, Real.dist_eq, add_sub_cancel_left]
      exact (abs_le.mpr ht).trans (by linarith)
    change (B z, c + s + t) ∈ range (EuclideanSpace.equivProdLast 2 ∘ e) ↔ _
    rw [hboxlevel z hzball (c + s + t) htball]
    constructor <;> intro heq <;> linarith
  have hmodelRect (t : ℝ) (ht : t ∈ Icc (-δ) δ) (σ' : ℝ) (hσ' : σ' ^ 2 = 1)
      (u : ℝ) (hu : u ∈ Icc (-h) h) :
      saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-(R / 4)) (R / 4) := by
    have hσ'mem : σ' ∈ ({-1, 1} : Set ℝ) := by
      rcases sq_eq_one_iff.mp hσ' with hpos | hneg
      · simp only [mem_insert_iff, mem_singleton_iff]
        exact Or.inr hpos
      · simp only [mem_insert_iff, mem_singleton_iff]
        exact Or.inl hneg
    have hupper := hparams δ ⟨hδ.le, by linarith⟩ σ' hσ'mem
      ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
    apply saddleBandLevelCurve_mem_rectangle_of_le ht.2 (huone u hu)
    exact ⟨hu, hupper.2.1.le, hupper.2.2.le⟩
  have hcoverage (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) δ) :
      IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
        (B (saddleBandLevelCurve s t σ h))
        (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
        (range (fun u => (L (e (Φ (t - τ) (η u)))).1)) := by
    have htt : t ∈ Icc (-δ) δ := ⟨by linarith [ht.1], ht.2⟩
    have htcap : t ∈ Ioo (0 : ℝ) δcap := ⟨ht.1, by linarith [ht.2]⟩
    obtain ⟨_, _, _, _, _, _, htmax, htregular,
        rt, hrt, hatbt, At, hAt, _, hcapt, Ψt, hΨt, _, hΨta, hlevelst,
        _, _, _, _, hselectedt, _⟩ := hcapdata t htcap
    obtain ⟨Gt, hGt, hCt⟩ := exists_diffeomorph_height_cap_component_level he hrt hatbt.le
      htregular At hAt hcapt Ψt hΨt.continuous hΨta hlevelst ⟨le_rfl, hatbt.le⟩
    have hArc₀ := isArcBetween_image_saddleBandLevelCurve B.continuous B.injective hs.le ht.1 hh
      (hhv.trans hvone) (σ := σ)
    have hArc : IsArcBetween (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
        (L (e (Φ (t - τ) (η 0)))).1 (L (e (Φ (t - τ) (η 1)))).1 := by
      rw [hendpoint0 t htt, hendpoint1 t htt]
      exact hArc₀
    have hsubt : B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) ⊆
        (fun y => Ψt (c + s + t) ((Ψt (e p 2 - rt ^ 2 / 2)).symm
          (At (y, e p 2 - rt ^ 2 / 2)).1)) '' sphere 0 rt :=
      (image_mono (image_mono (Icc_subset_Icc (show -k ≤ -h by linarith)
        (show h ≤ k by linarith)))).trans hselectedt
    have hc := isCutPair_of_height_cap_level_arc he hrt hatbt.le htregular At hAt hcapt Ψt
      hΨt.continuous hΨta hlevelst ⟨le_rfl, hatbt.le⟩
      ((Φ (t - τ)).continuous.comp hη.continuous)
      ((Φ (t - τ)).injective.comp hηemb.injective)
      (hfamily.2.2.1 t htt).2 hArc hsubt
      ⟨B (saddleBandLevelCurve s t σ 0),
        ⟨saddleBandLevelCurve s t σ 0, ⟨0, ⟨by linarith, hh.le⟩, rfl⟩, rfl⟩,
        hexclude t ht⟩
    change IsCutPair _ (L (e (Φ (t - τ) (η 0)))).1
      (L (e (Φ (t - τ) (η 1)))).1 _ _ at hc
    rw [hendpoint0 t htt, hendpoint1 t htt] at hc
    change IsCutPair ((fun x => (L (e x)).1) ''
      (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})) _ _ _ _
    rw [hCt, hGt]
    exact hc
  have hγrange := range_eq_sdiff_image_saddleBandLevelCurve B.injective hunion hinter
  rw [← hCτ] at hγrange hηrange
  obtain ⟨ε₀, hε₀, hεW⟩ := exists_pos_endpoint_intervals_subset hW hW0 hW1
  let ε := min ε₀ (1 / 4)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hεsub (u : unitInterval) (hu : (u : ℝ) < ε ∨ 1 - ε < (u : ℝ)) : u ∈ W := by
    apply hεW
    rcases hu with hu | hu
    · exact Or.inl (hu.trans_le (min_le_left _ _))
    · right
      linarith [min_le_left ε₀ (1 / 4)]
  obtain ⟨hsourcefamily, hplanefamily, hslices, hfamilyτ, hcompact, V, hV, hVe, htraceV⟩ := hfamily
  let Gbase := (Ap.restrictFiber hAcap (e p 2 - r ^ 2 / 2)).trans (Ψ (e p 2 - r ^ 2 / 2)).symm
  let Gcap : ℝ → Plane ≃ₘ[ℝ] Plane := fun t => Gbase.trans (Ψ t)
  have hGcap : ContDiff ℝ ∞ (fun z : ℝ × Plane => Gcap z.1 z.2) :=
    hΨ.comp (contDiff_fst.prodMk (Gbase.contDiff.comp contDiff_snd))
  have hGcapi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (Gcap z.1).symm z.2) :=
    Gbase.symm.contDiff.comp hΨi
  refine ⟨p, hpmax, hpnd, hpnotmax, σ, hσmem, h, hh, hhv.trans hvone, δ, hδ,
    r, hr, hab, Acap, hAcap, hnormal, hcap, Ψ, hΨ, hΨi, hΨa,
    Gcap, (fun _ _ => rfl), hGcap, hGcapi, ?_, hcontact, hcapgerm,
    γ, η, hγ, hη, hηeq, hγ0, hγ1, hγrange, hηrange,
    Φ, hΦ, hΦi, hΦ0, δflow, hδflow, ?_, hδflowd.trans_lt hdsh,
    R / 4, by positivity, N', hN', hηN', ?_, hN'circle,
    hsourcefamily, hplanefamily, ?_, ?_, hcoverage,
    ⟨Aflow, hAflow, hAflowi, hAflow0, hAflowe, hAflowsupp⟩,
    hcompact, V, hV, hVe, htraceV, hcontactRect, hmodelRect, hrectangle, hrectangleLevel⟩
  · intro t ht
    change t ∈ Icc τ (e p 2 - r ^ 2 / 2 - (c + s)) at ht
    obtain ⟨Gt, hGt, hCt⟩ := exists_diffeomorph_height_cap_component_level he hr hab.le
      hregular Acap hAcap hcap Ψ hΨ.continuous hΨa hlevels
      (show c + s + t ∈ Icc (c + s + τ) (e p 2 - r ^ 2 / 2) by
        constructor <;> linarith [ht.1, ht.2])
    rw [hGt] at hCt
    exact hCt
  · linarith
  · intro t ht x hx
    exact hheight x hx.1 t ht
  · intro t ht
    exact ⟨(hslices t ht).1, (hslices t ht).2, hendpoint0 t ht, hendpoint1 t ht, hcore t ht⟩
  · refine ⟨ε, hε, hεsmall, ?_⟩
    intro u hu
    have huW := hεsub u hu
    have hrect := (hWcurve u huW).1.1
    change (B.symm (γ u)).1 ∈ Ioo (-k) k at hrect
    have hsq := (hWcurve u huW).2.1
    change h ^ 2 ≤ (B.symm (γ u)).1 ^ 2 at hsq
    refine ⟨⟨by linarith [hrect.1], by linarith [hrect.2]⟩, hsq, ?_⟩
    intro t ht
    refine ⟨?_, hendpoint u huW t ht⟩
    have hmul := mul_le_mul_of_nonneg_left hsq hs.le
    linarith [ht.1, hδflowd.trans_lt hdsh]

theorem exists_closing_arc_family_and_height_cap_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ r : ℝ, 0 < r ∧ c + s + τ < e p 2 - r ^ 2 / 2 ∧
      ∃ Acap : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ z, (Acap z).2 = z.2) ∧
        (∃ R T : ℝ, r < R ∧ 0 < T ∧ r ^ 2 / 2 < T ∧
          (closedBall 0 R ×ˢ closedBall (e p 2) T) ∩ range (fun x => Acap.symm (L (e x))) =
            (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) ∧
        (L ∘ e) '' connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
          (fun y => Acap (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
      ∃ Ψ : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Ψ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Ψ z.1).symm z.2) ∧
        Ψ (c + s + τ) = Diffeomorph.refl (𝓡 2) Plane ∞ ∧
      ∃ Gcap : ℝ → Plane ≃ₘ[ℝ] Plane,
        (∀ t y, Gcap t y = Ψ t ((Ψ (e p 2 - r ^ 2 / 2)).symm
          (Acap (y, e p 2 - r ^ 2 / 2)).1)) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => Gcap z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (Gcap z.1).symm z.2) ∧
        (∀ t ∈ Icc τ (e p 2 - r ^ 2 / 2 - (c + s)),
          C t = Gcap (c + s + t) '' sphere 0 r) ∧
        (∀ t ∈ Icc (c + s + τ) (e p 2 - r ^ 2 / 2),
          (Gcap t '' closedBall 0 r) ∩ ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
            Gcap t '' sphere 0 r) ∧
        (∃ d : ℝ, 0 < d ∧ ∃ R : ℝ, r < R ∧
          ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - d) (e p 2 - r ^ 2 / 2 + d),
            ∀ x ∈ closedBall (0 : Plane) R,
              Gcap t x = (Acap (DifferentialGeometry.Analysis.ODE.quadraticLevelScaling
                (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1) ∧
      ∃ γ : unitInterval → Plane, ∃ η : unitInterval → SphereTwo,
        IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ γ ∧
        ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
        (∀ u, L (e (η u)) = (γ u, c + s + τ)) ∧
        γ 0 = B (saddleBandLevelCurve s τ σ (-h)) ∧
        γ 1 = B (saddleBandLevelCurve s τ σ h) ∧
        range γ = C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) ∧
        range η = {x | e x 2 = c + s + τ ∧ (L (e x)).1 ∈
          C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      ∃ D : ℝ, 0 < D ∧ 4 * δ < D ∧ D < s * h ^ 2 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set SphereTwo, IsOpen N ∧ range η ⊆ N ∧
        (∀ v ∈ Icc (-D) D, ∀ x ∈ N, e (Φ v x) 2 = e x 2 + v) ∧
        (∀ x ∈ N, e x 2 = c + s + τ → (L (e x)).1 ∈ C τ) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡 2) ∞
          (fun q : ℝ × unitInterval => Φ (q.1 - τ) (η q.2)) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞
          (fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1) ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => (L (e (Φ (t - τ) (η u)))).1) ∧
          (∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
          (L (e (Φ (t - τ) (η 0)))).1 = B (saddleBandLevelCurve s t σ (-h)) ∧
          (L (e (Φ (t - τ) (η 1)))).1 = B (saddleBandLevelCurve s t σ h) ∧
          ∀ u, B.symm (L (e (Φ (t - τ) (η u)))).1 ∉
            Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ) ∧
        (∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ u : unitInterval,
          (u : ℝ) < ε ∨ 1 - ε < (u : ℝ) →
          (B.symm (γ u)).1 ∈ Ioo (-1 : ℝ) 1 ∧
          h ^ 2 ≤ (B.symm (γ u)).1 ^ 2 ∧
          ∀ t ∈ Icc (-δ) δ,
            0 < t + s * (B.symm (γ u)).1 ^ 2 ∧
            (L (e (Φ (t - τ) (η u)))).1 =
              B (saddleBandLevelCurve s t σ (B.symm (γ u)).1)) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => (L (e (Φ (t - τ) (η u)))).1))) ∧
        (∃ A : ℝ → (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => A q.1 q.2) ∧
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => (A q.1).symm q.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, Plane × ℝ) (Plane × ℝ) ∞ ∧
          (∀ v ∈ Icc (-D) D, ∀ x, A v (L (e x)) = L (e (Φ v x)) ∧
            (A v).symm (L (e (Φ v x))) = L (e x)) ∧
          ∃ S : Set (Plane × ℝ), IsCompact S ∧ ∀ v,
            EqOn (A v) id Sᶜ ∧ EqOn (A v).symm id Sᶜ) ∧
        IsCompact ((fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
          (Icc (-δ) δ ×ˢ univ)) ∧
        ∃ V : Set (Plane × ℝ), IsOpen V ∧
          (L ∘ e) '' ((fun q : ℝ × SphereTwo => Φ q.1 q.2) ''
            (Ioo (-D) D ×ˢ (N ∩ {x | e x 2 = c + s + τ}))) = V ∩ range (L ∘ e) ∧
          (fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
            (Icc (-δ) δ ×ˢ univ) ⊆ V := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      r, hr, hab, Acap, hAcap, hnormal, hcap, Ψ, hΨ, hΨi, hΨa,
      Gcap, hGformula, hGcap, hGcapi, hCcap, hcontact, hgerm,
      γ, η, hγ, hη, hηeq, hγ0, hγ1, hγrange, hηrange,
      Φ, hΦ, hΦi, hΦ0, D, hD, hδD, hDsh, ρ, hρ, N, hN, hηN,
      hheight, hNcircle, hsourcefamily, hplanefamily, hslices, hendpoints,
      hcoverage, hambient, hcompact, V, hV, hVe, htraceV, _, _⟩ :=
    exists_closing_arc_family_and_height_cap_inter_rectangle_of_one_saddle
      he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  exact ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    r, hr, hab, Acap, hAcap, hnormal, hcap, Ψ, hΨ, hΨi, hΨa,
    Gcap, hGformula, hGcap, hGcapi, hCcap, hcontact, hgerm,
    γ, η, hγ, hη, hηeq, hγ0, hγ1, hγrange, hηrange,
    Φ, hΦ, hΦi, hΦ0, D, hD, hδD, hDsh, ρ, hρ, N, hN, hηN,
    hheight, hNcircle, hsourcefamily, hplanefamily, hslices, hendpoints,
    hcoverage, hambient, hcompact, V, hV, hVe, htraceV⟩

theorem exists_closing_arc_family_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ γ : unitInterval → Plane, ∃ η : unitInterval → SphereTwo,
        IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ γ ∧
        ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
        (∀ u, L (e (η u)) = (γ u, c + s + τ)) ∧
        γ 0 = B (saddleBandLevelCurve s τ σ (-h)) ∧
        γ 1 = B (saddleBandLevelCurve s τ σ h) ∧
        range γ = C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) ∧
        range η = {x | e x 2 = c + s + τ ∧ (L (e x)).1 ∈
          C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      ∃ D : ℝ, 0 < D ∧ 4 * δ < D ∧ D < s * h ^ 2 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : Set SphereTwo, IsOpen N ∧ range η ⊆ N ∧
        (∀ v ∈ Icc (-D) D, ∀ x ∈ N, e (Φ v x) 2 = e x 2 + v) ∧
        (∀ x ∈ N, e x 2 = c + s + τ → (L (e x)).1 ∈ C τ) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡 2) ∞
          (fun q : ℝ × unitInterval => Φ (q.1 - τ) (η q.2)) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞
          (fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1) ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => (L (e (Φ (t - τ) (η u)))).1) ∧
          (∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
          (L (e (Φ (t - τ) (η 0)))).1 = B (saddleBandLevelCurve s t σ (-h)) ∧
          (L (e (Φ (t - τ) (η 1)))).1 = B (saddleBandLevelCurve s t σ h) ∧
          ∀ u, B.symm (L (e (Φ (t - τ) (η u)))).1 ∉
            Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ) ∧
        (∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ u : unitInterval,
          (u : ℝ) < ε ∨ 1 - ε < (u : ℝ) →
          (B.symm (γ u)).1 ∈ Ioo (-1 : ℝ) 1 ∧
          h ^ 2 ≤ (B.symm (γ u)).1 ^ 2 ∧
          ∀ t ∈ Icc (-δ) δ,
            0 < t + s * (B.symm (γ u)).1 ^ 2 ∧
            (L (e (Φ (t - τ) (η u)))).1 =
              B (saddleBandLevelCurve s t σ (B.symm (γ u)).1)) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => (L (e (Φ (t - τ) (η u)))).1))) ∧
        (∃ A : ℝ → (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => A q.1 q.2) ∧
          ContDiff ℝ ∞ (fun q : ℝ × (Plane × ℝ) => (A q.1).symm q.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, Plane × ℝ) (Plane × ℝ) ∞ ∧
          (∀ v ∈ Icc (-D) D, ∀ x, A v (L (e x)) = L (e (Φ v x)) ∧
            (A v).symm (L (e (Φ v x))) = L (e x)) ∧
          ∃ S : Set (Plane × ℝ), IsCompact S ∧ ∀ v,
            EqOn (A v) id Sᶜ ∧ EqOn (A v).symm id Sᶜ) ∧
        IsCompact ((fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
          (Icc (-δ) δ ×ˢ univ)) ∧
        ∃ V : Set (Plane × ℝ), IsOpen V ∧
          (L ∘ e) '' ((fun q : ℝ × SphereTwo => Φ q.1 q.2) ''
            (Ioo (-D) D ×ˢ (N ∩ {x | e x 2 = c + s + τ}))) = V ∩ range (L ∘ e) ∧
          (fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
            (Icc (-δ) δ ×ˢ univ) ⊆ V := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      r, hr, hab, Acap, hAcap, hnormal, hcap, Ψ, hΨ, hΨi, hΨa,
      Gcap, hGformula, hGcap, hGcapi, hCcap, hcontact, hgerm, hfamily⟩ :=
    exists_closing_arc_family_and_height_cap_of_one_saddle he hnd hinj hone hconn
      B hU hzero hβ hs hgraph hβcrit hβindex
  exact ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ, hfamily⟩

theorem exists_height_preserving_diffeomorph_closing_arc_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ γ : unitInterval → Plane, ∃ η : unitInterval → SphereTwo,
        IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ γ ∧
        ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
        (∀ u, L (e (η u)) = (γ u, c + s + τ)) ∧
        range γ = C τ \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => (L (e (Φ (t - τ) (η u)))).1) ∧
          ∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => (L (e (Φ (t - τ) (η u)))).1))) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ y, (D y).2 = y.2) ∧
        (∀ y, D (y, c + s + τ) = (y, c + s + τ)) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, D (γ u, c + s + t) = L (e (Φ (t - τ) (η u)))) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, D.symm (L (e (Φ (t - τ) (η u)))) = (γ u, c + s + t)) ∧
        D '' (range γ ×ˢ Icc (c + s - δ) (c + s + δ)) =
          (fun q : ℝ × unitInterval => L (e (Φ (q.1 - τ) (η q.2)))) ''
            (Icc (-δ) δ ×ˢ univ) ∧
        ∃ K : Set (Plane × ℝ), IsCompact K ∧
          K ⊆ (B '' (Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ))ᶜ ×ˢ
            Ioo (c + s - 2 * δ) (c + s + 2 * δ) ∧
          EqOn D id Kᶜ ∧ EqOn D.symm id Kᶜ := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      γ, η, hγ, hη, hηeq, hγ0, hγ1, hγrange, hηrange,
      Φ, hΦ, hΦi, hΦ0, T, hT, hδT, hTsh, ρ, hρ, N, hN, hηN, hheight, hNcircle,
      hsourcefamily, hplanefamily, hslices, hendpoints, hcoverage, hambient,
      hcompact, V, hV, hVe, htraceV⟩ :=
    exists_closing_arc_family_of_one_saddle he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  obtain ⟨D, hDheight, hDfix, hDforward, hDinverse, hDimage, K, hK, hKsub, hKid, hKiid⟩ :=
    exists_height_preserving_diffeomorph_of_transported_level_arc
      (f := L ∘ e) (Φ := fun t x => Φ t x) (B := B.toHomeomorph)
      (show δ / 2 ∈ Icc (-δ) δ by constructor <;> linarith)
      (fun x => by rw [hΦ0]; rfl) hηeq hplanefamily.contMDiffOn
      (fun t ht => (hslices t ht).1) (fun t ht => (hslices t ht).2.1)
      (fun t ht => (hslices t ht).2.2.2.2) isOpen_Ioo
      (show Icc (c + s - δ) (c + s + δ) ⊆ Ioo (c + s - 2 * δ) (c + s + 2 * δ) by
        intro t ht; constructor <;> linarith [ht.1, ht.2])
  exact ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ, ρ, hρ,
    γ, η, hγ, hη, hηeq, hγrange, Φ, hΦ, hΦi, hΦ0,
    (fun t ht => ⟨(hslices t ht).1, (hslices t ht).2.1⟩), hcoverage,
    D, hDheight, hDfix, hDforward, hDinverse, hDimage, K, hK, hKsub, hKid, hKiid⟩

theorem exists_ambient_isotopy_closing_arc_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ η : unitInterval → SphereTwo,
        ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - δ / 2) (η q.2)))).1
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)) ∧
          ∀ u, e (Φ (t - δ / 2) (η u)) 2 = c + s + t) ∧
        ∀ t₀ ∈ Ioo (0 : ℝ) δ,
        ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (0 : ℝ) δ ∧
          ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
            ContDiff ℝ ∞ (fun q : ℝ × Plane => P q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (P q.1).symm q.2) ∧
            P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
            (∃ V : Set (ℝ × ℝ), IsOpen V ∧
              saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V ∧
              (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2) ∧
              (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
                0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
              ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
                P t (B z) = B (DifferentialGeometry.Analysis.ODE.saddleBandCurve z (t - t₀))) ∧
            (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), P t '' C t₀ = C t) ∧
            ∃ S : Set Plane, IsCompact S ∧ ∀ t,
              EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      γ₀, η, hγ₀, hη, hηeq, hγ₀0, hγ₀1, hγrange, hηrange,
      Φ, hΦ, hΦi, hΦ0, T, hT, hδT, hTsh, ρ, hρ, N, hN, hηN, hheight, hNcircle,
      hsourcefamily, hplanefamily, hslices, hendpoints, hcoverage, hambient,
      hcompact, V, hV, hVe, htraceV⟩ :=
    exists_closing_arc_family_of_one_saddle he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  refine ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    η, hη, Φ, hΦ, hΦi, hΦ0, hplanefamily,
    (fun t ht => ⟨(hslices t ht).1, (hslices t ht).2.1⟩), ?_⟩
  intro t₀ ht₀
  obtain ⟨ε, hε, hεhalf, hendpoint⟩ := hendpoints
  let W : Set unitInterval := {u | (u : ℝ) < ε ∨ 1 - ε < (u : ℝ)}
  have hW : IsOpen W := (isOpen_lt continuous_subtype_val continuous_const).union
    (isOpen_lt continuous_const continuous_subtype_val)
  have hW0 : (0 : unitInterval) ∈ W := Or.inl (by simpa using hε)
  have hW1 : (1 : unitInterval) ∈ W := Or.inr (by change 1 - ε < 1; linarith)
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with hσ | hσ
    · rw [hσ]; norm_num
    · rw [mem_singleton_iff.mp hσ]; norm_num
  exact exists_ambient_isotopy_closing_arc_eqOn_saddle hplanefamily B hs.le hσsq hh1 ht₀
    (fun t ht => (hslices t ht).1) hW hW0 hW1
    (v := fun u => (B.symm (γ₀ u)).1)
    (fun u hu => ⟨(hendpoint u hu).1, fun t ht => ((hendpoint u hu).2.2 t ht).2⟩)
    (fun t ht => ⟨(hslices t ⟨by linarith [ht.1], ht.2⟩).2.2.1,
      (hslices t ⟨by linarith [ht.1], ht.2⟩).2.2.2.1⟩) hcoverage

end DifferentialGeometry.Topology.SphereSeparation
