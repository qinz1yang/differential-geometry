import DifferentialGeometry.Topology.SphereSeparation.SaddleBand
import DifferentialGeometry.Topology.PlanarJordan.BandCollar
import DifferentialGeometry.Topology.Morse.OneSaddleComponents
import DifferentialGeometry.Topology.Morse.Affine

open Set Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_ambient_isotopy_saddle_band_of_one_saddle {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ p : SphereTwo, IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) p).symm y) 2)
        (extChartAt (𝓡 2) p p)) = 1 ∧
    ∃ s : ℝ, 0 < s ∧ s < η ∧ ∃ Φ : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
      (∀ x, Φ 1 (e x) 2 = e p 2 →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => Φ 1 (e y) 2) x ≠ 0) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x ↔
        IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
        chartHessianAt (fun y => Φ 1 (e ((extChartAt (𝓡 2) x).symm y)) 2)
          (extChartAt (𝓡 2) x x) =
        chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
          (extChartAt (𝓡 2) x x)) ∧
      (fun y => Φ 1 (e y) 2) =ᶠ[𝓝 p] (fun y => e y 2 + s) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x ≠ p →
        (fun y => Φ 1 (e y) 2) =ᶠ[𝓝 x] (fun y => e y 2)) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x →
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x) ∧
      InjOn (fun x => Φ 1 (e x) 2)
        {x | IsCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x} ∧
      ((∀ a : ℝ, IsPreconnected {x | Φ 1 (e x) 2 < a}) ∨
        (∀ a : ℝ, IsPreconnected {x | a < Φ 1 (e x) 2})) ∧
      (∃ K : Set EuclideanThree, IsCompact K ∧ ∀ t,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ) ∧
      ∃ h > 0, ∃ B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane,
        ∃ β : ℝ × ℝ → SphereTwo, β (0, 0) = p ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ∧
          InjOn β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ∧
          β '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆
            connectedComponentIn {x | e p 2 < Φ 1 (e x) 2} p ∧
          β '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆
            closure (connectedComponentIn {x | e p 2 < Φ 1 (e x) 2} p) ∧
          (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
            Φ 1 (e (β z)) 2 = e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
          (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h, z.1 = -1 ∨ z.1 = 1 →
            Φ 1 (e (β z)) = (EuclideanSpace.equivProdLast 2).symm (B z, e p 2)) ∧
        (∃ A : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ),
          (∀ z, (A z).2 = z.2) ∧ (∀ x, A (x, e p 2) = (x, e p 2)) ∧
          ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ U ∧
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U ∧ InjOn β U ∧
            (∀ z ∈ U, EuclideanSpace.equivProdLast 2 (Φ 1 (e (β z))) =
              A (B z, e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
            ∃ T : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
              ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => T z.1 z.2) ∧
              ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (T z.1).symm z.2) ∧
              T 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
              (∀ t x, T t x 2 = x 2) ∧
              (∀ t y, T t ((EuclideanSpace.equivProdLast 2).symm (y, e p 2)) =
                (EuclideanSpace.equivProdLast 2).symm (y, e p 2)) ∧
              (∀ z ∈ U, T 1 (Φ 1 (e (β z))) = (EuclideanSpace.equivProdLast 2).symm
                (B z, e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
              ∃ K : Set EuclideanThree, IsCompact K ∧ ∀ t,
                EqOn (T t) id Kᶜ ∧ EqOn (T t).symm id Kᶜ) ∧
        ∃ n : ℕ, ∃ γ : Fin n → AddCircle (1 : ℝ) → Schoenflies.Plane,
          (∀ i, IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (γ i)) ∧
          Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))) ∧
          (⋃ i, range (γ i)) =
            (fun y => (EuclideanSpace.equivProdLast 2).symm (y, e p 2)) ⁻¹' range (Φ 1 ∘ e) ∧
          (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
            B z ∈ ⋃ i, range (γ i) ↔ z.1 = -1 ∨ z.1 = 1) ∧
          (∀ a ∈ ({-1, 1} : Set ℝ), ∃! i,
            (fun u => B (a, u)) '' Icc (-h) h ⊆ range (γ i)) ∧
          ∀ i, B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.inside (range (γ i)) ∨
            B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.outside (range (γ i)) := by
  obtain ⟨p, hp⟩ := ncard_eq_one.mp hone
  have hpcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1 :=
    hp.symm.subset (mem_singleton p)
  obtain ⟨s, hs, hsη, Φ, hΦ, hΦi, hΦ0, hregular, hcritical, hhessian, hpgerm, hgerm,
    hnewnd, hnewinj, hsupport, hband⟩ :=
    exists_ambient_isotopy_saddle_band_of_excellent he hnd hinj hpcrit.1 hpcrit.2 hη
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => Φ 1 (e x) 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp ((he.diffeomorph_comp (Φ 1)).contMDiff)
  have hsaddles : {p | IsCriticalPointAt (𝓡 2) (fun x => Φ 1 (e x) 2) p ∧
      sigNeg (chartHessianAt (fun y => Φ 1 (e ((extChartAt (𝓡 2) p).symm y)) 2)
        (extChartAt (𝓡 2) p p)) = 1} =
      {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
        (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1} := by
    ext x
    simp only [mem_ofPred_eq, hcritical x]
    exact and_congr_right (fun hx => by rw [hhessian x hx])
  have hnewone : {p | IsCriticalPointAt (𝓡 2) (fun x => Φ 1 (e x) 2) p ∧
      sigNeg (chartHessianAt (fun y => Φ 1 (e ((extChartAt (𝓡 2) p).symm y)) 2)
        (extChartAt (𝓡 2) p p)) = 1}.ncard = 1 := by
    rw [hsaddles]
    exact hone
  refine ⟨p, hpcrit.1, hpcrit.2, s, hs, hsη, Φ, hΦ, hΦi, hΦ0, hregular,
    hcritical, hhessian, hpgerm, hgerm, hnewnd, hnewinj,
    Morse.isPreconnected_sublevel_or_superlevel_of_one_saddle hf hnewnd hnewinj hnewone,
    hsupport, ?_⟩
  obtain ⟨h, hh, B, β, hβzero, hβ, hβinj, hβcomponent, hβclosure, hβheight, hβedge, hβopen,
    n, γ, hγ, hdisj, hcover, hband, hedges, _, hregions⟩ := hband
  exact ⟨h, hh, B, β, hβzero, hβ, hβinj, hβcomponent, hβclosure, hβheight, hβedge, hβopen,
    n, γ, hγ, hdisj, hcover, hband, hedges, hregions⟩

theorem exists_linearIsometryEquiv_height_isPreconnected_sublevels_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1) :
    ∃ A : EuclideanThree ≃ₗᵢ[ℝ] EuclideanThree,
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x ↔
        IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x →
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x) ∧
      InjOn (fun x => A (e x) 2) {x | IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x} ∧
      {p | IsCriticalPointAt (𝓡 2) (fun x => A (e x) 2) p ∧ sigNeg (chartHessianAt
        (fun y => A (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1 ∧
      {p | IsCriticalPointAt (𝓡 2) (fun x => A (e x) 2) p ∧ sigNeg (chartHessianAt
        (fun y => A (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 0}.Subsingleton ∧
      ∀ a : ℝ, IsPreconnected {x | A (e x) 2 < a} := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  rcases subsingleton_index_zero_or_index_two_of_one_saddle hf hnd hinj hone with hzero | htwo
  · refine ⟨LinearIsometryEquiv.refl ℝ EuclideanThree, fun _ => Iff.rfl, hnd, hinj, hone, hzero, ?_⟩
    intro a
    apply isPreconnected_lt_of_subsingleton_index_zero hf
      ((isClosed_le hf.continuous continuous_const).isCompact) (fun p _ => hnd p)
    intro p hp q hq
    exact hzero hp.2 hq.2
  · let A := LinearIsometryEquiv.neg ℝ (E := EuclideanThree)
    have hcritical (x : SphereTwo) : IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x ↔
        IsCriticalPointAt (𝓡 2) (fun y => e y 2) x := by
      change IsCriticalPointAt (𝓡 2) (fun y => -e y 2) x ↔ _
      simpa only [zero_sub] using DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff
        (hf.mdifferentiableAt (by simp) (x := x)) 0
    have hnondegenerate (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x) :
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x := by
      have h := (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff
        hf (x := x) BoundarylessManifold.isInteriorPoint 0).mpr (hnd x ((hcritical x).mp hx))
      change IsNondegenerateCriticalPointAt (𝓡 2) (fun y => -e y 2) x
      simpa only [zero_sub] using h
    have hvalues : InjOn (fun x => A (e x) 2)
        {x | IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x} := by
      intro x hx y hy hxy
      exact hinj ((hcritical x).mp hx) ((hcritical y).mp hy) (neg_injective hxy)
    have hindex (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) :
        sigNeg (chartHessianAt (fun y => A (e ((extChartAt (𝓡 2) x).symm y)) 2)
          (extChartAt (𝓡 2) x x)) +
        sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
          (extChartAt (𝓡 2) x x)) = 2 := by
      change sigNeg (chartHessianAt (fun y => -e ((extChartAt (𝓡 2) x).symm y) 2)
        (extChartAt (𝓡 2) x x)) + _ = 2
      rw [DifferentialGeometry.Morse.chartHessianAt_neg, sigNeg_neg]
      let Q := chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2) (extChartAt (𝓡 2) x x)
      have hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft := (hnd x hx).2
      let _ : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
      have hrad : Q.radical = ⊥ := by
        rw [QuadraticMap.radical_eq_ker_associated, LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ]
      have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
      rw [hrad, finrank_bot, add_zero] at hsum
      change sigPos Q + sigNeg Q = 2
      simpa using hsum
    have hsaddles : {p | IsCriticalPointAt (𝓡 2) (fun x => A (e x) 2) p ∧ sigNeg (chartHessianAt
        (fun y => A (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 1} =
        {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
          (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1} := by
      ext x
      simp only [mem_ofPred_eq, hcritical x]
      apply and_congr_right
      intro hx
      have hi := hindex x hx
      omega
    have hzero : {p | IsCriticalPointAt (𝓡 2) (fun x => A (e x) 2) p ∧ sigNeg (chartHessianAt
        (fun y => A (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 0}.Subsingleton := by
      intro x hx y hy
      have hxc := (hcritical x).mp hx.1
      have hyc := (hcritical y).mp hy.1
      apply htwo
      · refine ⟨hxc, ?_⟩
        have hi := hindex x hxc
        rw [hx.2, zero_add] at hi
        exact hi
      · refine ⟨hyc, ?_⟩
        have hi := hindex y hyc
        rw [hy.2, zero_add] at hi
        exact hi
    refine ⟨A, hcritical, hnondegenerate, hvalues, ?_, hzero, ?_⟩
    · rw [hsaddles]
      exact hone
    · intro a
      have hfA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => A (e x) 2) :=
        (EuclideanSpace.proj 2).contMDiff.comp
          (he.continuousLinearEquiv_comp A.toContinuousLinearEquiv).contMDiff
      apply isPreconnected_lt_of_subsingleton_index_zero hfA
        ((isClosed_le hfA.continuous continuous_const).isCompact) (fun p _ => hnondegenerate p)
      intro p hp q hq
      exact hzero hp.2 hq.2
theorem exists_diffeomorph_saddle_band_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, ∃ p : SphereTwo, ∃ c s : ℝ, 0 < s ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x ↔
        IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x →
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x) ∧
      InjOn (fun x => D (e x) 2) {x | IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x} ∧
      (∀ a : ℝ, IsPreconnected {x | D (e x) 2 < a}) ∧
      (∀ x, D (e x) 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => D (e y) 2) x ≠ 0) ∧
      IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) p ∧
      sigNeg (chartHessianAt (fun y => D (e ((extChartAt (𝓡 2) p).symm y)) 2)
        (extChartAt (𝓡 2) p p)) = 1 ∧
      {x | IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x ∧
        sigNeg (chartHessianAt (fun y => D (e ((extChartAt (𝓡 2) x).symm y)) 2)
          (extChartAt (𝓡 2) x x)) = 1}.ncard = 1 ∧
      ∃ h > 0, ∃ B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane, ∃ β : ℝ × ℝ → SphereTwo,
        β (0, 0) = p ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ∧
        InjOn β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ∧
        β '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ connectedComponentIn {x | c < D (e x) 2} p ∧
        β '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ closure (connectedComponentIn {x | c < D (e x) 2} p) ∧
        (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
          D (e (β z)) 2 = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
        (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h, z.1 = -1 ∨ z.1 = 1 →
          D (e (β z)) = (EuclideanSpace.equivProdLast 2).symm (B z, c)) ∧
        (∃ A : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ),
          (∀ z, (A z).2 = z.2) ∧ (∀ x, A (x, c) = (x, c)) ∧
          ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ U ∧
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U ∧ InjOn β U ∧
            (∀ z ∈ U, EuclideanSpace.equivProdLast 2 (D (e (β z))) =
              A (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
            ∃ T : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
              ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => T z.1 z.2) ∧
              ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (T z.1).symm z.2) ∧
              T 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
              (∀ t x, T t x 2 = x 2) ∧
              (∀ t y, T t ((EuclideanSpace.equivProdLast 2).symm (y, c)) =
                (EuclideanSpace.equivProdLast 2).symm (y, c)) ∧
              (∀ z ∈ U, T 1 (D (e (β z))) = (EuclideanSpace.equivProdLast 2).symm
                (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
              ∃ K : Set EuclideanThree, IsCompact K ∧ ∀ t,
                EqOn (T t) id Kᶜ ∧ EqOn (T t).symm id Kᶜ) ∧
        ∃ n : ℕ, ∃ γ : Fin n → AddCircle (1 : ℝ) → Schoenflies.Plane,
          (∀ i, IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (γ i)) ∧
          Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))) ∧
          (⋃ i, range (γ i)) =
            (fun y => (EuclideanSpace.equivProdLast 2).symm (y, c)) ⁻¹' range (D ∘ e) ∧
          (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
            B z ∈ ⋃ i, range (γ i) ↔ z.1 = -1 ∨ z.1 = 1) ∧
          (∀ a ∈ ({-1, 1} : Set ℝ), ∃! i,
            (fun u => B (a, u)) '' Icc (-h) h ⊆ range (γ i)) ∧
          (∃ i, (fun u => B (-1, u)) '' Icc (-h) h ⊆ range (γ i) ∧
            (fun u => B (1, u)) '' Icc (-h) h ⊆ range (γ i) ∧
            ∀ k : ℝ, 0 < k → k < h → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
              (∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
                B z ∈ range (γ i) ↔ z.1 = -1) ∧
              (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
                B z ∈ range (γ i) ↔ z.1 = 1) ∧
              (((∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
                  B z ∈ Schoenflies.inside (range (γ i)) ↔ -1 < z.1) ∧
                (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
                  B z ∈ Schoenflies.inside (range (γ i)) ↔ z.1 < 1)) ∨
               ((∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
                  B z ∈ Schoenflies.inside (range (γ i)) ↔ z.1 < -1) ∧
                (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
                  B z ∈ Schoenflies.inside (range (γ i)) ↔ 1 < z.1)))) ∧
          ∀ i, B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.inside (range (γ i)) ∨
            B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.outside (range (γ i)) := by
  obtain ⟨A, hAcritical, hAnd, hAinj, hAone, hAzero, _⟩ :=
    exists_linearIsometryEquiv_height_isPreconnected_sublevels_of_one_saddle he hnd hinj hone
  have heA := he.continuousLinearEquiv_comp A.toContinuousLinearEquiv
  obtain ⟨p, hp⟩ := ncard_eq_one.mp hAone
  have hpcrit : IsCriticalPointAt (𝓡 2) (fun x => A (e x) 2) p ∧ sigNeg (chartHessianAt
      (fun y => A (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 1 :=
    hp.symm.subset (mem_singleton p)
  obtain ⟨s, hs, _, Φ, _, _, _, hregular, hcritical, hhessian, _, _, hnewnd, hnewinj, _,
    h, hh, B, β, hβzero, hβ, hβinj, hβcomponent, hβclosure, hβheight, hβedge, hβopen,
    n, γ, hγ, hdisj, hcover, hband, hedges, hsame, hregions⟩ :=
    exists_ambient_isotopy_saddle_band_of_excellent heA hAnd hAinj hpcrit.1 hpcrit.2
      (by norm_num : (0 : ℝ) < 1)
  let D : EuclideanThree ≃ₘ[ℝ] EuclideanThree := A.toContinuousLinearEquiv.toDiffeomorph.trans (Φ 1)
  have hDcritical (x : SphereTwo) : IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x ↔
      IsCriticalPointAt (𝓡 2) (fun y => e y 2) x := (hcritical x).trans (hAcritical x)
  have hDzero : {p | IsCriticalPointAt (𝓡 2) (fun x => D (e x) 2) p ∧ sigNeg (chartHessianAt
      (fun y => D (e ((extChartAt (𝓡 2) p).symm y)) 2) (extChartAt (𝓡 2) p p)) = 0}.Subsingleton := by
    intro x hx y hy
    have hxc := (hcritical x).mp hx.1
    have hyc := (hcritical y).mp hy.1
    apply hAzero
    · exact ⟨hxc, (congrArg sigNeg (hhessian x hxc)).symm.trans hx.2⟩
    · exact ⟨hyc, (congrArg sigNeg (hhessian y hyc)).symm.trans hy.2⟩
  have hfD : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => D (e x) 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp (he.diffeomorph_comp D).contMDiff
  have hlo (a : ℝ) : IsPreconnected {x | D (e x) 2 < a} := by
    apply isPreconnected_lt_of_subsingleton_index_zero hfD
      ((isClosed_le hfD.continuous continuous_const).isCompact) (fun x _ => hnewnd x)
    intro x hx y hy
    exact hDzero hx.2 hy.2
  have hDone : {x | IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x ∧
      sigNeg (chartHessianAt (fun y => D (e ((extChartAt (𝓡 2) x).symm y)) 2)
        (extChartAt (𝓡 2) x x)) = 1}.ncard = 1 := by
    have hset : {x | IsCriticalPointAt (𝓡 2) (fun y => D (e y) 2) x ∧
        sigNeg (chartHessianAt (fun y => D (e ((extChartAt (𝓡 2) x).symm y)) 2)
          (extChartAt (𝓡 2) x x)) = 1} =
        {x | IsCriticalPointAt (𝓡 2) (fun y => A (e y) 2) x ∧
          sigNeg (chartHessianAt (fun y => A (e ((extChartAt (𝓡 2) x).symm y)) 2)
            (extChartAt (𝓡 2) x x)) = 1} := by
      ext x
      refine (and_congr (hcritical x) Iff.rfl).trans ?_
      apply and_congr_right
      intro hx
      exact congrArg (fun Q => sigNeg Q = 1) (hhessian x hx) |>.to_iff
    rw [hset]
    exact hAone
  refine ⟨D, p, A (e p) 2, s, hs, hDcritical, hnewnd, hnewinj, hlo, hregular,
    (hcritical p).mpr hpcrit.1, ?_, hDone, h, hh, B, β, hβzero, hβ, hβinj,
    hβcomponent, hβclosure, hβheight, hβedge, hβopen, n, γ, hγ, hdisj, hcover, hband,
    hedges, ?_, hregions⟩
  · exact (congrArg sigNeg (hhessian p hpcrit.1)).trans hpcrit.2
  · obtain ⟨i, hleft, hright⟩ := hsame (hlo (A (e p) 2))
    refine ⟨i, hleft, hright, fun k hk hkh => ?_⟩
    apply PlanarJordan.exists_band_attaching_collars (hγ i) B hk hkh
      ((image_mono Ioo_subset_Icc_self).trans hleft)
      ((image_mono Ioo_subset_Icc_self).trans hright)
    intro z hz hzg
    have heq := (hband z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩).mp
      (mem_iUnion.mpr ⟨i, hzg⟩)
    rcases heq with heq | heq <;> linarith [hz.1.1, hz.1.2]

end DifferentialGeometry.Topology.SphereSeparation
