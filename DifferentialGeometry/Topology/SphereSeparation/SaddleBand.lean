import DifferentialGeometry.Topology.SphereSeparation.HeightSection
import DifferentialGeometry.Topology.SphereSeparation.LevelSet
import DifferentialGeometry.Topology.Morse.CriticalFinite
import DifferentialGeometry.Topology.Morse.ModelTransport
import DifferentialGeometry.Topology.Morse.SaddleResolution
import DifferentialGeometry.Topology.PlanarJordan.Band
import DifferentialGeometry.Topology.Diffeomorph.CompactFiberwiseReparametrization

open Set Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_ambient_isotopy_saddle_band {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p : SphereTwo} (hnd : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1)
    (hunique : ∀ x, e x 2 = e p 2 → IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p)
    {η : ℝ} (hη : 0 < η) :
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
          (IsPreconnected {x | Φ 1 (e x) 2 < e p 2} → ∃ i,
            (fun u => B (-1, u)) '' Icc (-h) h ⊆ range (γ i) ∧
            (fun u => B (1, u)) '' Icc (-h) h ⊆ range (γ i)) ∧
          ∀ i, B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.inside (range (γ i)) ∨
            B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.outside (range (γ i)) := by
  let I := 𝓡 2
  let L := EuclideanSpace.equiv (Fin 2) ℝ
  let J := I.transContinuousLinearEquiv L
  let P := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let D : SphereTwo ≃ₘ⟮I, J⟯ SphereTwo := ContinuousLinearEquiv.toTransContinuousLinearEquiv I SphereTwo L
  have hD := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D.symm.isLocalDiffeomorph D.symm.injective
  have he' : IsSmoothEmbedding J 𝓘(ℝ, Schoenflies.Plane × ℝ) ∞ (P ∘ e) :=
    (he.continuousLinearEquiv_comp P).comp hD (by simp)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hnd' : IsNondegenerateCriticalPointAt J (fun x => (P (e x)).2) p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindex' : sigNeg (chartHessianAt
      (fun y => (P (e ((extChartAt J p).symm y))).2) (extChartAt J p p)) = 1 :=
    (DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
      I L hf BoundarylessManifold.isInteriorPoint hnd.1).trans hindex
  have huniq : ∀ x, (P (e x)).2 = (P (e p)).2 →
      IsCriticalPointAt J (fun y => (P (e y)).2) x → x = p := by
    intro x hx hc
    exact hunique x hx ((DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L (fun y => e y 2) x).mp hc)
  obtain ⟨s, hs, hsη, r, t, h, _, _, hh, χ, A, hχ, hχ0, hA, hchart, H, hH, hHi, hH0,
    hgraph, hopen, hband, hreg, hcrit, _, hpgerm, hgerm, K, hK, _, hfix⟩ :=
    Morse.exists_ambient_isotopy_saddle_band he' hnd' hindex' huniq hη
  let Φ := fun t => P.toDiffeomorph.trans ((H t).trans P.symm.toDiffeomorph)
  have hΦ : ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => Φ z.1 z.2) :=
    P.symm.contDiff.comp (hH.comp (contDiff_fst.prodMk (P.contDiff.comp contDiff_snd)))
  have hΦi : ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (Φ z.1).symm z.2) :=
    P.symm.contDiff.comp (hHi.comp (contDiff_fst.prodMk (P.contDiff.comp contDiff_snd)))
  have hΦh (x : SphereTwo) : Φ 1 (e x) 2 = (H 1 (P (e x))).2 :=
    EuclideanSpace.equivProdLast_symm_last 2 _
  have hfg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => Φ 1 (e y) 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp ((Φ 1).contMDiff.comp he.contMDiff)
  have heq : (fun y => Φ 1 (e y) 2) = fun y => (H 1 (P (e y))).2 := funext hΦh
  have hcritical (x : SphereTwo) :
      IsCriticalPointAt I (fun y => Φ 1 (e y) 2) x ↔ IsCriticalPointAt I (fun y => e y 2) x := by
    rw [← DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L (fun y => Φ 1 (e y) 2) x, heq]
    exact (hcrit x).trans (DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L (fun y => e y 2) x)
  have hpgerm' : (fun y => Φ 1 (e y) 2) =ᶠ[𝓝 p] (fun y => e y 2 + s) := by
    rw [heq]
    exact hpgerm
  have hgerm' (x : SphereTwo) (hx : IsCriticalPointAt I (fun y => e y 2) x) (hxp : x ≠ p) :
      (fun y => Φ 1 (e y) 2) =ᶠ[𝓝 x] (fun y => e y 2) := by
    rw [heq]
    exact hgerm x ((DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L (fun y => e y 2) x).mpr hx) hxp
  have hhessian (x : SphereTwo) (hx : IsCriticalPointAt I (fun y => e y 2) x) :
      chartHessianAt (fun y => Φ 1 (e ((extChartAt I x).symm y)) 2) (extChartAt I x x) =
        chartHessianAt (fun y => e ((extChartAt I x).symm y) 2) (extChartAt I x x) := by
    by_cases hxp : x = p
    · subst x
      exact DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
        BoundarylessManifold.isInteriorPoint hpgerm'
    · have hgerm0 : (fun y => Φ 1 (e y) 2) =ᶠ[𝓝 x] (fun y => e y 2 + 0) := by
        simpa only [add_zero] using hgerm' x hx hxp
      exact DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
        (I := I) BoundarylessManifold.isInteriorPoint hgerm0
  have hregular (x : SphereTwo) (hx : Φ 1 (e x) 2 = e p 2) :
      mfderiv I 𝓘(ℝ, ℝ) (fun y => Φ 1 (e y) 2) x ≠ 0 := by
    intro hc
    have hc' := (DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
      I L (fun y => Φ 1 (e y) 2) x).mpr hc
    rw [heq] at hc'
    exact hreg x ((hΦh x).symm.trans hx) hc'
  let F := (saddleBandChart hs).toHomeomorph.trans (A.toHomeomorph.restrictFiber hA (e p 2))
  let B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane :=
    { toEquiv := F.toEquiv
      contMDiff_toFun := ((A.contMDiff.contDiff.comp
        ((saddleBandChart hs).contMDiff.contDiff.prodMk contDiff_const)).fst).contMDiff
      contMDiff_invFun := ((saddleBandChart hs).symm.contMDiff.contDiff.comp
        (A.symm.contMDiff.contDiff.comp (contDiff_id.prodMk contDiff_const)).fst).contMDiff }
  have hB (z : ℝ × ℝ) : (B z, e p 2) = A (saddleBandChart hs z, e p 2) :=
    Prod.ext rfl (hA (saddleBandChart hs z, e p 2)).symm
  let β : ℝ × ℝ → SphereTwo := fun z => χ (saddleBandChart hs z)
  have hβzero : β (0, 0) = p := by
    have hzero : saddleBandChart hs (0, 0) = 0 := by
      ext i
      fin_cases i <;> simp [saddleBandChart_apply_zero, saddleBandChart_apply_one]
    exact (congrArg χ hzero).trans hχ0
  have hβmap : MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) χ.source :=
    fun _ hz => hχ (Metric.ball_subset_closedBall (hchart hz))
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) :=
    D.symm.contMDiff.comp_contMDiffOn
      (χ.contMDiffOn.comp (saddleBandChart hs).contMDiff.contMDiffOn hβmap)
  have hβinj : InjOn β (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) :=
    χ.toPartialEquiv.injOn.comp (saddleBandChart hs).injective.injOn hβmap
  have hβheight (z : ℝ × ℝ) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) :
      Φ 1 (e (β z)) 2 = e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
    rw [hΦh]
    change (H 1 ((P ∘ e) (χ (saddleBandChart hs z)))).2 = _
    rw [hgraph z hz, hA]
    rfl
  have hβedge (z : ℝ × ℝ) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h)
      (hedge : z.1 = -1 ∨ z.1 = 1) : Φ 1 (e (β z)) = P.symm (B z, e p 2) := by
    apply P.injective
    change P (P.symm (H 1 (P (e (β z))))) = P (P.symm (B z, e p 2))
    rw [P.apply_symm_apply, P.apply_symm_apply]
    change H 1 ((P ∘ e) (χ (saddleBandChart hs z))) = _
    rw [hgraph z hz, hB]
    apply congrArg A
    rcases hedge with hedge | hedge <;> simp [hedge, P]
  have hβopen : ∃ G : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ),
      (∀ z, (G z).2 = z.2) ∧ (∀ x, G (x, e p 2) = (x, e p 2)) ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ U ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U ∧ InjOn β U ∧
        (∀ z ∈ U, P (Φ 1 (e (β z))) =
          G (B z, e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
        ∃ T : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => T z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (T z.1).symm z.2) ∧
          T 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
          (∀ t x, T t x 2 = x 2) ∧
          (∀ t y, T t (P.symm (y, e p 2)) = P.symm (y, e p 2)) ∧
          (∀ z ∈ U, T 1 (Φ 1 (e (β z))) = P.symm
            (B z, e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
          ∃ K : Set EuclideanThree, IsCompact K ∧ ∀ t,
            EqOn (T t) id Kᶜ ∧ EqOn (T t).symm id Kᶜ := by
    let A₀ : Diffeomorph (𝓘(ℝ, Schoenflies.Plane).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, Schoenflies.Plane).prod 𝓘(ℝ, ℝ))
        (Schoenflies.Plane × ℝ) (Schoenflies.Plane × ℝ) ∞ :=
      { toEquiv := A.toEquiv
        contMDiff_toFun := by
          rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
          exact A.contMDiff
        contMDiff_invFun := by
          rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
          exact A.symm.contMDiff }
    let f := A₀.restrictFiber hA (e p 2)
    let G₀ := (f.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans A₀
    let G : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ) :=
      { toEquiv := G₀.toEquiv
        contMDiff_toFun := by
          rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
          exact G₀.contMDiff
        contMDiff_invFun := by
          rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
          exact G₀.symm.contMDiff }
    have hBf (z : ℝ × ℝ) : B z = f (saddleBandChart hs z) := rfl
    obtain ⟨U, hU, hrect, hmaps, hformula⟩ := hopen
    have hGh (z : Schoenflies.Plane × ℝ) : (G z).2 = z.2 := hA _
    have hGfix (x : Schoenflies.Plane) : G (x, e p 2) = (x, e p 2) := by
      change A (f.symm x, e p 2) = (x, e p 2)
      exact Prod.ext (f.apply_symm_apply x) (hA _)
    have hformula_out (z : ℝ × ℝ) (hz : z ∈ U) : P (Φ 1 (e (β z))) =
        G (B z, e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
      change P (P.symm (H 1 ((P ∘ e) (χ (saddleBandChart hs z))))) =
        A (f.symm (B z), e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
      rw [P.apply_symm_apply, hformula z hz, hBf, f.symm_apply_apply]
      rfl
    obtain ⟨V, hV, hrectV, hVU, T, hT, hTi, hTzero, hTheight, hTfix, hTgraph,
      J, hJ, _, hTsupport⟩ :=
      G.exists_compact_isotopy_straightening_graph hGh (e p 2) hGfix P.symm.toDiffeomorph
        (k := fun z => Φ 1 (e (β z))) (x := B)
        (g := fun z => e p 2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
        hU (isCompact_Icc.prod isCompact_Icc) hrect
        (B.continuous.prodMk (by fun_prop)).continuousOn
        (fun z hz => (P.symm_apply_apply _).symm.trans
          (congrArg P.symm (hformula_out z hz))) isOpen_univ (fun _ _ => mem_univ _)
    refine ⟨G, hGh, hGfix, V, hV, hrectV, ?_, ?_,
      fun z hz => hformula_out z (hVU hz), T, hT, hTi, hTzero, hTheight, hTfix, hTgraph,
      J, hJ, hTsupport⟩
    · exact (D.symm.contMDiff.comp_contMDiffOn
        (χ.contMDiffOn.comp (saddleBandChart hs).contMDiff.contMDiffOn hmaps)).mono hVU
    · exact (χ.toPartialEquiv.injOn.comp (saddleBandChart hs).injective.injOn hmaps).mono hVU
  have hβconnected : IsPreconnected (β '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h)) :=
    (isPreconnected_Ioo.prod isPreconnected_Icc).image β
      (hβ.continuousOn.mono (prod_mono Ioo_subset_Icc_self Subset.rfl))
  have hβp : p ∈ β '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) := by
    refine ⟨(0, 0), ⟨?_, ?_⟩, hβzero⟩
    · norm_num
    · exact ⟨neg_nonpos.mpr hh.le, hh.le⟩
  have hβupper : β '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆
      {x | e p 2 < Φ 1 (e x) 2} := by
    rintro _ ⟨z, hz, rfl⟩
    change e p 2 < Φ 1 (e (β z)) 2
    rw [hβheight z ⟨Ioo_subset_Icc_self hz.1, hz.2⟩]
    have hfirst : 0 < 1 - z.1 ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hz.1.2) (show 0 < 1 + z.1 by linarith [hz.1.1])]
    have hsecond : 0 < z.2 ^ 2 + 2 * s := by nlinarith [sq_nonneg z.2]
    linarith [div_pos (mul_pos hfirst hsecond) (by norm_num : (0 : ℝ) < 2)]
  have hβcomponent := hβconnected.subset_connectedComponentIn hβp hβupper
  have hclosure : closure (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) =
      Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h := by
    rw [closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), isClosed_Icc.closure_eq]
  have hβclosure : β '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆
      closure (connectedComponentIn {x | e p 2 < Φ 1 (e x) 2} p) := by
    rw [← hclosure]
    exact (hβ.continuousOn.mono hclosure.subset).image_closure.trans (closure_mono hβcomponent)
  obtain ⟨hfinite, η, γ, hη, hγ, hcompat, hdisj, hcover⟩ :=
    exists_planar_height_level_circle_parametrizations (he.diffeomorph_comp (Φ 1)) (e p 2) hregular
  let C := ConnectedComponents {x : SphereTwo // Φ 1 (e x) 2 = e p 2}
  let : Finite C := hfinite
  let : Fintype C := Fintype.ofFinite C
  let ι := (Fintype.equivFin C).symm
  let γ' := fun i => γ (ι i)
  have hcover' : (⋃ i, range (γ' i)) = (⋃ i, range (γ i)) :=
    ι.surjective.iUnion_comp (fun i => range (γ i))
  have hdisj' : Pairwise (fun i j => Disjoint (range (γ' i)) (range (γ' j))) :=
    fun _ _ h => hdisj (ι.injective.ne h)
  have hband' : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
      B z ∈ ⋃ i, range (γ' i) ↔ z.1 = -1 ∨ z.1 = 1 := by
    intro z hz
    rw [hcover', hcover]
    change P.symm (B z, e p 2) ∈ range (Φ 1 ∘ e) ↔ _
    rw [hB]
    have hrange : P.symm (A (saddleBandChart hs z, e p 2)) ∈ range (Φ 1 ∘ e) ↔
        A (saddleBandChart hs z, e p 2) ∈ range (H 1 ∘ (P ∘ e)) := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, P.symm.injective hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, congrArg P.symm hx⟩
    rw [hrange]
    exact hband z hz
  have hcircles (i) : Schoenflies.IsJordanCurve (range (γ' i)) :=
    PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero (hγ (ι i)).isEmbedding
  obtain ⟨hedges, hregions⟩ := PlanarJordan.exists_band_edge_components
    (fun i => range (γ' i)) hcircles hdisj' B.contMDiff.continuous.continuousOn hh.le hband'
  have hsame (hlo : IsPreconnected {x | Φ 1 (e x) 2 < e p 2}) : ∃ i,
      (fun u => B (-1, u)) '' Icc (-h) h ⊆ range (γ' i) ∧
      (fun u => B (1, u)) '' Icc (-h) h ⊆ range (γ' i) := by
    obtain ⟨i₀, hi₀, _⟩ := hedges (-1) (by simp)
    obtain ⟨i₁, hi₁, _⟩ := hedges 1 (by simp)
    have hzero : (0 : ℝ) ∈ Icc (-h) h := ⟨neg_nonpos.mpr hh.le, hh.le⟩
    have hηlevel (i) : range (η (ι i)) ⊆ {x | Φ 1 (e x) 2 = e p 2} := by
      rintro x ⟨θ, rfl⟩
      change Φ 1 (e (η (ι i) θ)) 2 = e p 2
      exact (congrArg (fun z => z 2) (hcompat (ι i) θ)).trans
        (EuclideanSpace.equivProdLast_symm_last 2 _)
    have hpoint (a : ℝ) (ha : a = -1 ∨ a = 1) (i)
        (hedge : (fun u => B (a, u)) '' Icc (-h) h ⊆ range (γ' i)) :
        β (a, 0) ∈ range (η (ι i)) := by
      obtain ⟨θ, hθ⟩ := hedge ⟨0, hzero, rfl⟩
      have haI : a ∈ Icc (-1 : ℝ) 1 := by rcases ha with rfl | rfl <;> norm_num
      refine ⟨θ, (he.diffeomorph_comp (Φ 1)).isEmbedding.injective ?_⟩
      change Φ 1 (e (η (ι i) θ)) = Φ 1 (e (β (a, 0)))
      have hc : Φ 1 (e (η (ι i) θ)) = P.symm (γ (ι i) θ, e p 2) := hcompat (ι i) θ
      have hpair : (γ (ι i) θ, e p 2) = (B (a, 0), e p 2) := Prod.ext hθ rfl
      exact hc.trans ((congrArg P.symm hpair).trans (hβedge (a, 0) ⟨haI, hzero⟩ ha).symm)
    have hηeq : range (η (ι i₀)) = range (η (ι i₁)) :=
      range_eq_of_mem_closure_superlevel_component hfg hregular (hη (ι i₀)) (hη (ι i₁))
        (hηlevel i₀) (hηlevel i₁) hlo
        (hpoint (-1) (Or.inl rfl) i₀ hi₀) (hpoint 1 (Or.inr rfl) i₁ hi₁)
        (hβclosure ⟨(-1, 0), ⟨by norm_num, hzero⟩, rfl⟩)
        (hβclosure ⟨(1, 0), ⟨by norm_num, hzero⟩, rfl⟩)
    have hηimage (i) : range (γ' i) =
        (fun x => (P (Φ 1 (e x))).1) '' range (η (ι i)) := by
      rw [← range_comp]
      apply congrArg range
      funext θ
      change γ (ι i) θ = (P (Φ 1 (e (η (ι i) θ)))).1
      have hc : Φ 1 (e (η (ι i) θ)) = P.symm (γ (ι i) θ, e p 2) := hcompat (ι i) θ
      rw [hc, P.apply_symm_apply]
    have heq : range (γ' i₀) = range (γ' i₁) := by rw [hηimage, hηimage, hηeq]
    exact ⟨i₀, hi₀, hi₁.trans heq.symm.subset⟩
  refine ⟨s, hs, hsη, Φ, hΦ, hΦi, ?_, hregular, hcritical, hhessian, hpgerm', hgerm', ?_,
    h, hh, B, β, hβzero, hβ, hβinj, hβcomponent, hβclosure, hβheight, hβedge, hβopen, Fintype.card C, γ',
    fun i => hγ (ι i), hdisj', hcover'.trans hcover, hband', hedges, hsame, hregions⟩
  · apply Diffeomorph.ext
    intro z
    change P.symm (H 0 (P z)) = z
    rw [hH0]
    exact P.symm_apply_apply z
  · refine ⟨P.symm '' K, hK.image P.symm.continuous, ?_⟩
    intro u
    have hnot (z : EuclideanThree) (hz : z ∉ P.symm '' K) : P z ∉ K :=
      fun h => hz ⟨P z, h, P.symm_apply_apply z⟩
    constructor
    · intro z hz
      change P.symm (H u (P z)) = z
      rw [(hfix u).1 (hnot z hz)]
      exact P.symm_apply_apply z
    · intro z hz
      change P.symm ((H u).symm (P z)) = z
      rw [(hfix u).2 (hnot z hz)]
      exact P.symm_apply_apply z

theorem exists_ambient_isotopy_saddle_band_of_excellent {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x})
    {p : SphereTwo} (hp : IsCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1)
    {η : ℝ} (hη : 0 < η) :
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
          (IsPreconnected {x | Φ 1 (e x) 2 < e p 2} → ∃ i,
            (fun u => B (-1, u)) '' Icc (-h) h ⊆ range (γ i) ∧
            (fun u => B (1, u)) '' Icc (-h) h ⊆ range (γ i)) ∧
          ∀ i, B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.inside (range (γ i)) ∨
            B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.outside (range (γ i)) := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hfinite : {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}.Finite :=
    DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact hf isCompact_univ
      (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  let V := (fun x => e x 2) '' ({x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x} \ {p})
  have hV : V.Finite := hfinite.sdiff.image _
  have hpV : e p 2 ∈ Vᶜ := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (hinj hx.1 hp heq)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.isClosed.isOpen_compl.mem_nhds hpV)
  obtain ⟨s, hs, hsbound, Φ, hΦ, hΦi, hΦ0, hregular, hcritical, hhessian, hpgerm, hgerm,
    hsupport, hband⟩ := exists_ambient_isotopy_saddle_band he (hnd p hp) hindex
      (fun x heq hx => hinj hx hp heq) (lt_min hη hδ)
  have hsη : s < η := hsbound.trans_le (min_le_left _ _)
  have hsδ : s < δ := hsbound.trans_le (min_le_right _ _)
  have hshift : e p 2 + s ∉ V := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hs] using hsδ)
  have hnewinj : InjOn (fun x => Φ 1 (e x) 2)
      {x | IsCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x} := by
    intro x hx y hy hxy
    have hxold := (hcritical x).mp hx
    have hyold := (hcritical y).mp hy
    by_cases hxp : x = p
    · subst x
      by_cases hyp : y = p
      · exact hyp.symm
      · exfalso
        apply hshift
        refine ⟨y, ⟨hyold, hyp⟩, ?_⟩
        exact (hgerm y hyold hyp).eq_of_nhds.symm.trans (hxy.symm.trans hpgerm.eq_of_nhds)
    · by_cases hyp : y = p
      · subst y
        exfalso
        apply hshift
        refine ⟨x, ⟨hxold, hxp⟩, ?_⟩
        exact (hgerm x hxold hxp).eq_of_nhds.symm.trans (hxy.trans hpgerm.eq_of_nhds)
      · exact hinj hxold hyold
          ((hgerm x hxold hxp).eq_of_nhds.symm.trans (hxy.trans (hgerm y hyold hyp).eq_of_nhds))
  have hnewnd (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x) :
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => Φ 1 (e y) 2) x := by
    refine ⟨hx, ?_⟩
    rw [hhessian x ((hcritical x).mp hx)]
    exact (hnd x ((hcritical x).mp hx)).2
  exact ⟨s, hs, hsη, Φ, hΦ, hΦi, hΦ0, hregular, hcritical, hhessian, hpgerm, hgerm,
    hnewnd, hnewinj, hsupport, hband⟩


end DifferentialGeometry.Topology.SphereSeparation
