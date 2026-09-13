import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem slice_mfderivWithin_eq {Φ : ℝ × ℝ → M} {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hΦ : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ J) (x, t)) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun y : ℝ => Φ (y, t)) univ x =
      (mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ J) (x, t)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
  have hψ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y : ℝ => (y, t)) univ x
      (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) x).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) t x)).hasMFDerivWithinAt
  have hmaps : (univ : Set ℝ) ⊆ (fun y : ℝ => (y, t)) ⁻¹' (univ ×ˢ J) :=
    fun y _ => ⟨mem_univ y, ht⟩
  exact (hΦ.hasMFDerivWithinAt.comp x hψ hmaps).mfderivWithin
    (uniqueMDiffWithinAt_univ (𝓘(ℝ, ℝ)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem mfderiv_slice_eq {Φ : ℝ × ℝ → M} {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hΦ : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ J) (x, t)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => Φ (y, t)) x (1 : ℝ) =
      mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ J) (x, t) ((1 : ℝ), (0 : ℝ)) := by
  rw [← mfderivWithin_univ (I := 𝓘(ℝ, ℝ)) (I' := I) (f := fun y : ℝ => Φ (y, t)),
    slice_mfderivWithin_eq ht hΦ]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem continuousOn_tangentMapWithin_slice {a b : ℝ} (hab : a < b) {Φ : ℝ × ℝ → M}
    (hΦ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ Φ (univ ×ˢ Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (⟨Φ p, mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ Icc a b) p
        ((1 : ℝ), (0 : ℝ))⟩ : TangentBundle I M))
      (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hS : UniqueMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((univ : Set ℝ) ×ˢ Icc a b) :=
    uniqueMDiffOn_iff_uniqueDiffOn.mpr
      (UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hab))
  have hT := hΦ.contMDiffOn_tangentMapWithin (m := 0) (by simp) hS
  have hcont : ContinuousOn (tangentMapWithin 𝓘(ℝ, ℝ × ℝ) I Φ (univ ×ˢ Icc a b))
      (Bundle.TotalSpace.proj ⁻¹' ((univ : Set ℝ) ×ˢ Icc a b)) := hT.continuousOn
  have hlam : Continuous (fun p : ℝ × ℝ =>
      (Bundle.TotalSpace.mk' (ℝ × ℝ) p ((1 : ℝ), (0 : ℝ)) :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ × ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hlammaps : Set.MapsTo (fun p : ℝ × ℝ =>
      (Bundle.TotalSpace.mk' (ℝ × ℝ) p ((1 : ℝ), (0 : ℝ)) :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)))
      (Icc (0 : ℝ) 1 ×ˢ Icc a b)
      (Bundle.TotalSpace.proj ⁻¹' ((univ : Set ℝ) ×ˢ Icc a b)) :=
    fun p hp => ⟨mem_univ p.1, hp.2⟩
  exact (hcont.comp hlam.continuousOn hlammaps).congr (fun p _ => rfl)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuous_circleParameter_of_smoothOn {a b : ℝ} {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) :
    Continuous (fun p : Surgery.Topology.Circle × Icc a b => c p.1 p.2.1) := by
  have hsub : Continuous (fun p : ℝ × Icc a b =>
      (⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, p.2.2⟩⟩ :
        (univ ×ˢ Icc a b : Set (ℝ × ℝ)))) :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hjoint : Continuous (fun p : ℝ × Icc a b => c.lift p.1 p.2.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hc.continuousOn).comp hsub
  have hq : Topology.IsQuotientMap (fun x : ℝ => (x : Surgery.Topology.Circle)) :=
    isQuotientMap_quotient_mk'
  exact Topology.IsQuotientMap.continuous_lift_prod_left hq hjoint

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuousOn_loopFamily_of_smoothOn {a b : ℝ} (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b)) :
    ContinuousOn γ (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (DifferentialGeometry.Topology.FreeLoop.continuous_family_iff _).mpr ?_
  have h := continuous_circleParameter_of_smoothOn (I := I) hγ
  refine (h.comp (continuous_snd.prodMk continuous_fst)).congr (fun p => ?_)
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem continuousOn_loopLiftVelocity_of_smoothOn {a b : ℝ} (hab : a < b)
    {c : CurveMap M} (hc : c.SmoothOn (I := I) (Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (⟨c.lift p.1 p.2, mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y p.2) p.1 (1 : ℝ)⟩ :
        TangentBundle I M))
      (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hΦ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p : ℝ × ℝ => c.lift p.1 p.2)
      (univ ×ˢ Icc a b) := hc
  have hpt : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
      (⟨c.lift p.1 p.2, mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y p.2) p.1 (1 : ℝ)⟩ :
        TangentBundle I M) =
      (⟨(fun q : ℝ × ℝ => c.lift q.1 q.2) p,
        mfderivWithin 𝓘(ℝ, ℝ × ℝ) I (fun q : ℝ × ℝ => c.lift q.1 q.2)
          (univ ×ˢ Icc a b) p ((1 : ℝ), (0 : ℝ))⟩ : TangentBundle I M) := by
    intro p hp
    have h := mfderiv_slice_eq (Φ := fun q : ℝ × ℝ => c.lift q.1 q.2) (J := Icc a b) hp.2
      ((hΦ p ⟨mem_univ p.1, hp.2⟩).mdifferentiableWithinAt (by simp))
    rw [h]
  exact (continuousOn_tangentMapWithin_slice hab hΦ).congr hpt

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_continuousOn_contractibleRegularLoop_family_of_smoothOn {a b : ℝ}
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    ∃ Γ : ℝ → Width.ContractibleRegularLoop (I := I) (Q := M),
      ContinuousOn Γ (Icc a b) ∧ ∀ t ∈ Icc a b, (Γ t).1.toContinuousLoop = γ t := by
  by_cases hab : a < b
  · have hK : Continuous (fun q : Icc a b × Icc (0 : ℝ) 1 =>
        (⟨(curveOfLoopFamily γ).lift q.2.1 q.1.1,
          Width.loopVelocity (I := I) (γ q.1.1) q.2.1⟩ : TangentBundle I M)) :=
      ((continuousOn_loopLiftVelocity_of_smoothOn hab hγ).comp_continuous
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst))
        (fun q => ⟨q.2.2, q.1.2⟩)).congr (fun q => rfl)
    have hjet : Continuous (fun t : Icc a b =>
        (regularLoopSlice γ hγ t.1 t.2).firstJetMap) := by
      let Kmap : C(Icc a b × Icc (0 : ℝ) 1, TangentBundle I M) :=
        ⟨fun q => (⟨(curveOfLoopFamily γ).lift q.2.1 q.1.1,
          Width.loopVelocity (I := I) (γ q.1.1) q.2.1⟩ : TangentBundle I M), hK⟩
      exact Kmap.curry.continuous.congr (fun t => ContinuousMap.ext (fun s => rfl))
    have hval : Continuous (fun t : Icc a b =>
        (regularLoopSlice γ hγ t.1 t.2).toContinuousLoop) :=
      (continuousOn_iff_continuous_domRestrict.mp
        (continuousOn_loopFamily_of_smoothOn (I := I) γ hγ)).congr (fun t => rfl)
    have hRL : Continuous (fun t : Icc a b => regularLoopSlice γ hγ t.1 t.2) := by
      apply continuous_induced_rng.mpr
      exact hval.prodMk hjet
    have hF : Continuous (fun t : Icc a b =>
        (⟨regularLoopSlice γ hγ t.1 t.2, hctr t.1 t.2⟩ :
          Width.ContractibleRegularLoop (I := I) (Q := M))) :=
      hRL.subtype_mk (fun t => hctr t.1 t.2)
    refine ⟨fun t : ℝ => if ht : t ∈ Icc a b then
        (⟨regularLoopSlice γ hγ t ht, hctr t ht⟩ :
          Width.ContractibleRegularLoop (I := I) (Q := M))
      else Width.constantContractibleRegularLoop (I := I) (Q := M) (γ a 0), ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      exact hF.congr (fun t => by simp only [Set.domRestrict_apply, dif_pos t.2])
    · intro t ht
      simp only [dif_pos ht]
      rfl
  · have hba : b ≤ a := le_of_not_gt hab
    refine ⟨fun _ => if ha : a ∈ Icc a b then
          (⟨regularLoopSlice γ hγ a ha, hctr a ha⟩ :
            Width.ContractibleRegularLoop (I := I) (Q := M))
        else Width.constantContractibleRegularLoop (I := I) (Q := M) (γ a 0),
      continuousOn_const, ?_⟩
    intro t ht
    have hta : t = a := le_antisymm (ht.2.trans hba) ht.1
    have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
    rw [hta, dif_pos ha]
    rfl

theorem continuousOn_loopFamilyLeastArea_of_smoothOn
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) := by
  obtain ⟨Γ, hΓ, hagree⟩ :=
    exists_continuousOn_contractibleRegularLoop_family_of_smoothOn γ hγ hctr
  exact continuousOn_loopFamilyLeastArea_of_continuousRegularFamily B γ Γ hΓ hagree

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
