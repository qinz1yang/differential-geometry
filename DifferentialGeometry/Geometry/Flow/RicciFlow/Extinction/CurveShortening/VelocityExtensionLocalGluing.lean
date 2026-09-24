import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionProducer
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection

noncomputable section

open Bundle Manifold Set Filter

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]
variable {a b : ℝ} {γ : ℝ → ContinuousFreeLoop M}

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def LoopFamilyVelocityExtensionOn (γ : ℝ → ContinuousFreeLoop M) (a b : ℝ)
    (O : Set (ℝ × M)) (X : ℝ → (p : M) → TangentSpace I p) : Prop :=
  (∀ t ∈ Ico a b, ∀ z : Surgery.Topology.Circle, (t, γ t z) ∈ O →
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Ici t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))) ∧
  ∀ t ∈ Ioc a b, ∀ z : Surgery.Topology.Circle, (t, γ t z) ∈ O →
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Iic t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def LoopFamilyVelocityExtensionLocalAt (γ : ℝ → ContinuousFreeLoop M) (a b : ℝ)
    (q : ℝ × M) : Prop :=
  ∃ (X : ℝ → (p : M) → TangentSpace I p) (O : Set (ℝ × M)),
    IsOpen O ∧ q ∈ O ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun r : ℝ × M => (TotalSpace.mk' E r.2 (X r.1 r.2) : TangentBundle I M)) O ∧
    LoopFamilyVelocityExtensionOn (I := I) γ a b O X

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def LoopFamilyVelocityExtensionLocalCover (γ : ℝ → ContinuousFreeLoop M) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ x : ℝ,
    LoopFamilyVelocityExtensionLocalAt (I := I) γ a b (t, γ t (x : Surgery.Topology.Circle))

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem contMDiff_assembledLoopFamilySection {ι : Type*} [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ).prod I) (ℝ × M) univ)
    {U : ι → Set (ℝ × M)} (hUo : ∀ i, IsOpen (U i)) (hsub : ρ.IsSubordinate U)
    (Y : ι → ℝ → (p : M) → TangentSpace I p)
    (hY : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M)) (U i)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (∑ i, ρ i q • Y i q.1 q.2) : TangentBundle I M)) := by
  classical
  intro q₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  set x₀ : M := q₀.2 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  set g : ι → ℝ × M → E := fun i q => e.continuousLinearMapAt ℝ q.2 (Y i q.1 q.2) with hg
  have hsummand : ∀ i, q₀ ∈ tsupport (fun q : ℝ × M => ρ i q) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞ (g i) q₀ := by
    intro i hi
    have hq₀U : q₀ ∈ U i := hsub i hi
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x₀
    have hYat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M)) q₀ :=
      (hY i q₀ hq₀U).contMDiffAt ((hUo i).mem_nhds hq₀U)
    have hYat' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2) q₀ := by
      have hsrc : (TotalSpace.mk' E q₀.2 (Y i q₀.1 q₀.2) : TangentBundle I M) ∈
          e.source := by
        rw [Trivialization.mem_source]; exact hbase
      exact ((e.contMDiffAt_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
        (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M))
        hsrc).mp hYat).2
    refine hYat'.congr_of_eventuallyEq ?_
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      continuous_snd.continuousAt (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    show g i q = (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2
    rw [← chartE_section_repr_eq_trivialization_snd (I := I) x₀ (Y i q.1) hq]
    rfl
  have hfib_eq : (fun q : ℝ × M =>
      (e (TotalSpace.mk' E q.2 (∑ i, ρ i q • Y i q.1 q.2))).2)
      =ᶠ[𝓝 q₀] (fun q : ℝ × M => ∑ i, ρ i q • g i q) := by
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x₀
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      continuous_snd.continuousAt (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    have hcl : (e (TotalSpace.mk' E q.2 (∑ i, ρ i q • Y i q.1 q.2))).2
        = e.continuousLinearMapAt ℝ q.2 (∑ i, ρ i q • Y i q.1 q.2) :=
      (chartE_section_repr_eq_trivialization_snd (I := I) x₀
        (fun y => ∑ i, ρ i q • Y i q.1 y) hq).symm
    rw [hcl, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  change ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
    (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (∑ i, ρ i q • Y i q.1 q.2))).2) q₀
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hfib_eq
  refine ContMDiffAt.sum fun i _ => ?_
  by_cases hi : q₀ ∈ tsupport (fun q : ℝ × M => ρ i q)
  · exact (((ρ i).contMDiff.contMDiffAt).smul (hsummand i hi))
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (fun q : ℝ × M => ρ i q) (g i)) hi) ∞

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem hasMFDerivWithinAt_smulRight_value_unique {f : ℝ → M} {t : ℝ} {s : Set ℝ}
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) {v w : TangentSpace I (f t)}
    (h₁ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f s t ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (h₂ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f s t ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    v = w := by
  have hL := hs.eq h₁ h₂
  have h := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (f t) => L 1) hL
  simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionOn_value_unique {O O' : Set (ℝ × M)}
    {X X' : ℝ → (p : M) → TangentSpace I p}
    (hX : LoopFamilyVelocityExtensionOn (I := I) γ a b O X)
    (hX' : LoopFamilyVelocityExtensionOn (I := I) γ a b O' X')
    {t : ℝ} (ht : t ∈ Ico a b) {z : Surgery.Topology.Circle}
    (hmem : (t, γ t z) ∈ O) (hmem' : (t, γ t z) ∈ O') :
    X t (γ t z) = X' t (γ t z) :=
  hasMFDerivWithinAt_smulRight_value_unique (I := I)
    (uniqueDiffWithinAt_Ici t).uniqueMDiffWithinAt (hX.1 t ht z hmem) (hX'.1 t ht z hmem')

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionOn_value_unique' {O O' : Set (ℝ × M)}
    {X X' : ℝ → (p : M) → TangentSpace I p}
    (hX : LoopFamilyVelocityExtensionOn (I := I) γ a b O X)
    (hX' : LoopFamilyVelocityExtensionOn (I := I) γ a b O' X')
    {t : ℝ} (ht : t ∈ Ioc a b) {z : Surgery.Topology.Circle}
    (hmem : (t, γ t z) ∈ O) (hmem' : (t, γ t z) ∈ O') :
    X t (γ t z) = X' t (γ t z) :=
  hasMFDerivWithinAt_smulRight_value_unique (I := I)
    (uniqueDiffWithinAt_Iic t).uniqueMDiffWithinAt (hX.2 t ht z hmem) (hX'.2 t ht z hmem')

omit [CompleteSpace E] hBoundary hCompact hNonempty in
theorem loopFamilyVelocityExtension_of_localCover
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (h : LoopFamilyVelocityExtensionLocalCover (I := I) γ a b) :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  classical
  set F : ℝ × ℝ → ℝ × M := fun p => (p.2, γ p.2 (p.1 : Surgery.Topology.Circle)) with hF
  set P : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc a b with hP
  set K : Set (ℝ × M) := F '' P with hK
  have hFcont : ContinuousOn F P := by
    have hbase : ContinuousOn (fun p : ℝ × ℝ => (curveOfLoopFamily γ).lift p.1 p.2)
        (univ ×ˢ Icc a b) := hγ.continuousOn
    refine ContinuousOn.prodMk continuousOn_snd ?_
    exact hbase.mono fun p hp => ⟨trivial, hp.2⟩
  have hKcompact : IsCompact K := by
    rw [hK, hP]
    exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (by simpa only [hF] using hFcont)
  have hloc : ∀ p : ↥P, ∃ (X : ℝ → (p : M) → TangentSpace I p) (O : Set (ℝ × M)),
      IsOpen O ∧ F p.1 ∈ O ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun r : ℝ × M => (TotalSpace.mk' E r.2 (X r.1 r.2) : TangentBundle I M)) O ∧
      LoopFamilyVelocityExtensionOn (I := I) γ a b O X := by
    intro p
    have hmem : p.1 ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b := p.2
    exact h p.1.2 hmem.2 p.1.1
  choose X O hOo hFO hXs hXv using hloc
  have hcoverK : K ⊆ ⋃ p : ↥P, O p := by
    rintro q ⟨p, hp, rfl⟩
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hFO ⟨p, hp⟩⟩
  obtain ⟨s, hs⟩ := hKcompact.elim_finite_subcover O hOo hcoverK
  let U : Option {p : ↥P // p ∈ s} → Set (ℝ × M) := fun o =>
    match o with
    | none => Kᶜ
    | some p => O p.1
  have hUo : ∀ o, IsOpen (U o) := by
    rintro (_ | p)
    · exact hKcompact.isClosed.isOpen_compl
    · exact hOo p.1
  have hcoverU : (univ : Set (ℝ × M)) ⊆ ⋃ o, U o := by
    intro q _
    by_cases hq : q ∈ K
    · obtain ⟨p, hps, hqp⟩ := mem_iUnion₂.mp (hs hq)
      exact mem_iUnion.mpr ⟨some ⟨p, hps⟩, hqp⟩
    · exact mem_iUnion.mpr ⟨none, hq⟩
  obtain ⟨ρ, hρsub⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
      isClosed_univ U hUo hcoverU
  let Y : Option {p : ↥P // p ∈ s} → ℝ → (p : M) → TangentSpace I p := fun o =>
    match o with
    | none => 0
    | some p => X p.1
  have hY : ∀ o, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y o q.1 q.2) : TangentBundle I M)) (U o) := by
    rintro (_ | p)
    · exact ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := ∞))).contMDiffOn
    · exact hXs p.1
  refine ⟨fun t x => ∑ o, ρ o (t, x) • Y o t x, ?_, ?_, ?_⟩
  · exact contMDiff_assembledLoopFamilySection (I := I) ρ hUo hρsub Y hY
  · intro t ht z
    obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Icc z
    have htIcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have hqK : (t, γ t z) ∈ K := by
      refine ⟨(x, t), ⟨hx, htIcc⟩, ?_⟩
      change (t, γ t (x : Surgery.Topology.Circle)) = (t, γ t z)
      rw [hxz]
    obtain ⟨p, hps, hqp⟩ := mem_iUnion₂.mp (hs hqK)
    have hval : ∀ o, (t, γ t z) ∈ U o → Y o t (γ t z) = X p t (γ t z) := by
      rintro (_ | p') ho
      · exact absurd hqK ho
      · exact loopFamilyVelocityExtensionOn_value_unique (I := I) (hXv p') (hXv p) ht ho hqp
    have hsum1 : ∑ o, ρ o (t, γ t z) = 1 := by
      have h1 := ρ.sum_eq_one (show (t, γ t z) ∈ (univ : Set (ℝ × M)) from mem_univ _)
      rwa [finsum_eq_sum_of_fintype] at h1
    have hterm : ∀ o ∈ (Finset.univ : Finset _),
        ρ o (t, γ t z) • Y o t (γ t z) = ρ o (t, γ t z) • X p t (γ t z) := by
      intro o _
      by_cases h0 : ρ o (t, γ t z) = 0
      · rw [h0, zero_smul, zero_smul]
      · rw [hval o (hρsub o (subset_closure (Function.mem_support.mpr h0)))]
    have hsum_eq : ∑ o, ρ o (t, γ t z) • Y o t (γ t z) = X p t (γ t z) :=
      calc ∑ o, ρ o (t, γ t z) • Y o t (γ t z)
          = ∑ o, ρ o (t, γ t z) • X p t (γ t z) := Finset.sum_congr rfl hterm
        _ = (∑ o, ρ o (t, γ t z)) • X p t (γ t z) := (Finset.sum_smul ..).symm
        _ = X p t (γ t z) := by rw [hsum1, one_smul]
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Ici t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (∑ o, ρ o (t, γ t z) • Y o t (γ t z)))
    rw [hsum_eq]
    exact (hXv p).1 t ht z hqp
  · intro t ht z
    obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Icc z
    have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hqK : (t, γ t z) ∈ K := by
      refine ⟨(x, t), ⟨hx, htIcc⟩, ?_⟩
      change (t, γ t (x : Surgery.Topology.Circle)) = (t, γ t z)
      rw [hxz]
    obtain ⟨p, hps, hqp⟩ := mem_iUnion₂.mp (hs hqK)
    have hval : ∀ o, (t, γ t z) ∈ U o → Y o t (γ t z) = X p t (γ t z) := by
      rintro (_ | p') ho
      · exact absurd hqK ho
      · exact loopFamilyVelocityExtensionOn_value_unique' (I := I) (hXv p') (hXv p) ht ho hqp
    have hsum1 : ∑ o, ρ o (t, γ t z) = 1 := by
      have h1 := ρ.sum_eq_one (show (t, γ t z) ∈ (univ : Set (ℝ × M)) from mem_univ _)
      rwa [finsum_eq_sum_of_fintype] at h1
    have hterm : ∀ o ∈ (Finset.univ : Finset _),
        ρ o (t, γ t z) • Y o t (γ t z) = ρ o (t, γ t z) • X p t (γ t z) := by
      intro o _
      by_cases h0 : ρ o (t, γ t z) = 0
      · rw [h0, zero_smul, zero_smul]
      · rw [hval o (hρsub o (subset_closure (Function.mem_support.mpr h0)))]
    have hsum_eq : ∑ o, ρ o (t, γ t z) • Y o t (γ t z) = X p t (γ t z) :=
      calc ∑ o, ρ o (t, γ t z) • Y o t (γ t z)
          = ∑ o, ρ o (t, γ t z) • X p t (γ t z) := Finset.sum_congr rfl hterm
        _ = (∑ o, ρ o (t, γ t z)) • X p t (γ t z) := (Finset.sum_smul ..).symm
        _ = X p t (γ t z) := by rw [hsum1, one_smul]
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Iic t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (∑ o, ρ o (t, γ t z) • Y o t (γ t z)))
    rw [hsum_eq]
    exact (hXv p).2 t ht z hqp

omit [CompleteSpace E] hBoundary hCompact hNonempty in
theorem loopFamilyVelocityExtensionProducer_of_localCover
    (h : ∀ γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtensionLocalCover (I := I) γ a b) :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  fun γ hγ hi hemb => loopFamilyVelocityExtension_of_localCover (I := I) hγ (h γ hγ hi hemb)

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionLocalCover_of_velocityExtension
    (h : LoopFamilyVelocityExtension (I := I) a b γ) :
    LoopFamilyVelocityExtensionLocalCover (I := I) γ a b := by
  obtain ⟨X, hX, h1, h2⟩ := h
  intro t _ x
  exact ⟨X, univ, isOpen_univ, mem_univ _, hX.contMDiffOn,
    (fun t ht z _ => h1 t ht z), fun t ht z _ => h2 t ht z⟩

omit [CompleteSpace E] hBoundary hCompact hNonempty in
theorem loopFamilyVelocityExtensionLocalCover_iff_of_smoothOn
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b)) :
    LoopFamilyVelocityExtensionLocalCover (I := I) γ a b ↔
      LoopFamilyVelocityExtension (I := I) a b γ :=
  ⟨loopFamilyVelocityExtension_of_localCover (I := I) hγ,
    loopFamilyVelocityExtensionLocalCover_of_velocityExtension (I := I)⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionLocalCover_of_constantLoopFamily
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t') :
    LoopFamilyVelocityExtensionLocalCover (I := I) γ a b :=
  loopFamilyVelocityExtensionLocalCover_of_velocityExtension (I := I)
    (loopFamilyVelocityExtension_zero (I := I) a b γ hconst)

omit [CompleteSpace E] hBoundary hCompact hNonempty in
theorem loopFamilyVelocityExtensionProducer_iff_localCover :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b ↔
      ∀ γ : ℝ → ContinuousFreeLoop M,
        (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
        (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
        (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
        LoopFamilyVelocityExtensionLocalCover (I := I) γ a b :=
  ⟨fun h γ hγ hi hemb =>
      loopFamilyVelocityExtensionLocalCover_of_velocityExtension (I := I) (h γ hγ hi hemb),
    fun h => loopFamilyVelocityExtensionProducer_of_localCover (I := I) h⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
