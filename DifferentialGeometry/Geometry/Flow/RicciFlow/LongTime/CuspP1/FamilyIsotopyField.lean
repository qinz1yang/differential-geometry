import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyBasic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.Suspension

/-!
# CP1-D5: isotopy extension, step 2: the compactly supported extended time-dependent field
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Filter Bundle DifferentialGeometry.Analysis.ODE
noncomputable section
namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- the `∂ₜ` section of `T(ℝ × N)` is smooth -/
theorem contMDiff_timeSection_CPD5 :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent ∞
      (fun p : ℝ × N => (⟨p, ((1 : ℝ), (0 : E))⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × N))) := by
  have h0 : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × N => (⟨q.2, (fun (_ : ℝ) (_ : N) => (0 : E)) q.1 q.2⟩ : TangentBundle I N)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := N))).comp contMDiff_snd
  exact contMDiff_autonomizedFlowVF_section (fun (_ : ℝ) (_ : N) => (0 : E)) h0

omit [I.Boundaryless] in
/-- the time derivative of a smooth family, as a map into `TM`, is smooth on an open set -/
theorem contMDiffOn_timeDerivative_CPD5 {F : ℝ × N → M} {s : Set (ℝ × N)} (hs : IsOpen s)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × N => (⟨F p, mfderiv (𝓘(ℝ, ℝ).prod I) I F p ((1 : ℝ), (0 : E))⟩ :
        TangentBundle I M)) s := by
  have hT := hF.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hs.uniqueMDiffOn
  have hσ := (contMDiff_timeSection_CPD5 (I := I) (N := N)).contMDiffOn (s := s)
  have := hT.comp hσ (fun p hp => hp)
  refine this.congr fun p hp => ?_
  simp only [Function.comp, tangentMapWithin, mfderivWithin_of_isOpen hs hp]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
theorem smul_section_contMDiffWithinAt_CPD5
    (X : ℝ → ∀ x : M, TangentSpace I x) (ρ : ℝ × M → ℝ)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hρ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ ρ u q₀)
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (ρ q • X q.1 q.2) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hρ.smul hXfib
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).2 (ρ x) (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).2 (ρ q₀) (X q₀.1 q₀.2)

/-- The field `∂ₜ F` transported by the inverse of the graph map, on an open set containing the
graph image of `[c,d] × K`. -/
theorem exists_localField_CPD5 [T2Space M]
    {F : ℝ × N → M} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U) {c d : ℝ}
    (hJcd : Icc c d ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    (hinj : ∀ t ∈ J, InjOn (fun y => F (t, y)) K) :
    ∃ (T : Set (ℝ × M)) (X : ℝ → ∀ y : M, TangentSpace I y), IsOpen T ∧
      graphMap_CPD5 F '' (Icc c d ×ˢ K) ⊆ T ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)) T ∧
      ∀ s ∈ Icc c d, ∀ x ∈ K,
        X s (F (s, x)) = mfderiv (𝓘(ℝ, ℝ).prod I) I F (s, x) ((1 : ℝ), (0 : E)) := by
  classical
  have hopen : IsOpen (J ×ˢ U) := hJ.prod hU
  set S : Set (ℝ × N) := Icc c d ×ˢ K with hSdef
  by_cases hSne : S.Nonempty
  swap
  · have : S = ∅ := not_nonempty_iff_eq_empty.mp hSne
    refine ⟨∅, fun _ _ => 0, isOpen_empty, by simp [this], fun q hq => hq.elim, ?_⟩
    intro s hs x hx
    exact absurd ⟨(s, x), hs, hx⟩ hSne
  have hSc : IsCompact S := isCompact_Icc.prod hK
  have hSJU : S ⊆ J ×ˢ U := prod_mono hJcd hKU
  have hloc : IsLocalDiffeomorphOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (graphMap_CPD5 F) S := fun p =>
    isLocalDiffeomorphAt_graphMap_CPD5 hJ hU hF himm (hSJU p.2)
  have hinjG : InjOn (graphMap_CPD5 F) S := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩ ⟨t', x'⟩ ⟨ht', hx'⟩ h
    have h1 : t = t' := (Prod.ext_iff.mp h).1
    subst h1
    have h2 : F (t, x) = F (t, x') := (Prod.ext_iff.mp h).2
    exact Prod.ext rfl (hinj t (hJcd ht) hx hx' h2)
  obtain ⟨Φ0, hSΦ0, hΦ0⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hloc hSc hSne hinjG
  let Φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ0 (J ×ˢ U) hopen
  have hΦapp : ∀ p, Φ p = graphMap_CPD5 F p := fun p => congrFun hΦ0 p
  have hΦsrc : Φ.source = Φ0.source ∩ (J ×ˢ U) := rfl
  have hSΦ : S ⊆ Φ.source := fun p hp => by rw [hΦsrc]; exact ⟨hSΦ0 hp, hSJU hp⟩
  have hsrcJU : Φ.source ⊆ J ×ˢ U := fun p hp => by rw [hΦsrc] at hp; exact hp.2
  have hS'T : graphMap_CPD5 F '' S ⊆ Φ.target := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hΦapp]
    exact Φ.toPartialEquiv.map_source (hSΦ hp)
  -- the field on the target
  let X : ℝ → ∀ y : M, TangentSpace I y := fun s y =>
    (mfderiv (𝓘(ℝ, ℝ).prod I) I F (Φ.toPartialEquiv.symm (s, y)) ((1 : ℝ), (0 : E)) : E)
  have hinv : ∀ q ∈ Φ.target, F (Φ.toPartialEquiv.symm q) = q.2 := by
    intro q hq
    have := hΦapp (Φ.toPartialEquiv.symm q)
    rw [Φ.toPartialEquiv.right_inv hq] at this
    exact (Prod.ext_iff.mp this).2.symm
  refine ⟨Φ.target, X, Φ.open_target, hS'T, ?_, ?_⟩
  · have hT := contMDiffOn_timeDerivative_CPD5 hopen hF
    have hΦinv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ Φ.toPartialEquiv.symm Φ.target :=
      Φ.contMDiffOn_invFun
    have hc := hT.comp hΦinv (fun q hq => hsrcJU (Φ.toPartialEquiv.map_target hq))
    refine hc.congr fun q hq => ?_
    simp only [Function.comp]
    have h1 := hinv q hq
    refine Bundle.TotalSpace.ext ?_ ?_
    · exact h1.symm
    · rfl
  · intro s hs x hx
    have hp : (s, x) ∈ S := ⟨hs, hx⟩
    have h2 : Φ.toPartialEquiv.symm (s, F (s, x)) = (s, x) := by
      have := Φ.toPartialEquiv.left_inv (hSΦ hp)
      rw [hΦapp] at this
      exact this
    change (mfderiv (𝓘(ℝ, ℝ).prod I) I F (Φ.toPartialEquiv.symm (s, F (s, x)))
      ((1 : ℝ), (0 : E)) : E) = _
    rw [h2]

/-- A smooth section on an open `T`, cut off by a bump equal to `1` on a compact `S' ⊆ T`: a global
smooth section, equal to `X` on `S'`, vanishing off a compact subset of `T`. -/
theorem exists_bumpSection_CPD5 [T2Space M] [SigmaCompactSpace M]
    {T : Set (ℝ × M)} (hT : IsOpen T) {S' : Set (ℝ × M)} (hS'c : IsCompact S') (hS'T : S' ⊆ T)
    {X : ℝ → ∀ y : M, TangentSpace I y}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)) T) :
    ∃ (Z : ℝ → ∀ y : M, TangentSpace I y) (L : Set (ℝ × M)), IsCompact L ∧ L ⊆ T ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, Z q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ s y, (s, y) ∉ L → Z s y = 0) ∧ ∀ s y, (s, y) ∈ S' → Z s y = X s y := by
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hLc, hS'L, hLT⟩ := exists_compact_between hS'c hT hS'T
  obtain ⟨ρ, hρ1, hρ0, hρ01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, ℝ).prod I) (n := ⊤) hS'c.isClosed hS'L
  have hsuppρ : tsupport (fun q => ρ q) ⊆ L := by
    refine closure_minimal ?_ hLc.isClosed
    intro q hq
    by_contra hqL
    exact hq (hρ0 q hqL)
  have hρsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => ρ q) := ρ.contMDiff
  refine ⟨fun s y => ρ (s, y) • X s y, L, hLc, hLT, ?_, ?_, ?_⟩
  · have h1 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (ρ q • X q.1 q.2) : TangentBundle I M))
        T := fun q hq =>
      smul_section_contMDiffWithinAt_CPD5 X (fun q => ρ q) ((hρsm q).contMDiffWithinAt) (hX q hq)
    have h2 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (ρ q • X q.1 q.2) : TangentBundle I M))
        (tsupport (fun q : ℝ × M => ρ q))ᶜ := by
      have hzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
          (fun q : ℝ × M => (TotalSpace.mk' E q.2 (0 : TangentSpace I q.2) : TangentBundle I M))
          (tsupport (fun q : ℝ × M => ρ q))ᶜ :=
        ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
          contMDiff_snd).contMDiffOn
      refine hzero.congr ?_
      intro q hq
      have hη0 : ρ q = 0 := by
        have hnotsupp : q ∉ Function.support (fun q : ℝ × M => ρ q) :=
          fun hc => hq (subset_tsupport _ hc)
        simpa [Function.mem_support] using hnotsupp
      simp [hη0]
    have hcover : T ∪ (tsupport (fun q : ℝ × M => ρ q))ᶜ = Set.univ := by
      refine Set.eq_univ_of_forall (fun q => ?_)
      by_cases h : q ∈ tsupport (fun q : ℝ × M => ρ q)
      · exact Or.inl (hLT (hsuppρ h))
      · exact Or.inr h
    exact contMDiff_of_contMDiffOn_union_of_isOpen h1 h2 hcover hT
      (isClosed_tsupport _).isOpen_compl
  · intro s y hy
    have : ρ (s, y) = 0 := hρ0 (s, y) hy
    simp [this]
  · intro s y hy
    have h1 : ρ (s, y) = 1 := hρ1.self_of_nhdsSet _ hy
    change ρ (s, y) • X s y = X s y
    rw [h1, one_smul]

theorem exists_field_CPD5 [T2Space M] [SigmaCompactSpace M]
    {F : ℝ × N → M} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U) {c d : ℝ}
    (hJcd : Icc c d ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    (hinj : ∀ t ∈ J, InjOn (fun y => F (t, y)) K) :
    ∃ (W : ℝ → ∀ y : M, TangentSpace I y) (C : Set M), IsCompact C ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, W q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ s y, y ∉ C → W s y = 0) ∧
      ∀ s ∈ Icc c d, ∀ x ∈ K,
        W s (F (s, x)) = mfderiv (𝓘(ℝ, ℝ).prod I) I F (s, x) ((1 : ℝ), (0 : E)) := by
  obtain ⟨T, X, hT, hST, hXsm, hXval⟩ := exists_localField_CPD5 hJ hU hK hKU hJcd hF himm hinj
  have hS'c : IsCompact (graphMap_CPD5 F '' (Icc c d ×ˢ K)) := by
    have hGcont : ContinuousOn (graphMap_CPD5 F) (J ×ˢ U) :=
      (contMDiffOn_fst.prodMk hF).continuousOn
    exact (isCompact_Icc.prod hK).image_of_continuousOn
      (hGcont.mono (prod_mono hJcd hKU))
  obtain ⟨Z, L, hLc, hLT, hZsm, hZ0, hZX⟩ := exists_bumpSection_CPD5 hT hS'c hST hXsm
  refine ⟨Z, Prod.snd '' L, hLc.image continuous_snd, hZsm, ?_, ?_⟩
  · intro s y hy
    exact hZ0 s y (fun h => hy ⟨(s, y), h, rfl⟩)
  · intro s hs x hx
    rw [hZX s (F (s, x)) ⟨(s, x), ⟨hs, hx⟩, rfl⟩]
    exact hXval s hs x hx

end GC.LongTime.CuspP1
