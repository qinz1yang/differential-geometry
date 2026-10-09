import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowStage

/-!
# CP1-D7 (6): exterior kernel local constancy away from surgery times
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem exists_regionHomeo_of_window_CPD7 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (N : ℕ)
    (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (U : ∀ i, Set (L.cores.model i).Carrier)
    (D : ∀ i, SmoothDatum_CPD7 F.observation L.cores.start (L.cores.map i) N J (U i) Fs Ls hFL)
    (hJo : IsOpen J) (hJstart : J ⊆ Ioi L.cores.start) (hJord : J.OrdConnected)
    (hUo : ∀ i, IsOpen (U i)) (hSU : ∀ i, range (E.truncation i).inclusion ⊆ U i)
    (hUd : ∀ i, ∀ t ∈ J, ∀ (_ : L.cores.start ≤ t), U i ⊆ L.cores.domain i t)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t) (hsJ : s ∈ J) (htJ : t ∈ J)
    (hseq : (F.observation.history N).activeStage ⟨s, (hJh s hsJ).1, (hJh s hsJ).2⟩ =
      (F.observation.history N).activeStage ⟨t, (hJh t htJ).1, (hJh t htJ).2⟩) :
    ∃ e : E.region s ≃ₜ E.region t, ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count)
      (z : Torus), e (portLoopRegionMap_CPD3 E i q s hs z) = portLoopRegionMap_CPD3 E i q t ht z := by
  classical
  let cores := L.cores
  let T := F.observation
  let Pd := (T.history N).backwardSurvivorDomain Fs Ls hFL
  let jj : ∀ u, u ∈ J → Fin ((T.history N).eventCount + 1) := fun u hu =>
    (T.history N).activeStage ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  have hjj : ∀ u (hu : u ∈ J), Fs ≤ jj u hu ∧ jj u hu ≤ Ls := fun u hu =>
    hst u (hJh u hu).1 (hJh u hu).2 hu
  let Φ : ∀ u (hu : u ∈ J), Pd → ((T.history N).stage (jj u hu)).Carrier := fun u hu =>
    (T.history N).backwardSurvivorMap Fs Ls hFL (jj u hu) (hjj u hu).1 (hjj u hu).2
  have hΦo : ∀ u (hu : u ∈ J), Topology.IsOpenEmbedding (Φ u hu) := fun u hu =>
    isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _
  have hueq : ∀ u (hu : u ∈ J), postStage T u = (T.history N).stage (jj u hu) := fun u hu =>
    postStage_eq_stage_active_CPD2 T N ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  -- the family composed with Φ is the actual map, up to the cast
  have hcast : ∀ i u (hu : u ∈ J) (hu' : cores.start ≤ u) (y : (cores.model i).Carrier),
      y ∈ U i → Φ u hu ((D i).z (u, y)) = carrierHomeo_CPD2 (hueq u hu) (cores.map i u hu' y) := by
    intro i u hu hu' y hy
    exact (carrierHomeo_eq_of_heq_CPD2 (hueq u hu) _ _ ((D i).agrees u hu y hy).symm).symm
  have hcast' : ∀ i u (hu : u ∈ J) (hu' : cores.start ≤ u) (y : (cores.model i).Carrier),
      y ∈ U i → ∀ (j : Fin ((T.history N).eventCount + 1)) (hj : jj u hu = j) (h1 : Fs ≤ j)
        (h2 : j ≤ Ls), (T.history N).backwardSurvivorMap Fs Ls hFL j h1 h2 ((D i).z (u, y)) =
          carrierHomeo_CPD2 ((hueq u hu).trans (congrArg (T.history N).stage hj))
            (cores.map i u hu' y) := by
    intro i u hu hu' y hy j hj
    subst hj
    intro h1 h2
    exact hcast i u hu hu' y hy
  have hΦsm : ∀ u (hu : u ∈ J), ContMDiff (𝓡 3) (𝓡 3) ∞ (Φ u hu) := fun u hu =>
    contMDiff_survivorMap_CPD7 _ _ _ _ _ _ _
  have himm : ∀ i, ∀ τ ∈ J, ∀ x ∈ U i,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => (D i).z (τ, y)) x) := by
    intro i τ hτ x hx
    have hτ' : cores.start ≤ τ := (hJstart hτ).le
    have hzat : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (D i).z (τ, x) :=
      (D i).smooth.contMDiffAt ((hJo.prod (hUo i)).mem_nhds ⟨hτ, hx⟩)
    have hgat : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => (D i).z (τ, y)) x :=
      hzat.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    have hdx : x ∈ cores.domain i τ := hUd i τ hτ hτ' hx
    have hmap : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (cores.map i τ hτ') x :=
      (cores.smooth i τ hτ').contMDiffAt ((cores.domain i τ).isOpen.mem_nhds hdx)
    have hinjmap : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (cores.map i τ hτ') x) :=
      mfderiv_injective_of_subtype_CPD7 (cores.domain i τ) _ ⟨x, hdx⟩
        (hmap.mdifferentiableAt (by simp))
        ((cores.embedding i τ hτ').isImmersion.mfderiv_injective (by decide) ⟨x, hdx⟩)
    have h2 := (mfderiv_injective_carrierHomeo_CPD7 (hueq τ hτ) (cores.map i τ hτ') x).mpr hinjmap
    have hev : (fun y => Φ τ hτ ((D i).z (τ, y))) =ᶠ[𝓝 x]
        fun y => carrierHomeo_CPD2 (hueq τ hτ) (cores.map i τ hτ' y) := by
      filter_upwards [(hUo i).mem_nhds hx] with y hy
      exact hcast i τ hτ hτ' y hy
    have h3 : mfderiv (𝓡 3) (𝓡 3) (fun y => Φ τ hτ ((D i).z (τ, y))) x =
        (mfderiv (𝓡 3) (𝓡 3) (Φ τ hτ) ((D i).z (τ, x))).comp
          (mfderiv (𝓡 3) (𝓡 3) (fun y => (D i).z (τ, y)) x) :=
      mfderiv_comp x ((hΦsm τ hτ).contMDiffAt.mdifferentiableAt (by simp))
        (hgat.mdifferentiableAt (by simp))
    have h4 := hev.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
    rw [h3] at h4
    have h5 : Function.Injective
        ((mfderiv (𝓡 3) (𝓡 3) (Φ τ hτ) ((D i).z (τ, x))).comp
          (mfderiv (𝓡 3) (𝓡 3) (fun y => (D i).z (τ, y)) x)) := by rw [h4]; exact h2
    exact Function.Injective.of_comp (f := mfderiv (𝓡 3) (𝓡 3) (Φ τ hτ) ((D i).z (τ, x))) h5
  have hinj : ∀ i, ∀ τ ∈ J, InjOn (fun y => (D i).z (τ, y)) (range (E.truncation i).inclusion) := by
    intro i τ hτ x hx x' hx' h
    have hτ' : cores.start ≤ τ := (hJstart hτ).le
    have h1 := hcast i τ hτ hτ' x (hSU i hx)
    have h2 := hcast i τ hτ hτ' x' (hSU i hx')
    have h12 : cores.map i τ hτ' x = cores.map i τ hτ' x' := by
      apply (carrierHomeo_CPD2 (hueq τ hτ)).injective
      rw [← h1, ← h2]
      exact congrArg (Φ τ hτ) h
    have hdx : x ∈ cores.domain i τ := hUd i τ hτ hτ' (hSU i hx)
    have hdx' : x' ∈ cores.domain i τ := hUd i τ hτ hτ' (hSU i hx')
    exact congrArg Subtype.val ((cores.embedding i τ hτ').isEmbedding.injective
      (a₁ := ⟨x, hdx⟩) (a₂ := ⟨x', hdx'⟩) h12)
  have hdisj : ∀ i j, i ≠ j → ∀ τ ∈ J, ∀ x ∈ range (E.truncation i).inclusion,
      ∀ x' ∈ range (E.truncation j).inclusion, (D i).z (τ, x) ≠ (D j).z (τ, x') := by
    intro i j hij τ hτ x hx x' hx' h
    have hτ' : cores.start ≤ τ := (hJstart hτ).le
    have h1 := hcast i τ hτ hτ' x (hSU i hx)
    have h2 := hcast j τ hτ hτ' x' (hSU j hx')
    have h12 : cores.map i τ hτ' x = cores.map j τ hτ' x' := by
      apply (carrierHomeo_CPD2 (hueq τ hτ)).injective
      rw [← h1, ← h2]
      exact congrArg (Φ τ hτ) h
    exact Set.disjoint_left.mp (cores.disjoint τ hτ' hij) ⟨x, hUd i τ hτ hτ' (hSU i hx), rfl⟩
      (h12 ▸ ⟨x', hUd j τ hτ hτ' (hSU j hx'), rfl⟩)
  have hJab : Icc (min s t) (max s t) ⊆ J := by
    rcases le_total s t with h | h
    · rw [min_eq_left h, max_eq_right h]; exact hJord.out hsJ htJ
    · rw [min_eq_right h, max_eq_left h]; exact hJord.out htJ hsJ
  let hj0 := hjj s hsJ
  let ht_eq : postStage T t = (T.history N).stage (jj s hsJ) :=
    (hueq t htJ).trans (congrArg (T.history N).stage hseq.symm)
  let ιs : Pd → (postStage T s).Carrier := fun p => (carrierHomeo_CPD2 (hueq s hsJ)).symm (Φ s hsJ p)
  let ιt : Pd → (postStage T t).Carrier := fun p => (carrierHomeo_CPD2 ht_eq).symm (Φ s hsJ p)
  have hιs : Topology.IsOpenEmbedding ιs :=
    (carrierHomeo_CPD2 (hueq s hsJ)).symm.isOpenEmbedding.comp (hΦo s hsJ)
  let e : (postStage T s).Carrier ≃ₜ (postStage T t).Carrier :=
    (carrierHomeo_CPD2 (hueq s hsJ)).trans (carrierHomeo_CPD2 ht_eq).symm
  have he : ∀ p, e (ιs p) = ιt p := by
    intro p
    simp [e, ιs, ιt]
  have hfs : ∀ (i : Fin cores.count) (c : (E.truncation i).core.Carrier),
      cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c) =
        ιs ((D i).z (s, (E.truncation i).inclusion c)) := by
    intro i c
    simp only [ιs]
    rw [hcast i s hsJ (E.after_cores.trans hs) _ (hSU i ⟨c, rfl⟩)]
    simp
  have hft : ∀ (i : Fin cores.count) (c : (E.truncation i).core.Carrier),
      cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) =
        ιt ((D i).z (t, (E.truncation i).inclusion c)) := by
    intro i c
    simp only [ιt]
    have := hcast' i t htJ (E.after_cores.trans ht) _ (hSU i ⟨c, rfl⟩) (jj s hsJ) hseq.symm hj0.1 hj0.2
    change (T.history N).backwardSurvivorMap Fs Ls hFL (jj s hsJ) hj0.1 hj0.2 _ = _ at this
    show _ = (carrierHomeo_CPD2 ht_eq).symm ((T.history N).backwardSurvivorMap Fs Ls hFL (jj s hsJ)
      hj0.1 hj0.2 _)
    rw [this]
    simp
  exact exists_regionHomeo_of_smooth_cores_CPD5 E s t hs ht (fun i => (D i).z) hJo hUo hSU
    (min_le_max) hJab (fun i => (D i).smooth) himm hinj hdisj ιs hιs ιt e he
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩ hfs hft


/-- IMS01 (second kernel) away from surgery times: the kernel of `π₁ Torus → π₁ (E.region s)` is
locally constant at every time `τ > cores.start` which is not an event time of any history. -/
theorem hlocal_nonSurgery_CPD7 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start)
    (hτ : L.cores.start < τ.1) (hne : NonSurgeryTime_CPD7 F.observation τ.1) :
    ∀ᶠ s : Ici E.start in 𝓝 τ,
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker := by
  classical
  have hcomp : ∀ j, IsCompact (range (E.truncation j).inclusion) := fun j =>
    isCompact_range (E.truncation j).inclusion.continuous
  have hdom : ∀ j, range (E.truncation j).inclusion ⊆ L.cores.domain j τ.1 := fun j y hy =>
    L.cores.advertised_ball j τ.1 (E.after_cores.trans τ.2) (E.in_ball j τ.1 τ.2 hy)
  obtain ⟨N, Fs, Ls, hFL, J, U, D, hτJ, hJo, hJstart, hJord, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_smoothWindow_CPD7 L.cores hτ (fun j => range (E.truncation j).inclusion) hcomp hdom
  obtain ⟨δ, hδ, hconst⟩ := exists_const_activeStage_CPD7 (F.observation.history N)
    (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2 (hne N)
  set J' : Set ℝ := J ∩ Ioo (τ.1 - δ) (τ.1 + δ) with hJ'
  have hJ'o : IsOpen J' := hJo.inter isOpen_Ioo
  have hτJ' : τ.1 ∈ J' := ⟨hτJ, by constructor <;> linarith⟩
  have hsub : J' ⊆ J := inter_subset_left
  have hJ'ord : J'.OrdConnected := hJord.inter ordConnected_Ioo
  have hact : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J' →
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ =
        (F.observation.history N).activeStage ⟨τ.1, (hJh τ.1 hτJ).1, (hJh τ.1 hτJ).2⟩ := by
    intro t h0 h1 ht
    apply hconst t h0 h1
    rw [abs_lt]
    constructor <;> linarith [ht.2.1, ht.2.2]
  have hev : ∀ᶠ s : Ici E.start in 𝓝 τ, s.1 ∈ J' :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hJ'o.mem_nhds hτJ')
  filter_upwards [hev] with s hs
  obtain ⟨e, he⟩ := exists_regionHomeo_of_window_CPD7 E N Fs Ls hFL J' U
    (fun j => (D j).mono hsub hJ'o subset_rfl) hJ'o (fun t ht => hJstart (hsub ht)) hJ'ord hUo hSU
    (fun j t ht => hUd j t (hsub ht)) (fun t ht => hJh t (hsub ht))
    (fun t h0 h1 ht => hst t h0 h1 (hsub ht))
    s.1 τ.1 s.2 τ.2 hs hτJ' ((hact s.1 (hJh s.1 (hsub hs)).1 (hJh s.1 (hsub hs)).2 hs).trans
      (hact τ.1 (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2 hτJ').symm)
  have : portLoopRegionMap_CPD3 E i q τ.1 τ.2 =
      (e : C(E.region s.1, E.region τ.1)).comp (portLoopRegionMap_CPD3 E i q s.1 s.2) :=
    ContinuousMap.ext fun z => (he i q z).symm
  rw [this, kernel_comp_homeomorph]

/-- right-sided IMS01 at every time `τ > cores.start` (event times allowed): the active stage is
right-continuous, so the smooth window works on `[τ, τ + ε)`. -/
theorem hlocal_right_CPD7 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start)
    (hτ : L.cores.start < τ.1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 ≤ s.1 → s.1 < τ.1 + ε →
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker := by
  classical
  have hcomp : ∀ j, IsCompact (range (E.truncation j).inclusion) := fun j =>
    isCompact_range (E.truncation j).inclusion.continuous
  have hdom : ∀ j, range (E.truncation j).inclusion ⊆ L.cores.domain j τ.1 := fun j y hy =>
    L.cores.advertised_ball j τ.1 (E.after_cores.trans τ.2) (E.in_ball j τ.1 τ.2 hy)
  obtain ⟨N, Fs, Ls, hFL, J, U, D, hτJ, hJo, hJstart, hJord, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_smoothWindow_CPD7 L.cores hτ (fun j => range (E.truncation j).inclusion) hcomp hdom
  obtain ⟨δ, hδ, hconst⟩ := exists_right_const_activeStage_CPD7 (F.observation.history N)
    (hJh τ.1 hτJ).1 (hJh τ.1 hτJ).2
  set J' : Set ℝ := J ∩ Iio (τ.1 + δ) with hJ'
  have hJ'o : IsOpen J' := hJo.inter isOpen_Iio
  have hτJ' : τ.1 ∈ J' := ⟨hτJ, by simp [hδ]⟩
  have hsub : J' ⊆ J := inter_subset_left
  have hJ'ord : J'.OrdConnected := hJord.inter ordConnected_Iio
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ'o τ.1 hτJ'
  refine ⟨ε, hε, fun s hs1 hs2 => ?_⟩
  have hsJ' : s.1 ∈ J' := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith)
  obtain ⟨e, he⟩ := exists_regionHomeo_of_window_CPD7 E N Fs Ls hFL J' U
    (fun j => (D j).mono hsub hJ'o subset_rfl) hJ'o (fun t ht => hJstart (hsub ht)) hJ'ord hUo hSU
    (fun j t ht => hUd j t (hsub ht)) (fun t ht => hJh t (hsub ht))
    (fun t h0 h1 ht => hst t h0 h1 (hsub ht))
    s.1 τ.1 s.2 τ.2 hsJ' hτJ'
    (hconst s.1 (hJh s.1 (hsub hsJ')).1 (hJh s.1 (hsub hsJ')).2 hs1 hsJ'.2 |>.trans
      (rfl : (F.observation.history N).activeStage
          ⟨τ.1, (hJh τ.1 hτJ).1, (hJh τ.1 hτJ).2⟩ = _))
  have : portLoopRegionMap_CPD3 E i q τ.1 τ.2 =
      (e : C(E.region s.1, E.region τ.1)).comp (portLoopRegionMap_CPD3 E i q s.1 s.2) :=
    ContinuousMap.ext fun z => (he i q z).symm
  rw [this, kernel_comp_homeomorph]

/-- `hlocal` of CP1-D3 from the proved cases (surgery-free; right-sided at every `τ > cores.start`)
and two explicit residues: `hresLeft` (the left side of a surgery time `τ`, Q5: one retained region
with `π₁`-injective maps to the exteriors on both sides of the event) and `hresBoundary` (the
boundary time `τ = cores.start`, where no window below the base time exists). -/
theorem hlocal_of_residual_CPD7 {L : LateCutFamily F K slices}
    (hresLeft : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      L.cores.start < τ.1 → ¬ NonSurgeryTime_CPD7 F.observation τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 - ε < s.1 → s.1 < τ.1 →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker)
    (hresBoundary : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      ¬ L.cores.start < τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, |s.1 - τ.1| < ε →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker) :
    ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus),
      IsLocallyConstant (fun τ : Ici E.start =>
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker) := by
  intro E i q x
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ
  have hball : ∀ ε : ℝ, 0 < ε → ∀ᶠ s : Ici E.start in 𝓝 τ, |s.1 - τ.1| < ε := fun ε hε => by
    have := continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds τ.1 hε)
    filter_upwards [this] with s hs
    have h2 := Metric.mem_ball.mp (show s.1 ∈ Metric.ball τ.1 ε from hs)
    rwa [Real.dist_eq] at h2
  by_cases hst : L.cores.start < τ.1
  · by_cases hne : NonSurgeryTime_CPD7 F.observation τ.1
    · exact hlocal_nonSurgery_CPD7 E i q x τ hst hne
    · obtain ⟨ε₁, hε₁, h₁⟩ := hlocal_right_CPD7 E i q x τ hst
      obtain ⟨ε₂, hε₂, h₂⟩ := hresLeft E i q x τ hst hne
      filter_upwards [hball (min ε₁ ε₂) (lt_min hε₁ hε₂)] with s hs
      rw [abs_lt] at hs
      rcases le_or_gt τ.1 s.1 with h | h
      · exact h₁ s h (by linarith [hs.2, min_le_left ε₁ ε₂])
      · exact h₂ s (by linarith [hs.1, min_le_right ε₁ ε₂]) h
  · obtain ⟨ε, hε, h⟩ := hresBoundary E i q x τ hst
    filter_upwards [hball ε hε] with s hs
    exact h s hs

end GC.LongTime.CuspP1
