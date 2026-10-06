import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorBoundarySlice

/-!
# CP1-D8 (G1, 4): region homeomorphism from the base time via time reparametrisation
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

/-- the reparametrisation `φ(τ) = a + (τ - a)² / d` -/
def reparamBd_CPD8 (a d : ℝ) (τ : ℝ) : ℝ := a + (τ - a) ^ 2 / d

theorem contDiff_reparamBd_CPD8 (a d : ℝ) : ContDiff ℝ ∞ (reparamBd_CPD8 a d) := by
  unfold reparamBd_CPD8
  fun_prop

theorem exists_regionHomeo_of_boundaryWindow_CPD8 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (N : ℕ)
    (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (c : ℝ)
    (U : ∀ i, Set (L.cores.model i).Carrier)
    (D : ∀ i, SmoothDatumC_CPD8 F.observation L.cores.start (L.cores.map i) N
      (Ico L.cores.start c) (U i) Fs Ls hFL)
    (hUo : ∀ i, IsOpen (U i)) (hSU : ∀ i, range (E.truncation i).inclusion ⊆ U i)
    (hUd : ∀ i, ∀ t ∈ Ico L.cores.start c, ∀ (_ : L.cores.start ≤ t),
      U i ⊆ L.cores.domain i t)
    (hJh : ∀ t ∈ Ico L.cores.start c, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon),
      t ∈ Ico L.cores.start c →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (s t : ℝ) (hs : E.start ≤ s) (hsc : s = L.cores.start) (ht : E.start ≤ t)
    (hsJ : s ∈ Ico L.cores.start c) (htJ : t ∈ Ico L.cores.start c)
    (hseq : (F.observation.history N).activeStage ⟨s, (hJh s hsJ).1, (hJh s hsJ).2⟩ =
      (F.observation.history N).activeStage ⟨t, (hJh t htJ).1, (hJh t htJ).2⟩) :
    ∃ e : E.region s ≃ₜ E.region t, ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count)
      (z : Torus), e (portLoopRegionMap_CPD3 E i q s hs z) = portLoopRegionMap_CPD3 E i q t ht z := by
  classical
  have hle : s ≤ t := by rw [hsc]; exact htJ.1
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    exact ⟨Homeomorph.refl _, fun i q z => rfl⟩
  have hd : 0 < t - s := sub_pos.mpr h
  let cores := L.cores
  let T := F.observation
  obtain ⟨himm, hinj, hdisj⟩ := sliceFacts_CPD8 E N Fs Ls hFL c U D hUo hSU hUd hJh hst
  let φ : ℝ → ℝ := reparamBd_CPD8 s (t - s)
  have hφge : ∀ τ, s ≤ φ τ := fun τ => by
    simp only [φ, reparamBd_CPD8]
    have : 0 ≤ (τ - s) ^ 2 / (t - s) := div_nonneg (sq_nonneg _) hd.le
    linarith
  have hφs : φ s = s := by simp [φ, reparamBd_CPD8]
  have hφt : φ t = t := by
    simp only [φ, reparamBd_CPD8]
    field_simp
    ring
  have hφc : Continuous φ := (contDiff_reparamBd_CPD8 s (t - s)).continuous
  let J' : Set ℝ := φ ⁻¹' Iio c
  have hJ'o : IsOpen J' := isOpen_Iio.preimage hφc
  have hφJ : ∀ τ ∈ J', φ τ ∈ Ico cores.start c := fun τ hτ => ⟨hsc ▸ hφge τ, hτ⟩
  have hJab : Icc s t ⊆ J' := by
    intro τ hτ
    have h1 : φ τ ≤ τ := by
      simp only [φ, reparamBd_CPD8]
      have : (τ - s) ^ 2 / (t - s) ≤ τ - s := by
        rw [div_le_iff₀ hd]
        nlinarith [hτ.1, hτ.2]
      linarith
    show φ τ < c
    exact lt_of_le_of_lt (h1.trans hτ.2) htJ.2
  let jj : ∀ u, u ∈ Ico cores.start c → Fin ((T.history N).eventCount + 1) := fun u hu =>
    (T.history N).activeStage ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  have hjj : ∀ u (hu : u ∈ Ico cores.start c), Fs ≤ jj u hu ∧ jj u hu ≤ Ls := fun u hu =>
    hst u (hJh u hu).1 (hJh u hu).2 hu
  let Pd := (T.history N).backwardSurvivorDomain Fs Ls hFL
  let Φ : ∀ u (hu : u ∈ Ico cores.start c), Pd → ((T.history N).stage (jj u hu)).Carrier :=
    fun u hu =>
    (T.history N).backwardSurvivorMap Fs Ls hFL (jj u hu) (hjj u hu).1 (hjj u hu).2
  have hΦo : ∀ u (hu : u ∈ Ico cores.start c), Topology.IsOpenEmbedding (Φ u hu) := fun u hu =>
    isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _
  have hueq : ∀ u (hu : u ∈ Ico cores.start c), postStage T u = (T.history N).stage (jj u hu) :=
    fun u hu => postStage_eq_stage_active_CPD2 T N ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  have hcast : ∀ i u (hu : u ∈ Ico cores.start c) (y : (cores.model i).Carrier),
      y ∈ U i → Φ u hu ((D i).z (u, y)) = carrierHomeo_CPD2 (hueq u hu) (cores.map i u hu.1 y) := by
    intro i u hu y hy
    exact (carrierHomeo_eq_of_heq_CPD2 (hueq u hu) _ _ ((D i).agrees u hu y hy).symm).symm
  have hcast' : ∀ i u (hu : u ∈ Ico cores.start c) (y : (cores.model i).Carrier),
      y ∈ U i → ∀ (j : Fin ((T.history N).eventCount + 1)) (hj : jj u hu = j) (h1 : Fs ≤ j)
        (h2 : j ≤ Ls), (T.history N).backwardSurvivorMap Fs Ls hFL j h1 h2 ((D i).z (u, y)) =
          carrierHomeo_CPD2 ((hueq u hu).trans (congrArg (T.history N).stage hj))
            (cores.map i u hu.1 y) := by
    intro i u hu y hy j hj
    subst hj
    intro h1 h2
    exact hcast i u hu y hy
  have hhs : s ∈ Icc s t := ⟨le_rfl, hle⟩
  have hht : t ∈ Icc s t := ⟨hle, le_rfl⟩
  let ht_eq : postStage T t = (T.history N).stage (jj s hsJ) :=
    (hueq t htJ).trans (congrArg (T.history N).stage hseq.symm)
  let ιs : Pd → (postStage T s).Carrier := fun p =>
    (carrierHomeo_CPD2 (hueq s hsJ)).symm (Φ s hsJ p)
  let ιt : Pd → (postStage T t).Carrier := fun p => (carrierHomeo_CPD2 ht_eq).symm (Φ s hsJ p)
  have hιs : Topology.IsOpenEmbedding ιs :=
    (carrierHomeo_CPD2 (hueq s hsJ)).symm.isOpenEmbedding.comp (hΦo s hsJ)
  let e : (postStage T s).Carrier ≃ₜ (postStage T t).Carrier :=
    (carrierHomeo_CPD2 (hueq s hsJ)).trans (carrierHomeo_CPD2 ht_eq).symm
  have he : ∀ p, e (ιs p) = ιt p := by
    intro p
    simp [e, ιs, ιt]
  have hfs : ∀ (i : Fin cores.count) (c' : (E.truncation i).core.Carrier),
      cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c') =
        ιs ((D i).z (φ s, (E.truncation i).inclusion c')) := by
    intro i c'
    rw [hφs]
    simp only [ιs]
    rw [hcast i s hsJ _ (hSU i ⟨c', rfl⟩)]
    simp
  have hft : ∀ (i : Fin cores.count) (c' : (E.truncation i).core.Carrier),
      cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c') =
        ιt ((D i).z (φ t, (E.truncation i).inclusion c')) := by
    intro i c'
    rw [hφt]
    simp only [ιt]
    have := hcast' i t htJ _ (hSU i ⟨c', rfl⟩) (jj s hsJ) hseq.symm (hjj s hsJ).1 (hjj s hsJ).2
    change (T.history N).backwardSurvivorMap Fs Ls hFL (jj s hsJ) _ _ _ = _ at this
    show _ = (carrierHomeo_CPD2 ht_eq).symm ((T.history N).backwardSurvivorMap Fs Ls hFL
      (jj s hsJ) (hjj s hsJ).1 (hjj s hsJ).2 _)
    rw [this]
    simp
  have hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × (cores.model i).Carrier => (D i).z (φ p.1, p.2)) (J' ×ˢ U i) := by
    intro i
    have hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun p : ℝ × (cores.model i).Carrier => (φ p.1, p.2)) :=
      (((contDiff_reparamBd_CPD8 s (t - s)).contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
    exact ((D i).smooth).comp hg.contMDiffOn (fun p hp => ⟨hφJ p.1 hp.1, hp.2⟩)
  exact exists_regionHomeo_of_smooth_cores_CPD5 E s t hs ht
    (fun i p => (D i).z (φ p.1, p.2)) hJ'o hUo hSU hle hJab hF
    (fun i τ hτ x hx => himm i (φ τ) (hφJ τ hτ) x hx)
    (fun i τ hτ => hinj i (φ τ) (hφJ τ hτ))
    (fun i j hij τ hτ x hx x' hx' => hdisj i j hij (φ τ) (hφJ τ hτ) x hx x' hx')
    ιs hιs ιt e he hhs hht hfs hft

end GC.LongTime.CuspP1
