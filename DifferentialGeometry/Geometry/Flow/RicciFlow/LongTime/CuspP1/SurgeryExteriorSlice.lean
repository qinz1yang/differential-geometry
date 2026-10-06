import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowMain

/-!
# CP1-D8 (G4a): ambient isotopy inside one stage from a smooth window

For a smooth window (D7) and two times `s ≤ t` in it, an ambient homeomorphism of the stage `j`
(any `j` in the stage range) moves `Φ_j (z_i (s, ·))` to `Φ_j (z_i (t, ·))` on the retained cores.
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

theorem exists_ambient_stage_CPD8 {L : LateCutFamily F K slices}
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
    (s t : ℝ) (hsJ : s ∈ J) (htJ : t ∈ J) (hst' : s ≤ t)
    (j : Fin ((F.observation.history N).eventCount + 1)) (hj1 : Fs ≤ j) (hj2 : j ≤ Ls) :
    ∃ Θ : ((F.observation.history N).stage j).Carrier ≃ₜ ((F.observation.history N).stage j).Carrier,
      ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
        Θ ((F.observation.history N).backwardSurvivorMap Fs Ls hFL j hj1 hj2
            ((D i).z (s, (E.truncation i).inclusion c))) =
          (F.observation.history N).backwardSurvivorMap Fs Ls hFL j hj1 hj2
            ((D i).z (t, (E.truncation i).inclusion c)) := by
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
  have hJab : Icc s t ⊆ J := hJord.out hsJ htJ
  have hK : ∀ i, IsCompact (range (E.truncation i).inclusion) := fun i =>
    isCompact_range (E.truncation i).inclusion.continuous
  have hΦj : Topology.IsOpenEmbedding
      ((T.history N).backwardSurvivorMap Fs Ls hFL j hj1 hj2) :=
    isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _
  obtain ⟨Θ, hΘ⟩ := exists_ambient_homeo_of_smooth_families_CPD5 (I := 𝓡 3) hJo hUo hK hSU hst'
    hJab (fun i => (D i).smooth) himm hinj hdisj hΦj (Homeomorph.refl _) (fun p => rfl)
    (fs := fun i y => (T.history N).backwardSurvivorMap Fs Ls hFL j hj1 hj2 ((D i).z (s, y)))
    (ft := fun i y => (T.history N).backwardSurvivorMap Fs Ls hFL j hj1 hj2 ((D i).z (t, y)))
    ⟨le_rfl, hst'⟩ ⟨hst', le_rfl⟩ (fun i y _ => rfl) (fun i y _ => rfl)
  exact ⟨Θ, fun i c => hΘ i _ ⟨c, rfl⟩⟩

end GC.LongTime.CuspP1
