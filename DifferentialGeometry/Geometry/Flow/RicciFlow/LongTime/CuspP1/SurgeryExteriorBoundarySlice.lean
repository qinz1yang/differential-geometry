import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorBoundaryWindow

/-!
# CP1-D8 (G1, 3): slice facts for a boundary window
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

theorem sliceFacts_CPD8 {L : LateCutFamily F K slices}
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
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls) :
    (∀ i, ∀ u ∈ Ico L.cores.start c, ∀ x ∈ U i,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => (D i).z (u, y)) x)) ∧
    (∀ i, ∀ u ∈ Ico L.cores.start c,
      InjOn (fun y => (D i).z (u, y)) (range (E.truncation i).inclusion)) ∧
    (∀ i j, i ≠ j → ∀ u ∈ Ico L.cores.start c, ∀ x ∈ range (E.truncation i).inclusion,
      ∀ x' ∈ range (E.truncation j).inclusion, (D i).z (u, x) ≠ (D j).z (u, x')) := by
  classical
  let cores := L.cores
  let T := F.observation
  let Pd := (T.history N).backwardSurvivorDomain Fs Ls hFL
  let jj : ∀ u, u ∈ Ico cores.start c → Fin ((T.history N).eventCount + 1) := fun u hu =>
    (T.history N).activeStage ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  have hjj : ∀ u (hu : u ∈ Ico cores.start c), Fs ≤ jj u hu ∧ jj u hu ≤ Ls := fun u hu =>
    hst u (hJh u hu).1 (hJh u hu).2 hu
  let Φ : ∀ u (hu : u ∈ Ico cores.start c), Pd → ((T.history N).stage (jj u hu)).Carrier :=
    fun u hu =>
    (T.history N).backwardSurvivorMap Fs Ls hFL (jj u hu) (hjj u hu).1 (hjj u hu).2
  have hueq : ∀ u (hu : u ∈ Ico cores.start c), postStage T u = (T.history N).stage (jj u hu) :=
    fun u hu => postStage_eq_stage_active_CPD2 T N ⟨u, (hJh u hu).1, (hJh u hu).2⟩
  have hcast : ∀ i u (hu : u ∈ Ico cores.start c) (y : (cores.model i).Carrier),
      y ∈ U i → Φ u hu ((D i).z (u, y)) = carrierHomeo_CPD2 (hueq u hu) (cores.map i u hu.1 y) := by
    intro i u hu y hy
    exact (carrierHomeo_eq_of_heq_CPD2 (hueq u hu) _ _ ((D i).agrees u hu y hy).symm).symm
  have hΦsm : ∀ u (hu : u ∈ Ico cores.start c), ContMDiff (𝓡 3) (𝓡 3) ∞ (Φ u hu) := fun u hu =>
    contMDiff_survivorMap_CPD7 _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro i τ hτ x hx
    have hτ' : cores.start ≤ τ := hτ.1
    have hgat : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => (D i).z (τ, y)) x :=
      ((D i).slice_smooth hτ).contMDiffAt ((hUo i).mem_nhds hx)
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
      exact hcast i τ hτ y hy
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
  · intro i τ hτ x hx x' hx' h
    have hτ' : cores.start ≤ τ := hτ.1
    have h1 := hcast i τ hτ x (hSU i hx)
    have h2 := hcast i τ hτ x' (hSU i hx')
    have h12 : cores.map i τ hτ' x = cores.map i τ hτ' x' := by
      apply (carrierHomeo_CPD2 (hueq τ hτ)).injective
      rw [← h1, ← h2]
      exact congrArg (Φ τ hτ) h
    have hdx : x ∈ cores.domain i τ := hUd i τ hτ hτ' (hSU i hx)
    have hdx' : x' ∈ cores.domain i τ := hUd i τ hτ hτ' (hSU i hx')
    exact congrArg Subtype.val ((cores.embedding i τ hτ').isEmbedding.injective
      (a₁ := ⟨x, hdx⟩) (a₂ := ⟨x', hdx'⟩) h12)
  · intro i j hij τ hτ x hx x' hx' h
    have hτ' : cores.start ≤ τ := hτ.1
    have h1 := hcast i τ hτ x (hSU i hx)
    have h2 := hcast j τ hτ x' (hSU j hx')
    have h12 : cores.map i τ hτ' x = cores.map j τ hτ' x' := by
      apply (carrierHomeo_CPD2 (hueq τ hτ)).injective
      rw [← h1, ← h2]
      exact congrArg (Φ τ hτ) h
    exact Set.disjoint_left.mp (cores.disjoint τ hτ' hij) ⟨x, hUd i τ hτ hτ' (hSU i hx), rfl⟩
      (h12 ▸ ⟨x', hUd j τ hτ hτ' (hSU j hx'), rfl⟩)

end GC.LongTime.CuspP1
