import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportBasic

/-!
# CP1-D4: exterior-region kernel constancy, reduction to ambient homeomorphisms / common retained regions

* `exists_regionHomeo_of_ambient_CPD4`: an ambient homeomorphism `Φ : stage s ≃ₜ stage t` carrying the
  core images of time `s` onto those of time `t` (pointwise, compatibly with the parametrisation)
  restricts to a homeomorphism `E.region s ≃ₜ E.region t` carrying `portLoopRegionMap s` to
  `portLoopRegionMap t`.
* `kernel_region_eq_of_ambient_CPD4`: hence equal `π₁` kernels.
* `hlocal_of_common_retained_CPD4`: `hlocal` of CP1-D3 from the Q5 form: locally in time, one
  actual retained region `C` with a torus map and `π₁`-injective maps to both sides.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter Topology
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem image_region_eq_of_ambient_CPD4 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t)
    (Φ : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier)
    (hΦ : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      Φ (L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c)) =
        L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c)) :
    Φ '' (E.region s) = E.region t := by
  unfold PersistentCuspExterior.region
  rw [dif_pos hs, dif_pos ht, Φ.image_compl, image_iUnion]
  congr 2
  funext i
  simp only [image_image, hΦ]

theorem exists_regionHomeo_of_ambient_CPD4 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t)
    (Φ : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier)
    (hΦ : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      Φ (L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c)) =
        L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c)) :
    ∃ e : E.region s ≃ₜ E.region t, ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count)
      (z : Torus), e (portLoopRegionMap_CPD3 E i q s hs z) = portLoopRegionMap_CPD3 E i q t ht z := by
  refine ⟨(Φ.image (E.region s)).trans (Homeomorph.setCongr (image_region_eq_of_ambient_CPD4 E s t hs ht Φ hΦ)),
    fun i q z => ?_⟩
  apply Subtype.ext
  change Φ (portLoopMap_CPH E i q s hs z : (postStage F.observation s).Carrier) =
    portLoopMap_CPH E i q t ht z
  simp only [portLoopMap_apply_CPH]
  rw [(E.truncation i).cusp_zero q z]
  exact hΦ i _

theorem kernel_region_eq_of_ambient_CPD4 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t)
    (Φ : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier)
    (hΦ : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      Φ (L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c)) =
        L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c))
    (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (x : Torus) :
    (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s hs) x).ker =
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q t ht) x).ker := by
  obtain ⟨e, he⟩ := exists_regionHomeo_of_ambient_CPD4 E s t hs ht Φ hΦ
  have : portLoopRegionMap_CPD3 E i q t ht =
      (e : C(E.region s, E.region t)).comp (portLoopRegionMap_CPD3 E i q s hs) :=
    ContinuousMap.ext fun z => (he i q z).symm
  rw [this, kernel_comp_homeomorph]

/-- `hlocal` of CP1-D3 from the Q5 form (D-CP1Q-5): locally in time, one actual retained region
`C` (a type, with a torus map `a`) with `π₁`-injective maps `jA`, `jB` into the exterior regions of
both times, factoring the cusp-torus maps.  The ambient-homeomorphism case is `C := E.region s`. -/
theorem hlocal_of_common_retained_CPD4 {L : LateCutFamily F K slices}
    (hret : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      ∀ᶠ s : Ici E.start in 𝓝 τ, ∃ (C : Type u) (_ : TopologicalSpace C) (a : C(Torus, C))
        (jA : C(C, E.region s.1)) (jB : C(C, E.region τ.1)),
        (∀ z, jA (a z) = portLoopRegionMap_CPD3 E i q s.1 s.2 z) ∧
        (∀ z, jB (a z) = portLoopRegionMap_CPD3 E i q τ.1 τ.2 z) ∧
        Function.Injective (FundamentalGroup.map jA (a x)) ∧
        Function.Injective (FundamentalGroup.map jB (a x))) :
    ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus),
      IsLocallyConstant (fun τ : Ici E.start =>
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker) := by
  intro E i q x
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ
  filter_upwards [hret E i q x τ] with s ⟨C, _, a, jA, jB, hA, hB, hjA, hjB⟩
  have hsA : portLoopRegionMap_CPD3 E i q s.1 s.2 = jA.comp a := ContinuousMap.ext fun z => (hA z).symm
  have hsB : portLoopRegionMap_CPD3 E i q τ.1 τ.2 = jB.comp a := ContinuousMap.ext fun z => (hB z).symm
  obtain ⟨h1, h2⟩ := kernel_common_core a jA jB x hjA hjB
  rw [hsA, hsB]
  exact h1.trans h2

end GC.LongTime.CuspP1
