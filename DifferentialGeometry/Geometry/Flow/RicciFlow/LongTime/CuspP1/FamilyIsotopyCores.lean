import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyMulti
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorIsotopy

/-!
# CP1-D5: the ambient homeomorphism of CP1-D4 from a smooth family of core embeddings

The hypothesis `hΦ` of `exists_regionHomeo_of_ambient_CPD4` is produced from a jointly smooth
family `Fam i : ℝ × (model i).Carrier → P` into a fixed smooth manifold `P` (in the tree: the
`backwardSurvivorDomain` of a `PersistentModelPatch`) which, composed with open embeddings of `P`
into the stages at times `s`, `t`, reproduces `cores.map i s`, `cores.map i t` on the retained
cores, provided the stage carriers are identified compatibly by a homeomorphism `e`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter Topology
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P₀ : OrientedThreeStage.{u}} {g : P₀.Metric} {F : GC.Interface.RawSurgery P₀ g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem exists_ambient_of_smooth_cores_CPD5 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t)
    {P : Type*} [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P]
    [IsManifold (𝓡 3) ∞ P] [T2Space P] [SigmaCompactSpace P]
    (Fam : ∀ i : Fin L.cores.count, ℝ × (L.cores.model i).Carrier → P)
    {J : Set ℝ} {U : ∀ i : Fin L.cores.count, Set (L.cores.model i).Carrier}
    (hJ : IsOpen J) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, range (E.truncation i).inclusion ⊆ U i) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J)
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Fam i) (J ×ˢ U i))
    (himm : ∀ i, ∀ τ ∈ J, ∀ x ∈ U i,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => Fam i (τ, y)) x))
    (hinj : ∀ i, ∀ τ ∈ J, InjOn (fun y => Fam i (τ, y)) (range (E.truncation i).inclusion))
    (hdisj : ∀ i j, i ≠ j → ∀ τ ∈ J, ∀ x ∈ range (E.truncation i).inclusion,
      ∀ x' ∈ range (E.truncation j).inclusion, Fam i (τ, x) ≠ Fam j (τ, x'))
    (ιs : P → (postStage F.observation s).Carrier) (hιs : IsOpenEmbedding ιs)
    (ιt : P → (postStage F.observation t).Carrier)
    (e : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier)
    (he : ∀ p, e (ιs p) = ιt p) (hs' : s ∈ Icc a b) (ht' : t ∈ Icc a b)
    (hfs : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c) =
        ιs (Fam i (s, (E.truncation i).inclusion c)))
    (hft : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) =
        ιt (Fam i (t, (E.truncation i).inclusion c))) :
    ∃ Φ : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier,
      ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
        Φ (L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c)) =
          L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) := by
  classical
  have hK : ∀ i, IsCompact (range (E.truncation i).inclusion) := fun i =>
    isCompact_range (E.truncation i).inclusion.continuous
  obtain ⟨Φ, hΦ⟩ := exists_ambient_homeo_of_smooth_families_CPD5 (I := 𝓡 3) hJ hU hK hKU hab hJab
    hF himm hinj hdisj hιs e he
    (fs := fun i x => ιs (Fam i (s, x)))
    (ft := fun i x => ιt (Fam i (t, x))) hs' ht' (fun i x _ => rfl) (fun i x _ => rfl)
  refine ⟨Φ, fun i c => ?_⟩
  rw [hfs i c, hft i c]
  exact hΦ i _ ⟨c, rfl⟩

/-- the full chain: smooth core family ⟹ exterior region homeomorphism carrying port loops -/
theorem exists_regionHomeo_of_smooth_cores_CPD5 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (s t : ℝ) (hs : E.start ≤ s) (ht : E.start ≤ t)
    {P : Type*} [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P]
    [IsManifold (𝓡 3) ∞ P] [T2Space P] [SigmaCompactSpace P]
    (Fam : ∀ i : Fin L.cores.count, ℝ × (L.cores.model i).Carrier → P)
    {J : Set ℝ} {U : ∀ i : Fin L.cores.count, Set (L.cores.model i).Carrier}
    (hJ : IsOpen J) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, range (E.truncation i).inclusion ⊆ U i) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J)
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Fam i) (J ×ˢ U i))
    (himm : ∀ i, ∀ τ ∈ J, ∀ x ∈ U i,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => Fam i (τ, y)) x))
    (hinj : ∀ i, ∀ τ ∈ J, InjOn (fun y => Fam i (τ, y)) (range (E.truncation i).inclusion))
    (hdisj : ∀ i j, i ≠ j → ∀ τ ∈ J, ∀ x ∈ range (E.truncation i).inclusion,
      ∀ x' ∈ range (E.truncation j).inclusion, Fam i (τ, x) ≠ Fam j (τ, x'))
    (ιs : P → (postStage F.observation s).Carrier) (hιs : IsOpenEmbedding ιs)
    (ιt : P → (postStage F.observation t).Carrier)
    (e : (postStage F.observation s).Carrier ≃ₜ (postStage F.observation t).Carrier)
    (he : ∀ p, e (ιs p) = ιt p) (hs' : s ∈ Icc a b) (ht' : t ∈ Icc a b)
    (hfs : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      L.cores.map i s (E.after_cores.trans hs) ((E.truncation i).inclusion c) =
        ιs (Fam i (s, (E.truncation i).inclusion c)))
    (hft : ∀ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) =
        ιt (Fam i (t, (E.truncation i).inclusion c))) :
    ∃ e : E.region s ≃ₜ E.region t, ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count)
      (z : Torus), e (portLoopRegionMap_CPD3 E i q s hs z) = portLoopRegionMap_CPD3 E i q t ht z := by
  obtain ⟨Φ, hΦ⟩ := exists_ambient_of_smooth_cores_CPD5 E s t hs ht Fam hJ hU hKU hab hJab hF himm
    hinj hdisj ιs hιs ιt e he hs' ht' hfs hft
  exact exists_regionHomeo_of_ambient_CPD4 E s t hs ht Φ hΦ

end GC.LongTime.CuspP1
