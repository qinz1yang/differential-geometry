import Mathlib.Geometry.Manifold.Immersion
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice
import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceImmersion
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# E3 kernel, part 1: regular sublevels with boundary inside a boundaryless manifold are embedded
# disks / surfaces, and the boundary of an embedded copy is `{B = 0}` (lane S-EDGE-INT2)

Draft 74, package E3. For a boundaryless ambient manifold `M` (model `𝓘(ℝ, E)`), smooth
`Ψ : M → G`, `B : M → ℝ` with `dΨ` onto on `{Ψ = 0, 0 ≤ B}` and `d(Ψ, B)` onto on `{Ψ = 0, B = 0}`,
the regular sublevel `N = {Ψ = 0, 0 ≤ B}` (`regularSublevelChartedSpace`, model `𝓡∂ (d + 1)`) is
a smooth submanifold with boundary:

* `regularSublevel_isSmoothEmbedding_val_EIM`: the inclusion `N → M` is a smooth embedding (in the
  tree only the slices avoiding the boundary `{B = 0}` and the ambient-with-boundary variant
  were available; here a slice chart of height `c` with positive first coordinate is
  restricted around the point, `slice_isImmersionAtOfComplement_val_GARC`);
* `isBoundaryPoint_iff_of_range_eq_regularSublevel_EIM`: a smooth embedding `D` of a manifold `X`
  modelled on `𝓡∂ (d + 1)` into `M` whose range is exactly `N` has
  `(𝓡∂ (d + 1)).IsBoundaryPoint x ↔ B (D x) = 0` (`IsSmoothEmbedding.diffeomorphOfRangeEq` and the
  invariance of boundary points under a diffeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Manifold.RegularLevel

namespace GC.GraphManifold.Assembly.FC39P0

section Sublevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {d : ℕ}

/-- **Immersion at a point from a slice chart with positive first coordinate at the point**: the
chart is restricted to the open set where its first coordinate is positive. -/
theorem regularSublevel_isImmersionAt_of_chart_EIM
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    {B : M → ℝ} (hB : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))
    (x : {x : M // Ψ x = 0 ∧ 0 ≤ B x})
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) M
      (EuclideanHalfSpace (d + 1) × G) ∞)
    {c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ y ∈ Φ.source, (Ψ y = 0 ∧ 0 ≤ B y) ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (hx : x.1 ∈ Φ.source) (hxpos : 0 < (Φ x.1).1.1 0) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    IsImmersionAtOfComplement G (𝓡∂ (d + 1)) 𝓘(ℝ, E) ∞
      (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  let L : (EuclideanSpace ℝ (Fin (d + 1)) × G) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (by rw [Module.finrank_prod, finrank_euclideanSpace_fin, hdim])
  have hcoord : Continuous fun q : EuclideanHalfSpace (d + 1) × G => q.1.1 0 := by fun_prop
  have hopen : IsOpen (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) :=
    Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source
      (isOpen_lt continuous_const hcoord)
  let Φ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ
    (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) hopen
  have hsrc : Φ'.source = Φ.source ∩ (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) := rfl
  exact slice_isImmersionAtOfComplement_val_GARC (fun x => Ψ x = 0 ∧ 0 ≤ B x) (fun x => B x = 0)
    (regularSublevel_sliceCharts hdim hΨ hB hreg hregb) L x Φ' hc
    (fun y hy => hΦ y (by rw [hsrc] at hy; exact hy.1))
    (by rw [hsrc]; exact ⟨hx, hx, hxpos⟩)
    (fun y hy => by rw [hsrc] at hy; exact hy.2.2)

/-- **The inclusion of a regular sublevel with boundary is a smooth embedding** into a boundaryless
manifold. -/
theorem regularSublevel_isSmoothEmbedding_val_EIM
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    {B : M → ℝ} (hB : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x)) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, E) ∞
      (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  refine ⟨IsImmersionOfComplement.isImmersion (F := G) (fun x => ?_),
    Topology.IsEmbedding.subtypeVal⟩
  have hint : (𝓘(ℝ, E)).IsInteriorPoint x.1 := BoundarylessManifold.isInteriorPoint
  rcases x.2.2.eq_or_lt with h0 | hpos
  · obtain ⟨Φ, hxΦ, hΦ1, hΦ⟩ := exists_sliceChart_of_zero hdim hΨ hB hint h0.symm
      (hregb x.1 x.2.1 h0.symm)
    exact regularSublevel_isImmersionAt_of_chart_EIM hdim hΨ hB hreg hregb x Φ zero_le_one hΦ
      hxΦ (by rw [hΦ1]; exact one_pos)
  · obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos hdim hΨ hB hint hpos
      (hreg x.1 x.2.1 x.2.2)
    exact regularSublevel_isImmersionAt_of_chart_EIM hdim hΨ hB hreg hregb x Φ le_rfl hΦ hxΦ
      (hΦpos x.1 hxΦ)

/-- **The boundary of an embedded copy of a regular sublevel** (a smooth embedding `D` of a
manifold `X` modelled on `𝓡∂ (d + 1)` onto the sublevel `{Ψ = 0, 0 ≤ B}`): the boundary points of
`X` are exactly the points over `{B = 0}`. -/
theorem isBoundaryPoint_iff_of_range_eq_regularSublevel_EIM
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    {B : M → ℝ} (hB : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace (d + 1)) X]
    {D : X → M}
    (hD : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, E) ∞ D)
    (hDr : range D = {y | Ψ y = 0 ∧ 0 ≤ B y}) {x : X} :
    (𝓡∂ (d + 1)).IsBoundaryPoint x ↔ B (D x) = 0 := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  have _ := regularSublevel_isManifold hdim hΨ hB hreg hregb
  have hs := regularSublevel_isSmoothEmbedding_val_EIM hdim hΨ hB hreg hregb
  have hr : range D = range (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) := by
    rw [hDr, Subtype.range_coe_subtype]
  let e := hD.diffeomorphOfRangeEq hs hr
  have hDx : D x = (e x).1 := (hD.comp_diffeomorphOfRangeEq hs hr x).symm
  rw [((e.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)),
    regularSublevel_isBoundaryPoint_iff hdim hΨ hB hreg hregb, hDx]

end Sublevel

end GC.GraphManifold.Assembly.FC39P0
