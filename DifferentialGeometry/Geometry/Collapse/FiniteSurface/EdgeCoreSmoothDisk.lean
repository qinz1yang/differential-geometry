import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeModelCore
import DifferentialGeometry.Topology.Surface.Recognition.SublevelSmoothDisk

/-!
# LFR24: the core sublevel `D_s` is a smooth closed disk (binding of SF6)

Lane W4-F7c's kernel `EdgeModelCore.lean` proves every clause of LFR24 (blueprint master207A:26862)
except "`D_s` is a smooth compact disk", which the blueprint takes from Hirsch 9.3.7.  Lane SF-C's
`exists_smooth_disk_of_sublevel` replaces Hirsch: with LFR24's own hypotheses (`F` smooth on `U ⊇
{3/4 ≤ r ≤ 9}`, `|F - r| < μ ≤ 1/100`, a smooth outward field `V` on `U` with `dF(V) > 1/2` on
`2.1 ≤ r ≤ 8`), a compact ball `{r ≤ 7}`, and the topological disk structure of `D_s` (LFR23), the
sublevel `D_s` (`s ∈ [3,6]`) is the image of a smooth embedding of the closed unit disk, with boundary
circle the level `{F = s}`.  The regular band used is `[s, s + 1/10]`.
-/

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Surface DifferentialGeometry.Analysis

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [T2Space Z] [SigmaCompactSpace Z]

/-- **LFR24, the smooth disk.** Under LFR24's hypotheses, if the core sublevel `D_s`, `s ∈ [3,6]`, is
a topological closed disk with boundary circle `{F = s}`, it is a smooth closed disk with that
boundary circle. -/
theorem edgeCoreSublevel_smooth_disk (hE : Module.finrank ℝ E = 2) {r F : Z → ℝ} {μ : ℝ}
    (hF : Continuous F) {U : Set Z} (hU : IsOpen U) (hFU : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F U)
    (hA : ∀ x, 3 / 4 ≤ r x → r x ≤ 9 → x ∈ U) (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ)
    (hcpt : IsCompact {x | r x ≤ 7}) (V : (x : Z) → TangentSpace I x)
    (hVs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I Z)) U)
    (hV : ∀ x, 21 / 10 ≤ r x → r x ≤ 8 → 1 / 2 < mvfderiv (I := I) F x (V x))
    {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 6) {φ : Disk 2 → Z} (hφ : Continuous φ) (hφ' : Injective φ)
    (hrange : range φ = edgeCoreSublevel r F s) (hbd : φ '' diskSphere 2 = {x | F x = s}) :
    ∃ b : ClosedCell 2 → Z, Manifold.IsSmoothEmbedding (𝓡∂ 2) I ∞ b ∧
      range b = edgeCoreSublevel r F s ∧ range (b ∘ cellBoundaryInclusion 2) = {x | F x = s} := by
  obtain ⟨W, hWo, hW9, hhW⟩ := contMDiffOn_edgeModelCore (I := I) hF hU hFU hA hμ hFr
  have hh : Continuous (edgeModelCore F) := contDiff_edgeSublevelProfile.continuous.comp hF
  have hs2 : (2 : ℝ) < s := by linarith [hs.1]
  have hle : ∀ t : ℝ, 2 ≤ t → {x | edgeModelCore F x ≤ t} = {x | F x ≤ t} := fun t ht => by
    ext x
    exact edgeModelCore_le_iff ht
  have heq : {x | edgeModelCore F x = s} = {x | F x = s} := by
    ext x
    exact edgeModelCore_eq_iff hs2
  have hband : ∀ x, F x ∈ Icc s (s + 1 / 10) → 21 / 10 ≤ r x ∧ r x ≤ 8 := fun x hx => by
    have h := abs_lt.mp (hFr x)
    constructor <;> linarith [hx.1, hx.2, hs.1, hs.2]
  have hbandh : ∀ x, edgeModelCore F x ∈ Icc s (s + 1 / 10) → F x ∈ Icc s (s + 1 / 10) := by
    intro x hx
    refine ⟨?_, (edgeModelCore_le_iff (by linarith)).mp hx.2⟩
    by_contra hcon
    have hlt : F x < s := lt_of_not_ge hcon
    have h2 : edgeModelCore F x ≤ s := (edgeModelCore_le_iff hs2.le).mpr hlt.le
    have h4 : F x = s := (edgeModelCore_eq_iff hs2).mp (le_antisymm h2 hx.1)
    linarith
  have hsub : {x | edgeModelCore F x ≤ s + 1 / 10} ⊆ W := by
    rw [hle _ (by linarith)]
    intro x hx
    have h := abs_lt.mp (hFr x)
    exact hW9 (show r x ≤ 9 by change F x ≤ s + 1 / 10 at hx; linarith [hs.2])
  have hcpt' : IsCompact {x | edgeModelCore F x ≤ s + 1 / 10} := by
    rw [hle _ (by linarith)]
    refine hcpt.of_isClosed_subset (isClosed_le hF continuous_const) fun x hx => ?_
    have h := abs_lt.mp (hFr x)
    change F x ≤ s + 1 / 10 at hx
    change r x ≤ 7
    linarith [hs.2]
  have hKU : edgeModelCore F ⁻¹' Icc s (s + 1 / 10) ⊆ U := fun x hx => by
    obtain ⟨h1, h2⟩ := hband x (hbandh x hx)
    exact hA x (by linarith) (by linarith)
  have hpos : ∀ x ∈ edgeModelCore F ⁻¹' Icc s (s + 1 / 10),
      0 < mvfderiv (I := I) (edgeModelCore F) x (V x) := fun x hx => by
    obtain ⟨h1, h2⟩ := hband x (hbandh x hx)
    have := edgeModelCore_field hF hμ hFr V hV h1 h2
    linarith
  have hrange' : range φ = {x | edgeModelCore F x ≤ s} := by
    rw [hrange, edgeCoreSublevel_eq hμ hFr hs, hle s hs2.le]
  have hbd' : φ '' diskSphere 2 = {x | edgeModelCore F x = s} := by rw [hbd, heq]
  obtain ⟨b, hb, hbr, hbb⟩ := exists_smooth_disk_of_sublevel hE hh hWo hhW
    (by linarith : s < s + 1 / 10) hcpt' hsub hU hKU V hVs hpos hφ hφ' hrange' hbd'
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hbr, ← hrange', hrange]
  · rw [hbb, heq]

end DifferentialGeometry.Geometry.Collapse
