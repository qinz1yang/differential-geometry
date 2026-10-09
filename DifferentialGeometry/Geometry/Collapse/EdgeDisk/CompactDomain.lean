import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FibreSaturation
import DifferentialGeometry.Topology.Ehresmann.WholeDiskTransport

/-!
# E1: the compact edge base `C₂` with its descended face functions (EDP05 / FDC02)

Package E1 of draft 74 (`edgeCompactDomain_of_actual_faces74`, disposition D74-11 / D74-17): "E0 +
EDP05 descent + FDC02 compactness". Blueprint `master207B.tex`, EDP05 (B:7040–7090: "`M₂ ∩ X₂ =
f₂⁻¹(C₂)` is saturated ... A disk fiber meeting a zero boundary lies there ... Connectedness of the
disk then implies saturation"; "Near a horizontal face, an ambient defining function for `M₂`
descends to a smooth function `b` on the edge base ... The ambient defining differential for `M₂` is
nonzero. Since it is `D(b ∘ f₂)`, one has `db ≠ 0` on the one-dimensional base, and `C₂ = {b ≥ 0}`
locally") and FDC02 (B:7246–7283: "`M^edge = M₂ ∩ X₂` is compact ... Its continuous image `C₂` is
compact; EDP05 already identifies its smooth domain structure and every boundary point").

Abstract kernel on an ambient manifold `Y` (model `I`), an open source `O`, a projection
`proj : O → B` to a base manifold `B` (model `IB`), a height and a level `L`; the whole fibres are
`D(c) = {x ∈ O | proj x = c, height x ≤ L}`, the edge piece is `M₂ ∩ {height ≤ L}` and
`C₂ = proj(M₂ ∩ {height ≤ L})`.

* `edgePiece_saturated_EFC`: preconnected whole fibres (E0: each is a disk) and "a whole fibre
  meeting `∂M₂` lies in `M₂`" ((RF) / ZSP03 / GAF07) give `M₂ ∩ X₂ = proj⁻¹(C₂) ∩ X₂`.
* `isCompact_edgeBase_EFC`: FDC02's compact edge piece has compact base `C₂`.
* `edgeBase_inter_eq_of_descent_EFC`, `descent_zero_of_mem_frontier_EFC`: the descended defining
  identity `x ∈ M₂ ↔ b(proj x) ≥ 0` over a base patch `U` with nonempty fibres gives
  `C₂ ∩ U = {b ≥ 0}`, and `b = 0` at frontier points of `C₂`.
* `mfderiv_ne_zero_of_descent_EFC`: `db ≠ 0` from an ambient defining function `F` with `dF ≠ 0` and
  `F = b ∘ proj` near a point (EDP05's "Since it is `D(b ∘ f₂)`, `db ≠ 0`").
* **`edgeCompactDomain_of_actual_faces74`** (E1 head): E0's disks + the face condition + FDC02's
  compactness + EDP05's descent at every frontier point of `C₂` give: `C₂` compact, `M₂ ∩ X₂`
  saturated over `C₂`, and at every frontier point of `C₂` a smooth local defining function with
  nonzero differential, `C₂ = {φ ≥ 0}` locally — exactly `EdgeBundle.cbase_compact` /
  `cbase_domain` (FC39P0Base) and the `edgePiece` identity.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

open DifferentialGeometry.Topology

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]

omit [ChartedSpace H Y] [TopologicalSpace B] [ChartedSpace HB B] in
/-- **EDP05's saturation of the edge piece**: if every whole fibre `D(c)` is preconnected and every
whole fibre meeting `∂M₂` lies in `M₂`, then `M₂ ∩ X₂ = proj⁻¹(C₂) ∩ X₂`. -/
theorem edgePiece_saturated_EFC (O : Set Y) (proj : O → B) (height : O → ℝ) (L : ℝ)
    (M₂ : Set Y)
    (hconn : ∀ c, IsPreconnected (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L}))
    (hface : ∀ c, (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L} ∩ frontier M₂).Nonempty →
      Subtype.val '' {x : O | proj x = c ∧ height x ≤ L} ⊆ M₂) :
    M₂ ∩ Subtype.val '' {x : O | height x ≤ L} =
      Subtype.val '' {x : O | proj x ∈ proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L} ∧
        height x ≤ L} := by
  apply Subset.antisymm
  · rintro _ ⟨hM, x, hx, rfl⟩
    exact ⟨x, ⟨⟨x, ⟨hM, hx⟩, rfl⟩, hx⟩, rfl⟩
  · rintro _ ⟨x, ⟨⟨x', ⟨hM', hx'⟩, hpx⟩, hx⟩, rfl⟩
    refine ⟨?_, x, hx, rfl⟩
    have hxD : (x : Y) ∈ Subtype.val '' {z : O | proj z = proj x ∧ height z ≤ L} :=
      ⟨x, ⟨rfl, hx⟩, rfl⟩
    have hx'D : (x' : Y) ∈ Subtype.val '' {z : O | proj z = proj x ∧ height z ≤ L} :=
      ⟨x', ⟨hpx, hx'⟩, rfl⟩
    by_cases hmeet : (Subtype.val '' {z : O | proj z = proj x ∧ height z ≤ L} ∩
        frontier M₂).Nonempty
    · exact hface (proj x) hmeet hxD
    · have hdisj : Disjoint (Subtype.val '' {z : O | proj z = proj x ∧ height z ≤ L})
          (frontier M₂) := disjoint_left.mpr fun z hz hzF => hmeet ⟨z, hz, hzF⟩
      rcases isPreconnected_subset_interior_or_subset_compl_closure (hconn (proj x)) hdisj
        with h | h
      · exact interior_subset (h hxD)
      · exact absurd (subset_closure hM') (h hx'D)

omit [ChartedSpace H Y] [ChartedSpace HB B] in
/-- **FDC02's compact base**: a compact edge piece `M₂ ∩ X₂` has compact base `C₂`. -/
theorem isCompact_edgeBase_EFC (O : Set Y) {proj : O → B} (hproj : Continuous proj)
    (height : O → ℝ) (L : ℝ) (M₂ : Set Y)
    (hcpt : IsCompact (M₂ ∩ Subtype.val '' {x : O | height x ≤ L})) :
    IsCompact (proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L}) := by
  have hsub : M₂ ∩ Subtype.val '' {x : O | height x ≤ L} ⊆ range (Subtype.val : O → Y) :=
    fun _ ⟨_, x, _, hx⟩ => ⟨x, hx⟩
  have hpre : IsCompact (Subtype.val ⁻¹' (M₂ ∩ Subtype.val '' {x : O | height x ≤ L}) : Set O) :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).mpr hcpt
  have heq : (Subtype.val ⁻¹' (M₂ ∩ Subtype.val '' {x : O | height x ≤ L}) : Set O) =
      {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L} := by
    ext x
    constructor
    · rintro ⟨hM, z, hz, hzx⟩
      exact ⟨hM, (Subtype.ext hzx : z = x) ▸ hz⟩
    · rintro ⟨hM, hx⟩
      exact ⟨hM, x, hx, rfl⟩
  rw [← heq]
  exact hpre.image hproj

omit [TopologicalSpace Y] [ChartedSpace H Y] [TopologicalSpace B] [ChartedSpace HB B] in
/-- **EDP05's local base equation**: over a base patch `U` on which every point with `b ≥ 0` has a
nonempty whole fibre and the descended defining identity `x ∈ M₂ ↔ b(proj x) ≥ 0` holds on `X₂`,
`C₂ ∩ U = {b ≥ 0} ∩ U`. -/
theorem edgeBase_inter_eq_of_descent_EFC (O : Set Y) (proj : O → B) (height : O → ℝ) (L : ℝ)
    (M₂ : Set Y) (U : Set B) (b : B → ℝ)
    (hne : ∀ c ∈ U, 0 ≤ b c → (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L}).Nonempty)
    (hdef : ∀ x : O, proj x ∈ U → height x ≤ L → ((x : Y) ∈ M₂ ↔ 0 ≤ b (proj x))) :
    proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L} ∩ U = {c | c ∈ U ∧ 0 ≤ b c} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, ⟨hM, hx⟩, rfl⟩, hU⟩
    exact ⟨hU, (hdef x hU hx).mp hM⟩
  · rintro c ⟨hU, hb⟩
    obtain ⟨_, ⟨x, ⟨hxc, hx⟩, rfl⟩⟩ := hne c hU hb
    refine ⟨⟨x, ⟨(hdef x (hxc ▸ hU) hx).mpr (hxc ▸ hb), hx⟩, hxc⟩, hU⟩

omit [ChartedSpace H Y] in
/-- **The descended function vanishes at the frontier of `C₂`**: with `C₂ ∩ U = {b ≥ 0} ∩ U` on an
open `U` where `b` is continuous, `b(c₀) = 0` at every `c₀ ∈ U ∩ frontier C₂`. -/
theorem descent_zero_of_mem_frontier_EFC {C₂ : Set B} {U : Set B} (hU : IsOpen U) {b : B → ℝ}
    (hb : ContinuousOn b U) (heq : C₂ ∩ U = {c | c ∈ U ∧ 0 ≤ b c}) {c₀ : B} (hc₀U : c₀ ∈ U)
    (hc₀ : c₀ ∈ frontier C₂) : b c₀ = 0 := by
  have hcont : ContinuousAt b c₀ := hb.continuousAt (hU.mem_nhds hc₀U)
  apply le_antisymm
  · by_contra hpos
    push Not at hpos
    have hU' : ∀ᶠ c in 𝓝 c₀, c ∈ U := hU.mem_nhds hc₀U
    have hev : ∀ᶠ c in 𝓝 c₀, c ∈ U ∧ 0 < b c := hU'.and (hcont.eventually (lt_mem_nhds hpos))
    have hint : c₀ ∈ interior C₂ := by
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [hev] with c hc
      have : c ∈ C₂ ∩ U := by rw [heq]; exact ⟨hc.1, hc.2.le⟩
      exact this.1
    exact hc₀.2 hint
  · by_contra hneg
    push Not at hneg
    have hU' : ∀ᶠ c in 𝓝 c₀, c ∈ U := hU.mem_nhds hc₀U
    have hev : ∀ᶠ c in 𝓝 c₀, c ∈ U ∧ b c < 0 := hU'.and (hcont.eventually (gt_mem_nhds hneg))
    have hcl := hc₀.1
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨c, hc, hcC⟩ := hcl _ hev
    have : c ∈ C₂ ∩ U := ⟨hcC, hc.1⟩
    rw [heq] at this
    exact absurd this.2 (not_le.mpr hc.2)

/-- **EDP05's `db ≠ 0`**: if an ambient function `F` with `dF(x) ≠ 0` agrees near `x ∈ O` with
`b ∘ proj` (`b` differentiable at `proj x`, `proj` differentiable at `x`), then `db(proj x) ≠ 0`. -/
theorem mfderiv_ne_zero_of_descent_EFC (O : TopologicalSpace.Opens Y)
    {proj : O → B} (x : O) (hp : MDifferentiableAt I IB proj x) {b : B → ℝ}
    (hb : MDifferentiableAt IB 𝓘(ℝ) b (proj x)) {F : Y → ℝ}
    (hF : MDifferentiableAt I 𝓘(ℝ) F x) (hFne : mfderiv I 𝓘(ℝ) F x ≠ 0)
    (heq : (fun z : O => F z) =ᶠ[𝓝 x] b ∘ proj) :
    mfderiv IB 𝓘(ℝ) b (proj x) ≠ 0 := by
  intro hzero
  apply hFne
  rw [← DifferentialGeometry.Topology.Ehresmann.mfderiv_restrict_opens_EFC O F x hF,
    heq.mfderiv_eq, mfderiv_comp x hb hp, hzero, ContinuousLinearMap.zero_comp]
  ext v
  rfl

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc

/-- **E1 (`edgeCompactDomain_of_actual_faces74`): the compact edge base and its faces.** On an open
source `O` of `Y` with a smooth projection `proj : O → B`, a height and a level `L`:
* (E0) every whole fibre `D(c) = {x ∈ O | proj x = c, height x ≤ L}` is the image of a continuous
  map from `ClosedCell 2` (e.g. E0's smooth disk);
* ((RF) / ZSP03 / GAF07) a whole fibre meeting `∂M₂` lies in `M₂`;
* (FDC02) the edge piece `M₂ ∩ {height ≤ L}` is compact;
* (EDP05 descent) at every frontier point `c₀` of `C₂ = proj(M₂ ∩ {height ≤ L})`: a base patch
  `U ∋ c₀` and `b` smooth on `U` with `x ∈ M₂ ↔ b(proj x) ≥ 0` on `proj⁻¹(U) ∩ {height ≤ L}`, and an
  ambient function `F` with `dF ≠ 0` agreeing with `b ∘ proj` near a point of the fibre over `c₀`.
Then `C₂` is compact, the edge piece is the whole preimage of `C₂` below `L`, and every frontier
point of `C₂` has a smooth local defining function `φ` with `φ(c₀) = 0`, `dφ(c₀) ≠ 0` and
`C₂ ∩ U = {φ ≥ 0} ∩ U` (`EdgeBundle.cbase_compact`, `cbase_domain`). -/
theorem edgeCompactDomain_of_actual_faces74 (O : TopologicalSpace.Opens Y)
    (proj : O → B) (hproj : ContMDiff I IB ∞ proj) (height : O → ℝ) (L : ℝ) (M₂ : Set Y)
    (hdisk : ∀ c, ∃ φ : ClosedCell 2 → Y, Continuous φ ∧
      range φ = Subtype.val '' {x : O | proj x = c ∧ height x ≤ L})
    (hface : ∀ c, (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L} ∩ frontier M₂).Nonempty →
      Subtype.val '' {x : O | proj x = c ∧ height x ≤ L} ⊆ M₂)
    (hcpt : IsCompact (M₂ ∩ Subtype.val '' {x : O | height x ≤ L}))
    (hdesc : ∀ c₀ ∈ frontier (proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L}),
      ∃ U : TopologicalSpace.Opens B, c₀ ∈ U ∧ ∃ b : B → ℝ, ContMDiffOn IB 𝓘(ℝ) ∞ b U ∧
        (∀ x : O, proj x ∈ U → height x ≤ L → ((x : Y) ∈ M₂ ↔ 0 ≤ b (proj x))) ∧
        ∃ x : O, proj x = c₀ ∧ ∃ F : Y → ℝ, MDifferentiableAt I 𝓘(ℝ) F x ∧
          mfderiv I 𝓘(ℝ) F x ≠ 0 ∧ (fun z : O => F z) =ᶠ[𝓝 x] b ∘ proj) :
    IsCompact (proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L}) ∧
      M₂ ∩ Subtype.val '' {x : O | height x ≤ L} =
        Subtype.val '' {x : O | proj x ∈ proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L} ∧
          height x ≤ L} ∧
      ∀ c₀ ∈ frontier (proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L}),
        ∃ U : TopologicalSpace.Opens B, c₀ ∈ U ∧ ∃ φ : B → ℝ, ContMDiffOn IB 𝓘(ℝ) ∞ φ U ∧
          φ c₀ = 0 ∧ mfderiv IB 𝓘(ℝ) φ c₀ ≠ 0 ∧
          proj '' {x : O | (x : Y) ∈ M₂ ∧ height x ≤ L} ∩ U = {c | c ∈ U ∧ 0 ≤ φ c} := by
  have hconn : ∀ c, IsPreconnected (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L}) := by
    intro c
    obtain ⟨φ, hφ, hr⟩ := hdisk c
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
    let _ : PreconnectedSpace (ClosedCell 2) := Subtype.preconnectedSpace hconv.isPreconnected
    rw [← hr]
    exact isPreconnected_range hφ
  have hne : ∀ c, (Subtype.val '' {x : O | proj x = c ∧ height x ≤ L}).Nonempty := by
    intro c
    obtain ⟨φ, -, hr⟩ := hdisk c
    rw [← hr]
    exact ⟨φ ⟨0, by simp⟩, mem_range_self _⟩
  refine ⟨isCompact_edgeBase_EFC (O : Set Y) hproj.continuous height L M₂ hcpt,
    edgePiece_saturated_EFC (O : Set Y) proj height L M₂ hconn hface, ?_⟩
  intro c₀ hc₀
  obtain ⟨U, hc₀U, b, hb, hdef, x, hx, F, hF, hFne, heq⟩ := hdesc c₀ hc₀
  have hinter := edgeBase_inter_eq_of_descent_EFC (O : Set Y) proj height L M₂ U b
    (fun c _ _ => hne c) hdef
  have hbd : MDifferentiableAt IB 𝓘(ℝ) b (proj x) := by
    rw [hx]
    exact ((hb c₀ hc₀U).contMDiffAt (U.isOpen.mem_nhds hc₀U)).mdifferentiableAt (by simp)
  have hpd : MDifferentiableAt I IB proj x := (hproj x).mdifferentiableAt (by simp)
  have hdb := mfderiv_ne_zero_of_descent_EFC O x hpd hbd hF hFne heq
  rw [hx] at hdb
  exact ⟨U, hc₀U, b, hb,
    descent_zero_of_mem_frontier_EFC U.isOpen hb.continuousOn hinter hc₀U hc₀, hdb, hinter⟩

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
