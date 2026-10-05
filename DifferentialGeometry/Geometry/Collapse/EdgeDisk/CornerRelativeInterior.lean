import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# FDC03 at the horizontal faces: the relative interior of `M^edge` in a whole corner tube

Blueprint `master207B.tex`, FDC03 (B:7341–7344: "For a point of `M^edge` the relative interior in
(Last) is characterized by `T < 4Δ`") and draft 74 D74-14 (fourth layer: in the local model
`M₂ = {y ≥ 0}`, `int_{M₂}(M^edge) = {y ≥ 0, x < 0}` — "the points `x < 0, y = 0` of the horizontal
face are removed by the relative removal; the ambient interior gives the wrong remainder"). Lane
C14-EDP-FDCd's G2 proved the characterization at AMBIENT interior points of `M₂`
(`fdc03_relative_removal_C14Z_EFC`); here it is proved at EVERY point of a whole corner tube, the
horizontal face included, from the sign model of R1:

* `relInterior_edge_iff_of_cornerTube_EFC` (kernel): on an open `U` where a continuous, locally open
  `F = (x, y)` gives `M₂ = {y ≥ 0}` and `M^edge = {y ≥ 0, x ≤ 0}`, a point of `U` is in
  `int_{M₂} M^edge` iff `y ≥ 0` and `x < 0`, and in `M₃ = M₂ \ int_{M₂} M^edge` iff `x ≥ 0`,
  `y ≥ 0`;
* `fdc03_relInterior_of_wholeCornerTube_EFC`: the same on the WHOLE tube over an open base
  neighbourhood of the rim base point, from R1's inputs (`exists_whole_corner_tube74`) and an open
  circle map, with `x = T - level`, `y = h_F`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

open DifferentialGeometry.Topology

/-- **FDC03's relative interior in a corner model.** On an open `U` where `F = (x, y)` is continuous
and maps neighbourhoods of points of `U` onto neighbourhoods, with `M₂ = {y ≥ 0}` and
`M^edge = {y ≥ 0, x ≤ 0}` on `U`: for `p ∈ U`, `p ∈ int_{M₂} M^edge ↔ y(p) ≥ 0 ∧ x(p) < 0`, and
`p ∈ M₂ \ int_{M₂} M^edge ↔ x(p) ≥ 0 ∧ y(p) ≥ 0`. -/
theorem relInterior_edge_iff_of_cornerTube_EFC {Y : Type*} [TopologicalSpace Y]
    {M₂ Medge U : Set Y} (hU : IsOpen U) {F : Y → ℝ × ℝ} (hF : ContinuousOn F U)
    (hopen : ∀ p ∈ U, ∀ W ∈ 𝓝 p, F '' W ∈ 𝓝 (F p))
    (hM₂ : ∀ p ∈ U, p ∈ M₂ ↔ 0 ≤ (F p).2)
    (hE : ∀ p ∈ U, p ∈ Medge ↔ 0 ≤ (F p).2 ∧ (F p).1 ≤ 0) {p : Y} (hp : p ∈ U) :
    (p ∈ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
      0 ≤ (F p).2 ∧ (F p).1 < 0) ∧
    (p ∈ M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
      0 ≤ (F p).1 ∧ 0 ≤ (F p).2) := by
  have key : p ∈ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
      0 ≤ (F p).2 ∧ (F p).1 < 0 := by
    rw [mem_image_interior_preimage_val_iff]
    constructor
    · rintro ⟨hpM, O, hO, hpO, hOE⟩
      have hpE := (hE p hp).mp (hOE ⟨hpO, hpM⟩)
      refine ⟨hpE.1, lt_of_le_of_ne hpE.2 fun h0 => ?_⟩
      have hW : O ∩ U ∈ 𝓝 p := (hO.inter hU).mem_nhds ⟨hpO, hp⟩
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen p hp _ hW)
      have hv : ((F p).1 + r / 2, (F p).2) ∈ Metric.ball (F p) r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          add_sub_cancel_left, abs_of_pos (half_pos hr)]
        exact max_lt (half_lt_self hr) hr
      obtain ⟨q, ⟨hqO, hqU⟩, hqF⟩ := hball hv
      have hqM : q ∈ M₂ := by
        rw [hM₂ q hqU, hqF]
        exact hpE.1
      have hqE := (hE q hqU).mp (hOE ⟨hqO, hqM⟩)
      rw [hqF, ← h0] at hqE
      have := hqE.2
      simp only at this
      linarith
    · rintro ⟨hy, hx⟩
      refine ⟨(hM₂ p hp).mpr hy, U ∩ F ⁻¹' {v | v.1 < 0},
        hF.isOpen_inter_preimage hU (isOpen_lt continuous_fst continuous_const), ⟨hp, hx⟩, ?_⟩
      rintro q ⟨⟨hqU, hqx⟩, hqM⟩
      exact (hE q hqU).mpr ⟨(hM₂ q hqU).mp hqM, le_of_lt hqx⟩
  refine ⟨key, ?_⟩
  rw [Set.mem_sdiff, key, hM₂ p hp]
  constructor
  · rintro ⟨hy, hn⟩
    refine ⟨?_, hy⟩
    by_contra hneg
    exact hn ⟨hy, lt_of_not_ge hneg⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hy, fun h => absurd h.2 (not_lt.mpr hx)⟩

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- **FDC03 on the whole corner tube** (R1 + an open circle map): with R1's inputs (`f` continuous,
closed and open; descent of `(T, h)` over `V ∋ c₀`; centre values zero; rank two at a point of the
centre fibre; an open `N ⊇ f⁻¹(c₀)` on which `M₂ = {h ≥ 0}` and `M^edge = {h ≥ 0, T ≤ 0}`), there is
an open `U ∋ c₀` such that on the WHOLE tube `f⁻¹(U)`: `p ∈ int_{M₂} M^edge ↔ h(p) ≥ 0 ∧ T(p) < 0`
and `p ∈ M₃ = M₂ \ int_{M₂} M^edge ↔ T(p) ≥ 0 ∧ h(p) ≥ 0`. -/
theorem fdc03_relInterior_of_wholeCornerTube_EFC (hEB : Module.finrank ℝ EB = 2) {f : Y → B}
    (hfc : Continuous f) (hfcl : IsClosedMap f) (hfo : IsOpenMap f) {c₀ : B} {T h : Y → ℝ}
    {V : TopologicalSpace.Opens B} (hc₀ : c₀ ∈ V) {Tb hb : B → ℝ}
    (hTb : ContMDiffOn IB 𝓘(ℝ) ∞ Tb V) (hhb : ContMDiffOn IB 𝓘(ℝ) ∞ hb V)
    (hdesc : ∀ y, f y ∈ V → T y = Tb (f y) ∧ h y = hb (f y)) (hcen : Tb c₀ = 0 ∧ hb c₀ = 0)
    {x₀ : Y} (hx₀ : f x₀ = c₀) (hf : MDifferentiableAt I IB f x₀)
    (hrank : Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, h z)) x₀))
    {N : Set Y} (hN : IsOpen N) (hfib : f ⁻¹' {c₀} ⊆ N) {M₂ Medge : Set Y}
    (hsign : ∀ y ∈ N, (y ∈ M₂ ↔ 0 ≤ h y) ∧ (y ∈ Medge ↔ 0 ≤ h y ∧ T y ≤ 0)) :
    ∃ U : Set B, IsOpen U ∧ c₀ ∈ U ∧ ∀ p, f p ∈ U →
      (p ∈ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔ 0 ≤ h p ∧ T p < 0) ∧
      (p ∈ M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
        0 ≤ T p ∧ 0 ≤ h p) := by
  obtain ⟨Φ, hc₀Φ, -, -, htube, hcoord, hside⟩ := exists_whole_corner_tube74 hEB hfc hfcl hc₀
    hTb hhb hdesc hcen hx₀ hf hrank hN hfib (Vtx := {y | h y ≤ 0}) (Edg := Medge)
    (Reg := {y | 0 ≤ T y ∧ 0 ≤ h y}) (fun y hy => ⟨Iff.rfl, (hsign y hy).2, Iff.rfl⟩)
  refine ⟨Φ.source, Φ.open_source, hc₀Φ, fun p hp => ?_⟩
  let U' : Set Y := f ⁻¹' Φ.source
  have hU' : IsOpen U' := Φ.open_source.preimage hfc
  have hFc : ContinuousOn (fun y => Φ (f y)) U' :=
    Φ.contMDiffOn.continuousOn.comp hfc.continuousOn (fun y hy => hy)
  have hopen : ∀ q ∈ U', ∀ W ∈ 𝓝 q, (fun y => Φ (f y)) '' W ∈ 𝓝 (Φ (f q)) := by
    intro q hq W hW
    have h1 : f '' (W ∩ U') ∈ 𝓝 (f q) :=
      hfo.image_mem_nhds (inter_mem hW (hU'.mem_nhds hq))
    have h2 : f '' (W ∩ U') ∩ Φ.source ∈ 𝓝 (f q) := inter_mem h1 (Φ.open_source.mem_nhds hq)
    have h3 := Φ.toOpenPartialHomeomorph.image_mem_nhds hq h2
    refine Filter.mem_of_superset h3 ?_
    rintro _ ⟨c, ⟨⟨y, ⟨hyW, -⟩, rfl⟩, -⟩, rfl⟩
    exact ⟨y, hyW, rfl⟩
  have hM₂' : ∀ q ∈ U', q ∈ M₂ ↔ 0 ≤ (Φ (f q)).2 := by
    intro q hq
    rw [(hcoord q hq).2]
    exact (hsign q (htube hq)).1
  have hE' : ∀ q ∈ U', q ∈ Medge ↔ 0 ≤ (Φ (f q)).2 ∧ (Φ (f q)).1 ≤ 0 := by
    intro q hq
    exact (hside q hq).2.1
  have hres := relInterior_edge_iff_of_cornerTube_EFC hU' hFc hopen hM₂' hE' hp
  rw [(hcoord p hp).1, (hcoord p hp).2] at hres
  exact hres

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
