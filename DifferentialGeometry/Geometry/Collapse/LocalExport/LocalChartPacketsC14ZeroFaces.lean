import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypesApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceTypes

/-!
# The original zero faces of the complete closed family (ZSP02 / ZSP03 / ZSP05, original part)

Lane C14-ZSP35. Blueprint `master207B.tex`: ZSP02 (B:6374, "Every nonempty boundary is a connected
`S²` or `T²`. Empty-boundary cases retain their original compact types"), ZSP03 (B:6481, the zero
faces and the regularity of the original coordinate near them) and ZSP05 (B:6597, "A closed
connected zero … component, if present, is the entire connected carrier"), on the ORIGINAL radial
sublevels `{η_c ≤ a}`, `a ∈ [1/5, 2]`, of `LocalChartPacketsC14Z` (field `zero_sublevel_types`,
review 53 §4.1). The adjusted domains `Z_i` and their faces `E⁻¹{v ≥ .9R, u = .4v}` need ZSP01's
stage half (class (c)); here only the family's own fields are used.

* `LocalChartPacketsC14Z.zero_face_type_ZSP35`: the face `{η_c = a}` is empty with
  `{η_c ≤ a} = univ`, or homeomorphic to the round `S²`, or homeomorphic to `ℝ²/ℤ²`;
* `LocalChartPacketsC14Z.zero_face_empty_iff_ZSP35`: `{η_c = a} = ∅ ↔ {η_c ≤ a} = univ` (ZSP05: a
  zero piece without face is the whole carrier);
* `LocalChartPacketsC14Z.zero_face_connected_ZSP35`: a nonempty face is compact, connected and
  `≃ₜ S²` or `≃ₜ ℝ²/ℤ²`;
* `LocalChartPacketsC14Z.zero_face_regular_ZSP35`: the open band `{1/5 < η_c < 2}` contains the
  face, `η_c` is smooth there with nonzero gradient (for `r_c⁻² g`) and the original annular cutoff
  is `1` on `{3/10 ≤ η_c ≤ 4/5}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The type of an original zero face.** For every zero centre `c` and `a ∈ [1/5, 2]`, the face
`{η_c = a}` is empty and `{η_c ≤ a}` is the whole source (compact model), or it is homeomorphic to
the round `S²` (`D³`, `ℝP³ ∖ int D³`), or to `ℝ²/ℤ²` (`S¹ × D²`, `D(o(K))`). -/
theorem LocalChartPacketsC14Z.zero_face_type_ZSP35
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    ({x | (P.zero.zero c hc).radial x ≤ a} = univ ∧ {x | (P.zero.zero c hc).radial x = a} = ∅) ∨
    Nonempty ({x | (P.zero.zero c hc).radial x = a} ≃ₜ Metric.sphere (0 : E3) 1) ∨
    Nonempty ({x | (P.zero.zero c hc).radial x = a} ≃ₜ
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  have hfr := (P.zero_sublevel_regular_FAMZ hc ha).1
  rcases zero_sublevel_frontier_type_ZSP35 (P.isClosed_zero_sublevel_FAMZ hc a)
      (P.zero_sublevel_types c hc a ha) with ⟨hu, he⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨hu, hfr ▸ he⟩
  · exact Or.inr (Or.inl ⟨(Homeomorph.setCongr hfr.symm).trans e⟩)
  · exact Or.inr (Or.inr ⟨(Homeomorph.setCongr hfr.symm).trans e⟩)

/-- **A zero piece without face is the whole carrier** (ZSP05, original part): for `a ∈ [1/5, 2]`,
`{η_c = a} = ∅` exactly when `{η_c ≤ a} = univ`. -/
theorem LocalChartPacketsC14Z.zero_face_empty_iff_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {c : X} {hc : c ∈ P.zero.centres} {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    {x | (P.zero.zero c hc).radial x = a} = ∅ ↔ {x | (P.zero.zero c hc).radial x ≤ a} = univ := by
  have hfr := (P.zero_sublevel_regular_FAMZ hc ha).1
  constructor
  · intro hemp
    rcases P.zero_face_type_ZSP35 hc ha with ⟨hu, -⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hu
    · obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E3)) (r := 1)).mpr zero_le_one
      exact (Set.eq_empty_iff_forall_notMem.mp hemp _ (e.symm ⟨x, hx⟩).2).elim
    · exact (Set.eq_empty_iff_forall_notMem.mp hemp _ (e.symm (0, 0)).2).elim
  · intro hu
    rw [← hfr, hu, frontier_univ]

/-- **A nonempty original zero face is a compact connected `S²` or `T²`** (ZSP02's last sentences
and ZSP03's face, original part). -/
theorem LocalChartPacketsC14Z.zero_face_connected_ZSP35
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2)
    (hne : {x | (P.zero.zero c hc).radial x = a}.Nonempty) :
    IsCompact {x | (P.zero.zero c hc).radial x = a} ∧
    IsConnected {x | (P.zero.zero c hc).radial x = a} ∧
    (Nonempty ({x | (P.zero.zero c hc).radial x = a} ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty ({x | (P.zero.zero c hc).radial x = a} ≃ₜ
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  have hfr := (P.zero_sublevel_regular_FAMZ hc ha).1
  have hcpt : IsCompact {x | (P.zero.zero c hc).radial x = a} := by
    rw [← hfr]
    exact isClosed_frontier.isCompact
  rcases P.zero_face_type_ZSP35 hc ha with ⟨-, he⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [he] at hne
    exact absurd hne not_nonempty_empty
  · refine ⟨hcpt, ?_, Or.inl ⟨e⟩⟩
    have hS : IsConnected (Metric.sphere (0 : E3) 1) :=
      isConnected_sphere (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num)
        0 zero_le_one
    have : ConnectedSpace (Metric.sphere (0 : E3) 1) := isConnected_iff_connectedSpace.mp hS
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr this)
  · refine ⟨hcpt, ?_, Or.inr ⟨e⟩⟩
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)

/-- **Regularity of the original coordinate near a zero face** (ZSP03, original part): the open
band `{1/5 < η_c < 2}` contains every face `{η_c = a}`, `a ∈ (1/5, 2)`; on it `η_c` is smooth with
nonzero gradient for `r_c⁻² g`; and the original annular cutoff `ζ_c = ψ(η_c)` is `1` on
`{3/10 ≤ η_c ≤ 4/5}`. -/
theorem LocalChartPacketsC14Z.zero_face_regular_ZSP35
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) :
    IsOpen {x | 1 / 5 < (P.zero.zero c hc).radial x ∧ (P.zero.zero c hc).radial x < 2} ∧
    (∀ a ∈ Ioo (1 / 5 : ℝ) 2, {x | (P.zero.zero c hc).radial x = a} ⊆
      {x | 1 / 5 < (P.zero.zero c hc).radial x ∧ (P.zero.zero c hc).radial x < 2}) ∧
    (∀ x, 1 / 5 < (P.zero.zero c hc).radial x → (P.zero.zero c hc).radial x < 2 →
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero c hc).radial x ∧
      gradFun (scaleMetric (((P.zero.zero c hc).radius)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr (P.zero.zero c hc).radius_pos) 2) g)
        (P.zero.zero c hc).radial x ≠ 0) ∧
    ∀ x, (P.zero.zero c hc).radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero c hc).radial x) = 1 := by
  have hR := (P.zero.zero c hc).radius_pos
  obtain ⟨hlip, -, -, -, -, -, -, -, -, -, ⟨O', hO'o, hO'sub, hO'sm, hne⟩, -, -, -, -, -, hone,
    -⟩ :=
    (P.zero.zero c hc).radial_spec
  have hηc : Continuous (P.zero.zero c hc).radial :=
    @LipschitzWith.continuous X ℝ (mX.rescale ((P.zero.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoEMetricSpace _ _ _ hlip
  refine ⟨(isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const),
    fun a ha x hx => ⟨(show (P.zero.zero c hc).radial x = a from hx) ▸ ha.1,
      (show (P.zero.zero c hc).radial x = a from hx) ▸ ha.2⟩, fun x h1 h2 => ?_, hone⟩
  have hx : x ∈ O' := hO'sub ⟨h1.le, h2.le⟩
  exact ⟨(hO'sm.contMDiffAt (hO'o.mem_nhds hx)), hne x hx⟩

end DifferentialGeometry.Geometry.Collapse
