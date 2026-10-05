import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# ZSP02 on the complete closed family: the actual zero sublevel `{η_c ≤ .4}` (lane C14-FAM-Z)

Consumer of `LocalChartPacketsC14Z.zero_sublevel_types` (external review 53, §4.1 and its ZSP02 row:
"the compact smooth core type of the SAME `{η_c ≤ .4}` and its boundary"; blueprint 207B,
`thm:fibration-actual-zero-domains`, B:6374, "smoothly ambient isotopic to the SAME original radial
sublevel `{η_i ≤ .4}` and has its LPA05/LFR54 smooth type, including the boundary"). The ambient
isotopy to the adjusted domain `Z_i` is a certificate of the later construction (class (c)); what
the family has to supply about the original sublevel is proved here from the family's own fields.

* `LocalChartPacketsC14Z.zero_sublevel_regular_FAMZ` (every `a ∈ [1/5, 2]`, derived from the zero
  ball's `radial_spec`): `frontier {η_c ≤ a} = {η_c = a}` (regular level), the gradient of `η_c`
  for `r_c⁻² g` is strictly transverse to it, and the enclosure
  `B(c, (a - e) r_c) ⊆ {η_c ≤ a} ⊆ B(c, (a + e) r_c)`.
* `LocalChartPacketsC14Z.zsp02_zero_sublevel_FAMZ` (ZSP02 at `a = 2/5`): `{η_c ≤ 2/5}` is compact,
  has a regular boundary `{η_c = 2/5}` with transverse gradient and the ball enclosure, has one of
  LFR54's types (`CompactModelSublevel oM ∨ PointSoulCoreSublevel ∨ CircleSoulCoreSublevel ∨
  ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel`), and is the whole source or is carried by an
  ambient partial diffeomorphism onto a closed disc core of its model with the level `{η_c = 2/5}`
  onto the boundary of that core.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

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

/-- **The actual zero sublevels have a regular boundary** (from the zero ball's `radial_spec`).
For every zero centre `c` and every `a ∈ [1/5, 2]`: `frontier {η_c ≤ a} = {η_c = a}`, the gradient
of `η_c` for `r_c⁻² g` is strictly transverse to this level, and
`B(c, (a - e) r_c) ⊆ {η_c ≤ a} ⊆ B(c, (a + e) r_c)`. -/
theorem LocalChartPacketsC14Z.zero_sublevel_regular_FAMZ
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    frontier {x | (P.zero.zero c hc).radial x ≤ a} = {x | (P.zero.zero c hc).radial x = a} ∧
    (∀ q, (P.zero.zero c hc).radial q = a →
      0 < mvfderiv 𝓘(ℝ, E3) (P.zero.zero c hc).radial q
        (gradFun (scaleMetric (((P.zero.zero c hc).radius)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (P.zero.zero c hc).radius_pos) 2) g)
          (P.zero.zero c hc).radial q)) ∧
    (∀ x, dist x c < (a - e) * (P.zero.zero c hc).radius → (P.zero.zero c hc).radial x ≤ a) ∧
    (∀ x, (P.zero.zero c hc).radial x ≤ a → dist x c < (a + e) * (P.zero.zero c hc).radius) := by
  have hR := (P.zero.zero c hc).radius_pos
  have hcen := P.zero.zero_center c hc
  obtain ⟨hlip, -, hclose, -, -, -, -, -, -, -, ⟨O', hO'o, hO'sub, hO'sm, hne⟩, -⟩ :=
    (P.zero.zero c hc).radial_spec
  have hηc : Continuous (P.zero.zero c hc).radial :=
    @LipschitzWith.continuous X ℝ (mX.rescale ((P.zero.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoEMetricSpace _ _ _ hlip
  have hlevel : ∀ q, (P.zero.zero c hc).radial q = a → q ∈ O' := fun q hq =>
    hO'sub (show (P.zero.zero c hc).radial q ∈ Icc (1 / 5 : ℝ) 2 by rw [hq]; exact ha)
  have hcl : ∀ x, |(P.zero.zero c hc).radial x - ((P.zero.zero c hc).radius)⁻¹ * dist x c| < e := by
    intro x
    have h1 := hclose x
    rw [@Metric.infDist_singleton X (mX.rescale ((P.zero.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoMetricSpace] at h1
    have h2 : |(P.zero.zero c hc).radial x - ((P.zero.zero c hc).radius)⁻¹ *
        dist x (P.zero.zero c hc).center| < e := h1
    rw [hcen] at h2
    exact h2
  refine ⟨frontier_sublevel_eq_level_of_regular (I := 𝓘(ℝ, E3)) hηc fun q hq =>
      ⟨((hO'sm.contMDiffAt (hO'o.mem_nhds (hlevel q hq))).of_le (by norm_num)),
        mfderiv_ne_zero_of_gradFun_ne_zero _ (hne q (hlevel q hq))⟩,
    fun q hq => mvfderiv_gradFun_pos _ (hne q (hlevel q hq)), fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := (abs_lt.mp (hcl x)).2
    have h2 : ((P.zero.zero c hc).radius)⁻¹ * dist x c < a - e := by
      rw [inv_mul_lt_iff₀ hR]
      linarith
    linarith
  · have h1 := (abs_lt.mp (hcl x)).1
    have h2 : ((P.zero.zero c hc).radius)⁻¹ * dist x c < a + e := by linarith
    rw [inv_mul_lt_iff₀ hR] at h2
    linarith

/-- **ZSP02 at `a = 2/5` on the complete closed family.** For every zero centre `c`, the actual
sublevel `A = {η_c ≤ 2/5}` of the zero ball's radial function: is compact; has the regular boundary
`{η_c = 2/5}` with strictly transverse gradient; satisfies
`B(c, (2/5 - e) r_c) ⊆ A ⊆ B(c, (2/5 + e) r_c)`; has one of LFR54's types (LFR53's on a compact
model); and is the whole source, or lies in the source of an ambient partial diffeomorphism `Ψ` into
its model with `Ψ '' A` a closed disc core and `Ψ '' {η_c = 2/5} = frontier (Ψ '' A)`. -/
theorem LocalChartPacketsC14Z.zsp02_zero_sublevel_FAMZ
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) :
    IsCompact {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ∧
    frontier {x | (P.zero.zero c hc).radial x ≤ 2 / 5} =
      {x | (P.zero.zero c hc).radial x = 2 / 5} ∧
    (∀ q, (P.zero.zero c hc).radial q = 2 / 5 →
      0 < mvfderiv 𝓘(ℝ, E3) (P.zero.zero c hc).radial q
        (gradFun (scaleMetric (((P.zero.zero c hc).radius)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (P.zero.zero c hc).radius_pos) 2) g)
          (P.zero.zero c hc).radial q)) ∧
    (∀ x, dist x c < (2 / 5 - e) * (P.zero.zero c hc).radius →
      (P.zero.zero c hc).radial x ≤ 2 / 5) ∧
    (∀ x, (P.zero.zero c hc).radial x ≤ 2 / 5 →
      dist x c < (2 / 5 + e) * (P.zero.zero c hc).radius) ∧
    (CompactModelSublevel oM (P.N (P.zero.zero c hc).model)
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ∨
      PointSoulCoreSublevel (P.N (P.zero.zero c hc).model)
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ∨
      CircleSoulCoreSublevel (P.N (P.zero.zero c hc).model)
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ∨
      ProjectiveSoulCoreSublevel (P.N (P.zero.zero c hc).model)
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ∨
      KleinSoulCoreSublevel (P.N (P.zero.zero c hc).model)
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5}) ∧
    ({x | (P.zero.zero c hc).radial x ≤ 2 / 5} = univ ∨
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) X (P.N (P.zero.zero c hc).model) ∞,
        {x | (P.zero.zero c hc).radial x ≤ 2 / 5} ⊆ Ψ.source ∧
        IsClosed (Ψ '' {x | (P.zero.zero c hc).radial x ≤ 2 / 5}) ∧
        Ψ '' {x | (P.zero.zero c hc).radial x = 2 / 5} =
          frontier (Ψ '' {x | (P.zero.zero c hc).radial x ≤ 2 / 5})) := by
  have ha : (2 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hfr, htr, hin, hout⟩ := P.zero_sublevel_regular_FAMZ hc ha
  refine ⟨(P.isClosed_zero_sublevel_FAMZ hc (2 / 5)).isCompact, hfr, htr, hin, hout,
    P.zero_sublevel_types c hc (2 / 5) ha, ?_⟩
  rcases P.zero_sublevel_carrier_FAMZ hc ha with hu | ⟨Ψ, hΨs, hΨc, hΨf⟩
  · exact Or.inl hu
  · exact Or.inr ⟨Ψ, hΨs, hΨc, hfr ▸ hΨf⟩

end DifferentialGeometry.Geometry.Collapse
