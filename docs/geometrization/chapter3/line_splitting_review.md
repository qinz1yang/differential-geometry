# Line splitting: second-pass mathematical and interface review

This is a self-review, not independent-agent or human approval. The complete
new source files were reread against ALS01–ALS05 and the source passages in
`line_splitting.md`. The principal theorem has the intended proper geodesic
metric hypotheses and concludes a bijective Pythagorean product isometry,
not merely a map into a product or a conditional assertion assuming parallel
lines already exist. The rays, parallel lines, coordinate, translations,
zero slice, inverse map, factor geodesics and comparison are all constructed.

The proofs use global comparison. They neither globalize a local condition
nor make a Riemannian curvature-to-metric-comparison inference. Properness
is needed for the compact ray extraction; no independent completeness
hypothesis is missing because proper metric spaces are complete. Both signs
of the real parameter are essential to the polynomial coefficient arguments.
The coordinate convention is b(γ(t))=t. Factor dimension is an inequality,
not an asserted dimension drop or product-dimension equality.

The modified proof of ALS02 was checked separately: concavity of the even
part plus its global nonnegative lower bound implies constancy; reflection
then forces equality in all concavity inequalities. No continuity hypothesis
or unproved differentiability is needed. Ray limits use one common
ultrafilter for all parameters, so individual limits are not improperly
combined into an isometry. The source curves need no uniqueness. The
negative ray is calibrated using the explicitly proved coordinate reversal.
The cross-distance law proves uniqueness rather than importing nonbranching.

The extracted target is chosen before quantifying over its possible lines.
There is no assumption that its convergence basepoint lies on a line;
pointedness with that basepoint requires γ(0)=q. A point target is allowed
and makes the universal line-conditional conclusion vacuous, not false.
The source covering constant is fixed before mesh and tail index, and the
source comparison tail may depend on the fixed radius. No common index for
all radii is silently assumed.

The following executable review checks the zero-height case, the exclusion
of a max-metric product, inverse/surjectivity and exact alignment, a singleton
transverse factor when the original line exhausts X, and preservation of the
actual convergence basepoint when it equals γ(0). The final `#check` displays
the full same-target extraction signature; declaration provenance also
checks actual supplier constants in its proof body.

```lean
import DifferentialGeometry.Geometry.Comparison.AngleMonotonicity
import DifferentialGeometry.Geometry.Metric.Approximation.LineSplitting

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

example {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ) (t : ℝ) :
    lineCoordinate γ (γ t) = t ∧ dist (γ t) (γ (lineCoordinate γ (γ t))) = 0 := by
  rw [lineCoordinate_apply_isometry hγ]
  exact ⟨rfl, dist_self _⟩

example : dist (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)))
    (WithLp.toLp 2 ((1 : ℝ), (1 : ℝ))) = Real.sqrt 2 := by
  rw [WithLp.prod_dist_eq_of_L2]
  norm_num

example {X : Type*} [MetricSpace X] [ProperSpace X]
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t) :
    Function.Surjective (lineSplitting hs hγ hsegments) ∧
      (lineSplitting hs hγ hsegments).symm
        (WithLp.toLp 2 (0, ⟨γ 0, lineCoordinate_apply_isometry hγ 0⟩)) = γ 0 := by
  refine ⟨(lineSplitting hs hγ hsegments).surjective, ?_⟩
  have h := lineSplitting_apply_line hs hγ hsegments 0
  exact (lineSplitting hs hγ hsegments).symm_apply_eq.mpr h.symm

example {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    (honto : Function.Surjective γ) : Subsingleton {x : X // lineCoordinate γ x = 0} := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨s, hs⟩ := honto a.val
  obtain ⟨t, ht⟩ := honto b.val
  have hsa := a.property
  have htb := b.property
  rw [← hs, lineCoordinate_apply_isometry hγ] at hsa
  rw [← ht, lineCoordinate_apply_isometry hγ] at htb
  apply Subtype.ext
  rw [← hs, ← ht, hsa, htb]

example {X : ℕ → Type*} {Y : Type*} [∀ i, MetricSpace (X i)]
    [MetricSpace Y] [ProperSpace Y] {p : ∀ i, X i} {q : Y} {κ : ℕ → ℝ}
    (h : PointedGHConverges p q) (hκ : ∀ i, 0 ≤ κ i)
    (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    {γ : ℝ → Y} (hγ : Isometry γ) (hq : γ 0 = q) :
    ∃ e : Y ≃ᵢ WithLp 2 (ℝ × {x : Y // lineCoordinate γ x = 0}),
      e q = WithLp.toLp 2 (0, ⟨q, by rw [← hq, lineCoordinate_apply_isometry hγ]⟩) := by
  have hc := h.fourPointComparison_zero_of_eventual_comparison hκ hκzero hcompare
  refine ⟨lineSplitting hc hγ hsegments, ?_⟩
  simpa only [hq] using lineSplitting_apply_line hc hγ hsegments 0

#check @DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometryEquiv_real_prod
#check @GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod
#check @GC.MetricGeometry.exists_pointedGHConverges_with_line_splitting
#eval "LINE_SPLITTING_REVIEW_PASS"
```

Executed build, axiom, dependency and application results are recorded in
`evidence/line_splitting_verification.json`. The combined all-module result
remains in `evidence/verification.json`. These are scoped checks on the
isolated development branch, not a migrated PC-root build or mathematical
completion of all Chapters 3 and 4.

The supplemental provenance audit follows actual compiled constant
references through Lean-generated proof helpers. It separately inventories
all 44 authored declarations and all owned generated declarations; generated
equations such as `metricComparisonAngle.eq_1` are audited too. A supplier
edge is accepted only when that constant is reached in the compiled proof,
not from a matching theorem name or a textual import alone.

The mandatory blueprint static audit was rerun and still stops at the
historical absolute path for `KleinerLottAsterisqueLocalCollapse.pdf`, whose
archive directory has moved. See `evidence/blueprint_static_line_splitting.log`.
It is not reported as passing. The three blueprint files are byte-for-byte
unchanged; this path issue does not participate in the scoped Lean checks.

Final executed results: all ten added modules compile; their 44 authored
and 71 total owned declarations have only standard logical axioms in their
closures. All twelve dependency paths and five review examples pass.
The combined manifest build passes for 54 modules (2832 Lake jobs), and its
all-owned audit passes for 524 declarations. These are warm-cache checks.
The old baseline checkout is clean at `b456fb0eab29f8e61795123bf7df5dc5b3a824c8`;
no existing mathematical leaf changed relative to the preceding `9d649ae5`
checkpoint. The three blueprint SHA256 values remain unchanged. The full
PC root was not built on this target.
