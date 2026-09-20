/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361

/-!
# Limits of stagewise approximations over a locally finite piece tower

**This file is not on the route to `Moise352`, and the stagewise architecture it was built
for is not Moise's.**  Moise's own proof of 35.2 was read directly from the book, printed
p. 251: it performs no stagewise recursion at all.  It pushes `K` into `Int K` by a PL
homeomorphism close to the identity, reduces to `h` and the error function being defined on
an open set containing `K`, subdivides so that each simplex has small image, applies 35.1 to
a regular neighbourhood of the **1-skeleton**, and then extends over the 2- and 3-simplexes
one at a time by the argument of section 34.  The tree's `Moise351` (`MoiseChain.lean:191`)
is a faithful rendering of that input.  See `SkeletonReduction.lean`.

Consequently `moise352_of_stages` below is a valid implication from a **false** hypothesis:
`Moise352Stages` is refuted in `CompactRelativeApproximation.lean`, and its successor
`Moise352StageStep` is refuted in `StageTransport.lean`.  Both are kept as records of the
refutation, not as obligations.  What survives here as genuine infrastructure is the gluing
and limit machinery — `exists_forall_eqOn_coreSpace`, `exists_glue_of_eqOn`,
`exists_isPLHomeomorphInto_of_stages` and the separation estimates — which takes a pointwise
error function and is independent of the refuted packaging.

`Moise352` asks for a piecewise linear approximation of a topological embedding of a
locally finite, possibly non-compact, polyhedral manifold with boundary, with the error
controlled by a continuous positive function rather than by a constant.  Applying a
compact approximation theorem separately to the pieces of an exhaustion produces maps
that need not agree with one another, so the compact statement does not by itself give
the non-compact one.

This file supplies the *assembly* half.  Throughout, the exhaustion is the sequence of
compact stages `T.coreSpace i` of a `LocallyFinitePieceTower`, which satisfies
`T.coreSpace i ⊆ T.N i ⊆ T.coreSpace (i + 1)`, has union the whole set, and — this is
where local finiteness enters — satisfies `T.core_space_mem_nhdsWithin`, saying that
`T.coreSpace (i + 2)` is a neighbourhood *within the set* of every point of `T.N i`.

Given maps `f i` defined on the stages which agree with their predecessors,
`LocallyFinitePieceTower.exists_forall_eqOn_coreSpace` glues them into a single map `g`.
Because the stages are eventually neighbourhoods, `g` agrees with a single `f i` near
each point, and the piecewise linearity of `g` follows;
because the stages are increasing, injectivity of `g` follows as well.  The third
component of `IsPLHomeomorphInto`, the piecewise linear local inverse, is *not* local in
the domain: it asks for a property at a point of the full image `g '' U`, and a priori
points coming from far-out stages could accumulate there.  The remaining results isolate
exactly the extra input that rules this out, and reduce it to a metric separation
statement about the original embedding.

## Main results

* `LocallyFinitePieceTower.exists_forall_eqOn_coreSpace`: glue a compatible family of
  maps on the stages into a single map on the ambient space.
* `LocallyFinitePieceTower.isPLOn_of_forall_eqOn_coreSpace`: the glued map is piecewise
  linear on the whole set.
* `LocallyFinitePieceTower.injOn_of_forall_eqOn_coreSpace`: the glued map is injective on
  the whole set.
* `LocallyFinitePieceTower.isPLHomeomorphInto_of_forall_mem_nhdsWithin_image`: the glued
  map is a piecewise linear embedding, given that each stage image is a neighbourhood of
  the corresponding point inside the full image.
* `mem_nhdsWithin_image_of_dist_lt`: the stage-image neighbourhood condition follows from
  a metric separation estimate for the map being approximated.
* `exists_pos_le_dist_of_isEmbedding` and `exists_uniform_pos_le_dist_of_isEmbedding`:
  that separation estimate holds for any topological embedding, pointwise and then with a
  single constant over a compact set.
* `LocallyFinitePieceTower.exists_pos_le_dist_coreSpace`: the resulting separation
  constant attached to each stage of the tower.
* `LocallyFinitePieceTower.exists_isPLHomeomorphInto_of_stages`: the packaged assembly,
  producing the conclusion of `Moise352` from stagewise piecewise linear embeddings
  together with one uniformity hypothesis relating the error bound to the separation
  constants.
* `LocallyFinitePieceTower.exists_isPLHomeomorphInto_dist_lt_of_stages`: that uniformity
  hypothesis discharged.  The error function fed to the previous result is not required to
  be continuous, so it may be taken to be the step function assigning to a point the
  tolerance of the least stage containing it; the tolerances are then chosen after the
  separation constants and after the minima of `φ` on the stages.
* `Moise352Stages` and `moise352_of_stages`: the resulting reduction of `Moise352` to a
  statement about the compact stages alone.

## Remaining obligation

`Moise352Stages` is not proved here.  It asks, on each compact stage and for each
prescribed constant tolerance, for a piecewise linear embedding approximating `h` and
agreeing with the previous stage's map on the previous stage.  That is the compact
approximation theorem in its relative form; the absolute compact form, without the
agreement clause, is what `CompactEmbeddingApproximation` reduces to injectivity.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace LocallyFinitePieceTower

section Glue

variable {n : ℕ} {M₁ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] {U : Set M₁}

/-- Glue a family of maps that agree on the previous stage into a single map defined on
the whole ambient space.  This is the total-function form of
`LocallyFinitePieceTower.exists_glue_of_eqOn`, whose conclusion lives on the subtype. -/
theorem exists_forall_eqOn_coreSpace {Y : Type*} (T : LocallyFinitePieceTower n M₁ U)
    (f : ℕ → M₁ → Y) (hf : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) :
    ∃ g : M₁ → Y, ∀ i, EqOn g (f i) (T.coreSpace i) := by
  classical
  obtain ⟨G, hG⟩ := T.exists_glue_of_eqOn f hf
  refine ⟨fun x => if hx : x ∈ U then G ⟨x, hx⟩ else f 0 x, fun i x hx => ?_⟩
  have hxU : x ∈ U := T.core_space_subset_union i hx
  simp only [dif_pos hxU]
  exact hG i x hx

/-- A map that agrees on every stage with an injective map is injective on the whole set.
Two points of the set lie in a common stage, because the stages increase. -/
theorem injOn_of_forall_eqOn_coreSpace {Y : Type*} (T : LocallyFinitePieceTower n M₁ U)
    {f : ℕ → M₁ → Y} {g : M₁ → Y} (hg : ∀ i, EqOn g (f i) (T.coreSpace i))
    (hf : ∀ i, InjOn (f i) (T.coreSpace i)) : InjOn g U := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := T.exists_mem_core_space hx
  obtain ⟨j, hj⟩ := T.exists_mem_core_space hy
  have hi' : x ∈ T.coreSpace (max i j) := T.core_space_monotone (le_max_left i j) hi
  have hj' : y ∈ T.coreSpace (max i j) := T.core_space_monotone (le_max_right i j) hj
  exact hf (max i j) hi' hj' ((hg _ hi').symm.trans (hxy.trans (hg _ hj')))

end Glue

section PL

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  {U : Set M₁}

/-- A map that agrees on every stage with a map piecewise linear on that stage is
piecewise linear on the whole set.  Local finiteness enters through
`LocallyFinitePieceTower.core_space_mem_nhdsWithin`: every point of `T.N i` has
`T.coreSpace (i + 2)` as a neighbourhood within `U`, so the glued map coincides with a
single stage map near that point. -/
theorem isPLOn_of_forall_eqOn_coreSpace (T : LocallyFinitePieceTower n M₁ U)
    {f : ℕ → M₁ → M₂} {g : M₁ → M₂} (hg : ∀ i, EqOn g (f i) (T.coreSpace i))
    (hf : ∀ i, IsPLOn n n (f i) (T.coreSpace i)) : IsPLOn n n g U := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hx)
  have hmem : x ∈ T.coreSpace (i + 2) := T.subset_core (i + 1) (T.monotone (Nat.le_succ i) hi)
  have hnhds : T.coreSpace (i + 2) ∈ 𝓝[U] x := T.core_space_mem_nhdsWithin hi
  have hinter : U ∩ T.coreSpace (i + 2) = T.coreSpace (i + 2) :=
    inter_eq_right.mpr (T.core_space_subset_union _)
  have hbase : IsPLWithinAt n n g (T.coreSpace (i + 2)) x :=
    piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
      (hf (i + 2) x hmem) (fun y hy => hg (i + 2) hy) hmem
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnhds).mp ?_
  rw [hinter]
  exact hbase

/-- The glued map is a piecewise linear embedding, provided that at each point the image
of some stage containing it is a neighbourhood of the image point *inside the full
image*.  That hypothesis is what prevents points coming from far-out stages from
accumulating at the image point; it is not automatic, and is supplied in the metric
setting by `mem_nhdsWithin_image_of_dist_lt`.

The inverse produced here is `Function.invFunOn g U`, which is a genuine left inverse on
all of `U` by injectivity, and which agrees on each stage image with the local inverse
coming from that stage. -/
theorem isPLHomeomorphInto_of_forall_mem_nhdsWithin_image
    (T : LocallyFinitePieceTower n M₁ U) {f : ℕ → M₁ → M₂} {g : M₁ → M₂}
    (hg : ∀ i, EqOn g (f i) (T.coreSpace i)) (hPL : IsPLOn n n g U) (hinj : InjOn g U)
    (hstage : ∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i))
    (hnhds : ∀ x ∈ U, ∃ i, x ∈ T.coreSpace i ∧ g '' T.coreSpace i ∈ 𝓝[g '' U] g x) :
    IsPLHomeomorphInto n g U := by
  refine ⟨hPL, hinj, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have : Nonempty M₁ := ⟨x⟩
  obtain ⟨i, hxi, hnb⟩ := hnhds x hx
  have himg : g '' T.coreSpace i = f i '' T.coreSpace i := image_congr fun z hz => hg i hz
  obtain ⟨G, hGpl, hGinv⟩ := (hstage i).2.2 (f i x) ⟨x, hxi, rfl⟩
  have hGG : ∀ z ∈ g '' T.coreSpace i, Function.invFunOn g U z = G z := by
    rintro _ ⟨w, hw, rfl⟩
    have hwU : w ∈ U := T.core_space_subset_union i hw
    have h2 : G (g w) = w := by rw [hg i hw]; exact hGinv hw
    rw [hinj.leftInvOn_invFunOn hwU, h2]
  have hbase : IsPLWithinAt n n (Function.invFunOn g U) (g '' T.coreSpace i) (g x) := by
    refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem ?_ hGG
      ⟨x, hxi, rfl⟩
    rw [himg, hg i hxi]
    exact hGpl
  refine ⟨Function.invFunOn g U, ?_, hinj.leftInvOn_invFunOn⟩
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mp ?_
  rw [inter_eq_right.mpr (image_mono (T.core_space_subset_union i))]
  exact hbase

end PL

end LocallyFinitePieceTower

section Separation

variable {M₁ M₂ : Type*} [MetricSpace M₂]

/-- If every point of `U` outside `A` is moved by `g` to distance at least `ρ` from
`g x`, then the image of `A` is a neighbourhood of `g x` inside the image of `U`. -/
theorem mem_nhdsWithin_image_of_forall_le_dist {g : M₁ → M₂} {U A : Set M₁} {x : M₁}
    {ρ : ℝ} (hρ : 0 < ρ) (hsep : ∀ z ∈ U \ A, ρ ≤ dist (g z) (g x)) :
    g '' A ∈ 𝓝[g '' U] g x := by
  have hsub : ∀ y ∈ g '' U, y ∈ Metric.ball (g x) ρ → y ∈ g '' A := by
    rintro _ ⟨z, hz, rfl⟩ hy
    by_cases hzA : z ∈ A
    · exact ⟨z, hzA, rfl⟩
    · exact absurd (Metric.mem_ball.mp hy) (not_lt.mpr (hsep z ⟨hz, hzA⟩))
  exact mem_nhdsWithin.mpr ⟨Metric.ball (g x) ρ, Metric.isOpen_ball,
    Metric.mem_ball_self hρ, fun y hy => hsub y hy.2 hy.1⟩

/-- Transfer of the neighbourhood condition from the map being approximated to the
approximation.  If `h` separates `x` from `U \ A` by `ρ`, and `g` moves `x` and the
points of `U \ A` by less than `ρ / 3`, then the `g`-image of `A` is a neighbourhood of
`g x` inside the `g`-image of `U`. -/
theorem mem_nhdsWithin_image_of_dist_lt {g h : M₁ → M₂} {U A : Set M₁} {x : M₁} {ρ : ℝ}
    (hsep : ∀ z ∈ U \ A, ρ ≤ dist (h z) (h x))
    (hfar : ∀ z ∈ U \ A, 3 * dist (g z) (h z) < ρ)
    (hnear : 3 * dist (g x) (h x) < ρ) :
    g '' A ∈ 𝓝[g '' U] g x := by
  have hρ : 0 < ρ := lt_of_le_of_lt (by positivity) hnear
  refine mem_nhdsWithin_image_of_forall_le_dist (ρ := ρ / 3) (by linarith) fun z hz => ?_
  have h1 : 3 * dist (g z) (h z) < ρ := hfar z hz
  have h3 : ρ ≤ dist (h z) (h x) := hsep z hz
  have h4 := dist_triangle4 (h z) (g z) (g x) (h x)
  rw [dist_comm (h z) (g z)] at h4
  linarith

variable [TopologicalSpace M₁]

/-- A topological embedding separates a point from the complement of any of its
neighbourhoods within the domain, by a positive distance in the target. -/
theorem exists_pos_le_dist_of_isEmbedding {U A : Set M₁} {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) {x : M₁} (hxU : x ∈ U)
    (hA : A ∈ 𝓝[U] x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ U \ A, ρ ≤ dist (h z) (h x) := by
  obtain ⟨V, hV, hxV, hVA⟩ := mem_nhdsWithin.mp hA
  have hpre : (Subtype.val ⁻¹' V : Set U) ∈ 𝓝 (⟨x, hxU⟩ : U) :=
    (hV.preimage continuous_subtype_val).mem_nhds hxV
  rw [hh.toIsInducing.nhds_eq_comap ⟨x, hxU⟩] at hpre
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hpre
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hzW : (U.domRestrict h) ⟨z, hz.1⟩ ∈ W := hball (Metric.mem_ball.mpr hcon)
  exact hz.2 (hVA ⟨hWV hzW, hz.1⟩)

/-- The uniform form of `exists_pos_le_dist_of_isEmbedding`: one separation constant works
for every point of a compact subset of the domain.  The distance from `h x` to the image of
`U \ A` is a continuous function of `x`, positive at every point of the compact set by the
pointwise statement, hence bounded below by its positive minimum there. -/
theorem exists_uniform_pos_le_dist_of_isEmbedding {U A C : Set M₁} {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) (hC : IsCompact C) (hCU : C ⊆ U)
    (hA : ∀ x ∈ C, A ∈ 𝓝[U] x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ C, ∀ z ∈ U \ A, ρ ≤ dist (h z) (h x) := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
  rcases (U \ A).eq_empty_or_nonempty with hUA | hUAne
  · refine ⟨1, one_pos, fun _ _ z hz => absurd hz ?_⟩
    rw [hUA]
    exact notMem_empty z
  have hSne : (h '' (U \ A)).Nonempty := hUAne.image h
  have hcontU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hFcont : ContinuousOn (fun y => Metric.infDist (h y) (h '' (U \ A))) C :=
    (Metric.continuous_infDist_pt _).comp_continuousOn (hcontU.mono hCU)
  obtain ⟨x₀, hx₀, hmin⟩ := hC.exists_isMinOn hCne hFcont
  refine ⟨Metric.infDist (h x₀) (h '' (U \ A)), ?_, fun x hx z hz => ?_⟩
  · obtain ⟨ρ, hρ, hsep⟩ := exists_pos_le_dist_of_isEmbedding hh (hCU hx₀) (hA x₀ hx₀)
    refine lt_of_lt_of_le hρ ((Metric.le_infDist hSne).mpr ?_)
    rintro _ ⟨w, hw, rfl⟩
    rw [dist_comm]
    exact hsep w hw
  · refine (isMinOn_iff.mp hmin x hx).trans ?_
    have hmem : h z ∈ h '' (U \ A) := ⟨z, hz, rfl⟩
    rw [dist_comm (h z) (h x)]
    exact Metric.infDist_le_dist_of_mem (x := h x) hmem

end Separation

namespace LocallyFinitePieceTower

section Stage

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] {U : Set M₁}

/-- Stagewise separation constants.  For a topological embedding of the set carried by a
locally finite piece tower, each stage admits one positive constant separating every point
of that stage from every point lying outside the stage two steps later.  Local finiteness
is what makes this possible: the later stage is a neighbourhood within `U` of the earlier
one, by `LocallyFinitePieceTower.core_space_mem_nhdsWithin`. -/
theorem exists_pos_le_dist_coreSpace (T : LocallyFinitePieceTower n M₁ U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) (i : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ T.coreSpace i, ∀ z ∈ U \ T.coreSpace (i + 2),
      ρ ≤ dist (h z) (h x) :=
  exists_uniform_pos_le_dist_of_isEmbedding hh (T.isCompact_core_space i)
    (T.core_space_subset_union i)
    fun _ hx => T.core_space_mem_nhdsWithin (T.core_space_subset i hx)

end Stage

end LocallyFinitePieceTower

/-- A quarter of the running minimum of a sequence of reals. -/
private noncomputable def quarterMin (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0 / 4
  | i + 1 => min (quarterMin d i) (d (i + 1) / 4)

/-- Any sequence of positive reals dominates, term by term and after multiplication by
four, some antitone sequence of positive reals.  This lets a single tolerance be chosen
that is simultaneously admissible at every earlier stage. -/
private theorem exists_antitone_pos_four_mul_le {d : ℕ → ℝ} (hd : ∀ i, 0 < d i) :
    ∃ ε : ℕ → ℝ, (∀ i, 0 < ε i) ∧ Antitone ε ∧ ∀ i, 4 * ε i ≤ d i := by
  refine ⟨quarterMin d, ?_, antitone_nat_of_succ_le fun i => min_le_left _ _, ?_⟩
  · intro i
    induction i with
    | zero => exact div_pos (hd 0) (by norm_num)
    | succ k ih => exact lt_min ih (div_pos (hd (k + 1)) (by norm_num))
  · intro i
    cases i with
    | zero =>
      have h0 : quarterMin d 0 = d 0 / 4 := rfl
      rw [h0]
      linarith
    | succ k =>
      have h1 : quarterMin d (k + 1) ≤ d (k + 1) / 4 := min_le_right _ _
      linarith

namespace LocallyFinitePieceTower

section Assembly

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  {U : Set M₁}

/-- The packaged assembly.  From piecewise linear embeddings `f i` of the compact stages
of a locally finite piece tower, agreeing with their predecessors and approximating `h`
within `φ`, together with a uniformity hypothesis relating `φ` to separation constants
for `h`, one obtains a single piecewise linear embedding of the whole set approximating
`h` within `φ`.  This is the conclusion of `Moise352` for the set carrying the tower.

The hypothesis `hunif` asks, for each point `x`, for a stage containing `x` and a
constant `ρ` which both separates `x` from the complement of that stage under `h` and
dominates `3 * φ` there.  Its separation half is automatic for a topological embedding by
`exists_pos_le_dist_of_isEmbedding`; only the compatibility of the single constant `ρ`
with the values of `φ` far out is an additional requirement on `φ`. -/
theorem exists_isPLHomeomorphInto_of_stages (T : LocallyFinitePieceTower n M₁ U)
    {f : ℕ → M₁ → M₂} {h : M₁ → M₂} {φ : M₁ → ℝ}
    (hstep : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i))
    (hstage : ∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i))
    (hclose : ∀ i, ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < φ x)
    (hunif : ∀ x ∈ U, ∃ i, x ∈ T.coreSpace i ∧ ∃ ρ : ℝ, 3 * φ x < ρ ∧
      ∀ z ∈ U \ T.coreSpace i, ρ ≤ dist (h z) (h x) ∧ 3 * φ z < ρ) :
    ∃ g : M₁ → M₂, IsPLHomeomorphInto n g U ∧ ∀ x ∈ U, dist (g x) (h x) < φ x := by
  obtain ⟨g, hg⟩ := T.exists_forall_eqOn_coreSpace f hstep
  have hdist : ∀ x ∈ U, dist (g x) (h x) < φ x := by
    intro x hx
    obtain ⟨i, hxi⟩ := T.exists_mem_core_space hx
    rw [hg i hxi]
    exact hclose i x hxi
  have hPL : IsPLOn n n g U :=
    T.isPLOn_of_forall_eqOn_coreSpace hg fun i => (hstage i).isPLOn
  have hinj : InjOn g U :=
    T.injOn_of_forall_eqOn_coreSpace hg fun i => (hstage i).injOn
  refine ⟨g, T.isPLHomeomorphInto_of_forall_mem_nhdsWithin_image hg hPL hinj hstage ?_, hdist⟩
  intro x hx
  obtain ⟨i, hxi, ρ, hnear, hfar⟩ := hunif x hx
  refine ⟨i, hxi, mem_nhdsWithin_image_of_dist_lt (h := h) (fun z hz => (hfar z hz).1)
    (fun z hz => ?_) ?_⟩
  · have h1 := hdist z hz.1
    have h2 := (hfar z hz).2
    linarith
  · have h1 := hdist x hx
    linarith

/-- The reduction of the non-compact approximation statement to its compact stages.

If, for *every* sequence of positive tolerances, the compact stages of the tower carry
piecewise linear embeddings which agree with their predecessors and approximate `h` within
those tolerances, then `h` is approximated on all of `U` by a single piecewise linear
embedding within the given continuous positive `φ`.  This is the conclusion of `Moise352`
for the set carrying the tower, and the hypothesis `hstages` is a purely compact
statement: it never mentions `U`, only the compact sets `T.coreSpace i`.

The tolerances are chosen after the separation constants of
`LocallyFinitePieceTower.exists_pos_le_dist_coreSpace` and the minima of `φ` on the
stages, so that the error function of
`LocallyFinitePieceTower.exists_isPLHomeomorphInto_of_stages` may be taken to be the step
function `x ↦ ε (least stage containing x)`; no continuity of that step function is
needed, which is what makes the choice elementary. -/
theorem exists_isPLHomeomorphInto_dist_lt_of_stages (T : LocallyFinitePieceTower n M₁ U)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h)) {φ : M₁ → ℝ}
    (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x)
    (hstages : ∀ ε : ℕ → ℝ, (∀ i, 0 < ε i) → ∃ f : ℕ → M₁ → M₂,
      (∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) ∧
      (∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i)) ∧
      ∀ i, ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < ε i) :
    ∃ g : M₁ → M₂, IsPLHomeomorphInto n g U ∧ ∀ x ∈ U, dist (g x) (h x) < φ x := by
  classical
  choose ρ hρpos hρsep using fun i => T.exists_pos_le_dist_coreSpace hh i
  have hcex : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x := by
    intro i
    rcases (T.coreSpace i).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [he] at hx
      exact absurd hx (notMem_empty x)
    · obtain ⟨x₀, hx₀, hle⟩ := (T.isCompact_core_space i).exists_isMinOn hne
        (hφ.mono (T.core_space_subset_union i))
      exact ⟨φ x₀, hpos x₀ (T.core_space_subset_union i hx₀),
        fun x hx => isMinOn_iff.mp hle x hx⟩
  choose c hcpos hcle using hcex
  obtain ⟨ε, hεpos, hεanti, hεd⟩ := exists_antitone_pos_four_mul_le
    (d := fun i => min (ρ i) (c i)) fun i => lt_min (hρpos i) (hcpos i)
  obtain ⟨f, hstep, hstage, hclose⟩ := hstages ε hεpos
  obtain ⟨β, hβ⟩ : ∃ β : M₁ → ℝ, ∀ x ∈ U, ∃ i, x ∈ T.coreSpace i ∧ β x = ε i ∧
      ∀ j, x ∈ T.coreSpace j → i ≤ j := by
    refine ⟨fun x => if hx : ∃ i, x ∈ T.coreSpace i then ε (Nat.find hx) else 1, ?_⟩
    intro x hx
    have hex : ∃ i, x ∈ T.coreSpace i := T.exists_mem_core_space hx
    exact ⟨Nat.find hex, Nat.find_spec hex, dif_pos hex,
      fun j hj => Nat.find_min' hex hj⟩
  have hclose' : ∀ i, ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < β x := by
    intro i x hxi
    obtain ⟨j, -, hβx, hmin⟩ := hβ x (T.core_space_subset_union i hxi)
    rw [hβx]
    exact (hclose i x hxi).trans_le (hεanti (hmin i hxi))
  have hunif : ∀ x ∈ U, ∃ i, x ∈ T.coreSpace i ∧ ∃ r : ℝ, 3 * β x < r ∧
      ∀ z ∈ U \ T.coreSpace i, r ≤ dist (h z) (h x) ∧ 3 * β z < r := by
    intro x hx
    obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
    refine ⟨i + 2, T.core_space_monotone (by omega) hxi, ρ i, ?_, fun z hz => ⟨?_, ?_⟩⟩
    · have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : 0 < ε i := hεpos i
      rw [hβx]
      linarith
    · exact hρsep i x hxi z hz
    · obtain ⟨k, hzk, hβz, -⟩ := hβ z hz.1
      have hik : i ≤ k := by
        by_contra hcon
        exact hz.2 (T.core_space_monotone (by omega) hzk)
      have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : ε k ≤ ε i := hεanti hik
      have h4 : 0 < ε k := hεpos k
      rw [hβz]
      linarith
  obtain ⟨g, hg, hgd⟩ := T.exists_isPLHomeomorphInto_of_stages hstep hstage hclose' hunif
  refine ⟨g, hg, fun x hx => (hgd x hx).trans ?_⟩
  obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
  have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
  have h2 : min (ρ i) (c i) ≤ c i := min_le_right _ _
  have h3 : c i ≤ φ x := hcle i x hxi
  have h4 : 0 < ε i := hεpos i
  rw [hβx]
  linarith

end Assembly

end LocallyFinitePieceTower

section Reduction

universe u

/-- The stagewise compact input to `Moise352`.

For a locally finite polyhedral manifold with boundary `K`, presented by a piece tower `T`,
and a topological embedding `h` of `K`, this asks for piecewise linear embeddings of the
*compact* stages `T.coreSpace i`, each agreeing with its predecessor on the previous stage
and approximating `h` on its own stage within a prescribed constant.  Every set occurring
in the conclusion is compact, and the error bounds are constants, so this is a statement
about the compact case together with a relative agreement clause; the variable continuous
error of `Moise352` does not appear. -/
def Moise352Stages (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ ε : ℕ → ℝ, (∀ i, 0 < ε i) → ∃ f : ℕ → M₁ → M₂,
      (∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) ∧
      (∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i)) ∧
      ∀ i, ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < ε i

/-- `Moise352` follows from its stagewise compact input.  All of the non-compact content —
passing to the limit of the stages, keeping injectivity, keeping the piecewise linear local
inverse, and converting the constant stagewise errors into the prescribed continuous
positive error — is carried out here. -/
theorem moise352_of_stages {n : ℕ} (H : Moise352Stages.{u} n) : Moise352.{u} n := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  obtain ⟨T, hT⟩ := hK
  exact T.exists_isPLHomeomorphInto_dist_lt_of_stages hh hφ hpos (H T hT hh)

end Reduction

end DifferentialGeometry.Topology.PiecewiseLinear
