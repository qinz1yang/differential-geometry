import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeDefs
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections

/-!
# Foot points of a finite-order slice are normal (lane CMS3-FLOW, S3-TUBE, G1)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §3 "S3-TUBE" (image and
calibration by a nearest point and the first variation, both directions; the CMS-T pattern
`inner_minimizingDirection_geodesicFlow_eq_zero`, `ClosedGeodesicTube.lean`, in any codimension).

* `exists_sliceCurve_ofOrder`: every vector of `sliceTangent I S s` (slice of order `k ≠ 0`) is the
  velocity at `0` of a curve that stays in `S` near `0`.
* `inner_minimizingDirection_sliceTangent_eq_zero`: at a nearest point `s ∈ S` to `y ≠ s`, every
  minimizing direction from `s` to `y` is `g`-orthogonal to `sliceTangent I S s`.
* `exists_normal_expMap_eq_infDist` (**main**): every point `x` is `exp v` for a normal vector `v` of
  `S` (compact, nonempty) of `g`-length `d_S x`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞}

/-- **Slice curves.** A tangent vector of a slice of order `k ≠ 0` is the velocity of a curve that
stays in the slice near `0` (both time directions). -/
theorem exists_sliceCurve_ofOrder (hk : k ≠ 0) {S : Set M} {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I k d S) {s : M} (hs : s ∈ S) {w : TangentSpace I s}
    (hw : w ∈ sliceTangent I S s) :
    ∃ γ : ℝ → M, γ 0 = s ∧ (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S) ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (w : E)) := by
  obtain ⟨c, A, hA, hsc, -, himage⟩ := hS s hs
  have hwA : (mfderiv I 𝓘(ℝ, E) c s w : E) ∈ A.direction :=
    (mem_sliceTangent_chart_iff_ofOrder hk hs hA hsc himage).1 hw
  set a : E := mfderiv I 𝓘(ℝ, E) c s w with ha
  have hsA : c s ∈ A := (himage.apply_mem_iff hsc).2 hs
  have hst : c s ∈ c.target := c.toPartialEquiv.map_source hsc
  set ℓ : ℝ → E := fun t => c s + t • a with hℓ
  have hℓd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ℓ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight a) := by
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (c s)).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hℓ0 : ℓ 0 = c s := by simp [hℓ]
  have hℓt : ∀ᶠ t in 𝓝 (0 : ℝ), ℓ t ∈ c.target := by
    refine hℓd.continuousAt.preimage_mem_nhds ?_
    rw [hℓ0]
    exact c.open_target.mem_nhds hst
  refine ⟨fun t => c.symm (ℓ t), ?_, ?_, ?_⟩
  · change c.symm (ℓ 0) = s
    rw [hℓ0]
    exact c.toPartialEquiv.left_inv hsc
  · filter_upwards [hℓt] with t ht
    have hsrc : c.symm (ℓ t) ∈ c.source := c.toPartialEquiv.map_target ht
    refine (himage.apply_mem_iff hsrc).1 ?_
    rw [show c (c.symm (ℓ t)) = ℓ t from c.toPartialEquiv.right_inv ht]
    have hmem : t • a +ᵥ c s ∈ A := A.vadd_mem_of_mem_direction (A.direction.smul_mem t hwA) hsA
    simpa [hℓ, vadd_eq_add, add_comm] using hmem
  · have hcs : HasMFDerivAt 𝓘(ℝ, E) I c.symm (ℓ 0) (mfderiv 𝓘(ℝ, E) I c.symm (c s)) := by
      rw [hℓ0]
      exact (c.symm.mdifferentiableAt hk hst).hasMFDerivAt
    refine (hcs.comp 0 hℓd).congr_mfderiv (ContinuousLinearMap.ext fun (t : ℝ) => ?_)
    change mfderiv 𝓘(ℝ, E) I c.symm (c s) (t • a) = t • (w : E)
    have h1 := mfderiv_symm_apply_mfderiv_ofOrder hk hsc w
    exact (map_smul (mfderiv 𝓘(ℝ, E) I c.symm (c s)) t a).trans
      (congrArg (fun z : E => t • z) h1)

end Curve

section Foot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Orthogonality at a nearest point of a slice** (first variation, both directions). -/
theorem inner_minimizingDirection_sliceTangent_eq_zero
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) {s y : M} (hs : s ∈ S)
    (hnear : ∀ s' ∈ S, dist s y ≤ dist s' y) (hy : s ≠ y) {u : E}
    (hu : u ∈ g.finiteMinimizingDirectionsTo {y} s) {w : TangentSpace I s}
    (hw : w ∈ sliceTangent I S s) :
    g.inner s u w = 0 := by
  have hk : ((r : ℕ∞) : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_two.trans hr)).ne'
  have key : ∀ X : TangentSpace I s, X ∈ sliceTangent I S s → g.inner s u X ≤ 0 := by
    intro X hX
    obtain ⟨γ, hγ0, hγS, hγ⟩ := exists_sliceCurve_ofOrder hk hS hs hX
    by_contra hpos
    rw [not_le] at hpos
    have hev := g.eventually_infDist_sub_le_finite_of_eq hr hnorm isClosed_singleton
      (singleton_nonempty y) hγ0 hγ (fun h => hy (mem_singleton_iff.mp h)) hu
      (c := -(g.inner s u X) / 2) (by linarith)
    obtain ⟨t, ⟨hs', hS'⟩, htpos⟩ :=
      ((hev.and (hγS.filter_mono nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
    rw [infDist_singleton, infDist_singleton] at hs'
    have ht : (0 : ℝ) < t := htpos
    have := hnear (γ t) hS'
    nlinarith
  have h1 := key w hw
  have h2 := key (-w) (Submodule.neg_mem _ hw)
  have hneg : g.inner s u (-w) = -g.inner s u w := map_neg _ _
  rw [hneg] at h2
  linarith

/-- **Every point is the exponential of a normal vector of length `d_S`** (nearest point and first
variation). -/
theorem exists_normal_expMap_eq_infDist [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) (x : M) :
    ∃ v ∈ normalSetFinite g S, g.expMap v = x ∧
      Real.sqrt (g.inner v.proj v.snd v.snd) = infDist x S := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨s, hs, hds⟩ := hSc.exists_infDist_eq_dist hSne x
  by_cases hsx : s = x
  · subst hsx
    refine ⟨⟨s, 0⟩, zero_mem_normalSetFinite g hs, g.expMap_zero hr1 s, ?_⟩
    change Real.sqrt (g.inner s 0 0) = infDist s S
    rw [map_zero, Real.sqrt_zero, infDist_zero_of_mem hs]
  obtain ⟨u, hu⟩ := (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
    (singleton_nonempty x) s).1
  have hnear : ∀ s' ∈ S, dist s x ≤ dist s' x := by
    intro s' hs'
    rw [dist_comm s x, ← hds, dist_comm]
    exact infDist_le_dist_of_mem hs'
  set δ : ℝ := dist s x with hδ
  refine ⟨⟨s, δ • u⟩, ⟨hs, fun w hw => ?_⟩, ?_, ?_⟩
  · change g.inner s (δ • u) w = 0
    rw [map_smul, smul_apply,
      inner_minimizingDirection_sliceTangent_eq_zero g hr hnorm hS hs hnear hsx hu hw, smul_zero]
  · have h := hu.2
    rw [infDist_singleton] at h
    exact h
  · change Real.sqrt (g.inner s (δ • u) (δ • u)) = infDist x S
    have hu1 : g.inner s u u = 1 := hu.1
    rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g s δ u, hu1, mul_one,
      Real.sqrt_sq dist_nonneg, hds, dist_comm]

end Foot

end DifferentialGeometry.Geometry.FiniteSoul
