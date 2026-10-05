import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimQuadrantProducer
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# FC42 packet G1: interior / boundary image criteria and the half-space normal form

Lane ASM-CYC2, review 40 §3.4 and §4.1 (packet G1). For a smooth map `F : M → W` of a
three-dimensional manifold with corners `M` (model `I`, any convex model range) with bijective
differential everywhere:

* **interior criterion** `map_mem_interior_range_of_isInteriorPoint`: a model-interior point maps
  to an ambient interior point of the image (inverse function theorem at interior points);
* **boundary criterion** `not_mem_interior_range_of_isBoundaryPoint`: if `M` is compact, `F`
  injective and `q` a model-boundary point with `F q ∈ W.interior`, then `F q` is NOT in the ambient
  interior of `range F`. The restriction to `W.interior` matters (`P = W` is a counterexample
  otherwise). Proof: a supporting functional `ℓ` of the convex model range at the chart point
  (Hahn–Banach), the exterior estimate `halfSpace_exterior_estimate` (only differentiability within
  the model range is used, so corners are allowed), the points `ψ (F q) - s • A n` and the closed
  embedding `F`;
* **half-space normal form (entering cone)** `exists_entering_of_halfSpace`: at a point whose chart
  image is a half-space boundary point of the model range (`range I = {ℓ ≥ 0}` near it), there is a
  nonzero functional `κ` on the ambient chart such that every point of the cone
  `κ (y - y₀) > ε ‖y - y₀‖` near `y₀` is (in the chart) an ambient interior point of `range F`.

The Banach-level kernels are `halfSpace_cone_estimate`, `halfSpace_exterior_estimate` and
`halfSpace_entering` (the last one adapts the Lipschitz extension of
`Analysis/Calculus/Inverse/HalfSpaceLocalOnto.lean`: no target half-space is assumed).
Instances: `PieceFold` (vertex pieces, `𝓡∂ 3`) at model boundary points; `EdgeHandle` at vertical
points (rim × open interval) and at end-disk points (open disk × end).

Check of the tree (exists / new): the interior criterion is the core of
`exists_mem_inter_interior_range` (`AssemblyRimQuadrantProducer.lean`), restated pointwise; the
boundary criterion and the entering cone are NEW (`BoundaryLocalInverse.lean` needs a
smooth-boundary model and `C^∞` data; `HalfSpaceLocalOnto.lean` needs a target half-space).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology NNReal

universe u

namespace GC.GraphManifold.Assembly

section Banach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The basic estimate behind both cone statements: if `‖d - A v‖ ≤ c ‖v‖` with `‖A⁻¹‖ c ≤ 1/2`,
then `‖v‖ ≤ 2 ‖A⁻¹‖ ‖d‖` and `|ℓ (A⁻¹ d) - ℓ v| ≤ 2 ‖ℓ‖ ‖A⁻¹‖² c ‖d‖`. -/
theorem halfSpace_cone_estimate {ℓ : E →L[ℝ] ℝ} {A : E ≃L[ℝ] F} {v : E} {d : F} {c : ℝ}
    (hc : 0 ≤ c) (hNc : ‖(A.symm : F →L[ℝ] E)‖ * c ≤ 1 / 2)
    (hd : ‖d - (A : E →L[ℝ] F) v‖ ≤ c * ‖v‖) :
    ‖v‖ ≤ 2 * ‖(A.symm : F →L[ℝ] E)‖ * ‖d‖ ∧
      |ℓ (A.symm d) - ℓ v| ≤ 2 * ‖ℓ‖ * ‖(A.symm : F →L[ℝ] E)‖ ^ 2 * c * ‖d‖ := by
  set N := ‖(A.symm : F →L[ℝ] E)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set e : F := d - (A : E →L[ℝ] F) v with he
  have hsplit : A.symm d = v + A.symm e := by
    simp only [he, map_sub, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hAe : ‖A.symm e‖ ≤ N * ‖e‖ := (A.symm : F →L[ℝ] E).le_opNorm e
  have hAd : ‖A.symm d‖ ≤ N * ‖d‖ := (A.symm : F →L[ℝ] E).le_opNorm d
  have hv : ‖v‖ ≤ 2 * N * ‖d‖ := by
    have h1 : v = A.symm d - A.symm e := by rw [hsplit]; abel
    have h2 : ‖v‖ ≤ ‖A.symm d‖ + ‖A.symm e‖ := by rw [h1]; exact norm_sub_le _ _
    have h3 : N * ‖e‖ ≤ N * (c * ‖v‖) := mul_le_mul_of_nonneg_left hd hN0
    have h4 : N * (c * ‖v‖) ≤ 1 / 2 * ‖v‖ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hNc (norm_nonneg _)
    linarith
  refine ⟨hv, ?_⟩
  have hdiff : ℓ (A.symm d) - ℓ v = ℓ (A.symm e) := by rw [hsplit, map_add]; ring
  rw [hdiff]
  calc |ℓ (A.symm e)| = ‖ℓ (A.symm e)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ℓ‖ * ‖A.symm e‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (N * (c * ‖v‖)) := by
        gcongr
        exact hAe.trans (mul_le_mul_of_nonneg_left hd hN0)
    _ ≤ ‖ℓ‖ * (N * (c * (2 * N * ‖d‖))) := by gcongr
    _ = 2 * ‖ℓ‖ * N ^ 2 * c * ‖d‖ := by ring

/-- **Exterior estimate.** Let `ℓ` support a set `Q` at `x₀` (`ℓ x₀ ≤ ℓ` on `Q`) and let `f` be
differentiable within `Q` at `x₀` with invertible derivative `A`. Then near `x₀` inside `Q`, the
values of `f` lie in the cone `ℓ (A⁻¹ (f x - f x₀)) ≥ -ε ‖f x - f x₀‖`. -/
theorem halfSpace_exterior_estimate {Q : Set E} {ℓ : E →L[ℝ] ℝ} {f : E → F} {A : E ≃L[ℝ] F}
    {x₀ : E} (hQ : ∀ z ∈ Q, ℓ x₀ ≤ ℓ z) (hf : HasFDerivWithinAt f (A : E →L[ℝ] F) Q x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Q] x₀, -(ε * ‖f x - f x₀‖) ≤ ℓ (A.symm (f x - f x₀)) := by
  set N := ‖(A.symm : F →L[ℝ] E)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set η : ℝ := min (1 / (2 * N + 1)) (ε / (2 * ‖ℓ‖ * N ^ 2 + 1)) with hη
  have hl0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hNη : N * η ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * N + 1) := min_le_left _ _
    have h2 : N * η ≤ N * (1 / (2 * N + 1)) := mul_le_mul_of_nonneg_left h1 hN0
    have h3 : N * (1 / (2 * N + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hηε : 2 * ‖ℓ‖ * N ^ 2 * η ≤ ε := by
    have h1 : η ≤ ε / (2 * ‖ℓ‖ * N ^ 2 + 1) := min_le_right _ _
    have h2 : η * (2 * ‖ℓ‖ * N ^ 2 + 1) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  filter_upwards [hf.isLittleO.def hηpos, self_mem_nhdsWithin] with x hx hxQ
  have hd : ‖(f x - f x₀) - (A : E →L[ℝ] F) (x - x₀)‖ ≤ η * ‖x - x₀‖ := hx
  obtain ⟨-, hest⟩ := halfSpace_cone_estimate (ℓ := ℓ) hηpos.le hNη hd
  have hℓx : 0 ≤ ℓ (x - x₀) := by rw [map_sub]; linarith [hQ x hxQ]
  have hlow := (abs_le.mp hest).1
  have hεd : 2 * ‖ℓ‖ * N ^ 2 * η * ‖f x - f x₀‖ ≤ ε * ‖f x - f x₀‖ :=
    mul_le_mul_of_nonneg_right hηε (norm_nonneg _)
  linarith

variable [CompleteSpace E]

/-- **Entering cone at a half-space boundary point.** Let `S = {ℓ ≥ 0}` near `x₀` (`ℓ x₀ = 0`,
`ℓ n = 1`), let `f` be differentiable within `S ∩ O` with derivative `f'` continuous within
`S ∩ O` at `x₀` and invertible there (`f' x₀ = A`). For every `ε > 0`, every `y` near `f x₀` in the
cone `ℓ (A⁻¹ (y - f x₀)) > ε ‖y - f x₀‖` is a value `f x` at a point `x ∈ O` with `ℓ x > 0`.
Proof: the Lipschitz extension `G x = f (π x) + min (ℓ x) 0 • A n` (`π` the projection onto `S`
along `n`) approximates `A` on a small ball (as in `HalfSpaceLocalOnto.lean`), hence is onto a
ball around `f x₀`; the quantitative estimate `halfSpace_cone_estimate` puts the preimage of a cone
point inside `{ℓ > 0}`, where `G = f`. -/
theorem halfSpace_entering {ℓ : E →L[ℝ] ℝ} {n : E} (hn : ℓ n = 1) {f : E → F}
    {f' : E → E →L[ℝ] F} {A : E ≃L[ℝ] F} {O : Set E} {x₀ : E} (hO : IsOpen O) (hx₀O : x₀ ∈ O)
    (hx₀ : ℓ x₀ = 0) (hf : ∀ x ∈ O, 0 ≤ ℓ x → HasFDerivWithinAt f (f' x) ({x | 0 ≤ ℓ x} ∩ O) x)
    (hf' : ContinuousWithinAt f' ({x | 0 ≤ ℓ x} ∩ O) x₀) (hA : f' x₀ = A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (f x₀), ε * ‖y - f x₀‖ < ℓ (A.symm (y - f x₀)) →
      ∃ x ∈ O, 0 < ℓ x ∧ f x = y := by
  set S : Set E := {x | 0 ≤ ℓ x} with hS
  have hSc : Convex ℝ S := convex_halfSpace_ge (ℓ : E →ₗ[ℝ] ℝ).isLinear 0
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  set N : ℝ := ‖(A.symm : F →L[ℝ] E)‖ with hN
  have hNpos : 0 < N := by
    refine norm_pos_iff.mpr fun h => hn0 ?_
    have := congrArg (fun L : F →L[ℝ] E => L (A n)) h
    simpa using this
  have hl0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  set L : ℝ := 1 + ‖ℓ‖ * ‖n‖ with hL
  have hL1 : 1 ≤ L := by have := mul_nonneg (norm_nonneg ℓ) (norm_nonneg n); linarith
  have hLpos : 0 < L := by linarith
  set c : ℝ := min (N⁻¹ / 2) (ε / (2 * ‖ℓ‖ * N ^ 2 + 1)) with hc
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcN : c ≤ N⁻¹ / 2 := min_le_left _ _
  have hNc : N * c ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hcN hNpos.le
    rwa [mul_div_assoc', mul_inv_cancel₀ hNpos.ne'] at h
  have hcε : 2 * ‖ℓ‖ * N ^ 2 * c ≤ ε := by
    have h1 : c ≤ ε / (2 * ‖ℓ‖ * N ^ 2 + 1) := min_le_right _ _
    have h2 : c * (2 * ‖ℓ‖ * N ^ 2 + 1) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set ε' : ℝ := c / L with hε'
  have hε'pos : 0 < ε' := by positivity
  -- a radius on which the derivative is `ε'`-close to `A` and which lies in `O`
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.mp hO x₀ hx₀O
  obtain ⟨r₁, hr₁, hr₁d⟩ := Metric.continuousWithinAt_iff.mp hf' ε' hε'pos
  set r' : ℝ := min r₀ r₁ with hr'
  have hr'pos : 0 < r' := lt_min hr₀ hr₁
  have hballO : ball x₀ r' ⊆ O := (ball_subset_ball (min_le_left _ _)).trans hr₀O
  have hmv : ∀ x ∈ S ∩ ball x₀ r', ∀ y ∈ S ∩ ball x₀ r',
      ‖f y - f x - (A : E →L[ℝ] F) (y - x)‖ ≤ ε' * ‖y - x‖ := by
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f' := f') (φ := (A : E →L[ℝ] F))
      (fun z hz => (hf z (hballO hz.2) hz.1).mono
        (fun w hw => ⟨hw.1, hballO hw.2⟩)) (fun z hz => ?_)
      (hSc.inter (convex_ball x₀ r')) hx hy
    rw [← hA, ← dist_eq_norm]
    exact (hr₁d ⟨hz.1, hballO hz.2⟩ (lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_right _ _))).le
  -- the projection onto `S` and the extension
  let π : E → E := fun x => x - min (ℓ x) 0 • n
  have hπℓ : ∀ x, ℓ (π x) = max (ℓ x) 0 := by
    intro x
    simp only [π, map_sub, map_smul, hn, smul_eq_mul, mul_one]
    rcases le_total (ℓ x) 0 with h | h
    · rw [min_eq_left h, max_eq_right h, sub_self]
    · rw [min_eq_right h, max_eq_left h, sub_zero]
  have hπS : ∀ x, π x ∈ S := fun x => by
    change 0 ≤ ℓ (π x)
    rw [hπℓ]
    exact le_max_right _ _
  have hπlip : ∀ x y, ‖π x - π y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have hmin : |min (ℓ x) 0 - min (ℓ y) 0| ≤ ‖ℓ‖ * ‖x - y‖ := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← map_sub]
      exact (Real.norm_eq_abs _).symm.le.trans (ℓ.le_opNorm _)
    have heq : π x - π y = (x - y) - (min (ℓ x) 0 - min (ℓ y) 0) • n := by
      simp only [π, sub_smul]
      abel
    rw [heq]
    calc ‖(x - y) - (min (ℓ x) 0 - min (ℓ y) 0) • n‖
        ≤ ‖x - y‖ + |min (ℓ x) 0 - min (ℓ y) 0| * ‖n‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ + ‖ℓ‖ * ‖x - y‖ * ‖n‖ := by gcongr
      _ = L * ‖x - y‖ := by rw [hL]; ring
  have hπx₀ : π x₀ = x₀ := by simp [π, hx₀]
  set r : ℝ := r' / L with hr
  have hrpos : 0 < r := by positivity
  have hπball : ∀ x ∈ ball x₀ r, π x ∈ ball x₀ r' := by
    intro x hx
    rw [mem_ball, dist_eq_norm, ← hπx₀]
    calc ‖π x - π x₀‖ ≤ L * ‖x - x₀‖ := hπlip x x₀
      _ < L * r := by
          gcongr
          rw [← dist_eq_norm]
          exact mem_ball.mp hx
      _ = r' := by rw [hr]; field_simp
  have hrr' : r ≤ r' := by
    rw [hr, div_le_iff₀ hLpos]
    nlinarith
  let G : E → F := fun x => f (π x) + min (ℓ x) 0 • (A : E →L[ℝ] F) n
  have hGx₀ : G x₀ = f x₀ := by simp [G, hπx₀, hx₀]
  have happrox : ApproximatesLinearOn G (A : E →L[ℝ] F) (ball x₀ r) ⟨c, hcpos.le⟩ := by
    intro x hx y hy
    have hAxy : (A : E →L[ℝ] F) (x - y) = (A : E →L[ℝ] F) (π x - π y) +
        (min (ℓ x) 0 - min (ℓ y) 0) • (A : E →L[ℝ] F) n := by
      rw [← map_smul, ← map_add]
      congr 1
      simp only [π, sub_smul]
      abel
    have hkey : G x - G y - (A : E →L[ℝ] F) (x - y) =
        f (π x) - f (π y) - (A : E →L[ℝ] F) (π x - π y) := by
      rw [hAxy]
      simp only [G, sub_smul]
      abel
    rw [hkey]
    change _ ≤ c * ‖x - y‖
    calc ‖f (π x) - f (π y) - (A : E →L[ℝ] F) (π x - π y)‖ ≤ ε' * ‖π x - π y‖ :=
          hmv _ ⟨hπS y, hπball y hy⟩ _ ⟨hπS x, hπball x hx⟩
      _ ≤ ε' * (L * ‖x - y‖) := by gcongr; exact hπlip x y
      _ = c * ‖x - y‖ := by rw [hε']; field_simp
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hsub : closedBall x₀ ρ ⊆ ball x₀ r := closedBall_subset_ball (by linarith)
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse A.toNonlinearRightInverse
    hρpos.le hsub
  change SurjOn G (closedBall x₀ ρ) (closedBall (G x₀) ((N⁻¹ - c) * ρ)) at hsurj
  rw [hGx₀] at hsurj
  have hκ : 0 < (N⁻¹ - c) * ρ := by
    have : 0 < N⁻¹ - c := by linarith [inv_pos.mpr hNpos]
    positivity
  filter_upwards [ball_mem_nhds (f x₀) hκ] with y hyb hcone
  obtain ⟨x, hx, hGx⟩ := hsurj (ball_subset_closedBall hyb)
  have hxr : x ∈ ball x₀ r := hsub hx
  have hxO : x ∈ O := hballO (ball_subset_ball hrr' hxr)
  have hx₀r : x₀ ∈ ball x₀ r := mem_ball_self hrpos
  have hd : ‖(y - f x₀) - (A : E →L[ℝ] F) (x - x₀)‖ ≤ c * ‖x - x₀‖ := by
    have h := happrox x hxr x₀ hx₀r
    rw [hGx, hGx₀] at h
    exact h
  obtain ⟨-, hest⟩ := halfSpace_cone_estimate (ℓ := ℓ) hcpos.le hNc hd
  have hlow := (abs_le.mp hest).2
  have hcd : 2 * ‖ℓ‖ * N ^ 2 * c * ‖y - f x₀‖ ≤ ε * ‖y - f x₀‖ :=
    mul_le_mul_of_nonneg_right hcε (norm_nonneg _)
  have hℓx : 0 < ℓ x := by
    have : 0 < ℓ (x - x₀) := by linarith
    rwa [map_sub, hx₀, sub_zero] at this
  refine ⟨x, hxO, hℓx, ?_⟩
  rw [← hGx]
  simp [G, π, min_eq_right hℓx.le]

end Banach

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {W : CompactCarrier.{u}} {F : M → W.Carrier}

omit [IsManifold I ∞ M] in
/-- The differential of a full-rank map, as a continuous linear equivalence. -/
theorem exists_continuousLinearEquiv_mfderiv (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    (q : M) : ∃ A : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
      (A : E →L[ℝ] EuclideanSpace ℝ (Fin 3)) = mfderiv I W.model F q :=
  ⟨(LinearEquiv.ofBijective ((show E →L[ℝ] EuclideanSpace ℝ (Fin 3) from
      mfderiv I W.model F q) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) (hbij q)).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ => rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The chart expression of a smooth map is differentiable within the model range, with derivative
the manifold derivative. -/
theorem hasFDerivWithinAt_writtenInExtChartAt (hF : ContMDiff I W.model ∞ F) (q : M) :
    HasFDerivWithinAt (writtenInExtChartAt I W.model q F) (mfderiv I W.model F q) (range I)
      (extChartAt I q q) := by
  have h := hF.mdifferentiableAt (x := q) (by simp)
  rw [h.mfderiv_abuse]
  exact h.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem writtenInExtChartAt_self (q : M) :
    writtenInExtChartAt I W.model q F (extChartAt I q q) = extChartAt W.model (F q) (F q) := by
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- A neighbourhood of the chart point on which the chart expression is defined. -/
theorem exists_isOpen_chart_nhds (hF : Continuous F) (q : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I q q ∈ V ∧ ∀ x ∈ V ∩ range I,
      x ∈ (extChartAt I q).target ∧
        F ((extChartAt I q).symm x) ∈ (extChartAt W.model (F q)).source := by
  have h1 : (extChartAt I q).target ∈ 𝓝[range I] (extChartAt I q q) :=
    extChartAt_target_mem_nhdsWithin q
  have h2 : (extChartAt I q).symm ⁻¹' (F ⁻¹' (extChartAt W.model (F q)).source) ∈
      𝓝 (extChartAt I q q) :=
    extChartAt_preimage_mem_nhds (((isOpen_extChartAt_source (F q)).preimage hF).mem_nhds
      (mem_extChartAt_source (F q)))
  obtain ⟨V, hV, hqV, hVsub⟩ := mem_nhdsWithin.mp (inter_mem h1 (mem_nhdsWithin_of_mem_nhds h2))
  exact ⟨V, hV, hqV, fun x hx => hVsub hx⟩

/-- **Interior criterion.** A model-interior point is mapped to an ambient interior point of the
image. -/
theorem map_mem_interior_range_of_isInteriorPoint (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) {q : M}
    (hq : I.IsInteriorPoint q) : F q ∈ interior (range F) := by
  have hint : W.model.IsInteriorPoint (F q) :=
    (hF.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv (hbij q).2 hq
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [hdim, finrank_euclideanSpace_fin]
  have hnhds := GC.Seifert.image_mem_nhds_of_mfderiv_injective hF hq hint (hbij q).1 hdim'
    Filter.univ_mem
  rw [image_univ] at hnhds
  exact mem_interior_iff_mem_nhds.mpr hnhds

/-- A chart point in the interior of the model range, inside the chart domain, is mapped (through
the chart expression and back) to an ambient interior point of the image. -/
theorem symm_writtenInExtChartAt_mem_interior_range (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) {q : M}
    {x : E} (hxT : x ∈ (extChartAt I q).target)
    (hxS : F ((extChartAt I q).symm x) ∈ (extChartAt W.model (F q)).source)
    (hxI : x ∈ interior (range I)) :
    (extChartAt W.model (F q)).symm (writtenInExtChartAt I W.model q F x) ∈
      interior (range F) := by
  have hm : (extChartAt I q).symm x ∈ (chartAt H q).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I q).map_target hxT
  have heq : (extChartAt W.model (F q)).symm (writtenInExtChartAt I W.model q F x) =
      F ((extChartAt I q).symm x) := by
    simp only [writtenInExtChartAt, Function.comp_apply]
    exact (extChartAt W.model (F q)).left_inv hxS
  rw [heq]
  apply map_mem_interior_range_of_isInteriorPoint hdim hF hbij
  rw [I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H q) hm]
  change extChartAt I q ((extChartAt I q).symm x) ∈ interior (extChartAt I q).target
  rw [(extChartAt I q).right_inv hxT, extChartAt_target, interior_inter]
  refine ⟨?_, ?_⟩
  · have hopen : IsOpen (I.symm ⁻¹' (chartAt H q).target) :=
      (chartAt H q).open_target.preimage I.continuous_symm
    rw [hopen.interior_eq]
    rw [extChartAt_target] at hxT
    exact hxT.1
  · exact hxI

omit [FiniteDimensional ℝ E] in
/-- A supporting functional of the (convex, closed, solid) model range at a frontier point. -/
theorem exists_support_of_mem_frontier_range {x₀ : E} (hx : x₀ ∈ frontier (range I)) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ z ∈ range I, ℓ x₀ ≤ ℓ z := by
  have hconv : Convex ℝ (interior (range I)) := I.convex_range.interior
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv isOpen_interior hx.2
  obtain ⟨a, ha⟩ := I.nonempty_interior
  refine ⟨-f, fun h => ?_, fun z hz => ?_⟩
  · have h' : f = 0 := neg_eq_zero.mp h
    have := hf a ha
    simp [h'] at this
  · have hz' : z ∈ closure (interior (range I)) := by
      rw [I.convex_range.closure_interior_eq_closure_of_nonempty_interior I.nonempty_interior]
      exact subset_closure hz
    have hcl : closure (interior (range I)) ⊆ {a | f a ≤ f x₀} :=
      closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
    have := hcl hz'
    simpa using this

omit [IsManifold I ∞ M] in
/-- **Boundary criterion.** For an injective full-rank map of a compact manifold with corners, the
image of a model-boundary point lying in `W.interior` is not an ambient interior point of the
image. -/
theorem not_mem_interior_range_of_isBoundaryPoint [CompactSpace M]
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    (hinj : Injective F) {q : M} (hq : I.IsBoundaryPoint q) (hqW : F q ∈ W.interior) :
    F q ∉ interior (range F) := by
  intro hint
  set φ := extChartAt I q with hφ
  set ψ := extChartAt W.model (F q) with hψ
  set g := writtenInExtChartAt I W.model q F with hg
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_support_of_mem_frontier_range (I := I) hq
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_mfderiv hbij q
  have hd : HasFDerivWithinAt g (A : E →L[ℝ] EuclideanSpace ℝ (Fin 3)) (range I) (φ q) := by
    rw [hA]
    exact hasFDerivWithinAt_writtenInExtChartAt hF q
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    apply hℓ0
    ext v
    by_contra hv
    exact h ⟨v, by simpa using hv⟩
  set nn : E := (ℓ v)⁻¹ • v with hnn_def
  have hnn : ℓ nn = 1 := by simp [nn, hv]
  set w := A nn with hw
  set ε : ℝ := 1 / (2 * (‖w‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hext := halfSpace_exterior_estimate (Q := range I) (f := g) (fun z hz => hℓ z hz) hd hε
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hext
  have hVq : φ.source ∩ φ ⁻¹' V ∈ 𝓝 q :=
    inter_mem (extChartAt_source_mem_nhds q) ((continuousAt_extChartAt q).preimage_mem_nhds hV)
  have hemb := (hF.continuous.isClosedEmbedding hinj).isEmbedding
  rw [hemb.isInducing.nhds_eq_comap] at hVq
  obtain ⟨G, hG, hGsub⟩ := Filter.mem_comap.mp hVq
  have hK : G ∩ interior (range F) ∩ ψ.source ∈ 𝓝 (F q) :=
    inter_mem (inter_mem hG (isOpen_interior.mem_nhds hint)) (extChartAt_source_mem_nhds (F q))
  have hK' : ψ.symm ⁻¹' (G ∩ interior (range F) ∩ ψ.source) ∈ 𝓝 (ψ (F q)) :=
    extChartAt_preimage_mem_nhds hK
  have htarget : ψ.target ∈ 𝓝 (ψ (F q)) :=
    mem_interior_iff_mem_nhds.mp ((W.model.isInteriorPoint_iff (x := F q)).mp hqW)
  have hpath : Tendsto (fun s : ℝ => ψ (F q) - s • w) (𝓝[>] 0) (𝓝 (ψ (F q))) := by
    have hc : Continuous (fun s : ℝ => ψ (F q) - s • w) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_smul, sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨s, ⟨hsK, hsT⟩, hs⟩ :=
    ((hpath.eventually (inter_mem hK' htarget)).and self_mem_nhdsWithin).exists
  have hs0 : 0 < s := hs
  obtain ⟨⟨hzG, hzint⟩, -⟩ := hsK
  obtain ⟨m, hm⟩ := interior_subset hzint
  have hmV : m ∈ φ.source ∩ φ ⁻¹' V := hGsub (show F m ∈ G by rw [hm]; exact hzG)
  have hφm : φ m ∈ V ∩ range I :=
    ⟨hmV.2, extChartAt_target_subset_range q (φ.map_source hmV.1)⟩
  have hgm : g (φ m) = ψ (F q) - s • w := by
    have h1 : g (φ m) = ψ (F m) := by
      change ψ (F (φ.symm (φ m))) = ψ (F m)
      rw [φ.left_inv hmV.1]
    rw [h1, hm]
    exact ψ.right_inv hsT
  have hgq : g (φ q) = ψ (F q) := writtenInExtChartAt_self q
  have hest : -(ε * ‖g (φ m) - g (φ q)‖) ≤ ℓ (A.symm (g (φ m) - g (φ q))) := hVsub hφm
  rw [hgm, hgq] at hest
  have hsub : ψ (F q) - s • w - ψ (F q) = -(s • w) := by abel
  have h1 : ‖ψ (F q) - s • w - ψ (F q)‖ = s * ‖w‖ := by
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have h2 : ℓ (A.symm (ψ (F q) - s • w - ψ (F q))) = -s := by
    rw [hsub]
    simp [w, hnn]
  rw [h1, h2] at hest
  have hw1 : ε * ‖w‖ < 1 := by
    rw [hε_def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith [norm_nonneg w]
  nlinarith

/-- **Half-space normal form (entering cone).** At a point whose chart image is a boundary point of
a local half-space `{ℓ ≥ 0}` of the model range, there is a nonzero functional `κ` on the ambient
chart such that, for every `ε > 0`, the points `y` near `y₀ = ψ (F q)` with
`κ (y - y₀) > ε ‖y - y₀‖` are (through the chart) ambient interior points of `range F`. -/
theorem exists_entering_of_halfSpace (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) {q : M}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {O : Set E} (hO : IsOpen O) (hqO : extChartAt I q q ∈ O)
    (hℓq : ℓ (extChartAt I q q) = 0) (hrange : range I ∩ O = {x | 0 ≤ ℓ x} ∩ O) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (F q) (F q)),
        ε * ‖y - extChartAt W.model (F q) (F q)‖ < κ (y - extChartAt W.model (F q) (F q)) →
          (extChartAt W.model (F q)).symm y ∈ interior (range F) := by
  set φ := extChartAt I q with hφ
  set ψ := extChartAt W.model (F q) with hψ
  set g := writtenInExtChartAt I W.model q F with hg
  set x₀ := φ q with hx₀
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_mfderiv hbij q
  have hx₀I : x₀ ∈ range I := extChartAt_target_subset_range q (mem_extChartAt_target q)
  -- `C¹` data of the chart expression near `x₀` within the model range
  have hcd : ContDiffWithinAt ℝ ∞ g (range I) x₀ := (contMDiffAt_iff.mp (hF q)).2
  obtain ⟨u, hu, hx₀u, hgu⟩ := hcd.contDiffOn' (m := 1) (by exact_mod_cast le_top) (by simp)
  rw [insert_eq_of_mem hx₀I] at hgu
  have hT : UniqueDiffOn ℝ (range I ∩ u) := I.uniqueDiffOn.inter hu
  -- the chart domains
  obtain ⟨V, hVo, hx₀V, hVsub⟩ := exists_isOpen_chart_nhds (I := I) hF.continuous q
  set O' := u ∩ O ∩ V with hO'
  have hO'o : IsOpen O' := (hu.inter hO).inter hVo
  have hx₀O' : x₀ ∈ O' := ⟨⟨hx₀u, hqO⟩, hx₀V⟩
  have hmemI : ∀ x ∈ O', (x ∈ range I ↔ 0 ≤ ℓ x) := by
    intro x hx
    have h := Set.ext_iff.mp hrange x
    simp only [mem_inter_iff, mem_ofPred_eq] at h
    constructor
    · intro hxI
      exact (h.mp ⟨hxI, hx.1.2⟩).1
    · intro hℓx
      exact (h.mpr ⟨hℓx, hx.1.2⟩).1
  have hSO' : {x | 0 ≤ ℓ x} ∩ O' ⊆ range I ∩ u := fun x hx =>
    ⟨(hmemI x hx.2).mpr hx.1, hx.2.1.1⟩
  have hf : ∀ x ∈ O', 0 ≤ ℓ x →
      HasFDerivWithinAt g (fderivWithin ℝ g (range I ∩ u) x) ({x | 0 ≤ ℓ x} ∩ O') x := by
    intro x hx hℓx
    exact ((hgu.differentiableOn one_ne_zero x (hSO' ⟨hℓx, hx⟩)).hasFDerivWithinAt).mono hSO'
  have hf' : ContinuousWithinAt (fderivWithin ℝ g (range I ∩ u)) ({x | 0 ≤ ℓ x} ∩ O') x₀ :=
    (hgu.continuousOn_fderivWithin hT le_rfl x₀ ⟨hx₀I, hx₀u⟩).mono hSO'
  have hA' : fderivWithin ℝ g (range I ∩ u) x₀ = A := by
    rw [fderivWithin_inter (hu.mem_nhds hx₀u), hA]
    exact ((hF.mdifferentiableAt (x := q) (by simp)).mfderiv_abuse).symm
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    apply hℓ
    ext v
    by_contra hv
    exact h ⟨v, by simpa using hv⟩
  set nn : E := (ℓ v)⁻¹ • v with hnn_def
  have hnn : ℓ nn = 1 := by simp [nn, hv]
  refine ⟨ℓ.comp (A.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] E), fun h => ?_, fun ε hε => ?_⟩
  · have := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L (A nn)) h
    simp [hnn] at this
  · have hent := halfSpace_entering hnn hO'o hx₀O' hℓq hf hf' hA' hε
    rw [show g x₀ = ψ (F q) from writtenInExtChartAt_self q] at hent
    filter_upwards [hent] with y hy hcone
    obtain ⟨x, hxO', hℓx, hgx⟩ := hy (by simpa using hcone)
    have hxI : x ∈ range I := (hmemI x hxO').mpr hℓx.le
    obtain ⟨hxT, hxS⟩ := hVsub x ⟨hxO'.2, hxI⟩
    have hxint : x ∈ interior (range I) := by
      refine interior_maximal (t := {x | 0 < ℓ x} ∩ O') (fun z hz => ?_)
        ((isOpen_lt continuous_const ℓ.continuous).inter hO'o) ⟨hℓx, hxO'⟩
      exact (hmemI z hz.2).mpr hz.1.le
    rw [← hgx]
    exact symm_writtenInExtChartAt_mem_interior_range hdim hF hbij hxT hxS hxint

end Manifold

/-! ## The certificate pieces: vertex pieces (`𝓡∂ 3`) and product disk handles -/

section Pieces

local instance diskChartsG1_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothG1_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}}

/-- The first coordinate of a model-boundary point of a half-space manifold vanishes. -/
theorem extChartAt_coord_eq_zero_of_isBoundaryPoint {m : ℕ} [NeZero m] {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace m) X] {q : X}
    (hq : (𝓡∂ m).IsBoundaryPoint q) : extChartAt (𝓡∂ m) q q 0 = 0 := by
  have h := hq
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace] at h
  exact h.symm

/-- The first coordinate of a model-interior point of a half-space manifold is positive. -/
theorem extChartAt_coord_pos_of_isInteriorPoint {m : ℕ} [NeZero m] {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace m) X] {q : X}
    (hq : (𝓡∂ m).IsInteriorPoint q) : 0 < extChartAt (𝓡∂ m) q q 0 := by
  have h := hq
  rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace] at h
  exact h

theorem euclideanSpace_proj_ne_zero {m : ℕ} (i : Fin m) :
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) ≠ 0 := by
  intro h
  have := congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) h
  simp at this

/-- **Interior criterion for a piece.** -/
theorem PieceFold.map_mem_interior_range (P : PieceFold W) {q : P.Piece}
    (hq : (𝓡∂ 3).IsInteriorPoint q) : P.map q ∈ interior (range P.map) :=
  map_mem_interior_range_of_isInteriorPoint finrank_euclideanSpace_fin P.smooth
    P.mfderiv_bijective hq

/-- **Boundary criterion for an injective piece.** -/
theorem PieceEmbedding.map_not_mem_interior_range (P : PieceEmbedding W) {q : P.Piece}
    (hq : (𝓡∂ 3).IsBoundaryPoint q) (hqW : P.map q ∈ W.interior) :
    P.map q ∉ interior (range P.map) :=
  not_mem_interior_range_of_isBoundaryPoint P.smooth P.mfderiv_bijective P.injective hq hqW

/-- For an injective piece and a point of `W.interior` in its image: the point is an ambient
interior point of the image iff it is the image of a model-interior point. -/
theorem PieceEmbedding.map_mem_interior_range_iff {P : PieceEmbedding W} {q : P.Piece}
    (hqW : P.map q ∈ W.interior) :
    P.map q ∈ interior (range P.map) ↔ (𝓡∂ 3).IsInteriorPoint q := by
  refine ⟨fun h => ?_, P.map_mem_interior_range⟩
  rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
  exact fun hb => P.map_not_mem_interior_range hb hqW h

/-- **Half-space normal form for a piece** at a model-boundary point. -/
theorem PieceFold.exists_entering (P : PieceFold W) {q : P.Piece}
    (hq : (𝓡∂ 3).IsBoundaryPoint q) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (P.map q) (P.map q)),
        ε * ‖y - extChartAt W.model (P.map q) (P.map q)‖ <
            κ (y - extChartAt W.model (P.map q) (P.map q)) →
          (extChartAt W.model (P.map q)).symm y ∈ interior (range P.map) := by
  refine exists_entering_of_halfSpace finrank_euclideanSpace_fin P.smooth P.mfderiv_bijective
    (ℓ := EuclideanSpace.proj (0 : Fin 3)) (euclideanSpace_proj_ne_zero 0) isOpen_univ
    (mem_univ _) (extChartAt_coord_eq_zero_of_isBoundaryPoint hq) ?_
  rw [inter_univ, inter_univ, range_modelWithCornersEuclideanHalfSpace]
  rfl

/-! ### Product disk handles -/

theorem finrank_handleModel :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

theorem extChartAt_handle_apply (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    extChartAt ((𝓡∂ 2).prod (𝓡∂ 1)) p p =
      (extChartAt (𝓡∂ 2) p.1 p.1, extChartAt (𝓡∂ 1) p.2 p.2) := by
  rw [extChartAt_prod]
  rfl

theorem iccEnd_false_eq_bot : iccEnd false = (⊥ : Icc (0 : ℝ) 1) := by
  ext
  simp [iccEnd]

theorem iccEnd_true_eq_top : iccEnd true = (⊤ : Icc (0 : ℝ) 1) := by
  ext
  simp [iccEnd]

theorem isBoundaryPoint_iccEnd (b : Bool) : (𝓡∂ 1).IsBoundaryPoint (iccEnd b) := by
  cases b
  · rw [iccEnd_false_eq_bot]
    exact Icc_isBoundaryPoint_bot
  · rw [iccEnd_true_eq_top]
    exact Icc_isBoundaryPoint_top

/-- The model boundary of a product disk handle: the vertical face and the two end disks. -/
theorem handle_isBoundaryPoint_iff {p : ClosedCell 2 × Icc (0 : ℝ) 1} :
    ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint p ↔
      p.1 ∈ diskRim ∨ p.2 = iccEnd false ∨ p.2 = iccEnd true := by
  have h := Set.ext_iff.mp (ModelWithCorners.boundary_prod (I := 𝓡∂ 2) (J := 𝓡∂ 1)
    (M := ClosedCell 2) (N := Icc (0 : ℝ) 1)) p
  change ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint p ↔ _ at h
  rw [h, boundary_Icc, iccEnd_false_eq_bot, iccEnd_true_eq_top]
  simp only [Set.prod, mem_union, mem_ofPred_eq, mem_univ, true_and, and_true, mem_insert_iff,
    mem_singleton_iff]
  change (p.2 = ⊥ ∨ p.2 = ⊤) ∨ p.1 ∈ diskRim ↔ _
  tauto

/-- **Interior criterion for a handle.** -/
theorem EdgeHandle.map_mem_interior_range (H : EdgeHandle W) {p : ClosedCell 2 × Icc (0 : ℝ) 1}
    (hp : ((𝓡∂ 2).prod (𝓡∂ 1)).IsInteriorPoint p) : H.map p ∈ _root_.interior (range H.map) :=
  map_mem_interior_range_of_isInteriorPoint finrank_handleModel H.smooth H.mfderiv_bijective hp

/-- **Boundary criterion for a handle** (vertical face, end disks and corners). -/
theorem EdgeHandle.map_not_mem_interior_range (H : EdgeHandle W)
    {p : ClosedCell 2 × Icc (0 : ℝ) 1} (hp : ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint p) :
    H.map p ∉ _root_.interior (range H.map) :=
  not_mem_interior_range_of_isBoundaryPoint H.smooth H.mfderiv_bijective H.injective hp
    (H.interior ⟨p, rfl⟩)

/-- A handle point is an ambient interior point of the handle image iff it is a model-interior
point. -/
theorem EdgeHandle.map_mem_interior_range_iff (H : EdgeHandle W)
    {p : ClosedCell 2 × Icc (0 : ℝ) 1} :
    H.map p ∈ _root_.interior (range H.map) ↔ ((𝓡∂ 2).prod (𝓡∂ 1)).IsInteriorPoint p := by
  refine ⟨fun h => ?_, H.map_mem_interior_range⟩
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  exact fun hb => H.map_not_mem_interior_range hb h

/-- **Half-space normal form at a vertical point** (rim of the disk, interior time). -/
theorem EdgeHandle.exists_entering_vertical (H : EdgeHandle W) {x : ClosedCell 2}
    (hx : x ∈ diskRim) {t : Icc (0 : ℝ) 1} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (H.map (x, t)) (H.map (x, t))),
        ε * ‖y - extChartAt W.model (H.map (x, t)) (H.map (x, t))‖ <
            κ (y - extChartAt W.model (H.map (x, t)) (H.map (x, t))) →
          (extChartAt W.model (H.map (x, t))).symm y ∈ _root_.interior (range H.map) := by
  set ℓ₁ : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ _ _) with hℓ₁
  set ℓ₂ : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℝ _ _) with hℓ₂
  have hℓ₁0 : ℓ₁ ≠ 0 := by
    intro h
    have := congrArg (fun L : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ =>
      L (EuclideanSpace.single 0 1, 0)) h
    simp [ℓ₁] at this
  have htint : (𝓡∂ 1).IsInteriorPoint t := Icc_isInteriorPoint_interior ⟨ht0, ht1⟩
  refine exists_entering_of_halfSpace finrank_handleModel H.smooth H.mfderiv_bijective
    (ℓ := ℓ₁) hℓ₁0 (O := ℓ₂ ⁻¹' Ioi 0) (isOpen_Ioi.preimage ℓ₂.continuous) ?_ ?_ ?_
  · rw [mem_preimage, extChartAt_handle_apply]
    exact extChartAt_coord_pos_of_isInteriorPoint htint
  · rw [extChartAt_handle_apply]
    exact extChartAt_coord_eq_zero_of_isBoundaryPoint hx
  · ext p
    simp only [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace, mem_inter_iff,
      mem_prod, mem_ofPred_eq, mem_preimage, mem_Ioi, ℓ₁, ℓ₂, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.le⟩, h2⟩

/-- **Half-space normal form at an end-disk point** (interior of the disk, end time). -/
theorem EdgeHandle.exists_entering_endDisk (H : EdgeHandle W) {x : ClosedCell 2}
    (hx : x ∉ diskRim) (b : Bool) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (H.map (x, iccEnd b)) (H.map (x, iccEnd b))),
        ε * ‖y - extChartAt W.model (H.map (x, iccEnd b)) (H.map (x, iccEnd b))‖ <
            κ (y - extChartAt W.model (H.map (x, iccEnd b)) (H.map (x, iccEnd b))) →
          (extChartAt W.model (H.map (x, iccEnd b))).symm y ∈ _root_.interior (range H.map) := by
  set ℓ₁ : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ _ _) with hℓ₁
  set ℓ₂ : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℝ _ _) with hℓ₂
  have hℓ₂0 : ℓ₂ ≠ 0 := by
    intro h
    have := congrArg (fun L : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ =>
      L (0, EuclideanSpace.single 0 1)) h
    simp [ℓ₂] at this
  have hxint : (𝓡∂ 2).IsInteriorPoint x :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx
  refine exists_entering_of_halfSpace finrank_handleModel H.smooth H.mfderiv_bijective
    (ℓ := ℓ₂) hℓ₂0 (O := ℓ₁ ⁻¹' Ioi 0) (isOpen_Ioi.preimage ℓ₁.continuous) ?_ ?_ ?_
  · rw [mem_preimage, extChartAt_handle_apply]
    exact extChartAt_coord_pos_of_isInteriorPoint hxint
  · rw [extChartAt_handle_apply]
    exact extChartAt_coord_eq_zero_of_isBoundaryPoint (isBoundaryPoint_iccEnd b)
  · ext p
    simp only [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace, mem_inter_iff,
      mem_prod, mem_ofPred_eq, mem_preimage, mem_Ioi, ℓ₁, ℓ₂, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.le, h1⟩, h2⟩

end Pieces

end GC.GraphManifold.Assembly
