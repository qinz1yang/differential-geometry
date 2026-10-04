import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# LC43 and the compact alternative of LC38

Blueprint LC43 (master207A:21886) and LC38 (master207A:21622), compact alternative of the
LC37 packet.

* `partialDiffeomorph_target_eq_univ_of_compactSpace`, `exists_diffeomorph_of_compactSpace`:
  a smooth embedding (partial diffeomorphism defined on all of `N`) of a nonempty compact
  manifold into a connected Hausdorff manifold of the same dimension is onto, hence a
  diffeomorphism (open image by equal dimension, closed image by compactness).
* `riemannianEDistOf_map_le_two_mul`: `j^* g ≤ 4 h` gives `d_g(j n, j x) ≤ 2 d_h(n, x)`.
* `radial_lt_fifth_of_compact_model` (LC43): if every point of `N` is within `D` of `n`,
  `j^* g ≤ 4 h`, `|η - d_g(j n, ·)/R| < e` and `2D/R + e < 1/5`, then `η < 1/5` on all of `M`.
  (`d_g/R` is the distance of the rescaled metric `R⁻² g`.) `exists_scale_two_mul_div_add_lt`:
  such an `R` exists above any prescribed bound.
* `sublevel_eq_univ_of_lt_fifth` (LC38, compact alternative): then every `A_ρ`, `ρ ≥ 1/5`, is
  all of `M`, which is diffeomorphic to `N`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry

section Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N M : Type*} [TopologicalSpace N] [ChartedSpace H N] [TopologicalSpace M] [ChartedSpace H' M]
  {n : WithTop ℕ∞}

/-- A partial diffeomorphism defined on all of a nonempty compact space, into a connected
Hausdorff space, is onto. -/
theorem partialDiffeomorph_target_eq_univ_of_compactSpace [CompactSpace N] [Nonempty N]
    [ConnectedSpace M] [T2Space M] (j : PartialDiffeomorph I J N M n) (hsrc : j.source = univ) :
    j.target = univ := by
  have himage : j.target = j.toPartialEquiv '' univ := by
    rw [← hsrc]
    exact j.toPartialEquiv.image_source_eq_target.symm
  have hcont : Continuous (j : N → M) := by
    have h := j.contMDiffOn_toFun.continuousOn
    rw [hsrc] at h
    exact continuousOn_univ.mp h
  have hclosed : IsClosed j.target := by
    rw [himage]
    exact (isCompact_univ.image hcont).isClosed
  have hne : j.target.Nonempty := by
    rw [himage]
    exact univ_nonempty.image _
  exact (IsClopen.eq_univ ⟨hclosed, j.open_target⟩ hne)

/-- LC38, compact alternative: the embedding is a diffeomorphism. -/
theorem exists_diffeomorph_of_compactSpace [CompactSpace N] [Nonempty N] [ConnectedSpace M]
    [T2Space M] (j : PartialDiffeomorph I J N M n) (hsrc : j.source = univ) :
    ∃ d : Diffeomorph I J N M n, ∀ x, d x = j x := by
  have htgt := partialDiffeomorph_target_eq_univ_of_compactSpace j hsrc
  have hto : ContMDiff I J n (j : N → M) := by
    have h := j.contMDiffOn_toFun
    rw [hsrc] at h
    exact contMDiffOn_univ.mp h
  have hinv : ContMDiff J I n j.toPartialEquiv.symm := by
    have h := j.contMDiffOn_invFun
    rw [htgt] at h
    exact contMDiffOn_univ.mp h
  refine ⟨{ toFun := j
            invFun := j.toPartialEquiv.symm
            left_inv := fun x => j.toPartialEquiv.left_inv (by rw [hsrc]; exact mem_univ x)
            right_inv := fun y => j.toPartialEquiv.right_inv (by rw [htgt]; exact mem_univ y)
            contMDiff_toFun := hto
            contMDiff_invFun := hinv }, fun _ => rfl⟩

end Topology

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N M : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- `j^* g ≤ 4 h` on the whole source gives `d_g(j n, j x) ≤ 2 d_h(n, x)`. -/
theorem riemannianEDistOf_map_le_two_mul (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (j : PartialDiffeomorph I I N M ∞) (hsrc : j.source = univ)
    (hupper : ∀ z (v : TangentSpace I z),
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        4 * h.inner z v v)
    (n x : N) :
    riemannianEDistOf g (j n) (j x) ≤ 2 * riemannianEDistOf h n x := by
  by_cases htop : riemannianEDistOf h n x = ⊤
  · rw [htop, ENNReal.mul_top two_ne_zero]
    exact le_top
  · set R := (riemannianEDistOf h n x).toReal + 1 with hR
    have hR0 : 0 < R := by rw [hR]; positivity
    have hlt : riemannianEDistOf h n x < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_toReal htop]
      exact (ENNReal.ofReal_lt_ofReal_iff hR0).mpr (by rw [hR]; linarith)
    have hmain := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      h g j n x hR0 (by norm_num : (0 : ℝ) < 2) (by rw [hsrc]; exact subset_univ _)
      (fun z _ v => by
        have := hupper z v
        norm_num
        linarith) hlt
    rwa [show ENNReal.ofReal 2 = 2 by norm_num] at hmain

/-- LC43: the compact model forces the radial function below `1/5` everywhere. -/
theorem radial_lt_fifth_of_compact_model [CompactSpace N] [Nonempty N] [ConnectedSpace M]
    [T2Space M] (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (j : PartialDiffeomorph I I N M ∞) (hsrc : j.source = univ)
    (hupper : ∀ z (v : TangentSpace I z),
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        4 * h.inner z v v)
    (n : N) {D R e : ℝ} (hR : 0 < R) (hD0 : 0 ≤ D)
    (hD : ∀ x, riemannianEDistOf h n x ≤ ENNReal.ofReal D)
    {η : M → ℝ} (hη : ∀ y, |η y - (riemannianEDistOf g (j n) y).toReal / R| < e)
    (hsmall : 2 * D / R + e < 1 / 5) (y : M) : η y < 1 / 5 := by
  have htgt := partialDiffeomorph_target_eq_univ_of_compactSpace j hsrc
  obtain ⟨x, -, rfl⟩ : y ∈ j.toPartialEquiv '' j.source := by
    rw [j.toPartialEquiv.image_source_eq_target, htgt]
    exact mem_univ y
  have hd := riemannianEDistOf_map_le_two_mul h g j hsrc hupper n x
  have hle : (riemannianEDistOf g (j n) (j x)).toReal ≤ 2 * D := by
    have h2 : riemannianEDistOf g (j n) (j x) ≤ ENNReal.ofReal (2 * D) := by
      calc riemannianEDistOf g (j n) (j x) ≤ 2 * riemannianEDistOf h n x := hd
        _ ≤ 2 * ENNReal.ofReal D := by gcongr; exact hD x
        _ = ENNReal.ofReal (2 * D) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  have hdiv : (riemannianEDistOf g (j n) (j x)).toReal / R ≤ 2 * D / R :=
    div_le_div_of_nonneg_right hle hR.le
  have habs := (abs_lt.mp (hη (j x))).2
  linarith

/-- The scale of LC43 can be chosen above any prescribed bound, before any sequence index. -/
theorem exists_scale_two_mul_div_add_lt {D e R₀ : ℝ} (he : e < 1 / 5) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧ 2 * D / R + e < 1 / 5 := by
  set c := 1 / 5 - e with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  refine ⟨max R₀ 0 + 2 * |D| / c + 1, ?_, ?_, ?_⟩
  · have : 0 ≤ 2 * |D| / c := by positivity
    linarith [le_max_left R₀ 0]
  · have : 0 ≤ 2 * |D| / c := by positivity
    linarith [le_max_right R₀ 0]
  · set R := max R₀ 0 + 2 * |D| / c + 1 with hRdef
    have hR0 : 0 < R := by
      have : 0 ≤ 2 * |D| / c := by positivity
      linarith [le_max_right R₀ 0]
    have hgt : 2 * |D| / c < R := by linarith [le_max_right R₀ 0]
    have h1 : 2 * |D| < R * c := (div_lt_iff₀ hc0).mp hgt
    have h2 : 2 * D / R < c := by
      rw [div_lt_iff₀ hR0]
      linarith [le_abs_self D]
    linarith

end Metric

/-- LC38, compact alternative: if the radial function stays below `1/5`, every radial sublevel
`A_ρ`, `ρ ≥ 1/5`, is the whole manifold. -/
theorem sublevel_eq_univ_of_lt_fifth {M : Type*} {η : M → ℝ} (hη : ∀ y, η y < 1 / 5)
    {ρ : ℝ} (hρ : 1 / 5 ≤ ρ) : {y | η y ≤ ρ} = univ :=
  eq_univ_of_forall fun y => ((hη y).le.trans hρ)

end DifferentialGeometry
