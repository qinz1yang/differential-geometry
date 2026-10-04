import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionGap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# A retained coordinate is injective on the whole local graph (CGP06)

Blueprint 207B, CGP06 (`lem:fibration-retained-coordinate-graph`, B:4130–4174).

First part: `L` a subspace of a Euclidean space `H`, `π` a coordinate projection (`‖π‖ ≤ 1`) with
`|π v| ≥ m |v|` on `L`, and `g` with `‖Dg‖ ≤ a` on the parameter ball. Then
`|π(G t₁) - π(G t₂)| ≥ (m - a)|t₁ - t₂|` for the graph map `G t = x + t + g t`, so `π ∘ G` is
injective when `a < m`, and its differential has the same lower bound (the local-diffeomorphism
input of the inverse function theorem).

Second part (the sufficient criterion): if `T = DΦ` has `π T = I`, `‖T‖ ≤ Ω`,
`‖D - T Dη‖ ≤ e` with `Dη` admitting a right inverse of norm at most two, and the plane `L` of the
same dimension has normal error `‖(I - Π_L) D‖ ≤ ν`, then `Ω ≥ 1` and `ν + e ≤ 1/(48Ω)` give
`|π v| ≥ |v|/(2Ω)` on `L`. The projector comparison is CFS03's equal-dimensional estimate
`Submodule.norm_starProjection_sub_le_three_mul_of_one_sided_bound`.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

section Graph

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- CGP06, quantitative injectivity of a retained coordinate along a graph over `L`. -/
theorem retained_coordinate_lower_bound_on_graph (L : Submodule ℝ H) (π : H →L[ℝ] F)
    (hπ : ‖π‖ ≤ 1) {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (g : L → H)
    (hg : ∀ t ∈ Metric.ball (0 : L) R, DifferentiableAt ℝ g t)
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) {t₁ t₂ : L}
    (h₁ : t₁ ∈ Metric.ball (0 : L) R) (h₂ : t₂ ∈ Metric.ball (0 : L) R) :
    (m - a) * ‖t₁ - t₂‖ ≤ ‖π (x + t₁ + g t₁) - π (x + t₂ + g t₂)‖ := by
  have hmv : ‖g t₁ - g t₂‖ ≤ a * ‖t₁ - t₂‖ :=
    (convex_ball (0 : L) R).norm_image_sub_le_of_norm_fderiv_le hg hDg h₂ h₁
  have hsplit : π (x + t₁ + g t₁) - π (x + t₂ + g t₂) =
      π ((t₁ - t₂ : L) : H) + π (g t₁ - g t₂) := by
    simp only [map_add, map_sub, Submodule.coe_sub]
    abel
  have hlow : m * ‖t₁ - t₂‖ ≤ ‖π ((t₁ - t₂ : L) : H)‖ := by
    have := hm _ (t₁ - t₂).property
    rwa [Submodule.norm_coe] at this
  have hup : ‖π (g t₁ - g t₂)‖ ≤ a * ‖t₁ - t₂‖ :=
    (π.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hπ).trans hmv)
  rw [hsplit]
  have htri := norm_sub_norm_le (π ((t₁ - t₂ : L) : H)) (-π (g t₁ - g t₂))
  rw [sub_neg_eq_add, norm_neg] at htri
  linarith

/-- CGP06: for `a < m` the retained coordinate is injective on the whole graph. -/
theorem injOn_retained_coordinate_graph (L : Submodule ℝ H) (π : H →L[ℝ] F)
    (hπ : ‖π‖ ≤ 1) {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m) (g : L → H)
    (hg : ∀ t ∈ Metric.ball (0 : L) R, DifferentiableAt ℝ g t)
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    Set.InjOn (fun t : L => π (x + t + g t)) (Metric.ball 0 R) := by
  intro t₁ h₁ t₂ h₂ heq
  have h := retained_coordinate_lower_bound_on_graph L π hπ hm g hg hDg x h₁ h₂
  simp only at heq
  rw [heq, sub_self, norm_zero] at h
  have hz : ‖t₁ - t₂‖ = 0 := le_antisymm
    (by nlinarith [norm_nonneg (t₁ - t₂)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- CGP06: the differential of the retained coordinate along the graph has the same lower bound
`m - a`; for `dim L = dim F` it is therefore invertible (local diffeomorphism input). -/
theorem retained_coordinate_fderiv_lower_bound (L : Submodule ℝ H) (π : H →L[ℝ] F)
    (hπ : ‖π‖ ≤ 1) {m a : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (A : L →L[ℝ] H) (hA : ‖A‖ ≤ a)
    (v : L) : (m - a) * ‖v‖ ≤ ‖π ((v : H) + A v)‖ := by
  have hlow : m * ‖v‖ ≤ ‖π (v : H)‖ := by
    have := hm _ v.property
    rwa [Submodule.norm_coe] at this
  have hup : ‖π (A v)‖ ≤ a * ‖v‖ :=
    (π.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hπ).trans
      ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))))
  rw [map_add]
  have htri := norm_sub_norm_le (π (v : H)) (-π (A v))
  rw [sub_neg_eq_add, norm_neg] at htri
  linarith

end Graph

section Criterion

variable {X E H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- CGP06, the sufficient criterion: the reference graph derivative `T` (identity component
`π T = I`, `‖T‖ ≤ Ω`), the comparison `‖D - T Dη‖ ≤ e` with a right inverse of `Dη` of norm at
most two, and a same-dimensional plane `L` with normal error `‖(I - Π_L) D‖ ≤ ν` give the retained
lower bound `|v| ≤ 2Ω |π v|` on `L`, provided `Ω ≥ 1` and `ν + e ≤ 1/(48Ω)`. -/
theorem retained_coordinate_lower_bound_of_reference_graph (π : H →L[ℝ] E) (hπ : ‖π‖ ≤ 1)
    (T : E →L[ℝ] H) (hπT : π.comp T = ContinuousLinearMap.id ℝ E) {Ω e ν : ℝ} (hT : ‖T‖ ≤ Ω)
    (D : X →L[ℝ] H) (Dη : X →L[ℝ] E) (B : E →L[ℝ] X)
    (hB : Dη.comp B = ContinuousLinearMap.id ℝ E) (hBn : ‖B‖ ≤ 2) (hD : ‖D - T.comp Dη‖ ≤ e)
    (L : Submodule ℝ H) (hdim : Module.finrank ℝ L = Module.finrank ℝ E)
    (hν : ‖Lᗮ.starProjection.comp D‖ ≤ ν) (hΩ : 1 ≤ Ω) (he : 0 ≤ e) (hν0 : 0 ≤ ν)
    (hsmall : ν + e ≤ 1 / (48 * Ω)) :
    ∀ v ∈ L, ‖v‖ ≤ 2 * Ω * ‖π v‖ := by
  have hπTz (z : E) : π (T z) = z := by
    simpa using congrArg (fun A : E →L[ℝ] E => A z) hπT
  have hBz (z : E) : Dη (B z) = z := by
    simpa using congrArg (fun A : E →L[ℝ] E => A z) hB
  have hΩ0 : 0 < Ω := by linarith
  have hsmall' : ν + e ≤ 1 / 48 := hsmall.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  -- the image of `T` is `2(e+ν)`-close to `L`
  set P : Submodule ℝ H := LinearMap.range (T : E →ₗ[ℝ] H) with hP
  have hTinj : Function.Injective T := by
    intro z₁ z₂ h
    rw [← hπTz z₁, ← hπTz z₂, h]
  have hPdim : Module.finrank ℝ P = Module.finrank ℝ L := by
    rw [hdim, hP, LinearMap.finrank_range_of_inj hTinj]
  have hbound : ∀ u ∈ P, ‖u - L.starProjection u‖ ≤ (2 * (e + ν)) * ‖u‖ := by
    intro u hu
    obtain ⟨z, rfl⟩ := hu
    change ‖T z - L.starProjection (T z)‖ ≤ (2 * (e + ν)) * ‖T z‖
    have horth : T z - L.starProjection (T z) = Lᗮ.starProjection (T z) := by
      rw [← Submodule.starProjection_add_starProjection_orthogonal (K := L) (T z)]
      simp
    have hdecomp : Lᗮ.starProjection (T z) =
        Lᗮ.starProjection ((T.comp Dη - D) (B z)) + (Lᗮ.starProjection.comp D) (B z) := by
      rw [ContinuousLinearMap.comp_apply, ← map_add]
      congr 1
      simp only [sub_apply, ContinuousLinearMap.comp_apply, hBz,
        sub_add_cancel]
    have hz : ‖z‖ ≤ ‖T z‖ := by
      calc ‖z‖ = ‖π (T z)‖ := by rw [hπTz]
        _ ≤ ‖π‖ * ‖T z‖ := π.le_opNorm _
        _ ≤ ‖T z‖ := mul_le_of_le_one_left (norm_nonneg _) hπ
    have hBz' : ‖B z‖ ≤ 2 * ‖z‖ :=
      (B.le_opNorm z).trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg z))
    have h1 : ‖Lᗮ.starProjection ((T.comp Dη - D) (B z))‖ ≤ e * ‖B z‖ := by
      refine (Lᗮ.norm_starProjection_apply_le _).trans ?_
      refine ((T.comp Dη - D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rwa [norm_sub_rev]
    have h2 : ‖(Lᗮ.starProjection.comp D) (B z)‖ ≤ ν * ‖B z‖ :=
      ((Lᗮ.starProjection.comp D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hν (norm_nonneg _))
    rw [horth, hdecomp]
    refine (norm_add_le _ _).trans ?_
    have hnB := norm_nonneg (B z)
    nlinarith
  have hgap := Submodule.norm_starProjection_sub_le_three_mul_of_one_sided_bound P L hPdim
    (by positivity) (by linarith) hbound
  -- the retained lower bound on `L`
  intro v hv
  set v₀ := P.starProjection v with hv₀
  have hv₀P : v₀ ∈ P := P.starProjection_apply_mem v
  obtain ⟨z₀, hz₀⟩ := hv₀P
  have hz₀' : T z₀ = v₀ := hz₀
  have hv₀norm : ‖v₀‖ ≤ Ω * ‖π v₀‖ := by
    rw [← hz₀', hπTz]
    exact (T.le_opNorm z₀).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg z₀))
  have hLv : L.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hdiff : ‖v - v₀‖ ≤ 6 * (e + ν) * ‖v‖ := by
    have h := (P.starProjection - L.starProjection).le_opNorm v
    rw [sub_apply, hLv, ← hv₀, norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v))
  have hv₀low : (1 - 6 * (e + ν)) * ‖v‖ ≤ ‖v₀‖ := by
    have := norm_sub_norm_le v (v - v₀)
    rw [sub_sub_cancel] at this
    nlinarith [norm_nonneg v]
  have hπdiff : ‖π v - π v₀‖ ≤ 6 * (e + ν) * ‖v‖ := by
    rw [← map_sub]
    exact (π.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hπ).trans hdiff)
  have hπv₀ : ‖π v₀‖ ≤ ‖π v‖ + 6 * (e + ν) * ‖v‖ := by
    have := norm_sub_norm_le (π v₀) (π v)
    rw [norm_sub_rev] at this
    linarith
  have hθΩ : 6 * (e + ν) * (1 + Ω) ≤ 1 / 4 := by
    have h48 : (ν + e) * (48 * Ω) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hsmall
    nlinarith
  have hvn := norm_nonneg v
  nlinarith [mul_le_mul_of_nonneg_left hπv₀ hΩ0.le]

end Criterion

end DifferentialGeometry.Analysis
