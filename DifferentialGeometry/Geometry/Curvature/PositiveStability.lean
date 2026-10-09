import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.Euclidean.Construction
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Mathlib.Tactic
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff InnerProductSpace Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian Bundle
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E → E → E → E → ℝ}

private theorem smul_two (hA : IsAlgCurvForm A) (c : ℝ) (u v w z : E) :
    A u (c • v) w z = c * A u v w z := by
  rw [hA.anti_first u, hA.smul_left, hA.anti_first v]
  ring

private theorem smul_three (hA : IsAlgCurvForm A) (c : ℝ) (u v w z : E) :
    A u v (c • w) z = c * A u v w z := by
  rw [hA.pair_swap u v, hA.smul_left, hA.pair_swap w z]

private theorem smul_four (hA : IsAlgCurvForm A) (c : ℝ) (u v w z : E) :
    A u v w (c • z) = c * A u v w z := by
  rw [hA.anti_last u v, smul_three hA, hA.anti_last u v z]
  ring

private theorem sectional_sub_smul (hA : IsAlgCurvForm A) (u v : E) (c : ℝ) :
    A u (v - c • u) (v - c • u) u = A u v v u := by
  have hz₁ (w z : E) : A u u w z = 0 := by
    have h := hA.anti_first u u w z
    linarith
  have hz₂ (w z : E) : A w z u u = 0 := by
    have h := hA.anti_last w z u u
    linarith
  simp only [sub_eq_add_neg, ← neg_smul, hA.add_two, hA.add_three,
    smul_two hA, smul_three hA, hz₁, hz₂, mul_zero, add_zero]

private theorem pos_of_unit_orthogonal (hA : IsAlgCurvForm A)
    (hpos : ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → 0 < A u v v u)
    (u v : E) (hplane : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2) :
    0 < A u v v u := by
  have hu : u ≠ 0 := by
    intro hu
    simp [hu] at hplane
  let c : ℝ := ⟪u, v⟫_ℝ / ‖u‖ ^ 2
  let w : E := v - c • u
  have horth : ⟪u, w⟫_ℝ = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hw : w ≠ 0 := by
    intro hw
    have hv : v = c • u := sub_eq_zero.mp hw
    have he : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 = 0 := by
      rw [hv, norm_smul, real_inner_smul_right, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [he] at hplane
    exact (lt_irrefl 0) hplane
  have hnorth : ⟪NormedSpace.normalize u, NormedSpace.normalize w⟫_ℝ = 0 := by
    simp only [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right, horth, mul_zero]
  have hp := hpos (NormedSpace.normalize u) (NormedSpace.normalize w)
    (NormedSpace.norm_normalize hu) (NormedSpace.norm_normalize hw) hnorth
  have he : A u w w u = ‖u‖ ^ 2 * ‖w‖ ^ 2 *
      A (NormedSpace.normalize u) (NormedSpace.normalize w)
        (NormedSpace.normalize w) (NormedSpace.normalize u) := by
    calc
      A u w w u = A (‖u‖ • NormedSpace.normalize u) (‖w‖ • NormedSpace.normalize w)
          (‖w‖ • NormedSpace.normalize w) (‖u‖ • NormedSpace.normalize u) := by
        rw [NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]
      _ = _ := by rw [hA.smul_left, smul_two hA, smul_three hA, smul_four hA]; ring
  have hscaled : 0 < A u w w u := by
    rw [he]
    exact mul_pos (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hu))
      (sq_pos_of_pos (norm_pos_iff.mpr hw))) hp
  exact (sectional_sub_smul hA u v c) ▸ hscaled

private theorem euclidean_gram_pos_of_bilinear_gram_ne_zero
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E)
    (hB : B u u * B v v - B u v ^ 2 ≠ 0) :
    0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by
  have hCS := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hCS
  have hnn : 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by nlinarith
  apply lt_of_le_of_ne hnn
  intro he
  have habs : ‖⟪u, v⟫_ℝ‖ = ‖u‖ * ‖v‖ := by
    rw [Real.norm_eq_abs]
    have hs : |⟪u, v⟫_ℝ| ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
      rw [sq_abs, mul_pow]
      linarith
    exact (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs
  rcases ((norm_inner_eq_norm_tfae ℝ u v).out 1 3).mp habs with hu | ⟨c, hv⟩
  · apply hB
    simp [hu]
  · apply hB
    rw [hv]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

private theorem bilinear_gram_pos_of_euclidean_gram_pos
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hBsym : ∀ u v, B u v = B v u)
    (hBpos : ∀ u, u ≠ 0 → 0 < B u u) (u v : E)
    (hplane : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2) :
    0 < B u u * B v v - B u v ^ 2 := by
  have hu : u ≠ 0 := by intro he; simp [he] at hplane
  let c := B u v / B u u
  let w := v - c • u
  have hw : w ≠ 0 := by
    intro he
    have hv : v = c • u := sub_eq_zero.mp he
    have hz : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 = 0 := by
      rw [hv, norm_smul, real_inner_smul_right, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [hz] at hplane
    exact (lt_irrefl 0) hplane
  have he : B u u * B w w = B u u * B v v - B u v ^ 2 := by
    dsimp [w, c]
    simp only [map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul]
    rw [hBsym v u]
    field_simp [ne_of_gt (hBpos u hu)]
    ring
  rw [← he]
  exact mul_pos (hBpos u hu) (hBpos w hw)

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
private theorem lowered_curvature_error
    (g G : SmoothRiemannianMetric I M) (x : M) (ε C : ℝ)
    (hε : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (u v : TangentSpace I x)
    (hu : Real.sqrt (G.inner x u u) ≤ C)
    (hv : Real.sqrt (G.inner x v v) ≤ C)
    (hR : let R := riemannOp (LeviCivita G) x u v v;
      Real.sqrt (G.inner x R R) ≤ C) :
    |metricRm04StandardAt g x u v v u - metricRm04StandardAt G x u v v u| ≤
      ε * (360 * C ^ 4 + C ^ 2) := by
  have heps0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have h := abs_metricRm04_sub_le_of_small_metric_derivatives g G x hε hsmall u v v u
  apply h.trans
  calc
    _ ≤ ε * (360 * C * C * C + C) * C := by gcongr
    _ = _ := by ring

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
private local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
set_option backward.isDefEq.respectTransparency false in
private theorem continuous_riemannOp_model (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    Continuous (fun x : E => (show E →L[ℝ] E →L[ℝ] E →L[ℝ] E from by exact riemannOp (LeviCivita g) x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply continuous_iff_continuousAt.mpr
  intro x
  have h := (FiberBundle.continuousAt_section (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (E := fun y : E => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ]
      TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y) x).mp
    (riemannOp_section_continuous g).continuousAt
  convert h using 1
  funext y
  ext u v w
  simp [Trivialization.continuousLinearMapAt_apply, hom_trivializationAt,
    Trivialization.continuousLinearMap_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_compact_frame_bounds
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) {K : Set E} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ u v : TangentSpace 𝓘(ℝ, E) x,
      G.inner x u u * G.inner x v v - G.inner x u v ^ 2 ≠ 0 →
      0 < sectionalCurvature G x u v) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x ∈ K, ∀ u v : E,
      ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 →
      a ≤ metricRm04StandardAt G x u v v u ∧
      Real.sqrt (G.inner x u u) ≤ C ∧ Real.sqrt (G.inner x v v) ≤ C ∧
      (let R := riemannOp (LeviCivita G) x u v v; Real.sqrt (G.inner x R R) ≤ C) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let S : Set (E × E) := {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ ⟪p.1, p.2⟫_ℝ = 0}
  have hS : IsCompact S := by
    have hprod := (isCompact_sphere (0 : E) 1).prod (isCompact_sphere (0 : E) 1)
    apply hprod.of_isClosed_subset
    · exact (isClosed_eq (continuous_fst.norm) continuous_const).inter
        ((isClosed_eq (continuous_snd.norm) continuous_const).inter
          (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const))
    · intro p hp
      exact ⟨by simpa using hp.1, by simpa using hp.2.1⟩
  let T : Set (E × (E × E)) := K ×ˢ S
  have hT : IsCompact T := hK.prod hS
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => by exact G.inner x
  let R : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fun x => by exact riemannOp (LeviCivita G) x
  have hB : Continuous B := (DifferentialGeometry.Geometry.Riemannian.contDiff_metric_inner G).continuous
  have hR : Continuous R := continuous_riemannOp_model G
  let f (p : E × (E × E)) := B p.1 p.2.1 (R p.1 p.2.1 p.2.2 p.2.2)
  let F (p : E × (E × E)) := max (Real.sqrt (B p.1 p.2.1 p.2.1))
    (max (Real.sqrt (B p.1 p.2.2 p.2.2))
      (Real.sqrt (B p.1 (R p.1 p.2.1 p.2.2 p.2.2) (R p.1 p.2.1 p.2.2 p.2.2))))
  have hfst : Continuous (fun p : E × (E × E) => p.2.1) := continuous_fst.comp continuous_snd
  have hsnd : Continuous (fun p : E × (E × E) => p.2.2) := continuous_snd.comp continuous_snd
  have hBp : Continuous (fun p : E × (E × E) => B p.1) := hB.comp continuous_fst
  have hBu : Continuous (fun p : E × (E × E) => B p.1 p.2.1) := hBp.clm_apply hfst
  have hBv : Continuous (fun p : E × (E × E) => B p.1 p.2.2) := hBp.clm_apply hsnd
  have hBuu : Continuous (fun p : E × (E × E) => B p.1 p.2.1 p.2.1) :=
    hBu.clm_apply hfst
  have hBvv : Continuous (fun p : E × (E × E) => B p.1 p.2.2 p.2.2) :=
    hBv.clm_apply hsnd
  have hRp : Continuous (fun p : E × (E × E) => R p.1) := hR.comp continuous_fst
  have hRu : Continuous (fun p : E × (E × E) => R p.1 p.2.1) := hRp.clm_apply hfst
  have hRuv : Continuous (fun p : E × (E × E) => R p.1 p.2.1 p.2.2) :=
    hRu.clm_apply hsnd
  have hRuvv : Continuous (fun p : E × (E × E) => R p.1 p.2.1 p.2.2 p.2.2) :=
    hRuv.clm_apply hsnd
  have hBRR : Continuous (fun p : E × (E × E) =>
      B p.1 (R p.1 p.2.1 p.2.2 p.2.2) (R p.1 p.2.1 p.2.2 p.2.2)) :=
    (hBp.clm_apply hRuvv).clm_apply hRuvv
  have hf : Continuous f := by
    exact hBu.clm_apply hRuvv
  have hF : Continuous F := by
    exact (Real.continuous_sqrt.comp hBuu).max
      ((Real.continuous_sqrt.comp hBvv).max (Real.continuous_sqrt.comp hBRR))
  have hfpos : ∀ p ∈ T, 0 < f p := by
    rintro ⟨x, u, v⟩ ⟨hx, hu, hv, huv⟩
    have hplane : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by rw [hu, hv, huv]; norm_num
    have hgram := bilinear_gram_pos_of_euclidean_gram_pos (B x) (G.symm x) (G.pos x) u v hplane
    have hs := hpos x hx u v (ne_of_gt hgram)
    rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div] at hs
    have hnum := (div_pos_iff.mp hs).resolve_right (fun h => (not_lt_of_ge hgram.le) h.2)
    change 0 < G.inner x u (riemannOp (LeviCivita G) x u v v)
    rw [← metricRm04StandardAt_eq_inner_riemannOp]
    exact hnum.1
  by_cases hne : T.Nonempty
  · obtain ⟨p, hp, hpmin⟩ := hT.exists_isMinOn hne hf.continuousOn
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hF.continuousOn
    refine ⟨f p, max 1 C, hfpos p hp, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
    intro x hx u v hu hv huv
    have hm : (x, u, v) ∈ T := ⟨hx, hu, hv, huv⟩
    have hc : |F (x, u, v)| ≤ C := by simpa only [Real.norm_eq_abs] using hC _ hm
    have hb : F (x, u, v) ≤ max 1 C :=
      (le_abs_self _).trans (hc.trans (le_max_right _ _))
    have hh := hpmin hm
    change f p ≤ G.inner x u (riemannOp (LeviCivita G) x u v v) at hh
    rw [← metricRm04StandardAt_eq_inner_riemannOp] at hh
    exact ⟨hh, (le_max_left _ _).trans hb,
      (le_max_left _ _).trans ((le_max_right _ _).trans hb),
      (le_max_right _ _).trans ((le_max_right _ _).trans hb)⟩
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro x hx u v hu hv huv
    exact False.elim (hne ⟨(x, u, v), hx, hu, hv, huv⟩)

set_option backward.isDefEq.respectTransparency false in
theorem exists_pos_sectionalCurvature_of_small_metricDerivENormSupOn
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) {K : Set E} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ u v : TangentSpace 𝓘(ℝ, E) x,
      G.inner x u u * G.inner x v v - G.inner x u v ^ 2 ≠ 0 →
      0 < sectionalCurvature G x u v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ O : TopologicalSpace.Opens E,
      ∀ g : SmoothRiemannianMetric 𝓘(ℝ, E) O,
      DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn {x : O | (x : E) ∈ K} 2
        g (G.restrictOpen O) (G.restrictOpen O) < ENNReal.ofReal ε →
      ∀ x : O, (x : E) ∈ K → ∀ u v : TangentSpace 𝓘(ℝ, E) x,
        g.inner x u u * g.inner x v v - g.inner x u v ^ 2 ≠ 0 →
        0 < sectionalCurvature g x u v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨a, C, ha, hC, hbounds⟩ := exists_compact_frame_bounds G hK hpos
  let D := 360 * C ^ 4 + C ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min (1 / 2 : ℝ) (a / (2 * D))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos ha (mul_pos (by norm_num) hD))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεD : ε * D ≤ a / 2 := by
    calc
      ε * D ≤ (a / (2 * D)) * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
      _ = a / 2 := by field_simp
  refine ⟨ε, hε, ?_⟩
  intro O g hsmall x hx u v hplane
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hjet (j : ℕ) (hj : j ≤ 2) : metricDerivNorm j g (G.restrictOpen O) (G.restrictOpen O) x ≤ ε :=
    (DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt _ 2 g
      (G.restrictOpen O) (G.restrictOpen O) hsmall hj hx).le
  let A : E → E → E → E → ℝ := fun u v w z => metricRm04StandardAt g x u v w z
  have hA : IsAlgCurvForm A := by
    exact mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hunit : ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → 0 < A u v v u := by
    intro U V hU hV hUV
    obtain ⟨hm, hU', hV', hR⟩ := hbounds (x : E) hx U V hU hV hUV
    have hReq : riemannOp (LeviCivita (G.restrictOpen O)) x U V V =
        riemannOp (LeviCivita G) (x : E) U V V := by
      simpa only [mfderiv_subtype_val_apply] using riemannOp_restrictOpen G O x U V V
    have hR' : let R := riemannOp (LeviCivita (G.restrictOpen O)) x U V V;
        Real.sqrt ((G.restrictOpen O).inner x R R) ≤ C := by
      dsimp only
      rw [hReq, SmoothRiemannianMetric.restrictOpen_inner]
      exact hR
    have he := lowered_curvature_error g (G.restrictOpen O) x ε C hεhalf hC.le hjet U V hU' hV' hR'
    simp only [metricRm04StandardAt_restrictOpen, mfderiv_subtype_val_apply] at he
    have hnum : |A U V V U - metricRm04StandardAt G (x : E) U V V U| ≤ a / 2 := by
      apply he.trans
      apply le_trans (mul_le_mul_of_nonneg_left (show 360 * C ^ 4 + C ^ 2 ≤ D by dsimp [D]; linarith) hε.le)
      exact hεD
    have habs := neg_le_abs (A U V V U - metricRm04StandardAt G (x : E) U V V U)
    linarith
  let B : E →L[ℝ] E →L[ℝ] ℝ := by exact g.inner x
  have hEuclid : 0 < ‖(show E from u)‖ ^ 2 * ‖(show E from v)‖ ^ 2 -
      ⟪(show E from u), (show E from v)⟫_ℝ ^ 2 :=
    euclidean_gram_pos_of_bilinear_gram_ne_zero B u v hplane
  have hnum := pos_of_unit_orthogonal hA hunit u v hEuclid
  have hden := bilinear_gram_pos_of_euclidean_gram_pos B (g.symm x) (g.pos x) u v hEuclid
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
  exact div_pos hnum hden

end DifferentialGeometry.Geometry.Curvature
