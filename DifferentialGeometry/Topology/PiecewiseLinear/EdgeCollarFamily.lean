/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def tetraDepth (z : Fin 4 → ℝ) : ℝ := min (min (z 0) (z 1)) (min (z 2) (z 3))

noncomputable def tetraRadialPoint (b : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  stdCenter 2 + t • (b - stdCenter 2)

noncomputable def tetraRadialProjection (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  stdCenter 2 + (1 - 4 * tetraDepth z)⁻¹ • (z - stdCenter 2)

def tetraRadialCollar (B : Set (Fin 4 → ℝ)) (τ : (Fin 4 → ℝ) → ℝ) : Set (Fin 4 → ℝ) :=
  {z | ∃ b ∈ B, ∃ t : ℝ, 1 - τ b ≤ t ∧ t ≤ 1 ∧ tetraRadialPoint b t = z}

theorem stdCenter_two_apply (i : Fin 4) : stdCenter 2 i = 1 / 4 := by
  simp only [stdCenter]
  norm_num

theorem tetraRadialPoint_apply (b : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    tetraRadialPoint b t i = 1 / 4 + t * (b i - 1 / 4) := by
  simp only [tetraRadialPoint, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    stdCenter_two_apply]

theorem tetraRadialProjection_apply (z : Fin 4 → ℝ) (i : Fin 4) :
    tetraRadialProjection z i = 1 / 4 + (1 - 4 * tetraDepth z)⁻¹ * (z i - 1 / 4) := by
  simp only [tetraRadialProjection, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    stdCenter_two_apply]

theorem tetraRadialPoint_one (b : Fin 4 → ℝ) : tetraRadialPoint b 1 = b := by
  funext i
  rw [tetraRadialPoint_apply]
  ring

theorem tetraDepth_le (z : Fin 4 → ℝ) (i : Fin 4) : tetraDepth z ≤ z i := by
  unfold tetraDepth
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem exists_eq_tetraDepth (z : Fin 4 → ℝ) : ∃ i, z i = tetraDepth z := by
  unfold tetraDepth
  rcases min_choice (min (z 0) (z 1)) (min (z 2) (z 3)) with h | h <;> rw [h]
  · rcases min_choice (z 0) (z 1) with h' | h' <;> rw [h']
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rcases min_choice (z 2) (z 3) with h' | h' <;> rw [h']
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

theorem le_tetraDepth {z : Fin 4 → ℝ} {a : ℝ} (h : ∀ i, a ≤ z i) : a ≤ tetraDepth z := by
  obtain ⟨i, hi⟩ := exists_eq_tetraDepth z
  rw [← hi]
  exact h i

theorem continuous_tetraDepth : Continuous tetraDepth := by
  unfold tetraDepth
  exact ((continuous_apply 0).min (continuous_apply 1)).min
    ((continuous_apply 2).min (continuous_apply 3))

theorem tetraDepth_stdCenter : tetraDepth (stdCenter 2) = 1 / 4 :=
  le_antisymm ((tetraDepth_le _ 0).trans (stdCenter_two_apply 0).le)
    (le_tetraDepth fun i => (stdCenter_two_apply i).ge)

theorem tetraDepth_eq_zero {b : Fin 4 → ℝ} (hb : b ∈ stdSimplexBoundary 3) : tetraDepth b = 0 := by
  obtain ⟨hbΔ, i, hi⟩ := hb
  exact le_antisymm ((tetraDepth_le b i).trans hi.le) (le_tetraDepth hbΔ.1)

theorem tetraDepth_tetraRadialPoint {b : Fin 4 → ℝ} (hb : b ∈ stdSimplexBoundary 3) {t : ℝ}
    (ht : 0 ≤ t) : tetraDepth (tetraRadialPoint b t) = (1 - t) / 4 := by
  obtain ⟨hbΔ, i, hi⟩ := hb
  apply le_antisymm
  · calc tetraDepth (tetraRadialPoint b t) ≤ tetraRadialPoint b t i := tetraDepth_le _ i
      _ = (1 - t) / 4 := by
          rw [tetraRadialPoint_apply, hi]
          ring
  · refine le_tetraDepth fun j => ?_
    rw [tetraRadialPoint_apply]
    have := mul_nonneg ht (hbΔ.1 j)
    nlinarith

theorem tetraRadialPoint_mem_stdSimplex {b : Fin 4 → ℝ} (hb : b ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : tetraRadialPoint b t ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
  (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 4)).add_smul_sub_mem
    (openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 2)) hb ⟨ht0, ht1⟩

theorem tetraRadialPoint_mem_openSimplex {b : Fin 4 → ℝ} (hb : b ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : tetraRadialPoint b t ∈ openSimplex (stdVertices 2) := by
  refine (mem_openSimplex_stdVertices_iff 2).mpr
    ⟨fun i => ?_, (tetraRadialPoint_mem_stdSimplex hb ht0 ht1.le).2⟩
  rw [tetraRadialPoint_apply]
  have := mul_nonneg ht0 (hb.1 i)
  nlinarith

theorem eq_of_tetraRadialPoint_eq {b b' : Fin 4 → ℝ} (hb : b ∈ stdSimplexBoundary 3)
    (hb' : b' ∈ stdSimplexBoundary 3) {t t' : ℝ} (ht : 0 < t) (ht' : 0 ≤ t')
    (h : tetraRadialPoint b t = tetraRadialPoint b' t') : b = b' ∧ t = t' := by
  have htt : t = t' := by
    have h1 := congrArg tetraDepth h
    rw [tetraDepth_tetraRadialPoint hb ht.le, tetraDepth_tetraRadialPoint hb' ht'] at h1
    linarith
  subst htt
  refine ⟨?_, rfl⟩
  funext i
  have h2 := congrFun h i
  rw [tetraRadialPoint_apply, tetraRadialPoint_apply] at h2
  have h3 : t * (b i - b' i) = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith

theorem dist_tetraRadialPoint_le {b : Fin 4 → ℝ} (hb : b ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) {t : ℝ}
    (ht : t ≤ 1) : dist (tetraRadialPoint b t) b ≤ 1 - t := by
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
  rw [Pi.sub_apply, tetraRadialPoint_apply, Real.norm_eq_abs, abs_le]
  have hb1 : b i ≤ 1 := by
    rw [← hb.2]
    exact Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ i)
  have hs : 0 ≤ 1 - t := by linarith
  have h1 := mul_nonneg hs (hb.1 i)
  have h2 := mul_nonneg hs (sub_nonneg.mpr hb1)
  constructor <;> nlinarith

theorem tetraRadialProjection_mem {z : Fin 4 → ℝ} (hz : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4))
    (hd : tetraDepth z < 1 / 4) : tetraRadialProjection z ∈ stdSimplexBoundary 3 := by
  have hs : 0 < 1 - 4 * tetraDepth z := by linarith
  have hsne : 1 - 4 * tetraDepth z ≠ 0 := hs.ne'
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [tetraRadialProjection_apply]
    have h1 := tetraDepth_le z i
    have h2 : (1 - 4 * tetraDepth z)⁻¹ * (tetraDepth z - 1 / 4) = -(1 / 4) := by
      field_simp
      ring
    have h3 : (1 - 4 * tetraDepth z)⁻¹ * (tetraDepth z - 1 / 4) ≤
        (1 - 4 * tetraDepth z)⁻¹ * (z i - 1 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hs.le)
    linarith
  · change ∑ i : Fin 4, tetraRadialProjection z i = 1
    rw [Fin.sum_univ_four, tetraRadialProjection_apply, tetraRadialProjection_apply,
      tetraRadialProjection_apply, tetraRadialProjection_apply]
    have hsum : z 0 + z 1 + z 2 + z 3 = 1 := by
      rw [← Fin.sum_univ_four]
      exact hz.2
    have h4 : (1 - 4 * tetraDepth z)⁻¹ * (z 0 - 1 / 4) +
        (1 - 4 * tetraDepth z)⁻¹ * (z 1 - 1 / 4) + (1 - 4 * tetraDepth z)⁻¹ * (z 2 - 1 / 4) +
        (1 - 4 * tetraDepth z)⁻¹ * (z 3 - 1 / 4) =
        (1 - 4 * tetraDepth z)⁻¹ * (z 0 + z 1 + z 2 + z 3 - 1) := by ring
    rw [hsum, sub_self, mul_zero] at h4
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_tetraDepth z
    refine ⟨i, ?_⟩
    rw [tetraRadialProjection_apply, hi]
    field_simp
    ring

theorem tetraRadialPoint_tetraRadialProjection {z : Fin 4 → ℝ} (hd : tetraDepth z < 1 / 4) :
    tetraRadialPoint (tetraRadialProjection z) (1 - 4 * tetraDepth z) = z := by
  have hsne : 1 - 4 * tetraDepth z ≠ 0 := (by linarith : (0 : ℝ) < 1 - 4 * tetraDepth z).ne'
  funext i
  rw [tetraRadialPoint_apply, tetraRadialProjection_apply]
  field_simp
  ring

theorem tetraRadialProjection_eq_self {b : Fin 4 → ℝ} (hb : b ∈ stdSimplexBoundary 3) :
    tetraRadialProjection b = b := by
  funext i
  rw [tetraRadialProjection_apply, tetraDepth_eq_zero hb]
  ring

theorem continuousAt_tetraRadialProjection {z : Fin 4 → ℝ} (hd : tetraDepth z < 1 / 4) :
    ContinuousAt tetraRadialProjection z := by
  have hsne : 1 - 4 * tetraDepth z ≠ 0 := (by linarith : (0 : ℝ) < 1 - 4 * tetraDepth z).ne'
  unfold tetraRadialProjection
  exact continuousAt_const.add (((continuousAt_const.sub (continuousAt_const.mul
    continuous_tetraDepth.continuousAt)).inv₀ hsne).smul (continuousAt_id.sub continuousAt_const))

section Collar

variable {B : Set (Fin 4 → ℝ)} {τ : (Fin 4 → ℝ) → ℝ}

theorem tetraRadialCollar_subset_stdSimplex (hB : B ⊆ stdSimplexBoundary 3)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) : tetraRadialCollar B τ ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := by
  rintro _ ⟨b, hb, t, ht1, ht2, rfl⟩
  exact tetraRadialPoint_mem_stdSimplex (hB hb).1 (by linarith [hτ1 b]) ht2

theorem subset_tetraRadialCollar (hτ0 : ∀ b, 0 ≤ τ b) : B ⊆ tetraRadialCollar B τ :=
  fun b hb => ⟨b, hb, 1, by linarith [hτ0 b], le_rfl, tetraRadialPoint_one b⟩

theorem tetraDepth_le_of_mem_tetraRadialCollar (hB : B ⊆ stdSimplexBoundary 3)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) {z : Fin 4 → ℝ} (hz : z ∈ tetraRadialCollar B τ) :
    tetraDepth z ≤ 1 / 8 := by
  obtain ⟨b, hb, t, ht1, ht2, rfl⟩ := hz
  rw [tetraDepth_tetraRadialPoint (hB hb) (by linarith [hτ1 b])]
  linarith [hτ1 b]

theorem stdCenter_notMem_tetraRadialCollar (hB : B ⊆ stdSimplexBoundary 3)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) : stdCenter 2 ∉ tetraRadialCollar B τ := fun hc => by
  have h := tetraDepth_le_of_mem_tetraRadialCollar hB hτ1 hc
  rw [tetraDepth_stdCenter] at h
  norm_num at h

theorem mem_of_mem_tetraRadialCollar_of_notMem_openSimplex (hB : B ⊆ stdSimplexBoundary 3)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) {z : Fin 4 → ℝ} (hz : z ∈ tetraRadialCollar B τ)
    (hzo : z ∉ openSimplex (stdVertices 2)) : z ∈ B := by
  obtain ⟨b, hb, t, ht1, ht2, rfl⟩ := hz
  rcases ht2.lt_or_eq with ht | ht
  · exact absurd (tetraRadialPoint_mem_openSimplex (hB hb).1 (by linarith [hτ1 b]) ht) hzo
  · rw [ht, tetraRadialPoint_one]
    exact hb

theorem exists_dist_le_of_mem_tetraRadialCollar (hB : B ⊆ stdSimplexBoundary 3)
    {z : Fin 4 → ℝ} (hz : z ∈ tetraRadialCollar B τ) : ∃ b ∈ B, dist z b ≤ τ b := by
  obtain ⟨b, hb, t, ht1, ht2, rfl⟩ := hz
  exact ⟨b, hb, (dist_tetraRadialPoint_le (hB hb).1 ht2).trans (by linarith)⟩

theorem mem_of_mem_tetraRadialCollar_of_mem {Z : Set (Fin 4 → ℝ)} (hB : B ⊆ stdSimplexBoundary 3)
    (hτ0 : ∀ b, 0 ≤ τ b) (hτZ : ∀ b, τ b ≤ Metric.infDist b Z / 2) {z : Fin 4 → ℝ}
    (hz : z ∈ tetraRadialCollar B τ) (hzZ : z ∈ Z) : z ∈ B := by
  obtain ⟨b, hb, t, ht1, ht2, rfl⟩ := hz
  rcases (hτ0 b).eq_or_lt with h0 | h0
  · have ht : t = 1 := le_antisymm ht2 (by linarith)
    rw [ht, tetraRadialPoint_one]
    exact hb
  · exfalso
    have hdist := dist_tetraRadialPoint_le (hB hb).1 ht2
    have hinf : Metric.infDist b Z ≤ dist b (tetraRadialPoint b t) :=
      Metric.infDist_le_dist_of_mem hzZ
    rw [dist_comm] at hinf
    have := hτZ b
    linarith

theorem isCompact_tetraRadialCollar (hBc : IsCompact B) (hτ : Continuous τ)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) : IsCompact (tetraRadialCollar B τ) := by
  have hS : IsCompact {p : (Fin 4 → ℝ) × ℝ | p.1 ∈ B ∧ 1 - τ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
    refine (hBc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
    · exact (hBc.isClosed.preimage continuous_fst).inter
        ((isClosed_le (continuous_const.sub (hτ.comp continuous_fst)) continuous_snd).inter
          (isClosed_le continuous_snd continuous_const))
    · intro p hp
      exact ⟨hp.1, by linarith [hτ1 p.1, hp.2.1], hp.2.2⟩
  have heq : tetraRadialCollar B τ = (fun p : (Fin 4 → ℝ) × ℝ => tetraRadialPoint p.1 p.2) ''
      {p : (Fin 4 → ℝ) × ℝ | p.1 ∈ B ∧ 1 - τ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
    ext z
    constructor
    · rintro ⟨b, hb, t, ht1, ht2, rfl⟩
      exact ⟨(b, t), ⟨hb, ht1, ht2⟩, rfl⟩
    · rintro ⟨⟨b, t⟩, ⟨hb, ht1, ht2⟩, rfl⟩
      exact ⟨b, hb, t, ht1, ht2, rfl⟩
  rw [heq]
  refine hS.image ?_
  unfold tetraRadialPoint
  exact continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))

theorem disjoint_tetraRadialCollar {B' : Set (Fin 4 → ℝ)} {τ' : (Fin 4 → ℝ) → ℝ}
    (hB : B ⊆ stdSimplexBoundary 3) (hB' : B' ⊆ stdSimplexBoundary 3) (hτ1 : ∀ b, τ b ≤ 1 / 2)
    (hτ1' : ∀ b, τ' b ≤ 1 / 2) (hd : Disjoint B B') :
    Disjoint (tetraRadialCollar B τ) (tetraRadialCollar B' τ') := by
  rw [disjoint_left]
  rintro _ ⟨b, hb, t, ht1, ht2, rfl⟩ ⟨b', hb', t', ht1', ht2', heq⟩
  have hbb := (eq_of_tetraRadialPoint_eq (hB hb) (hB' hb') (by linarith [hτ1 b])
    (by linarith [hτ1' b']) heq.symm).1
  refine disjoint_left.mp hd hb ?_
  rw [hbb]
  exact hb'

theorem starConvex_sdiff_tetraRadialCollar (hB : B ⊆ stdSimplexBoundary 3)
    (hτ1 : ∀ b, τ b ≤ 1 / 2) :
    StarConvex ℝ (stdCenter 2) (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) \ tetraRadialCollar B τ) := by
  have hcΔ : stdCenter 2 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 2)
  intro y ⟨hyΔ, hyM⟩ a b ha hb hab
  refine ⟨(Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 4)) hcΔ hyΔ ha hb hab, fun hw => ?_⟩
  have hwd := tetraDepth_le_of_mem_tetraRadialCollar hB hτ1 hw
  have ha' : a = 1 - b := by linarith
  subst ha'
  by_cases hyc : tetraDepth y < 1 / 4
  · have hs0 : 0 < 1 - 4 * tetraDepth y := by linarith
    have hsne : 1 - 4 * tetraDepth y ≠ 0 := hs0.ne'
    have hy0 : 0 ≤ tetraDepth y := le_tetraDepth hyΔ.1
    have hπ := tetraRadialProjection_mem hyΔ hyc
    have hweq : (1 - b) • stdCenter 2 + b • y =
        tetraRadialPoint (tetraRadialProjection y) (b * (1 - 4 * tetraDepth y)) := by
      funext i
      rw [tetraRadialPoint_apply, tetraRadialProjection_apply]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, stdCenter_two_apply]
      field_simp
      ring
    obtain ⟨b₀, hb₀, t₀, ht₀1, ht₀2, hρ⟩ := hw
    rw [hweq] at hρ
    obtain ⟨hbb, htt⟩ := eq_of_tetraRadialPoint_eq (hB hb₀) hπ (by linarith [hτ1 b₀])
      (mul_nonneg hb hs0.le) hρ
    apply hyM
    have hb1 : b ≤ 1 := by linarith
    have hbs : b * (1 - 4 * tetraDepth y) ≤ 1 - 4 * tetraDepth y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hs0.le]
    refine ⟨tetraRadialProjection y, hbb ▸ hb₀, 1 - 4 * tetraDepth y, ?_, by linarith,
      tetraRadialPoint_tetraRadialProjection hyc⟩
    rw [← hbb]
    linarith
  · have hge : ∀ i, 1 / 4 ≤ y i := fun i => (not_lt.mp hyc).trans (tetraDepth_le y i)
    have hw4 : 1 / 4 ≤ tetraDepth ((1 - b) • stdCenter 2 + b • y) := by
      refine le_tetraDepth fun i => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, stdCenter_two_apply]
      have := mul_le_mul_of_nonneg_left (hge i) hb
      linarith
    linarith

theorem exists_ball_inter_subset_tetraRadialCollar {β : Fin 4 → ℝ}
    (hβ : β ∈ stdSimplexBoundary 3) (hτ : ContinuousAt τ β) (hτβ : 0 < τ β)
    (hBβ : ∀ᶠ b in 𝓝[stdSimplexBoundary 3] β, b ∈ B) :
    ∃ r > 0, Metric.ball β r ∩ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ⊆ tetraRadialCollar B τ := by
  have hd0 : tetraDepth β = 0 := tetraDepth_eq_zero hβ
  have hdlt : tetraDepth β < 1 / 4 := by
    rw [hd0]
    norm_num
  have hπβ : tetraRadialProjection β = β := tetraRadialProjection_eq_self hβ
  have hπc : ContinuousAt tetraRadialProjection β := continuousAt_tetraRadialProjection hdlt
  have hU : {z | tetraDepth z < 1 / 4} ∈ 𝓝 β :=
    (isOpen_lt continuous_tetraDepth continuous_const).mem_nhds hdlt
  have hπ : Tendsto tetraRadialProjection (𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 4)] β)
      (𝓝[stdSimplexBoundary 3] β) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto tetraRadialProjection (𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 4)] β)
          (𝓝 (tetraRadialProjection β)) := hπc.tendsto.mono_left nhdsWithin_le_nhds
      rwa [hπβ] at h
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU] with z hz hzd
      exact tetraRadialProjection_mem hz hzd
  have h1 : ∀ᶠ z in 𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 4)] β, tetraRadialProjection z ∈ B := hπ.eventually hBβ
  have hτπ : ContinuousAt (fun z => τ (tetraRadialProjection z)) β := hτ.comp_of_eq hπc hπβ
  have hlt : 1 - τ (tetraRadialProjection β) < 1 - 4 * tetraDepth β := by
    rw [hπβ, hd0]
    linarith
  have h2 : ∀ᶠ z in 𝓝 β, 1 - τ (tetraRadialProjection z) < 1 - 4 * tetraDepth z :=
    (continuousAt_const.sub hτπ).eventually_lt
      (continuousAt_const.sub (continuousAt_const.mul continuous_tetraDepth.continuousAt)) hlt
  have hall : ∀ᶠ z in 𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 4)] β, z ∈ tetraRadialCollar B τ := by
    filter_upwards [self_mem_nhdsWithin, h1, mem_nhdsWithin_of_mem_nhds hU,
      mem_nhdsWithin_of_mem_nhds h2] with z hz hzB hzd hzτ
    have hz0 : 0 ≤ tetraDepth z := le_tetraDepth hz.1
    exact ⟨tetraRadialProjection z, hzB, 1 - 4 * tetraDepth z, hzτ.le, by linarith,
      tetraRadialPoint_tetraRadialProjection hzd⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hall
  exact ⟨r, hr, hball⟩

end Collar

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

theorem exists_edgeCollarFamily (ht : IsTube K N C D Dbd h N') (V : E3 → Set E3)
    (hV : ∀ v ∈ K.vertices, V v ∈ nhdsSet (h '' C v)) :
    ∃ W : Finset E3 → Set E3, IsEdgeCollarFamily K C D Dbd h V W := by
  have hcont := ht.continuousOn
  have hinj := ht.injOn
  have hVfin := ht.finite_vertices
  have hvert : ∀ e ∈ K.faces, ∀ a ∈ e, a ∈ K.vertices := fun e he a ha =>
    K.down_closed he (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)
  have hCN : ∀ a ∈ K.vertices, C a ⊆ N := fun a ha => ht.dualCell_subset ha
  have hCc : ∀ a ∈ K.vertices, IsCompact (C a) := fun a ha =>
    (ht.dualBall a ha).isPolyhedron.isCompact
  have hC'c : ∀ a ∈ K.vertices, IsCompact (h '' C a) := fun a ha =>
    (hCc a ha).image_of_continuousOn (hcont.mono (hCN a ha))
  have hKN : K.space ⊆ N := subset_of_mem_nhdsSet ht.isNeighborhood
  have hKcl : IsClosed (h '' K.space) := by
    have : Finite K.faces := ht.facesFinite.to_subtype
    exact ((isPolyhedron_space K).isCompact.image_of_continuousOn (hcont.mono hKN)).isClosed
  obtain ⟨ε, hε, hεV⟩ : ∃ ε > 0, ∀ v ∈ K.vertices, Metric.thickening ε (h '' C v) ⊆ V v := by
    have hev : ∀ v ∈ K.vertices, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Metric.thickening ε (h '' C v) ⊆ V v := by
      intro v hv
      obtain ⟨U, hU, hCU, hUV⟩ := mem_nhdsSet_iff_exists.mp (hV v hv)
      obtain ⟨δ, hδ, hδU⟩ := (hC'c v hv).exists_thickening_subset_open hU hCU
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      exact (Metric.thickening_mono hε.2.le _).trans (hδU.trans hUV)
    obtain ⟨ε, hε1, hε2⟩ :=
      (((eventually_all_finite hVfin).mpr hev).and self_mem_nhdsWithin).exists
    exact ⟨ε, hε2, hε1⟩
  have hmodel : ∀ a : E3, ∃ g : (Fin 4 → ℝ) → E3, ∃ δ : ℝ, a ∈ K.vertices →
      ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∧ InjOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∧
      g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) = h '' C a ∧ g '' stdSimplexBoundary 3 = frontier (h '' C a) ∧
      g '' openSimplex (stdVertices 2) = interior (h '' C a) ∧ 0 < δ ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4), ∀ y ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4), dist x y < δ →
        dist (g x) (g y) < ε := by
    intro a
    by_cases ha : a ∈ K.vertices
    · obtain ⟨g, hgc, hgi, hgim, hgbd, hgint⟩ := ht.exists_dualCell_model ha
      obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp
        ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 4)).uniformContinuousOn_of_continuous hgc) ε hε
      exact ⟨g, δ, fun _ => ⟨hgc, hgi, hgim, hgbd, hgint, hδ, hδg⟩⟩
    · exact ⟨fun _ => 0, 0, fun h' => absurd h' ha⟩
  choose g δ hg using hmodel
  obtain ⟨τ, hτdef⟩ : ∃ τ : E3 → (Fin 4 → ℝ) → ℝ, τ = fun a b => min (1 / 2) (min (δ a / 2)
      (Metric.infDist b (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space)) / 2)) := ⟨_, rfl⟩
  have hτ1 : ∀ a b, τ a b ≤ 1 / 2 := fun a b => by
    rw [hτdef]
    exact min_le_left _ _
  have hτδ : ∀ a b, τ a b ≤ δ a / 2 := fun a b => by
    rw [hτdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτZ : ∀ a b, τ a b ≤
      Metric.infDist b (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space)) / 2 := fun a b => by
    rw [hτdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hτ0 : ∀ a ∈ K.vertices, ∀ b, 0 ≤ τ a b := fun a ha b => by
    have hδ := (hg a ha).2.2.2.2.2.1
    have hinf := Metric.infDist_nonneg (x := b)
      (s := Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space))
    rw [hτdef]
    exact le_min (by norm_num) (le_min (by linarith) (by linarith))
  have hτc : ∀ a, Continuous (τ a) := fun a => by
    rw [hτdef]
    exact continuous_const.min (continuous_const.min
      ((Metric.continuous_infDist_pt _).div_const 2))
  obtain ⟨Bs, hBdef⟩ : ∃ Bs : E3 → Finset E3 → Set (Fin 4 → ℝ),
      Bs = fun a e => Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' D e) := ⟨_, rfl⟩
  have hBmem : ∀ a e b, b ∈ Bs a e ↔ b ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∧ g a b ∈ h '' D e := by
    intro a e b
    rw [hBdef]
    exact Iff.rfl
  obtain ⟨M, hMdef⟩ : ∃ M : E3 → Finset E3 → Set (Fin 4 → ℝ),
      M = fun a e => tetraRadialCollar (Bs a e) (τ a) := ⟨_, rfl⟩
  have hMeq : ∀ a e, M a e = tetraRadialCollar (Bs a e) (τ a) := by
    intro a e
    rw [hMdef]
  have hDc : ∀ e ∈ K.faces, e.card = 2 → IsCompact (D e) := fun e he hc => by
    obtain ⟨r, hr, -⟩ := ht.splitCell e he hc
    exact (show IsPLBall 2 (D e) from ⟨r, hr⟩).isPolyhedron.isCompact
  have hDCa : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, D e ⊆ C a := fun e he hc a hae =>
    (ht.splitDisk_subset_frontier (hvert e he a hae) he hc hae).trans
      (hCc a (hvert e he a hae)).isClosed.frontier_subset
  have hDN : ∀ e ∈ K.faces, e.card = 2 → D e ⊆ N := fun e he hc => by
    obtain ⟨a, hae⟩ := K.nonempty_of_mem_faces he
    exact (hDCa e he hc a hae).trans (hCN a (hvert e he a hae))
  have hDfrA : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, h '' D e ⊆ frontier (h '' C a) := by
    intro e he hc a hae
    have ha := hvert e he a hae
    rw [frontier_image_eq_image_frontier_of_isCompact (hCc a ha) (hcont.mono (hCN a ha))
      (hinj.mono (hCN a ha))]
    exact image_mono (ht.splitDisk_subset_frontier ha he hc hae)
  have hBbd : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, Bs a e ⊆ stdSimplexBoundary 3 := by
    intro e he hc a hae b hb
    have ha := hvert e he a hae
    obtain ⟨hbΔ, hbD⟩ := (hBmem a e b).mp hb
    obtain ⟨-, hgi, -, hgbd, -⟩ := hg a ha
    have hfr := hDfrA e he hc a hae hbD
    rw [← hgbd] at hfr
    obtain ⟨b', hb', hbb'⟩ := hfr
    rw [← hgi hb'.1 hbΔ hbb']
    exact hb'
  have hBc : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, IsCompact (Bs a e) := by
    intro e he hc a hae
    have ha := hvert e he a hae
    have hcl : IsClosed (Bs a e) := by
      rw [hBdef]
      exact (hg a ha).1.preimage_isClosed_of_isClosed (Convexity.StdSimplex.isCompact_coordinateSet ℝ _).isClosed
        ((hDc e he hc).image_of_continuousOn (hcont.mono (hDN e he hc))).isClosed
    exact (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 4)).of_isClosed_subset hcl
      fun b hb => ((hBmem a e b).mp hb).1
  have hMsubΔ : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, M a e ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
    fun e he hc a hae => by
      rw [hMeq]
      exact tetraRadialCollar_subset_stdSimplex (hBbd e he hc a hae) (hτ1 a)
  have hBM : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, Bs a e ⊆ M a e := fun e he hc a hae => by
    rw [hMeq]
    exact subset_tetraRadialCollar (hτ0 a (hvert e he a hae))
  have hGsub : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, g a '' M a e ⊆ h '' C a :=
    fun e he hc a hae => by
      rw [← (hg a (hvert e he a hae)).2.2.1]
      exact image_mono (hMsubΔ e he hc a hae)
  have hGc : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, IsCompact (g a '' M a e) :=
    fun e he hc a hae => by
      have hMc : IsCompact (M a e) := by
        rw [hMeq]
        exact isCompact_tetraRadialCollar (hBc e he hc a hae) (hτc a) (hτ1 a)
      exact hMc.image_of_continuousOn ((hg a (hvert e he a hae)).1.mono (hMsubΔ e he hc a hae))
  have hDG : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, h '' D e ⊆ g a '' M a e := by
    intro e he hc a hae y hy
    have ha := hvert e he a hae
    obtain ⟨-, -, -, hgbd, -⟩ := hg a ha
    have hfr := hDfrA e he hc a hae hy
    rw [← hgbd] at hfr
    obtain ⟨β, hβ, hgβ⟩ := hfr
    refine ⟨β, hBM e he hc a hae ((hBmem a e β).mpr ⟨hβ.1, ?_⟩), hgβ⟩
    rw [hgβ]
    exact hy
  have hGbd : ∀ e ∈ K.faces, e.card = 2 → ∀ a ∈ e, ∀ z ∈ g a '' M a e,
      z ∉ interior (h '' C a) → z ∈ h '' D e := by
    intro e he hc a hae z hz hzi
    have ha := hvert e he a hae
    obtain ⟨-, -, -, -, hgint, -, -⟩ := hg a ha
    obtain ⟨w, hw, rfl⟩ := hz
    have hwo : w ∉ openSimplex (stdVertices 2) := by
      intro hwo
      apply hzi
      rw [← hgint]
      exact ⟨w, hwo, rfl⟩
    rw [hMeq] at hw
    exact ((hBmem a e w).mp (mem_of_mem_tetraRadialCollar_of_notMem_openSimplex
      (hBbd e he hc a hae) (hτ1 a) hw hwo)).2
  have hIeqp : ∀ e ∈ K.faces, ∀ a ∈ e, ∀ a' ∈ e, interior (h '' C a ∪ h '' C a') =
      h '' interior (C a ∪ C a') := by
    intro e he a hae a' ha'e
    have ha := hvert e he a hae
    have ha' := hvert e he a' ha'e
    rw [← image_union]
    exact interior_image_eq_image_interior_of_isCompact ((hCc a ha).union (hCc a' ha'))
      (hcont.mono (union_subset (hCN a ha) (hCN a' ha')))
      (hinj.mono (union_subset (hCN a ha) (hCN a' ha')))
  have hFeqp : ∀ e ∈ K.faces, ∀ a ∈ e, ∀ a' ∈ e, frontier (h '' C a ∪ h '' C a') =
      h '' frontier (C a ∪ C a') := by
    intro e he a hae a' ha'e
    have ha := hvert e he a hae
    have ha' := hvert e he a' ha'e
    rw [← image_union]
    exact frontier_image_eq_image_frontier_of_isCompact ((hCc a ha).union (hCc a' ha'))
      (hcont.mono (union_subset (hCN a ha) (hCN a' ha')))
      (hinj.mono (union_subset (hCN a ha) (hCN a' ha')))
  have hDIp : ∀ e ∈ K.faces, ∀ a ∈ e, ∀ a' ∈ e, a ≠ a' →
      h '' (D e \ Dbd e) ⊆ interior (h '' C a ∪ h '' C a') := by
    intro e he a hae a' ha'e haa'
    rw [hIeqp e he a hae a' ha'e]
    exact image_mono (ht.splitDisk_sdiff_subset_interior (hvert e he a hae) (hvert e he a' ha'e)
      haa' he hae ha'e)
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Finset E3 → Set E3, Wf = fun e => ⋃ a ∈ e, g a '' M a e :=
    ⟨_, rfl⟩
  have hWe : ∀ e, Wf e = ⋃ a ∈ e, g a '' M a e := by
    intro e
    rw [hWf]
  refine ⟨Wf, ?_⟩
  intro e he hc
  obtain ⟨u, hue⟩ := K.nonempty_of_mem_faces he
  obtain ⟨v, hve, hvu⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) u
  have huv : u ≠ v := Ne.symm hvu
  have hDK : h '' D e ∩ h '' K.space = {h (e.centroid ℝ id)} := by
    rw [← hinj.image_inter (hDN e he hc) hKN, ht.splitMidpoint he hc, image_singleton]
  have hWcl : IsClosed (Wf e) := by
    rw [hWe]
    exact isClosed_biUnion_finset fun a hae => (hGc e he hc a hae).isClosed
  have hWK : Wf e ∩ h '' K.space = {h (e.centroid ℝ id)} := by
    apply Subset.antisymm
    · rintro z ⟨hzW, hzK⟩
      rw [hWe] at hzW
      obtain ⟨a, hae, hza⟩ := mem_iUnion₂.mp hzW
      have ha := hvert e he a hae
      obtain ⟨w, hw, rfl⟩ := hza
      have hwZ : w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space) :=
        ⟨hMsubΔ e he hc a hae hw, hzK⟩
      rw [hMeq] at hw
      have hwB := mem_of_mem_tetraRadialCollar_of_mem (hBbd e he hc a hae) (hτ0 a ha) (hτZ a)
        hw hwZ
      rw [← hDK]
      exact ⟨((hBmem a e w).mp hwB).2, hzK⟩
    · rintro _ rfl
      have hmid : e.centroid ℝ id ∈ D e ∩ K.space := by
        rw [ht.splitMidpoint he hc]
        exact mem_singleton _
      refine ⟨?_, ⟨_, hmid.2, rfl⟩⟩
      rw [hWe]
      exact mem_iUnion₂.mpr ⟨u, hue, hDG e he hc u hue ⟨_, hmid.1, rfl⟩⟩
  have hlocal : ∀ a ∈ e, ∀ a' ∈ e, a ≠ a' → ∀ y ∈ h '' (D e \ Dbd e),
      y ≠ h (e.centroid ℝ id) → ∃ T : Set E3, IsOpen T ∧ y ∈ T ∧ T ∩ h '' C a ⊆ g a '' M a e := by
    intro a hae a' ha'e haa' y hyD hyc
    have ha := hvert e he a hae
    have ha' := hvert e he a' ha'e
    obtain ⟨hgc, hgi, hgim, hgbd, -, hδ, -⟩ := hg a ha
    have hyI := hDIp e he a hae a' ha'e haa' hyD
    have hyD' : y ∈ h '' D e := image_mono sdiff_subset hyD
    have hyfr := hDfrA e he hc a hae hyD'
    rw [← hgbd] at hyfr
    obtain ⟨β, hβ, hgβ⟩ := hyfr
    have hkey : ∀ w ∈ frontier (h '' C a), w ∈ interior (h '' C a ∪ h '' C a') →
        w ∈ h '' D e := by
      intro w hwF hwI
      have hwC : w ∈ h '' C a := (hC'c a ha).isClosed.frontier_subset hwF
      by_contra hwD
      have hwa' : w ∉ h '' C a' := by
        intro hwa'
        apply hwD
        rw [← ht.inter_eq_of_mem_faces ha ha' haa' he hae ha'e,
          hinj.image_inter (hCN a ha) (hCN a' ha')]
        exact ⟨hwC, hwa'⟩
      have hopen : IsOpen (interior (h '' C a ∪ h '' C a') ∩ (h '' C a')ᶜ) :=
        isOpen_interior.inter (hC'c a' ha').isClosed.isOpen_compl
      have hsub : interior (h '' C a ∪ h '' C a') ∩ (h '' C a')ᶜ ⊆ h '' C a := by
        rintro x ⟨hxI, hxa'⟩
        rcases interior_subset hxI with h1 | h1
        · exact h1
        · exact absurd h1 hxa'
      exact hwF.2 (interior_maximal hsub hopen ⟨hwI, hwa'⟩)
    have hBβ : ∀ᶠ b in 𝓝[stdSimplexBoundary 3] β, b ∈ Bs a e := by
      have hyI' : g a β ∈ interior (h '' C a ∪ h '' C a') := by
        rw [hgβ]
        exact hyI
      have h1 : g a ⁻¹' interior (h '' C a ∪ h '' C a') ∈ 𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 4)] β :=
        (hgc β hβ.1).preimage_mem_nhdsWithin (isOpen_interior.mem_nhds hyI')
      have h2 : g a ⁻¹' interior (h '' C a ∪ h '' C a') ∈ 𝓝[stdSimplexBoundary 3] β :=
        nhdsWithin_mono _ (fun b hb => hb.1) h1
      filter_upwards [h2, self_mem_nhdsWithin] with b hbI hb
      refine (hBmem a e b).mpr ⟨hb.1, hkey _ ?_ hbI⟩
      rw [← hgbd]
      exact ⟨b, hb, rfl⟩
    have hZcl : IsClosed (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space)) :=
      hgc.preimage_isClosed_of_isClosed (Convexity.StdSimplex.isCompact_coordinateSet ℝ _).isClosed hKcl
    have hZne : (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space)).Nonempty := by
      have hha : h a ∈ g a '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := by
        rw [hgim]
        exact ⟨a, ht.mem_dualCell ha, rfl⟩
      obtain ⟨w, hw, hwa⟩ := hha
      exact ⟨w, hw, a, Geometry.SimplicialComplex.vertices_subset_space ha, hwa.symm⟩
    have hβZ : β ∉ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ∩ g a ⁻¹' (h '' K.space) := by
      rintro ⟨-, hβK⟩
      have hyK : y ∈ h '' K.space := by
        rw [← hgβ]
        exact hβK
      have hmem : y ∈ h '' D e ∩ h '' K.space := ⟨hyD', hyK⟩
      rw [hDK] at hmem
      exact hyc hmem
    have hτβ : 0 < τ a β := by
      have hinf := (hZcl.notMem_iff_infDist_pos hZne).mp hβZ
      rw [hτdef]
      exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
    obtain ⟨r, hr, hball⟩ := exists_ball_inter_subset_tetraRadialCollar hβ
      (hτc a).continuousAt hτβ hBβ
    obtain ⟨T, hT, hTeq⟩ := exists_isOpen_inter_image_eq_of_isCompact
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 4)) hgc hgi (Metric.isOpen_ball (x := β) (ε := r))
    refine ⟨T, hT, ?_, ?_⟩
    · have hmem : g a β ∈ g a '' (Metric.ball β r ∩ Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) :=
        ⟨β, ⟨Metric.mem_ball_self hr, hβ.1⟩, rfl⟩
      rw [← hTeq, hgβ] at hmem
      exact hmem.1
    · rw [← hgim, hTeq, hMeq]
      exact image_mono hball
  have hint : h '' (D e \ Dbd e) \ {h (e.centroid ℝ id)} ⊆ interior (Wf e) := by
    rintro y ⟨hyD, hyc⟩
    obtain ⟨Tu, hTu, hyTu, hTuG⟩ := hlocal u hue v hve huv y hyD hyc
    obtain ⟨Tv, hTv, hyTv, hTvG⟩ := hlocal v hve u hue hvu y hyD hyc
    have hyI := hDIp e he u hue v hve huv hyD
    refine mem_interior.mpr ⟨interior (h '' C u ∪ h '' C v) ∩ Tu ∩ Tv, ?_,
      (isOpen_interior.inter hTu).inter hTv, ⟨⟨hyI, hyTu⟩, hyTv⟩⟩
    rintro z ⟨⟨hzI, hzTu⟩, hzTv⟩
    rw [hWe]
    rcases interior_subset hzI with hzu | hzv
    · exact mem_iUnion₂.mpr ⟨u, hue, hTuG ⟨hzTu, hzu⟩⟩
    · exact mem_iUnion₂.mpr ⟨v, hve, hTvG ⟨hzTv, hzv⟩⟩
  have hpair : ∀ a ∈ e, ∀ a' ∈ e, a ≠ a' → Wf e ⊆ h '' C a ∪ h '' C a' ∧
      Wf e ∩ frontier (h '' C a ∪ h '' C a') = h '' Dbd e := by
    intro a hae a' ha'e haa'
    have ha := hvert e he a hae
    have ha' := hvert e he a' ha'e
    have hY₀N : C a ∪ C a' ⊆ N := union_subset (hCN a ha) (hCN a' ha')
    have hsub : Wf e ⊆ h '' C a ∪ h '' C a' := by
      rw [hWe]
      refine iUnion₂_subset fun c hce => ?_
      rcases eq_or_eq_of_mem_of_card_eq_two hc hae ha'e haa' hce with h1 | h1
      · rw [h1]
        rw [h1] at hce
        exact (hGsub e he hc a hce).trans subset_union_left
      · rw [h1]
        rw [h1] at hce
        exact (hGsub e he hc a' hce).trans subset_union_right
    refine ⟨hsub, Subset.antisymm ?_ ?_⟩
    · rintro z ⟨hzW, hzF⟩
      rw [hWe] at hzW
      obtain ⟨c, hce, hzc⟩ := mem_iUnion₂.mp hzW
      have hzD : z ∈ h '' D e := by
        refine hGbd e he hc c hce z hzc fun hzi => hzF.2 ?_
        rcases eq_or_eq_of_mem_of_card_eq_two hc hae ha'e haa' hce with h1 | h1
        · rw [h1] at hzi
          exact interior_mono subset_union_left hzi
        · rw [h1] at hzi
          exact interior_mono subset_union_right hzi
      obtain ⟨x, hxD, rfl⟩ := hzD
      by_contra hxb
      have hxb' : x ∉ Dbd e := fun h' => hxb ⟨x, h', rfl⟩
      exact hzF.2 (hDIp e he a hae a' ha'e haa' ⟨x, ⟨hxD, hxb'⟩, rfl⟩)
    · rintro _ ⟨x, hxb, rfl⟩
      have hxDN : x ∈ D e ∩ frontier N := by
        rw [ht.splitProper e he hc]
        exact hxb
      refine ⟨?_, ?_⟩
      · rw [hWe]
        exact mem_iUnion₂.mpr ⟨a, hae, hDG e he hc a hae ⟨x, hxDN.1, rfl⟩⟩
      · rw [hFeqp e he a hae a' ha'e]
        exact ⟨x, ⟨subset_closure (Or.inl (hDCa e he hc a hae hxDN.1)),
          fun hxint => hxDN.2.2 (interior_mono hY₀N hxint)⟩, rfl⟩
  have hconnV : ∀ a ∈ e, IsConnected (h '' C a \ Wf e) ∧ Wf e ⊆ V a := by
    intro a hae
    have ha := hvert e he a hae
    obtain ⟨hgc, hgi, hgim, -, -, -, -⟩ := hg a ha
    refine ⟨?_, ?_⟩
    · have hWC : Wf e ∩ h '' C a ⊆ g a '' M a e := by
        rintro z ⟨hzW, hzC⟩
        rw [hWe] at hzW
        obtain ⟨c, hce, hzc⟩ := mem_iUnion₂.mp hzW
        by_cases hca : c = a
        · rw [hca] at hzc
          exact hzc
        · have hc' := hvert e he c hce
          have hzD : z ∈ h '' D e := by
            rw [← ht.inter_eq_of_mem_faces hc' ha hca he hce hae,
              hinj.image_inter (hCN c hc') (hCN a ha)]
            exact ⟨hGsub e he hc c hce hzc, hzC⟩
          exact hDG e he hc a hae hzD
      have heq : h '' C a \ Wf e = g a '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) \ M a e) := by
        rw [hgi.image_sdiff_subset (hMsubΔ e he hc a hae), hgim]
        apply Subset.antisymm
        · rintro z ⟨hzC, hzW⟩
          refine ⟨hzC, fun hzG => hzW ?_⟩
          rw [hWe]
          exact mem_iUnion₂.mpr ⟨a, hae, hzG⟩
        · rintro z ⟨hzC, hzG⟩
          exact ⟨hzC, fun hzW => hzG (hWC ⟨hzW, hzC⟩)⟩
      rw [heq, hMeq]
      have hsc := starConvex_sdiff_tetraRadialCollar (hBbd e he hc a hae) (hτ1 a)
      have hcM : stdCenter 2 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) \ tetraRadialCollar (Bs a e) (τ a) :=
        ⟨openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 2),
          stdCenter_notMem_tetraRadialCollar (hBbd e he hc a hae) (hτ1 a)⟩
      exact ((hsc.isPathConnected hcM).isConnected).image _ (hgc.mono sdiff_subset)
    · rw [hWe]
      refine iUnion₂_subset fun c hce => ?_
      have hc' := hvert e he c hce
      obtain ⟨-, -, -, -, -, hδ', hδg'⟩ := hg c hc'
      rintro _ ⟨w, hw, rfl⟩
      have hwΔ := hMsubΔ e he hc c hce hw
      rw [hMeq] at hw
      obtain ⟨b, hb, hwb⟩ := exists_dist_le_of_mem_tetraRadialCollar (hBbd e he hc c hce) hw
      obtain ⟨hbΔ, hbD⟩ := (hBmem c e b).mp hb
      have hgb : g c b ∈ h '' C a := image_mono (hDCa e he hc a hae) hbD
      refine hεV a ha (Metric.mem_thickening_iff.mpr ⟨g c b, hgb, hδg' w hwΔ b hbΔ ?_⟩)
      linarith [hτδ c b]
  have hdisj : ∀ f ∈ K.faces, f.card = 2 → e ≠ f → Disjoint (Wf e) (Wf f) := by
    intro f hf hfc hef
    have hDD : Disjoint (h '' D e) (h '' D f) := by
      rw [disjoint_iff_inter_eq_empty, ← hinj.image_inter (hDN e he hc) (hDN f hf hfc),
        (ht.splitDisjoint he hc hf hfc hef).inter_eq, image_empty]
    rw [hWe, hWe, disjoint_left]
    intro z hze hzf
    obtain ⟨a, hae, hza⟩ := mem_iUnion₂.mp hze
    obtain ⟨c, hcf, hzc⟩ := mem_iUnion₂.mp hzf
    have ha := hvert e he a hae
    have hc' := hvert f hf c hcf
    by_cases hac : a = c
    · subst hac
      obtain ⟨-, hgi, -, -, -⟩ := hg a ha
      obtain ⟨w, hw, rfl⟩ := hza
      obtain ⟨w', hw', hww'⟩ := hzc
      have hweq : w' = w := hgi (hMsubΔ f hf hfc a hcf hw') (hMsubΔ e he hc a hae hw) hww'
      rw [hweq] at hw'
      rw [hMeq] at hw hw'
      have hBB : Disjoint (Bs a e) (Bs a f) := by
        rw [disjoint_left]
        intro b hbe hbf
        exact disjoint_left.mp hDD ((hBmem a e b).mp hbe).2 ((hBmem a f b).mp hbf).2
      exact disjoint_left.mp (disjoint_tetraRadialCollar (hBbd e he hc a hae)
        (hBbd f hf hfc a hcf) (hτ1 a) (hτ1 a) hBB) hw hw'
    · have hzCa := hGsub e he hc a hae hza
      have hzCc := hGsub f hf hfc c hcf hzc
      have hfr : ∀ p q : E3, p ∈ K.vertices → q ∈ K.vertices → p ≠ q →
          h '' C p ∩ h '' C q ⊆ frontier (h '' C p) := by
        intro p q hp hq hpq
        rw [← hinj.image_inter (hCN p hp) (hCN q hq),
          frontier_image_eq_image_frontier_of_isCompact (hCc p hp) (hcont.mono (hCN p hp))
            (hinj.mono (hCN p hp))]
        exact image_mono (ht.dualCell_inter_subset_frontier hp hq hpq)
      have hzDe := hGbd e he hc a hae z hza fun hzi => (hfr a c ha hc' hac ⟨hzCa, hzCc⟩).2 hzi
      have hzDf := hGbd f hf hfc c hcf z hzc fun hzi =>
        (hfr c a hc' ha (Ne.symm hac) ⟨hzCc, hzCa⟩).2 hzi
      exact disjoint_left.mp hDD hzDe hzDf
  exact ⟨hWcl, hint, hWK, hpair, hconnV, hdisj⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
