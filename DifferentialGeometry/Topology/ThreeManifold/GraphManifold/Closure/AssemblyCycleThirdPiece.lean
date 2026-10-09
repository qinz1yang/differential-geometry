import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpaceApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSides
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# FC42 packet G2: no third piece, the full rim chart, corner fibres

Lane ASM-CYC2, review 40 §4.1–§4.2 (packet G2).

* **No third piece** (`false_of_entering_entering_frequently`, abstract, and its ambient form
  `false_of_two_entering_and_piece`): at a point where two sets enter along half-spaces (the
  half-space normal form of G1, or the depth-one circle region) with disjoint interiors, no third
  set whose interior reaches the point along a NON-flat direction can have interior disjoint from
  both. The two entering half-spaces are forced to be opposite (`κ_B = -c κ_A`), and the third set
  comes in along a direction with `|κ_A| > ε ‖·‖`.
* **Corner germs** (`exists_frequently_mem_interior_range`): the image of ANY full-rank map of a
  three-manifold with corners (a vertex piece, a handle with its corners, an edge circle piece)
  reaches each of its points along every non-flat direction: only differentiability along a ray
  into the interior of the convex model range is used.
* **The circle region at depth one** (`CircleRegion.exists_entering`) and at depth zero
  (`CircleRegion.mem_interior_region_of_defining_neg`); the depth trichotomy `depth_cases`.
* **The full rim chart excludes other pieces** (`disjoint_rimChart_target_of_interior`, and the
  certificate forms `disjoint_vertex_rimChart_target`, `disjoint_handle_rimChart_target`,
  `disjoint_edgeCircle_rimChart_target`): the three closed sectors of a rim chart are its own
  vertex, handle and the circle region, so a set whose interior avoids those three interiors and
  which reaches its interior from every point (`exists_mem_inter_interior_range`) avoids the target.
* **Corner fibres are rim circles** (`exists_rimCircle_of_proj_eq_corner`).
* **Rim whole-fibre saturation** `rimChart_target_eq`: EXISTS in the tree as
  `roundingSupport_handleCorner` (`AssemblyCertificateSides.lean`); restated in the review's form.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The abstract no-third-piece lemma -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two half-space entering cones with disjoint targets point in opposite directions. -/
theorem not_pos_pos_of_entering {y₀ : F} {SA SB : Set F} {κA κB : F →L[ℝ] ℝ}
    (hA : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 y₀, ε * ‖y - y₀‖ < κA (y - y₀) → y ∈ SA)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 y₀, ε * ‖y - y₀‖ < κB (y - y₀) → y ∈ SB)
    (hAB : Disjoint SA SB) {w : F} (hwA : 0 < κA w) : κB w ≤ 0 := by
  by_contra hwB
  push Not at hwB
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hwA
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hpath : Tendsto (fun t : ℝ => y₀ + t • w) (𝓝[>] 0) (𝓝 y₀) := by
    have hc : Continuous (fun t : ℝ => y₀ + t • w) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hεA : 0 < κA w / (2 * ‖w‖) := by positivity
  have hεB : 0 < κB w / (2 * ‖w‖) := by positivity
  obtain ⟨t, ⟨htA, htB⟩, ht⟩ := (((hpath.eventually (hA _ hεA)).and
    (hpath.eventually (hB _ hεB))).and self_mem_nhdsWithin).exists
  have ht0 : 0 < t := ht
  have hsub : y₀ + t • w - y₀ = t • w := by abel
  have hnorm : ‖t • w‖ = t * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  rw [hsub, hnorm, map_smul, smul_eq_mul] at htA htB
  have hkA : κA w / (2 * ‖w‖) * (t * ‖w‖) < t * κA w := by
    field_simp
    nlinarith
  have hkB : κB w / (2 * ‖w‖) * (t * ‖w‖) < t * κB w := by
    field_simp
    nlinarith
  exact Set.disjoint_left.mp hAB (htA hkA) (htB hkB)

/-- Two nonzero functionals with no common positive direction are negatively proportional. -/
theorem exists_neg_mul_of_not_pos_pos {κA κB : F →L[ℝ] ℝ} (hκB : κB ≠ 0) (hA0 : κA ≠ 0)
    (h : ∀ w, 0 < κA w → κB w ≤ 0) : ∃ c : ℝ, 0 < c ∧ ∀ w, κB w = -(c * κA w) := by
  obtain ⟨v, hv⟩ : ∃ v, κA v ≠ 0 := by
    by_contra hc
    apply hA0
    ext v
    by_contra hv
    exact hc ⟨v, by simpa using hv⟩
  set w₀ : F := (κA v)⁻¹ • v with hw₀
  have hw₀1 : κA w₀ = 1 := by simp [w₀, hv]
  have hker : ∀ w', κA w' = 0 → κB w' = 0 := by
    intro w' hw'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- go along `w₀ - t • w'`
      set t : ℝ := (|κB w₀| + 1) / (-κB w')
      have ht : 0 < t := div_pos (by positivity) (by linarith)
      have h1 : 0 < κA (w₀ - t • w') := by simp [hw₀1, hw']
      have h2 := h _ h1
      have h3 : κB (w₀ - t • w') = κB w₀ + (|κB w₀| + 1) := by
        simp only [map_sub, map_smul, smul_eq_mul, t]
        field_simp
        ring
      rw [h3] at h2
      linarith [neg_abs_le (κB w₀)]
    · set t : ℝ := (|κB w₀| + 1) / κB w'
      have ht : 0 < t := div_pos (by positivity) hpos
      have h1 : 0 < κA (w₀ + t • w') := by simp [hw₀1, hw']
      have h2 := h _ h1
      have h3 : κB (w₀ + t • w') = κB w₀ + (|κB w₀| + 1) := by
        simp only [map_add, map_smul, smul_eq_mul, t]
        field_simp
      rw [h3] at h2
      linarith [neg_abs_le (κB w₀)]
  have hform : ∀ w, κB w = κA w * κB w₀ := by
    intro w
    have h0 : κA (w - κA w • w₀) = 0 := by simp [hw₀1]
    have h1 := hker _ h0
    simp only [map_sub, map_smul, smul_eq_mul] at h1
    linarith
  have hle : κB w₀ ≤ 0 := h w₀ (by rw [hw₀1]; exact one_pos)
  have hne : κB w₀ ≠ 0 := by
    intro h0
    apply hκB
    ext w
    simp [hform w, h0]
  refine ⟨-κB w₀, by
    rcases lt_or_eq_of_le hle with hl | he
    · linarith
    · exact absurd he hne, fun w => ?_⟩
  rw [hform w]
  ring

/-- **No third piece (abstract).** Two sets entering at `y₀` along half-spaces, with disjoint
targets, and a third set reached at `y₀` along non-flat directions for `κ_A`: the third set meets
one of the first two. -/
theorem false_of_entering_entering_frequently {y₀ : F} {SA SB SC : Set F}
    {κA κB : F →L[ℝ] ℝ} (hκA : κA ≠ 0) (hκB : κB ≠ 0)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 y₀, ε * ‖y - y₀‖ < κA (y - y₀) → y ∈ SA)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 y₀, ε * ‖y - y₀‖ < κB (y - y₀) → y ∈ SB)
    (hC : ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ y in 𝓝 y₀, ε * ‖y - y₀‖ < |κA (y - y₀)| ∧ y ∈ SC)
    (hAB : Disjoint SA SB) (hAC : Disjoint SA SC) (hBC : Disjoint SB SC) : False := by
  obtain ⟨c, hc, hBA⟩ := exists_neg_mul_of_not_pos_pos hκB hκA
    (fun w hw => not_pos_pos_of_entering hA hB hAB hw)
  obtain ⟨ε, hε, hfr⟩ := hC
  obtain ⟨y, ⟨hyC1, hyC2⟩, hyA, hyB⟩ :=
    (hfr.and_eventually ((hA ε hε).and (hB (c * ε) (by positivity)))).exists
  rcases le_or_gt 0 (κA (y - y₀)) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hyC1
    exact Set.disjoint_left.mp hAC (hyA hyC1) hyC2
  · rw [abs_of_neg hneg] at hyC1
    have : c * ε * ‖y - y₀‖ < κB (y - y₀) := by
      rw [hBA]
      nlinarith
    exact Set.disjoint_left.mp hBC (hyB this) hyC2

end Abstract

/-! ## Corner germs of full-rank maps -/

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {W : CompactCarrier.{u}} {F : M → W.Carrier}

/-- **Corner germ.** The image of a full-rank map of a three-manifold with corners (any convex
model) reaches each of its points, in the ambient chart, along every non-flat direction: for every
nonzero `μ` there are ambient interior points of the image arbitrarily close to `y₀ = ψ (F q)` with
`|μ (y - y₀)| > ε ‖y - y₀‖`. -/
theorem exists_frequently_mem_interior_range (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) (q : M)
    {μ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ} (hμ : μ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ y in 𝓝 (extChartAt W.model (F q) (F q)),
      ε * ‖y - extChartAt W.model (F q) (F q)‖ < |μ (y - extChartAt W.model (F q) (F q))| ∧
        (extChartAt W.model (F q)).symm y ∈ interior (range F) := by
  set φ := extChartAt I q with hφ
  set ψ := extChartAt W.model (F q) with hψ
  set g := writtenInExtChartAt I W.model q F with hg
  set x₀ := φ q with hx₀
  set y₀ := ψ (F q) with hy₀
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_mfderiv hbij q
  have hd : HasFDerivWithinAt g (A : E →L[ℝ] EuclideanSpace ℝ (Fin 3)) (range I) x₀ := by
    rw [hA]
    exact hasFDerivWithinAt_writtenInExtChartAt hF q
  have hgx₀ : g x₀ = y₀ := writtenInExtChartAt_self q
  have hx₀I : x₀ ∈ range I := extChartAt_target_subset_range q (mem_extChartAt_target q)
  -- a direction into the interior of the model range, not flat for `μ ∘ A`
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, μ (A v₀) ≠ 0 := by
    obtain ⟨w, hw⟩ : ∃ w, μ w ≠ 0 := by
      by_contra hc
      apply hμ
      ext w
      by_contra hw
      exact hc ⟨w, by simpa using hw⟩
    exact ⟨A.symm w, by simpa using hw⟩
  obtain ⟨z₀, hz₀⟩ := I.nonempty_interior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hz₀
  obtain ⟨z, hz, hzμ⟩ : ∃ z ∈ interior (range I), μ (A (z - x₀)) ≠ 0 := by
    by_cases h0 : μ (A (z₀ - x₀)) = 0
    · set δ : ℝ := r / (2 * (‖v₀‖ + 1)) with hδ
      have hδpos : 0 < δ := by positivity
      refine ⟨z₀ + δ • v₀, hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hδpos, hδ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v₀]
      · have : z₀ + δ • v₀ - x₀ = (z₀ - x₀) + δ • v₀ := by abel
        rw [this, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, zero_add]
        exact mul_ne_zero hδpos.ne' hv₀
    · exact ⟨z₀, hz₀, h0⟩
  set v : E := z - x₀ with hv
  set a : ℝ := |μ (A v)| with ha
  have hapos : 0 < a := abs_pos.mpr hzμ
  set b : ℝ := ‖A v‖ with hb
  set δ : ℝ := a / (4 * (‖μ‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hμδ : ‖μ‖ * δ ≤ a / 4 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg μ]
  have hδa : δ ≤ a / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg μ]
  set η : ℝ := δ / (‖v‖ + 1) with hη
  have hηpos : 0 < η := by positivity
  have hηv : η * ‖v‖ ≤ δ := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  set ε : ℝ := a / (2 * (b + a + 1)) with hε
  have hεpos : 0 < ε := by positivity
  -- the ray `x₀ + s • v`
  set p : ℝ → E := fun s => x₀ + s • v with hp
  have hpc : Continuous p := by fun_prop
  have hp0 : p 0 = x₀ := by simp [p]
  have hpint : ∀ s ∈ Ioo (0 : ℝ) 1, p s ∈ interior (range I) := fun s hs =>
    I.convex_range.add_smul_sub_mem_interior' (subset_closure hx₀I) hz ⟨hs.1, hs.2.le⟩
  have hev01 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hpT : Tendsto p (𝓝[>] 0) (𝓝[range I] x₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 := hpc.tendsto 0
      rw [hp0] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [hev01] with s hs
      exact interior_subset (hpint s hs)
  -- the chart domain
  obtain ⟨V, hVo, hx₀V, hVsub⟩ := exists_isOpen_chart_nhds (I := I) hF.continuous q
  have hpV : ∀ᶠ s in 𝓝[>] (0 : ℝ), p s ∈ V := by
    have h0 := hpc.tendsto 0
    rw [hp0] at h0
    exact (h0.mono_left nhdsWithin_le_nhds).eventually (hVo.mem_nhds hx₀V)
  have hlo := hpT.eventually (hd.isLittleO.def hηpos)
  have hyT : Tendsto (fun s => g (p s)) (𝓝[>] 0) (𝓝 y₀) := by
    rw [← hgx₀]
    exact hd.continuousWithinAt.tendsto.comp hpT
  refine ⟨ε, hεpos, hyT.frequently ?_⟩
  refine Eventually.frequently ?_
  filter_upwards [hev01, hpV, hlo] with s hs hsV hsl
  have hs0 : 0 < s := hs.1
  refine ⟨?_, ?_⟩
  · -- the quantitative estimate
    have hpx : p s - x₀ = s • v := by simp [p]
    rw [hpx, hgx₀] at hsl
    set r' := g (p s) - y₀ - (A : E →L[ℝ] EuclideanSpace ℝ (Fin 3)) (s • v) with hr'
    have hr'n : ‖r'‖ ≤ η * (s * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hsl
      exact hsl
    have hr'δ : ‖r'‖ ≤ s * δ := by
      have := mul_le_mul_of_nonneg_left hηv hs0.le
      nlinarith
    have hsplit : g (p s) - y₀ = s • A v + r' := by
      rw [hr']
      simp only [ContinuousLinearEquiv.coe_coe, map_smul]
      abel
    have hμr : |μ r'| ≤ ‖μ‖ * ‖r'‖ := by
      rw [← Real.norm_eq_abs]
      exact μ.le_opNorm r'
    have hμlow : 3 / 4 * (s * a) ≤ |μ (g (p s) - y₀)| := by
      rw [hsplit, map_add, map_smul, smul_eq_mul]
      have h1 : |s * μ (A v)| = s * a := by rw [abs_mul, abs_of_pos hs0]
      have h2 : |s * μ (A v)| - |μ r'| ≤ |s * μ (A v) + μ r'| := by
        have := abs_sub_abs_le_abs_sub (s * μ (A v)) (-(μ r'))
        simpa [sub_neg_eq_add] using this
      have h3 : ‖μ‖ * ‖r'‖ ≤ s * (a / 4) := by
        calc ‖μ‖ * ‖r'‖ ≤ ‖μ‖ * (s * δ) := mul_le_mul_of_nonneg_left hr'δ (norm_nonneg μ)
          _ = s * (‖μ‖ * δ) := by ring
          _ ≤ s * (a / 4) := mul_le_mul_of_nonneg_left hμδ hs0.le
      linarith
    have hnorm : ‖g (p s) - y₀‖ ≤ s * (b + a / 4) := by
      rw [hsplit]
      calc ‖s • A v + r'‖
          ≤ ‖s • A v‖ + ‖r'‖ := norm_add_le _ _
        _ ≤ s * b + s * δ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
            linarith
        _ ≤ s * (b + a / 4) := by
            have := mul_le_mul_of_nonneg_left hδa hs0.le
            linarith
    have hεb : ε * (b + a / 4) ≤ a / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hb0 : 0 ≤ b := norm_nonneg _
      nlinarith
    calc ε * ‖g (p s) - y₀‖ ≤ ε * (s * (b + a / 4)) := mul_le_mul_of_nonneg_left hnorm hεpos.le
      _ = s * (ε * (b + a / 4)) := by ring
      _ ≤ s * (a / 2) := mul_le_mul_of_nonneg_left hεb hs0.le
      _ < 3 / 4 * (s * a) := by have := mul_pos hs0 hapos; linarith
      _ ≤ |μ (g (p s) - y₀)| := hμlow
  · obtain ⟨hxT, hxS⟩ := hVsub (p s) ⟨hsV, interior_subset (hpint s hs)⟩
    exact symm_writtenInExtChartAt_mem_interior_range hdim hF hbij hxT hxS (hpint s hs)

/-- **No third piece (ambient form).** At a point `x` of `W` where two sets `A`, `B` enter along
half-spaces (in the ambient chart at `x`) with disjoint interiors, the image of a full-rank map of a
three-manifold with corners cannot pass through `x` with interior disjoint from both. -/
theorem false_of_two_entering_and_piece (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q)) (q : M)
    {A B : Set W.Carrier}
    (hA : ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (F q) (F q)),
        ε * ‖y - extChartAt W.model (F q) (F q)‖ < κ (y - extChartAt W.model (F q) (F q)) →
          (extChartAt W.model (F q)).symm y ∈ interior A)
    (hB : ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model (F q) (F q)),
        ε * ‖y - extChartAt W.model (F q) (F q)‖ < κ (y - extChartAt W.model (F q) (F q)) →
          (extChartAt W.model (F q)).symm y ∈ interior B)
    (hAB : Disjoint (interior A) (interior B)) (hAF : Disjoint (interior A) (interior (range F)))
    (hBF : Disjoint (interior B) (interior (range F))) : False := by
  obtain ⟨κA, hκA, hA⟩ := hA
  obtain ⟨κB, hκB, hB⟩ := hB
  exact false_of_entering_entering_frequently (SA := (extChartAt W.model (F q)).symm ⁻¹' interior A)
    (SB := (extChartAt W.model (F q)).symm ⁻¹' interior B)
    (SC := (extChartAt W.model (F q)).symm ⁻¹' interior (range F)) hκA hκB hA hB
    (exists_frequently_mem_interior_range hdim hF hbij q hκA)
    (hAB.preimage _) (hAF.preimage _) (hBF.preimage _)

end Germ

/-! ## Full-rank images reach their interior from every point -/

section Reach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {W : CompactCarrier.{u}} {F : M → W.Carrier}

/-- An open set meeting a full-rank image meets its ambient interior
(`exists_mem_inter_interior_range`, `AssemblyRimQuadrantProducer.lean`). -/
theorem inter_interior_range_nonempty (hdim : Module.finrank ℝ E = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    {O : Set W.Carrier} (hO : IsOpen O) (hne : (O ∩ range F).Nonempty) :
    (O ∩ interior (range F)).Nonempty := by
  obtain ⟨_, hxO, ⟨x, rfl⟩⟩ := hne
  exact exists_mem_inter_interior_range hdim hF hbij hO hxO

end Reach

/-! ## The circle region at depth zero and one -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The points of the domain where every defining function is negative. -/
theorem isOpen_negPart :
    IsOpen (Subtype.val '' (R.proj ⁻¹' {b | ∀ l, R.defining l b < 0})) := by
  apply R.domain.isOpen.isOpenMap_subtype_val
  apply R.proj.continuous.isOpen_preimage
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite fun l =>
    isOpen_lt (R.defining_smooth l).continuous continuous_const

theorem negPart_subset_region :
    Subtype.val '' (R.proj ⁻¹' {b | ∀ l, R.defining l b < 0}) ⊆ R.region := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  change R.proj z ∈ R.cornerBase
  rw [R.cornerBase_eq]
  exact fun l => (hz l).le

/-- **Depth zero.** A domain point over which every defining function is negative is an ambient
interior point of the region. -/
theorem mem_interior_region_of_defining_neg {x : W.Carrier} (hx : x ∈ R.domain)
    (h : ∀ l, R.defining l (R.proj ⟨x, hx⟩) < 0) : x ∈ interior R.region :=
  interior_maximal R.negPart_subset_region R.isOpen_negPart ⟨⟨x, hx⟩, h, rfl⟩

/-- **Depth trichotomy** of a point of the cornered base: depth zero, depth one, or a corner (the
centre of a corner chart). -/
theorem depth_cases {b : R.Base} (hb : b ∈ R.cornerBase) :
    (∀ l, R.defining l b < 0) ∨
      (∃ l, R.defining l b = 0 ∧ ∀ l', l' ≠ l → R.defining l' b < 0) ∨
        ∃ k, b = R.cornerChart k (0, 0) := by
  rw [R.cornerBase_eq] at hb
  by_cases h0 : ∃ l, R.defining l b = 0
  · obtain ⟨l, hl⟩ := h0
    by_cases h1 : ∃ l', l' ≠ l ∧ R.defining l' b = 0
    · obtain ⟨l', hne, hl'⟩ := h1
      exact Or.inr (Or.inr (R.corner_center b l' l hne hl' hl))
    · exact Or.inr (Or.inl ⟨l, hl, fun l' hne =>
        lt_of_le_of_ne (hb l') fun h => h1 ⟨l', hne, h⟩⟩)
  · exact Or.inl fun l => lt_of_le_of_ne (hb l) fun h => h0 ⟨l, h⟩

/-- **The circle region at depth one enters along a half-space.** At a domain point over which
exactly the defining function `l` vanishes, the region contains, in the ambient chart, every point
of the cone `κ (y - y₀) > ε ‖y - y₀‖` near `y₀` in its ambient interior (`κ` = minus the
differential of `defining l ∘ proj`). -/
theorem exists_entering {x : W.Carrier} (hx : x ∈ R.domain) {l : Fin R.definingCount}
    (hl : R.defining l (R.proj ⟨x, hx⟩) = 0)
    (hother : ∀ l', l' ≠ l → R.defining l' (R.proj ⟨x, hx⟩) < 0) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model x x),
        ε * ‖y - extChartAt W.model x x‖ < κ (y - extChartAt W.model x x) →
          (extChartAt W.model x).symm y ∈ interior R.region := by
  set ψ := extChartAt W.model x with hψ
  set y₀ := ψ x with hy₀
  set G : W.Carrier → ℝ := Function.extend (Subtype.val : R.domain → W.Carrier)
    (fun z => R.defining l (R.proj z)) 0 with hG
  have hGval : ∀ z : R.domain, G z = R.defining l (R.proj z) := fun z =>
    Subtype.val_injective.extend_apply _ _ z
  have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun z : R.domain => R.defining l (R.proj z)) :=
    (R.defining_smooth l).comp R.proj_smooth
  have hGfun : (fun z : R.domain => G z) = fun z => R.defining l (R.proj z) := funext hGval
  have hGat : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ G x := by
    have h1 : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun z : R.domain => G z) ⟨x, hx⟩ := by
      rw [hGfun]
      exact hsm _
    exact contMDiffAt_subtype_iff.mp h1
  have hMD : MDifferentiableAt W.model 𝓘(ℝ, ℝ) G x := hGat.mdifferentiableAt (by simp)
  -- the differential is not zero
  have hL : mfderiv W.model 𝓘(ℝ, ℝ) G x ≠ 0 := by
    intro h0
    have hval : MDifferentiableAt W.model W.model (Subtype.val : R.domain → W.Carrier) ⟨x, hx⟩ :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    have hc1 := mfderiv_comp (I := W.model) (I' := W.model) (I'' := 𝓘(ℝ, ℝ))
      (x := (⟨x, hx⟩ : R.domain))
      hMD hval
    have hfun : G ∘ (Subtype.val : R.domain → W.Carrier) = fun z => R.defining l (R.proj z) :=
      hGfun
    have hdl : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) (R.proj ⟨x, hx⟩) :=
      (R.defining_smooth l).mdifferentiableAt (by simp)
    have hpr : MDifferentiableAt W.model (𝓡 2) R.proj ⟨x, hx⟩ :=
      R.proj_smooth.mdifferentiableAt (by simp)
    have hc2 := mfderiv_comp (I := W.model) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
      (x := (⟨x, hx⟩ : R.domain)) hdl hpr
    apply R.defining_regular l _ hl
    ext w
    obtain ⟨v, hv⟩ := R.proj_submersion ⟨x, hx⟩ w
    have e1 : (mfderiv W.model 𝓘(ℝ, ℝ) (G ∘ Subtype.val) ⟨x, hx⟩) v = 0 := by
      rw [hc1, DifferentialGeometry.mfderiv_subtype_val, h0]
      rfl
    have e2 : (mfderiv W.model 𝓘(ℝ, ℝ) (G ∘ Subtype.val) ⟨x, hx⟩) v =
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) (R.proj ⟨x, hx⟩) w := by
      rw [hfun]
      change (mfderiv W.model 𝓘(ℝ, ℝ) (R.defining l ∘ R.proj) ⟨x, hx⟩) v = _
      rw [hc2, ContinuousLinearMap.comp_apply, hv]
    rw [← e2, e1]
    rfl
  -- the chart expression and its derivative
  have hint : W.model.IsInteriorPoint x := R.domain_interior hx
  have hFW : HasFDerivWithinAt (writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x G)
      (mfderiv W.model 𝓘(ℝ, ℝ) G x) (range W.model) y₀ := by
    rw [hMD.mfderiv_abuse]
    exact hMD.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hFD := hFW.hasFDerivAt (range_mem_nhds_isInteriorPoint hint)
  have hwr : ∀ y, writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x G y = G (ψ.symm y) := fun y => by
    simp [writtenInExtChartAt, ψ]
  have hGx : G (ψ.symm y₀) = 0 := by
    rw [hy₀, hψ, extChartAt_to_inv, show x = ((⟨x, hx⟩ : R.domain) : W.Carrier) from rfl,
      hGval, hl]
  set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) G x with hLdef
  refine ⟨-L, neg_ne_zero.mpr hL, fun ε hε => ?_⟩
  have hlo := hFD.isLittleO.def hε
  have hN : Subtype.val '' (R.proj ⁻¹' {b | ∀ l', l' ≠ l → R.defining l' b < 0}) ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ⟨⟨x, hx⟩, hother, rfl⟩
    apply R.domain.isOpen.isOpenMap_subtype_val
    apply R.proj.continuous.isOpen_preimage
    rw [ofPred_forall]
    refine isOpen_iInter_of_finite fun l' => ?_
    by_cases hl' : l' = l
    · simp [hl']
    · simpa [hl'] using isOpen_lt (R.defining_smooth l').continuous continuous_const
  filter_upwards [hlo, extChartAt_preimage_mem_nhds hN] with y hy hyN hcone
  obtain ⟨z, hz, hzy⟩ := hyN
  rw [hwr, hwr, hGx] at hy
  have hneg : G (ψ.symm y) < 0 := by
    have h1 : G (ψ.symm y) - L (y - y₀) ≤ ε * ‖y - y₀‖ := by
      have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hy)
      simpa using this
    change ε * ‖y - y₀‖ < -(L (y - y₀)) at hcone
    linarith
  rw [← hzy, hGval] at hneg
  refine interior_maximal R.negPart_subset_region R.isOpen_negPart ⟨z, fun l'' => ?_, hzy⟩
  by_cases hl'' : l'' = l
  · rw [hl'']
    exact hneg
  · exact hz l'' hl''

end CircleRegion

/-! ## The full rim chart, corner fibres, rim saturation -/

namespace DecompositionCertificate

local instance diskChartsG2_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothG2_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **Rim whole-fibre saturation** (review 40 §4.2; the tree's `roundingSupport_handleCorner`). -/
theorem rimChart_target_eq (h : Fin D.handleCount) (b : Bool) :
    (D.rimChart h b).target =
      Subtype.val '' (D.circ.proj ⁻¹' (D.circ.cornerChart (D.handleCorner h b)).target) :=
  (D.roundingSupport_handleCorner h b).symm

/-- A point of a rim chart image of an open set of chart coordinates lies in the ambient interior
of any set containing that image. -/
theorem rimChart_mem_interior {h : Fin D.handleCount} {b : Bool} {T : Set W.Carrier}
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hT : ∀ q, q ∈ (D.rimChart h b).source → q.2 ∈ O → D.rimChart h b q ∈ T)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart h b).source) (hpO : p.2 ∈ O) :
    D.rimChart h b p ∈ interior T := by
  refine interior_maximal (t := D.rimChart h b '' ((D.rimChart h b).source ∩ Prod.snd ⁻¹' O)) ?_
    ?_ ⟨p, ⟨hp, hpO⟩, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hT q hq.1 hq.2
  · exact (D.rimChart h b).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      ((D.rimChart h b).open_source.inter (hO.preimage continuous_snd)) inter_subset_left

/-- **The full rim chart excludes other pieces.** A set reaching its interior from each of its
points, whose interior avoids the interiors of the rim's vertex, handle and circle region, avoids
the rim chart target (the three closed sectors cover the chart). -/
theorem disjoint_rimChart_target_of_interior {S : Set W.Carrier}
    (hS : ∀ O : Set W.Carrier, IsOpen O → (O ∩ S).Nonempty → (O ∩ interior S).Nonempty)
    (h : Fin D.handleCount) (b : Bool)
    (hV : Disjoint (interior S) (interior (D.vertex (D.handleEnd h b)).image))
    (hH : Disjoint (interior S) (interior (range (D.handle h).map)))
    (hR : Disjoint (interior S) (interior D.circ.region)) :
    Disjoint S (D.rimChart h b).target := by
  rw [Set.disjoint_left]
  intro z hzS hzT
  obtain ⟨z', hz'T, hz'S⟩ := hS _ (D.rimChart h b).open_target ⟨z, hzT, hzS⟩
  set U := (D.rimChart h b).source ∩ (D.rimChart h b) ⁻¹' interior S with hU
  have hUo : IsOpen U :=
    (D.rimChart h b).toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
      (D.rimChart h b).open_source isOpen_interior
  have hUne : U.Nonempty := by
    refine ⟨(D.rimChart h b).symm z', (D.rimChart h b).map_target hz'T, ?_⟩
    have hri := (D.rimChart h b).right_inv hz'T
    simp only [mem_preimage]
    convert hz'S using 1
    exact hri
  have hdense : Dense {p : Circle × (ℝ × ℝ) | p.2.1 ≠ 0 ∧ p.2.2 ≠ 0} := by
    have h0 : Dense ((univ : Set Circle) ×ˢ (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ))) :=
      dense_univ.prod ((dense_compl_singleton 0).prod (dense_compl_singleton 0))
    convert h0 using 1
    ext p
    simp
  obtain ⟨p, ⟨hpsrc, hpS⟩, hp1, hp2⟩ := hdense.inter_open_nonempty U hUo hUne
  rcases lt_or_gt_of_ne hp2 with hy | hy
  · have hmem := D.rimChart_mem_interior (T := (D.vertex (D.handleEnd h b)).image)
      (O := {v | v.2 < 0}) (isOpen_lt continuous_snd continuous_const)
      (fun q hq hqO => (D.rim_vertex h b hq).mpr (le_of_lt hqO)) hpsrc hy
    exact Set.disjoint_left.mp hV hpS hmem
  · rcases lt_or_gt_of_ne hp1 with hx | hx
    · have hmem := D.rimChart_mem_interior (T := range (D.handle h).map)
        (O := {v | 0 < v.2 ∧ v.1 < 0})
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_fst continuous_const))
        (fun q hq hqO => (D.rim_handle h b hq).mpr ⟨hqO.1.le, hqO.2.le⟩) hpsrc ⟨hy, hx⟩
      exact Set.disjoint_left.mp hH hpS hmem
    · have hmem := D.rimChart_mem_interior (T := D.circ.region)
        (O := {v | 0 < v.1 ∧ 0 < v.2})
        ((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_const continuous_snd))
        (fun q hq hqO => (D.rim_region h b hq).mpr ⟨hqO.1.le, hqO.2.le⟩) hpsrc ⟨hx, hy⟩
      exact Set.disjoint_left.mp hR hpS hmem

/-- **G2.** Any vertex other than the rim's own end vertex avoids the rim chart target. -/
theorem disjoint_vertex_rimChart_target (h : Fin D.handleCount) (b : Bool) (k : Fin D.vertexCount)
    (hk : k ≠ D.handleEnd h b) : Disjoint (D.vertex k).image (D.rimChart h b).target := by
  have hreach : ∀ O : Set W.Carrier, IsOpen O → (O ∩ (D.vertex k).image).Nonempty →
      (O ∩ interior (D.vertex k).image).Nonempty := by
    intro O hO hne
    rw [Vertex.image_eq_range_piece] at hne ⊢
    exact inter_interior_range_nonempty finrank_euclideanSpace_fin (D.vertex k).piece.smooth
      (D.vertex k).piece.mfderiv_bijective hO hne
  exact D.disjoint_rimChart_target_of_interior hreach h b (D.vertex_disjoint hk)
    (D.vertex_handle_disjoint k h) (D.circ_vertex_disjoint k).symm

/-- **G2.** Any handle other than the rim's own handle avoids the rim chart target. -/
theorem disjoint_handle_rimChart_target (h : Fin D.handleCount) (b : Bool) (h' : Fin D.handleCount)
    (hh' : h' ≠ h) : Disjoint (range (D.handle h').map) (D.rimChart h b).target := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 :=
    finrank_handleModel
  exact D.disjoint_rimChart_target_of_interior
    (fun _ hO hne => inter_interior_range_nonempty hdim (D.handle h').smooth
      (D.handle h').mfderiv_bijective hO hne) h b
    (D.vertex_handle_disjoint (D.handleEnd h b) h').symm (D.handle_disjoint hh')
    (D.circ_handle_disjoint h').symm

/-- **G2.** Every edge circle piece avoids every rim chart target. -/
theorem disjoint_edgeCircle_rimChart_target (h : Fin D.handleCount) (b : Bool)
    (e : Fin D.edgeCircleCount) :
    Disjoint (range (D.edgeCircle e).piece.map) (D.rimChart h b).target :=
  D.disjoint_rimChart_target_of_interior
    (fun _ hO hne => inter_interior_range_nonempty finrank_euclideanSpace_fin
      (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective hO hne) h b
    (D.edgeCircle_vertex_disjoint e _) (D.edgeCircle_handle_disjoint e h)
    (D.circ_edgeCircle_disjoint e).symm

/-- **Corner fibres are rim circles.** A domain point over the centre of a corner chart lies on the
rim circle of the handle end with that corner, inside its rim chart target. -/
theorem exists_rimCircle_of_proj_eq_corner {x : W.Carrier} (hx : x ∈ D.circ.domain)
    {k : Fin D.circ.cornerCount} (hk : D.circ.proj ⟨x, hx⟩ = D.circ.cornerChart k (0, 0)) :
    ∃ h b, D.handleCorner h b = k ∧
      x ∈ (fun z : ClosedCell 2 => (D.handle h).map (z, iccEnd b)) '' diskRim ∧
        x ∈ (D.rimChart h b).target := by
  obtain ⟨⟨h, b⟩, hhb⟩ := D.handleCorner_bijective.2 k
  change D.handleCorner h b = k at hhb
  obtain ⟨b₀, hb₀⟩ := D.vertical_fibre h (iccEnd b)
  set p : Circle × (ℝ × ℝ) := (1, (0, 0)) with hpdef
  have hp : p ∈ (D.rimChart h b).source := (D.rim_source h b).mpr (by simp [p, rimBox])
  have hpr : D.rimChart h b p ∈
      (fun z : ClosedCell 2 => (D.handle h).map (z, iccEnd b)) '' diskRim := by
    rw [← D.rim_label h b]
    exact ⟨p, rfl, rfl⟩
  rw [hb₀] at hpr
  obtain ⟨w, hw, hwp⟩ := hpr
  obtain ⟨hxd, hproj⟩ := D.rim_proj h b p hp
  have hwe : w = ⟨D.rimChart h b p, hxd⟩ := Subtype.ext hwp
  have hb₀eq : b₀ = D.circ.cornerChart k (0, 0) := by
    have hw' : D.circ.proj w = b₀ := hw
    rw [← hw', hwe, hproj, hhb]
  have hxc : x ∈ Subtype.val '' (D.circ.proj ⁻¹' {b₀}) := by
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change D.circ.proj ⟨x, hx⟩ = b₀
    rw [hk, hb₀eq]
  rw [← hb₀] at hxc
  refine ⟨h, b, hhb, hxc, ?_⟩
  rw [← D.rim_label h b] at hxc
  obtain ⟨q, hq, rfl⟩ := hxc
  exact (D.rimChart h b).map_source ((D.rim_source h b).mpr (by
    rw [show q.2 = (0, 0) from hq]
    simp [rimBox]))

end DecompositionCertificate

end GC.GraphManifold.Assembly
