import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMap
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.MorseLine
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IdealTriangle

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_origin_displacement_bound_of_boundaryMap_fixed_triple
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (ξ : Fin 3 → Metric.sphere (0 : E) 1) (hξ : Function.Injective ξ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : C(Hyperboloid E, Hyperboloid E))
      (hf : ∀ x y : Hyperboloid E,
        L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ L * dist x y + C),
      (∀ j : Fin 3, boundaryMap f ⟨L, C, hL, hC, hf⟩ (ξ j) = ξ j) →
        dist (origin : Hyperboloid E) (f origin) ≤ B := by
  classical
  have hne (j : Fin 3) : ξ j ≠ ξ (j + 1) := by
    intro h
    have hj := hξ h
    fin_cases j <;> norm_num at hj
  choose x v hv ho hback hforward hchord using
    fun j : Fin 3 => exists_geodesicLine_with_endpoints (ξ j) (ξ (j + 1)) (hne j)
  let c (j : Fin 3) := geodesicLine (x j) (v j) (hv j) (ho j)
  obtain ⟨R, hR, hMorse⟩ := morse_lemma_line (E := E) L C hL hC
  let A : ℝ := ∑ j : Fin 3, dist (origin : Hyperboloid E) (x j)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => dist_nonneg
  have hAj (j : Fin 3) : dist (origin : Hyperboloid E) (x j) ≤ A :=
    Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ j)
  have hLp : 0 ≤ L := zero_le_one.trans hL
  let S : NNReal := ⟨R + L * A + C, by positivity⟩
  let K : Set (Hyperboloid E) := ⋂ j : Fin 3, Metric.cthickening (S : ℝ) (Set.range (c j))
  have hK : IsCompact K := isCompact_iInter_cthickening_geodesicLine_triangle
    ξ hξ x v hv ho hback hforward S
  obtain ⟨B, hKB⟩ := hK.isBounded.subset_closedBall (origin : Hyperboloid E)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro f hf hfix
  have hmem : f origin ∈ K := by
    apply Set.mem_iInter.mpr
    intro j
    have hc : Isometry (c j) := isometry_geodesicLine _ _ _ _
    have hq : Continuous (fun t => f (c j t)) := f.continuous.comp hc.continuous
    have hquasi (s t : ℝ) : L⁻¹ * dist s t - C ≤ dist (f (c j s)) (f (c j t)) ∧
        dist (f (c j s)) (f (c j t)) ≤ L * dist s t + C := by
      simpa only [hc.dist_eq] using hf (c j s) (c j t)
    obtain ⟨ηminus, ηplus, _, hm, hp, y, w, hw, how, hb, hfw, hhaus⟩ :=
      hMorse (fun t => f (c j t)) hq hquasi
    have hsourceMinus : Filter.Tendsto (fun t => (kleinHomeomorph (c j t) : E)) Filter.atBot
        (𝓝 (ξ j : E)) := by
      simpa only [hback j] using tendsto_kleinHomeomorph_geodesicLine_atBot (x j) (v j) (hv j) (ho j)
    have hsourcePlus : Filter.Tendsto (fun t => (kleinHomeomorph (c j t) : E)) Filter.atTop
        (𝓝 (ξ (j + 1) : E)) := by
      simpa only [hforward j] using tendsto_kleinHomeomorph_geodesicLine_atTop (x j) (v j) (hv j) (ho j)
    have htargetMinus := tendsto_kleinHomeomorph_boundaryMap f ⟨L, C, hL, hC, hf⟩ hsourceMinus
    have htargetPlus := tendsto_kleinHomeomorph_boundaryMap f ⟨L, C, hL, hC, hf⟩ hsourcePlus
    rw [hfix j] at htargetMinus
    rw [hfix (j + 1)] at htargetPlus
    have hmEq : ηminus = ξ j := Subtype.ext (tendsto_nhds_unique hm htargetMinus)
    have hpEq : ηplus = ξ (j + 1) := Subtype.ext (tendsto_nhds_unique hp htargetPlus)
    have hrange : Set.range (geodesicLine y w hw how) = Set.range (c j) := by
      have himage : (fun z : Hyperboloid E => (kleinHomeomorph z : E)) ''
          Set.range (geodesicLine y w hw how) =
          (fun z : Hyperboloid E => (kleinHomeomorph z : E)) '' Set.range (c j) := by
        rw [kleinHomeomorph_image_range_geodesicLine, hchord j, hb, hfw, hmEq, hpEq]
      exact Set.image_injective.mpr
        (fun a b h => (kleinHomeomorph (E := E)).injective (Subtype.ext h)) himage
    rw [hrange] at hhaus
    have hnear : Metric.infEDist (f (x j)) (Set.range (c j)) ≤ ENNReal.ofReal R := by
      have hm0 : f (x j) ∈ Set.range (fun t => f (c j t)) := by
        refine ⟨0, ?_⟩
        exact congrArg f (geodesicLine_zero (x j) (v j) (hv j) (ho j))
      exact (Metric.infEDist_le_hausdorffEDist_of_mem hm0).trans hhaus
    have hdist : dist (f origin) (f (x j)) ≤ L * A + C :=
      (hf origin (x j)).2.trans (add_le_add (mul_le_mul_of_nonneg_left (hAj j) hLp) le_rfl)
    apply Metric.mem_cthickening_iff.mpr
    calc
      Metric.infEDist (f origin) (Set.range (c j)) ≤
          edist (f origin) (f (x j)) + Metric.infEDist (f (x j)) (Set.range (c j)) :=
        Metric.infEDist_le_edist_add_infEDist
      _ ≤ ENNReal.ofReal (L * A + C) + ENNReal.ofReal R := by
        rw [edist_dist]
        exact add_le_add (ENNReal.ofReal_le_ofReal hdist) hnear
      _ = ENNReal.ofReal (S : ℝ) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ L * A + C) hR]
        congr 1
        change L * A + C + R = R + L * A + C
        ring
  have hb : dist (f origin) origin ≤ B := hKB hmem
  rw [dist_comm] at hb
  exact hb.trans (le_max_left _ _)

end DifferentialGeometry.Hyperboloid
