import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinConvergence
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences

noncomputable section

open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem sphere_limit_mem_endpoint_pair
    (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (ξminus ξplus : Metric.sphere (0 : E) 1)
    (hminus : (x.time - v.1)⁻¹ • (x.space - v.2) = (ξminus : E))
    (hplus : (x.time + v.1)⁻¹ • (x.space + v.2) = (ξplus : E))
    (R : ℝ≥0) (z : ℕ → Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hz : ∀ n, z n ∈ Metric.cthickening (R : ℝ) (Set.range (geodesicLine x v hv ho)))
    (hlim : Filter.Tendsto (fun n => (kleinHomeomorph (z n) : E)) Filter.atTop (𝓝 (ξ : E))) :
    ξ = ξminus ∨ ξ = ξplus := by
  have hne : (ξminus : E) ≠ (ξplus : E) := by
    have h := geodesicLine_endpoints_ne x v hv ho
    rw [hminus, hplus] at h
    exact h.symm
  have hnear (n : ℕ) : ∃ y ∈ Set.range (geodesicLine x v hv ho), dist (z n) y < (R : ℝ) + 1 := by
    have hlt : ENNReal.ofReal (R : ℝ) < ENNReal.ofReal ((R : ℝ) + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    obtain ⟨y, hy, hdist⟩ := Metric.infEDist_lt_iff.mp ((hz n).trans_lt hlt)
    refine ⟨y, hy, ?_⟩
    rw [edist_dist] at hdist
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hdist
  choose y hy hdist using hnear
  have hylim := tendsto_kleinHomeomorph_of_dist_bounded
    (Filter.Eventually.of_forall fun n => (hdist n).le) hlim
  have hclosed : IsClosed (segment ℝ (ξminus : E) (ξplus : E)) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hmem : (ξ : E) ∈ segment ℝ (ξminus : E) (ξplus : E) := by
    apply hclosed.mem_of_tendsto hylim
    apply Filter.Eventually.of_forall
    intro n
    have h : (kleinHomeomorph (y n) : E) ∈
        (fun q : Hyperboloid E => (kleinHomeomorph q : E)) ''
          Set.range (geodesicLine x v hv ho) := ⟨y n, hy n, rfl⟩
    rw [kleinHomeomorph_image_range_geodesicLine, hminus, hplus] at h
    exact openSegment_subset_segment ℝ (ξminus : E) (ξplus : E) h
  by_cases hm : ξ = ξminus
  · exact Or.inl hm
  by_cases hp : ξ = ξplus
  · exact Or.inr hp
  have hopen : (ξ : E) ∈ openSegment ℝ (ξminus : E) (ξplus : E) :=
    mem_openSegment_of_ne_left_right
      (fun h => hm (Subtype.ext h.symm)) (fun h => hp (Subtype.ext h.symm)) hmem
  have hball := openSegment_subset_ball_of_ne
    (Metric.sphere_subset_closedBall ξminus.property)
    (Metric.sphere_subset_closedBall ξplus.property) hne hopen
  have hnorm : ‖(ξ : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
  have hlt : ‖(ξ : E)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hball
  exact (lt_irrefl 1 (hnorm ▸ hlt)).elim

theorem isCompact_iInter_cthickening_geodesicLine_triangle
    [ProperSpace E] (ξ : Fin 3 → Metric.sphere (0 : E) 1) (hξ : Function.Injective ξ)
    (x : Fin 3 → Hyperboloid E) (v : Fin 3 → ℝ × E)
    (hv : ∀ i, lorentzForm E (v i) (v i) = 1)
    (ho : ∀ i, lorentzForm E ((x i).time, (x i).space) (v i) = 0)
    (hminus : ∀ i, ((x i).time - (v i).1)⁻¹ • ((x i).space - (v i).2) = (ξ i : E))
    (hplus : ∀ i, ((x i).time + (v i).1)⁻¹ • ((x i).space + (v i).2) = (ξ (i + 1) : E))
    (R : ℝ≥0) :
    IsCompact (⋂ i : Fin 3,
      Metric.cthickening (R : ℝ) (Set.range (geodesicLine (x i) (v i) (hv i) (ho i)))) := by
  classical
  let S : Set (Hyperboloid E) := ⋂ i : Fin 3,
    Metric.cthickening (R : ℝ) (Set.range (geodesicLine (x i) (v i) (hv i) (ho i)))
  have hclosed : IsClosed S := isClosed_iInter fun _ => Metric.isClosed_cthickening
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  by_contra hbounded
  have hex (n : ℕ) : ∃ z ∈ S, (n : ℝ) < dist (origin : Hyperboloid E) z := by
    by_contra h
    push Not at h
    apply hbounded
    apply (Metric.isBounded_iff_subset_closedBall (origin : Hyperboloid E)).mpr
    refine ⟨n, ?_⟩
    intro z hz
    simpa only [Metric.mem_closedBall, dist_comm] using h z hz
  choose z hz hdist using hex
  have hK (n : ℕ) : (kleinHomeomorph (z n) : E) ∈ Metric.closedBall (0 : E) 1 :=
    Metric.ball_subset_closedBall (kleinHomeomorph (z n)).property
  obtain ⟨u, hu, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hK
  have hescape : Filter.Tendsto (fun n => dist (origin : Hyperboloid E) (z (φ n)))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    have hn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
    exact hn.trans (hdist (φ n)).le
  have hunorm : ‖u‖ = 1 := by
    have hle : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    by_contra hne
    have hlt : ‖u‖ < 1 := lt_of_le_of_ne hle hne
    let ub : Metric.ball (0 : E) 1 := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hlt⟩
    have hk : Filter.Tendsto (fun n => kleinHomeomorph (z (φ n))) Filter.atTop (𝓝 ub) :=
      tendsto_subtype_rng.mpr hlim
    have hzlim : Filter.Tendsto (fun n => z (φ n)) Filter.atTop (𝓝 (kleinHomeomorph.symm ub)) := by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
        (kleinHomeomorph.symm.continuous.tendsto ub).comp hk
    have hdlim : Filter.Tendsto (fun n => dist (origin : Hyperboloid E) (z (φ n)))
        Filter.atTop (𝓝 (dist origin (kleinHomeomorph.symm ub))) :=
      ((continuous_const.dist continuous_id).tendsto (kleinHomeomorph.symm ub)).comp hzlim
    exact (not_tendsto_nhds_of_tendsto_atTop hescape _) hdlim
  let η : Metric.sphere (0 : E) 1 := ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hunorm⟩
  have hpair (i : Fin 3) : η = ξ i ∨ η = ξ (i + 1) := by
    apply sphere_limit_mem_endpoint_pair (x i) (v i) (hv i) (ho i)
      (ξ i) (ξ (i + 1)) (hminus i) (hplus i) R (fun n => z (φ n)) η
    · intro n
      exact Set.mem_iInter.mp (hz (φ n)) i
    · exact hlim
  have h01 := hpair 0
  have h12 := hpair 1
  have h20 := hpair 2
  change η = ξ 0 ∨ η = ξ 1 at h01
  change η = ξ 1 ∨ η = ξ 2 at h12
  change η = ξ 2 ∨ η = ξ 0 at h20
  rcases h01 with h0 | h1
  · rcases h12 with h1 | h2
    · have h := hξ (h0.symm.trans h1)
      norm_num at h
    · have h := hξ (h0.symm.trans h2)
      norm_num at h
  · rcases h20 with h2 | h0
    · have h := hξ (h1.symm.trans h2)
      norm_num at h
    · have h := hξ (h1.symm.trans h0)
      norm_num at h

end DifferentialGeometry.Hyperboloid
