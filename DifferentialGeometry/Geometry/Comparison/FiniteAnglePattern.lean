import DifferentialGeometry.Geometry.Comparison.GeodesicDirectionCurvature
import DifferentialGeometry.Geometry.Comparison.ModelAngleContinuity

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Finite ι] {q : X} [HasAnglesAt q]

theorem exists_common_shortening_angle_pattern
    {κ ε S : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hS : 0 < S)
    (ξ : ι → SpaceOfDirections q) (b : ι → ι → ℝ)
    (hsep : ∀ i j, i ≠ j → b i j < dist (ξ i) (ξ j)) :
    ∃ (σ : ι → GeodesicRepresentative q) (s θ : ℝ),
      0 < s ∧ s < S ∧ 0 < θ ∧
      (∀ i, dist (ξ i) (σ i).direction < ε) ∧
      (∀ i, s ≤ (σ i).length) ∧ (∀ i, dist q ((σ i).path s) = s) ∧
      (∀ i j, i ≠ j → b i j + 6 * θ < dist (σ i).direction (σ j).direction) ∧
      (∀ i j, i ≠ j → b i j + 5 * θ <
        comparisonAngleNegCurvature κ (dist q ((σ i).path s))
          (dist q ((σ j).path s)) (dist ((σ i).path s) ((σ j).path s))) ∧
      ∀ cap : ℝ, 0 < cap → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s / 8 ∧ ρ < cap ∧
        (∀ x ∈ ball q ρ, ∀ i, s / 2 < dist x ((σ i).path s)) ∧
        ∀ x ∈ ball q ρ, ∀ i j, i ≠ j → b i j + 4 * θ <
          comparisonAngleNegCurvature κ (dist x ((σ i).path s))
            (dist x ((σ j).path s)) (dist ((σ i).path s) ((σ j).path s)) := by
  have hmargin : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ i j : ι, i ≠ j →
      b i j + 8 * θ < dist (ξ i) (ξ j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have ht : Tendsto (fun θ : ℝ => b i j + 8 * θ)
        (𝓝[>] (0 : ℝ)) (𝓝 (b i j)) := by
      have hc : Continuous (fun θ : ℝ => b i j + 8 * θ) := by fun_prop
      have hc0 : ContinuousAt (fun θ : ℝ => b i j + 8 * θ) 0 := hc.continuousAt
      have ht0 : Tendsto (fun θ : ℝ => b i j + 8 * θ)
          (𝓝[>] (0 : ℝ)) (𝓝 (b i j + 8 * 0)) :=
        hc0.tendsto.mono_left nhdsWithin_le_nhds
      simpa using ht0
    filter_upwards [ht.eventually (eventually_lt_nhds (hsep i j hij))] with θ h _ using h
  have hεev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  obtain ⟨θ, hθε, hmarginθ⟩ := (hεev.and hmargin).exists
  choose σ hσ using fun i => (ξ i).exists_representative_dist_lt hθε.1
  have hdir (i j : ι) (hij : i ≠ j) :
      b i j + 6 * θ < dist (σ i).direction (σ j).direction := by
    have h₁ := dist_triangle (ξ i) (σ i).direction (ξ j)
    have h₂ := dist_triangle (σ i).direction (σ j).direction (ξ j)
    rw [dist_comm (σ j).direction (ξ j)] at h₂
    linarith [hσ i, hσ j, hmarginθ i j hij]
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i : ι, s ≤ (σ i).length := by
    apply eventually_all.mpr
    intro i
    filter_upwards [Ioc_mem_nhdsGT (σ i).length_pos] with s hs using hs.2
  have hcomp : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i j : ι, i ≠ j →
      b i j + 5 * θ < comparisonAngleNegCurvature κ s s
        (dist ((σ i).path s) ((σ j).path s)) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have hlim := (σ i).tendsto_comparisonAngleNegCurvature_dist_direction (σ j) hκ
    have hdiag : Tendsto (fun s : ℝ => (s, s)) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := tendsto_id.prodMk tendsto_id
    have hlim' : Tendsto (fun s : ℝ => comparisonAngleNegCurvature κ s s
        (dist ((σ i).path s) ((σ j).path s))) (𝓝[>] (0 : ℝ))
        (𝓝 (dist (σ i).direction (σ j).direction)) := by
      simpa only [Function.comp_def] using hlim.comp hdiag
    have hlt : b i j + 5 * θ < dist (σ i).direction (σ j).direction := by
      linarith [hdir i j hij, hθε.1]
    filter_upwards [hlim'.eventually (eventually_gt_nhds hlt)] with s hs _ using hs
  have hSev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 S := Ioo_mem_nhdsGT hS
  obtain ⟨s, hs, hsr, hsc⟩ := (hSev.and (hsmall.and hcomp)).exists
  have hrad (i : ι) : dist q ((σ i).path s) = s :=
    (σ i).dist_base_path ⟨hs.1.le, hsr i⟩
  refine ⟨σ, s, θ, hs.1, hs.2, hθε.1, (fun i => (hσ i).trans hθε.2),
    hsr, hrad, hdir, ?_, ?_⟩
  · intro i j hij
    rw [hrad i, hrad j]
    exact hsc i j hij
  · intro cap hcap
    have hne (i : ι) : q ≠ (σ i).path s := dist_pos.mp (by rw [hrad]; exact hs.1)
    have hcont (i j : ι) : ContinuousAt (fun x => comparisonAngleNegCurvature κ
        (dist x ((σ i).path s)) (dist x ((σ j).path s))
        (dist ((σ i).path s) ((σ j).path s))) q := by
      by_cases hk : κ = 0
      · subst κ
        simp only [comparisonAngleNegCurvature_zero, comparisonAngle]
        apply ContinuousAt.arccos
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · exact (mul_pos (mul_pos (by norm_num) (dist_pos.mpr (hne i)))
            (dist_pos.mpr (hne j))).ne'
      · exact tendsto_comparisonAngleNegCurvature_of_pos (lt_of_le_of_ne hκ (Ne.symm hk))
          ((continuous_id.dist continuous_const).continuousAt.tendsto)
          ((continuous_id.dist continuous_const).continuousAt.tendsto) tendsto_const_nhds
          (dist_pos.mpr (hne i)) (dist_pos.mpr (hne j))
    have hev : ∀ᶠ x in 𝓝 q, ∀ i j, i ≠ j → b i j + 4 * θ <
        comparisonAngleNegCurvature κ (dist x ((σ i).path s))
          (dist x ((σ j).path s)) (dist ((σ i).path s) ((σ j).path s)) := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      by_cases hij : i = j
      · exact Eventually.of_forall (fun _ h => (h hij).elim)
      have hbase : b i j + 4 * θ < comparisonAngleNegCurvature κ
          (dist q ((σ i).path s)) (dist q ((σ j).path s))
          (dist ((σ i).path s) ((σ j).path s)) := by
        rw [hrad i, hrad j]
        linarith [hsc i j hij, hθε.1]
      exact ((tendsto_order.mp (hcont i j)).1 _ hbase).mono (fun _ h _ => h)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
    let ρ := min (r / 2) (min (s / 16) (cap / 2))
    have hs0 : 0 < s := hs.1
    have hρ : 0 < ρ := lt_min (by positivity)
      (lt_min (by positivity) (by positivity))
    have hρr : ρ < r := (min_le_left _ _).trans_lt (by linarith)
    have hρs : ρ ≤ s / 16 := (min_le_right _ _).trans (min_le_left _ _)
    have hρcap : ρ ≤ cap / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ρ, hρ, by linarith, by linarith, ?_, ?_⟩
    · intro x hx i
      have hx' : dist x q < ρ := hx
      have ht := dist_triangle q x ((σ i).path s)
      rw [hrad, dist_comm q x] at ht
      linarith
    · intro x hx
      exact hball (by exact (show dist x q < ρ from hx).trans hρr)

end DifferentialGeometry.Geometry.Comparison.Toponogov
