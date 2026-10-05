import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Actual short ambient minimizing geodesic segments remain inside a prescribed chart
neighborhood, by compact trapping of near-minimizers and the native smooth minimizer producer.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]

theorem exists_boundary_short_segment (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : E) (O : Set E) (hO : IsOpen O) (hp : p ∈ O) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ riemannianClosedBallOf g p r,
      ∀ b ∈ riemannianClosedBallOf g p r, ∃ γ : ℝ → E,
        γ 0 = a ∧ γ 1 = b ∧ ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O) ∧
        metricPathELength g γ 0 1 = riemannianEDistOf g a b ∧
        IsGeodesicOn g γ (Icc (0 : ℝ) 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.inner (γ t) (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t 1)
            (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t 1) = (riemannianEDistOf g a b).toReal ^ 2 := by
  obtain ⟨R, hR, hK, hKO⟩ :=
    exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds g p (hO.mem_nhds hp)
  let r : ℝ := R / 4
  have hr : 0 < r := div_pos hR (by norm_num)
  have hsum : ENNReal.ofReal r + (ENNReal.ofReal (2 * r) + ENNReal.ofReal r) =
      ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * r) hr.le,
      ← ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * r + r)]
    congr 1
    dsimp only [r]
    ring
  refine ⟨r, hr, ?_⟩
  intro a ha b hb
  change riemannianEDistOf g p a ≤ ENNReal.ofReal r at ha
  change riemannianEDistOf g p b ≤ ENNReal.ofReal r at hb
  have hap : riemannianEDistOf g a p ≤ ENNReal.ofReal r := by
    simpa only [riemannianEDistOf_comm g a p] using ha
  have habound : riemannianEDistOf g a b ≤ ENNReal.ofReal (2 * r) := by
    have h := (riemannianEDistOf_triangle g a p b).trans (add_le_add hap hb)
    simpa only [two_mul, ENNReal.ofReal_add hr.le hr.le] using h
  have hfinite : riemannianEDistOf g a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top habound
  have htrap : ∀ η : ℝ → E,
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc (0 : ℝ) 1) → η 0 = a → η 1 = b →
      metricPathELength g η 0 1 ≤ riemannianEDistOf g a b + ENNReal.ofReal r →
      ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ riemannianClosedBallOf g p R := by
    intro η hη hstart hend hnear s hs
    have hprefix := edistOf_le_metricPathELength g hs.1
      (hη.mono (Icc_subset_Icc le_rfl hs.2))
    rw [hstart] at hprefix
    have hprefixTotal :=
      (hprefix.trans (metricPathELength_mono g η le_rfl hs.2)).trans hnear
    have hbound := (riemannianEDistOf_triangle g p a (η s)).trans
      (add_le_add ha hprefixTotal)
    change riemannianEDistOf g p (η s) ≤ ENNReal.ofReal R
    calc
      _ ≤ ENNReal.ofReal r + (riemannianEDistOf g a b + ENNReal.ofReal r) := hbound
      _ ≤ ENNReal.ofReal r + (ENNReal.ofReal (2 * r) + ENNReal.ofReal r) :=
        by simpa only [add_assoc] using
          add_le_add_left (add_le_add_right habound (ENNReal.ofReal r)) (ENNReal.ofReal r)
      _ = ENNReal.ofReal R := hsum
  obtain ⟨γ, hstart, hend, hsmooth, hmem, hlength, hsub, hgeo, hspeed⟩ :=
    exists_smooth_geodesic_minimizer_of_compact_trapping g hK hr hfinite htrap
  exact ⟨γ, hstart, hend, hsmooth, fun t ht => hKO (hmem t ht), hlength, hgeo, hspeed⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
