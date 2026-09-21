import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckAnnulus
import DifferentialGeometry.Topology.Order.Iteration

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_spatialNeck_sequence_along_isometric_curve
    (g : SmoothRiemannianMetric I3 M) {a b eps : ℝ} (hab : a < b)
    (hsmall : eps < 1 / 1000000)
    (gamma : C(Ico a b, M))
    (hgamma : ∀ s t, riemannianEDistOf g (gamma s) (gamma t) = edist s t)
    (hnecks : ∀ t, Nonempty (SpatialNeck g eps (gamma t)))
    (hquant : ∀ t : Ico a b,
      (eps⁻¹) ^ 2 ≤ metricScalarAt g (gamma t) * (b - t) ^ 2) :
    ∃ s : ℕ → Ico a b, ∃ nk : ∀ n, SpatialNeck g eps (gamma (s n)),
      (s 0 : ℝ) = a ∧ StrictMono (fun n => (s n : ℝ)) ∧
      Tendsto (fun n => (s n : ℝ)) atTop (𝓝 b) ∧
      (∀ n, (s (n + 1) : ℝ) - s n =
        (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n)))) ∧
      (∀ n, ∀ t : Ico a b, (s n : ℝ) ≤ t → (t : ℝ) ≤ s (n + 1) →
        gamma t ∈ (nk n).map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10))) ∧
      (∀ n, ∃ (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (height : Sphere 2 → ℝ),
        ContMDiff I2 𝓘(ℝ, ℝ) ∞ height ∧
        (∀ p, height p ∈ Ioo (-eps⁻¹) eps⁻¹) ∧
        ∀ p, (nk n).map (p, height p) = (nk (n + 1)).map (eta p, 0)) ∧
      Pairwise (fun i j => Disjoint ((nk i).map '' (univ ×ˢ ({0} : Set ℝ)))
        ((nk j).map '' (univ ×ˢ ({0} : Set ℝ)))) ∧
      (∀ n, ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
        ∃ Ψ : PartialDiffeomorph IC I3 Cylinder M ∞,
          (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
          (∀ p, Ψ (p, 0) = (nk n).map (p, 0)) ∧
          (∀ p, Ψ (p, 1) = (nk (n + 1)).map (eta p, 0)) ∧
          IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
          (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
            (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
              (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
          Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
            (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) := by
  classical
  have heps : 0 < eps := (Classical.choice (hnecks ⟨a, le_rfl, hab⟩)).eps_pos
  let neck (t : Ico a b) := Classical.choice (hnecks t)
  have hQ (t : Ico a b) : 0 < metricScalarAt g (gamma t) := (neck t).Q_pos
  have hc : Continuous (fun t : Ico a b => metricScalarAt g (gamma t)) :=
    (metricScalar_smooth g).continuous.comp gamma.continuous
  let d : C(Ico a b, ℝ) :=
    ⟨fun t => (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma t)),
      continuous_const.div hc.sqrt (fun t => (Real.sqrt_pos.mpr (hQ t)).ne')⟩
  have hd (t : Ico a b) : 0 < d t :=
    div_pos (div_pos (inv_pos.mpr heps) (by norm_num)) (Real.sqrt_pos.mpr (hQ t))
  have hfit (t : Ico a b) : (t : ℝ) + d t < b := by
    have hs := Real.sq_sqrt (hQ t).le
    have hg : 0 < b - t := sub_pos.mpr t.property.2
    have hsep : eps⁻¹ ≤ Real.sqrt (metricScalarAt g (gamma t)) * (b - t) := by
      have hh : (eps⁻¹) ^ 2 ≤ (Real.sqrt (metricScalarAt g (gamma t)) * (b - t)) ^ 2 := by
        rw [mul_pow, hs]
        exact hquant t
      exact (sq_le_sq₀ (inv_pos.mpr heps).le
        (mul_nonneg (Real.sqrt_nonneg _) hg.le)).mp hh
    have hh : (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma t)) < b - t := by
      apply (div_lt_iff₀ (Real.sqrt_pos.mpr (hQ t))).mpr
      nlinarith [inv_pos.mpr heps]
    change (t : ℝ) + (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma t)) < b
    linarith
  obtain ⟨s, hs0, hmono, hlim, hstep⟩ :=
    DifferentialGeometry.Topology.exists_strictMono_sequence_of_pos_continuous_step hab d hd hfit
  let nk (n : ℕ) := neck (s n)
  have hcover (n : ℕ) (t : Ico a b) (ht0 : (s n : ℝ) ≤ t)
      (ht1 : (t : ℝ) ≤ s (n + 1)) :
      gamma t ∈ (nk n).map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)) := by
    have hi : 0 < eps⁻¹ := inv_pos.mpr heps
    apply (nk n).ball_subset_image_slab (by positivity) (by linarith)
    change riemannianEDistOf g (gamma (s n)) (gamma t) < _
    rw [hgamma, edist_dist, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht0), neg_sub]
    have hsqrt : 1 / 2 < Real.sqrt (1 - eps) := by
      have hh := Real.sq_sqrt (by linarith : 0 ≤ 1 - eps)
      nlinarith [Real.sqrt_nonneg (1 - eps)]
    have hnum : eps⁻¹ / 40 < (eps⁻¹ / 10) * Real.sqrt (1 - eps) := by
      nlinarith [mul_lt_mul_of_pos_left hsqrt (by positivity : 0 < eps⁻¹ / 10)]
    have hgap : (t : ℝ) - s n ≤ d (s n) := by linarith [hstep n]
    apply (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (by linarith)))
        (Real.sqrt_pos.mpr (hQ (s n))))).mpr
    exact hgap.trans_lt (div_lt_div_of_pos_right hnum (Real.sqrt_pos.mpr (hQ (s n))))
  have hdisjoint (i j : ℕ) (hij : i < j) :
      Disjoint ((nk i).map '' (univ ×ˢ ({0} : Set ℝ)))
        ((nk j).map '' (univ ×ˢ ({0} : Set ℝ))) := by
    apply (nk i).disjoint_central_spheres_of_edist_gt (nk j) hsmall
    rw [hgamma, edist_dist, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hmono hij).le), neg_sub]
    have hi : (1000000 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) heps).mpr
      (by simpa only [one_div] using hsmall)
    have hb := div_lt_div_of_pos_right (by linarith : (21 : ℝ) < eps⁻¹ / 40)
      (Real.sqrt_pos.mpr (hQ (s i)))
    have hs := hstep i
    change (s (i + 1) : ℝ) = (s i : ℝ) +
      (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s i))) at hs
    apply (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr (hmono hij))).mpr
    linarith [hmono.monotone (Nat.succ_le_of_lt hij)]
  refine ⟨s, nk, hs0, hmono, hlim, ?_, hcover, ?_, ?_, ?_⟩
  · intro n
    have hh := hstep n
    change (s (n + 1) : ℝ) = (s n : ℝ) +
      (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))) at hh
    linarith
  · intro n
    exact (nk n).exists_graph_in_nearby_neck (nk (n + 1)) hsmall
      (hcover n (s (n + 1)) (hmono.monotone (Nat.le_succ n)) le_rfl)
      (by have hi := inv_pos.mpr heps; constructor <;> linarith)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hdisjoint i j hlt
    · exact (hdisjoint j i hgt).symm
  · intro n
    exact (nk n).exists_annulus_in_nearby_neck (nk (n + 1)) hsmall
      (hcover n (s (n + 1)) (hmono.monotone (Nat.le_succ n)) le_rfl)
      (hdisjoint n (n + 1) (Nat.lt_succ_self n))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
