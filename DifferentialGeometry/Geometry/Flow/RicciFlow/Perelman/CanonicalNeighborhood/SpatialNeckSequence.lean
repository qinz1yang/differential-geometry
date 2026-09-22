import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckAnnulus
import DifferentialGeometry.Topology.Connected.FrontierChain
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarUnion
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
      ∃ eta : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
        ∃ Ψ : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞,
          (∀ n, (univ ×ˢ Icc (0 : ℝ) 1 ⊆ (Ψ n).source) ∧
            (∀ p, Ψ n (p, 0) = (nk n).map (p, 0)) ∧
            (∀ p, Ψ n (p, 1) = (nk (n + 1)).map (eta n p, 0)) ∧
            IsCompact (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            (frontier (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
                (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
            (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
              (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
            Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
              riemannianClosedBallOf g (gamma (s n))
                ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s n)))) ∩
              riemannianClosedBallOf g (gamma (s (n + 1)))
                ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s n))))) ∧
          (∀ i j, i + 1 < j → Disjoint (Ψ i '' (univ ×ˢ Icc (0 : ℝ) 1))
            (Ψ j '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
          Pairwise (fun i j => Disjoint (interior (Ψ (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))
            (interior (Ψ (j + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))) ∧
          (∀ n, (Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
            (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
          ∀ n, (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ)) ⊆
            interior ((Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∪
              (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
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
  have hscale (n : ℕ) : Real.sqrt (metricScalarAt g (gamma (s n))) ≤
      2 * Real.sqrt (metricScalarAt g (gamma (s (n + 1)))) ∧
      Real.sqrt (metricScalarAt g (gamma (s (n + 1)))) ≤
        2 * Real.sqrt (metricScalarAt g (gamma (s n))) := by
    have hi : 0 < eps⁻¹ := inv_pos.mpr heps
    have hy := hcover n (s (n + 1)) (hmono.monotone (Nat.le_succ n)) le_rfl
    have hratio : |metricScalarAt g (gamma (s (n + 1))) /
        metricScalarAt g (gamma (s n)) - 1| ≤ 4323 * eps := by
      obtain ⟨z, hz, hzval⟩ := hy
      rw [← hzval]
      exact (nk n).abs_scalar_ratio_sub_one_le
        ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hQn : metricScalarAt g (gamma (s n)) ≤
        4 * metricScalarAt g (gamma (s (n + 1))) := by
      have hh : (1 : ℝ) / 2 ≤ metricScalarAt g (gamma (s (n + 1))) /
          metricScalarAt g (gamma (s n)) := by linarith [(abs_le.mp hratio).1]
      have hh' := (le_div_iff₀ (hQ (s n))).mp hh
      linarith [hQ (s (n + 1))]
    have hQnext : metricScalarAt g (gamma (s (n + 1))) ≤
        4 * metricScalarAt g (gamma (s n)) := by
      apply (div_le_iff₀ (hQ (s n))).mp
      linarith [(abs_le.mp hratio).2]
    constructor <;>
      nlinarith [Real.sq_sqrt (hQ (s n)).le, Real.sq_sqrt (hQ (s (n + 1))).le,
        Real.sqrt_nonneg (metricScalarAt g (gamma (s n))),
        Real.sqrt_nonneg (metricScalarAt g (gamma (s (n + 1))))]
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
  · have hannuli : ∀ n, ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
        ∃ Ψ : PartialDiffeomorph IC I3 Cylinder M ∞,
          (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
          (∀ p, Ψ (p, 0) = (nk n).map (p, 0)) ∧
          (∀ p, Ψ (p, 1) = (nk (n + 1)).map (eta p, 0)) ∧
          IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
          (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
            (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
              (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
          (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
            (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
          Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
            riemannianClosedBallOf g (gamma (s n))
              ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s n)))) ∩
            riemannianClosedBallOf g (gamma (s (n + 1)))
              ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s n)))) := by
      intro n
      have hi : (1000000 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) heps).mpr
        (by simpa only [one_div] using hsmall)
      have hdiv : 7 / Real.sqrt (metricScalarAt g (gamma (s (n + 1)))) ≤
          14 / Real.sqrt (metricScalarAt g (gamma (s n))) := by
        apply (div_le_div_iff₀ (Real.sqrt_pos.mpr (hQ (s (n + 1))))
          (Real.sqrt_pos.mpr (hQ (s n)))).mpr
        linarith [(hscale n).1]
      have hm : 99 / 100 ≤ Real.sqrt (1 - eps) := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 1 - eps), Real.sqrt_nonneg (1 - eps)]
      have hp : Real.sqrt (1 + eps) ≤ 101 / 100 := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 1 + eps), Real.sqrt_nonneg (1 + eps)]
      have hn : eps⁻¹ / 40 + 14 < (eps⁻¹ / 36) * Real.sqrt (1 - eps) := by
        nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ eps⁻¹ / 36)]
      have hnear : riemannianEDistOf g (gamma (s n)) (gamma (s (n + 1))) +
          ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g (gamma (s (n + 1))))) <
          ENNReal.ofReal ((eps⁻¹ / 36) * Real.sqrt (1 - eps) /
            Real.sqrt (metricScalarAt g (gamma (s n)))) := by
        rw [hgamma, edist_dist, Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr (hmono (Nat.lt_succ_self n)).le), neg_sub]
        have hs := hstep n
        change (s (n + 1) : ℝ) = (s n : ℝ) +
          (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))) at hs
        have hgap : (s (n + 1) : ℝ) - s n =
            (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))) := by linarith
        rw [hgap]
        apply lt_of_le_of_lt (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdiv))
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div]
        exact (ENNReal.ofReal_lt_ofReal_iff
          (div_pos (lt_of_le_of_lt (by linarith) hn)
            (Real.sqrt_pos.mpr (hQ (s n))))).mpr
          (div_lt_div_of_pos_right hn (Real.sqrt_pos.mpr (hQ (s n))))
      obtain ⟨eta, Ψ, hsource, hleft, hright, hc, hf, hsub, hballs⟩ :=
        (nk n).exists_annulus_in_intersection_closedBalls (nk (n + 1)) hsmall
          (by linarith : eps⁻¹ / 36 ≤ eps⁻¹ / 10) hnear
          (hdisjoint n (n + 1) (Nat.lt_succ_self n))
      refine ⟨eta, Ψ, hsource, hleft, hright, hc, hf, hsub, ?_⟩
      intro z hz
      have hb := hballs hz
      constructor
      · apply hb.1.trans (ENNReal.ofReal_le_ofReal _)
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ eps⁻¹ / 36 + 6)]
      · apply hb.2.trans (ENNReal.ofReal_le_ofReal _)
        apply (add_le_add le_rfl hdiv).trans
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ eps⁻¹ / 36)]
    choose eta Ψ hsource hleft hright hc hf hsub hballs using hannuli
    have hsepAnn : ∀ i j, i + 1 < j →
        Disjoint (Ψ i '' (univ ×ˢ Icc (0 : ℝ) 1))
          (Ψ j '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      have hspacing (n : ℕ) : d (s n) ≤ 2 * d (s (n + 1)) ∧
          d (s (n + 1)) ≤ 2 * d (s n) := by
        have hs := hscale n
        have hn := Real.sqrt_pos.mpr (hQ (s n))
        have hn' := Real.sqrt_pos.mpr (hQ (s (n + 1)))
        have hi : 0 < eps⁻¹ / 40 := by positivity
        change (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))) ≤ _ ∧ _
        constructor
        · change (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))) ≤
            2 * ((eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s (n + 1)))))
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ hn hn').mpr
          nlinarith [mul_le_mul_of_nonneg_left hs.2 hi.le]
        · change (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s (n + 1)))) ≤
            2 * ((eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s n))))
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ hn' hn).mpr
          nlinarith [mul_le_mul_of_nonneg_left hs.1 hi.le]
      have hfar (i j : ℕ) (hij : i + 1 < j) :
          (6 : ℝ) / 5 * (d (s i) + d (s j)) < (s (j + 1) : ℝ) - s i := by
        by_cases hj : j = i + 2
        · subst j
          have hh := (hspacing (i + 1)).2
          have hj' : i + 1 + 1 = i + 2 := by omega
          rw [hj'] at hh
          linarith [hd (s i), hd (s (i + 2)), (hspacing i).1,
            hstep i, hstep (i + 1), hstep (i + 2)]
        · have hjpos : 1 ≤ j := by omega
          have hprev : j - 1 + 1 = j := Nat.sub_add_cancel hjpos
          have hc := (hspacing (j - 1)).2
          rw [hprev] at hc
          have hjstep := hstep (j - 1)
          rw [hprev] at hjstep
          have hmiddle := hmono.monotone (show i + 1 + 1 ≤ j - 1 by omega)
          linarith [hd (s i), hd (s j), (hspacing i).1, hstep i, hstep (i + 1), hstep j]
      intro i j hij
      apply Set.disjoint_left.mpr
      intro z hzi hzj
      have hleftDist := (hballs i hzi).1
      have hrightDist := (hballs j hzj).2
      change riemannianEDistOf g (gamma (s i)) z ≤ _ at hleftDist
      change riemannianEDistOf g (gamma (s (j + 1))) z ≤ _ at hrightDist
      rw [riemannianEDistOf_comm] at hrightDist
      have hbound := (riemannianEDistOf_triangle g (gamma (s i)) z (gamma (s (j + 1)))).trans
        (add_le_add hleftDist hrightDist)
      rw [hgamma, edist_dist, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (hmono (by omega : i < j + 1)).le), neg_sub,
        ← ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
      have hfar' := hfar i j hij
      change 6 / 5 * ((eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s i))) +
        (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s j)))) < _ at hfar'
      have heq : 6 / 5 * ((eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s i))) +
        (eps⁻¹ / 40) / Real.sqrt (metricScalarAt g (gamma (s j)))) =
        (3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s i))) +
        (3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g (gamma (s j))) := by ring
      rw [heq] at hfar'
      exact (not_lt_of_ge hreal) hfar'
    let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
        (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
        (by norm_num : (0 : ℝ) ≤ 1))
    have hreg (n : ℕ) : closure (interior (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1))) =
        Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      apply (Ψ n).toOpenPartialHomeomorph.closure_interior_image_of_subset_source
        (hsource n) _ (hc n).isClosed
      rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq, closure_univ,
        closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    have hconn (n : ℕ) : IsPreconnected (interior (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
      change IsPreconnected (interior ((Ψ n).toOpenPartialHomeomorph ''
        (univ ×ˢ Icc (0 : ℝ) 1)))
      rw [← (Ψ n).toOpenPartialHomeomorph.image_interior_of_subset_source (hsource n),
        interior_prod_eq, interior_univ, interior_Icc]
      exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
        ((Ψ n).contMDiffOn_toFun.continuousOn.mono
          (fun z hz => hsource n ⟨hz.1, hz.2.1.le, hz.2.2.le⟩))
    have hne (n : ℕ) : ((nk n).map '' (univ ×ˢ ({0} : Set ℝ))).Nonempty :=
      ⟨(nk n).map ((nk n).center, 0), ((nk n).center, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    have hS : Pairwise (fun i j => Disjoint ((nk i).map '' (univ ×ˢ ({0} : Set ℝ)))
        ((nk j).map '' (univ ×ˢ ({0} : Set ℝ)))) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hdisjoint i j h
      · exact (hdisjoint j i h).symm
    have hpair := DifferentialGeometry.Topology.pairwise_disjoint_interiors_of_frontier_chain
      _ _ hreg hconn hf hne hS hsepAnn
    have hinter := DifferentialGeometry.Topology.inter_succ_eq_of_frontier_chain
      _ _ hreg hconn hf hne hS hsepAnn
    have hupper (n : ℕ) : Ψ n '' (univ ×ˢ ({1} : Set ℝ)) =
        (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ)) := by
      ext z
      constructor
      · rintro ⟨⟨p, t⟩, ht, rfl⟩
        have ht1 : t = 1 := ht.2
        subst t
        exact ⟨(eta n p, 0), ⟨mem_univ _, rfl⟩, (hright n p).symm⟩
      · rintro ⟨⟨p, t⟩, ht, rfl⟩
        have ht0 : t = 0 := ht.2
        subst t
        refine ⟨((eta n).symm p, 1), ⟨mem_univ _, rfl⟩, ?_⟩
        simpa only [(eta n).apply_symm_apply] using hright n ((eta n).symm p)
    have hSclosed (n : ℕ) : IsClosed ((nk n).map '' (univ ×ˢ ({0} : Set ℝ))) := by
      apply IsCompact.isClosed
      apply (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
      apply (nk n).map.contMDiffOn_toFun.continuousOn.mono
      intro z hz
      have hz0 : z.2 = 0 := hz.2
      apply (nk n).domain
      refine ⟨hz.1, ?_⟩
      rw [hz0]
      have hi := inv_pos.mpr heps
      constructor <;> linarith
    have hseam (n : ℕ) : (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ)) ⊆
        interior ((Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∪
          (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
      rw [← hupper (n + 1)]
      apply (Ψ (n + 1)).toOpenPartialHomeomorph.image_upper_boundary_subset_interior_union
        (by norm_num : (0 : ℝ) < 1) (hsource (n + 1)) (hreg (n + 2))
        (hSclosed (n + 3)) (hpair (by omega : n ≠ n + 1))
      · change Ψ (n + 1) '' (univ ×ˢ ({1} : Set ℝ)) ⊆ _
        rw [hupper]
        intro z hz
        apply (hc (n + 2)).isClosed.frontier_subset
        rw [hf]
        exact Or.inl hz
      · change frontier (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
          Ψ (n + 1) '' (univ ×ˢ ({1} : Set ℝ)) ∪ _
        rw [hf, hupper]
      · change Disjoint (Ψ (n + 1) '' (univ ×ˢ ({1} : Set ℝ))) _
        rw [hupper]
        exact hS (by omega : n + 1 + 1 ≠ n + 3)
    exact ⟨eta, Ψ, fun n => ⟨hsource n, hleft n, hright n, hc n, hf n, hsub n, hballs n⟩,
      hsepAnn, hpair, hinter, hseam⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
