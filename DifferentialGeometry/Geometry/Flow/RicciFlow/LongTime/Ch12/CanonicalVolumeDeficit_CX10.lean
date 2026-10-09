import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNeckDeficit_CX10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalRoundPositive_CX10

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

/-!
# CH12-CX10: a fixed canonical volume deficit

This is the independent geometric input of review CH12-R2 Q4(b), adopted in
D-R2-6. The smallness condition is explicit: eps ≤ 1/100. The constants are
A = 2 max(C1,1) + 30 max(C2,1) and eta = 1/2, chosen before the manifold and
the witness. A negative plane anywhere in the same connected component
excludes both whole-component alternatives; round positivity is proved in
CanonicalRoundPositive_CX10 from the comparison's first two derivatives.

For a cap, the neck center is the image of (nk.center,0) under the actual
tube map supplied by capTubeHasNeckChart. It therefore lies in the witness
domain. The witness's inside_ball and scalar_bounds control the displacement
and the change of scalar-curvature scale, respectively. No KL83.1 input is used.
-/

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {q : M}

/-- Convert a lower scalar comparison to an upper bound for a fixed neck radius. -/
theorem canonical_neck_radius_le_CX10 (W : SpatialCanonicalWitness g eps C1 C2 q)
    {z : M} (hz : z ∈ W.domain.carrier) (hRz : 0 < metricScalarAt g z) :
    30 / Real.sqrt (metricScalarAt g z) ≤
      30 * max C2 1 / Real.sqrt (metricScalarAt g q) := by
  have hC : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hB : 1 ≤ max C2 1 := le_max_right _ _
  have hBpos : 0 < max C2 1 := zero_lt_one.trans_le hB
  have hscalar : metricScalarAt g q ≤ max C2 1 * metricScalarAt g z := by
    have h := (W.scalar_bounds z hz).1
    rw [inv_mul_eq_div, div_le_iff₀ hC] at h
    exact h.trans ((mul_comm _ _).le.trans
      (mul_le_mul_of_nonneg_right (le_max_left C2 1) hRz.le))
  have hsB : Real.sqrt (max C2 1) ≤ max C2 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hBpos.le, by nlinarith⟩
  have hs : Real.sqrt (metricScalarAt g q) ≤
      max C2 1 * Real.sqrt (metricScalarAt g z) := by
    calc
      _ ≤ Real.sqrt (max C2 1 * metricScalarAt g z) := Real.sqrt_le_sqrt hscalar
      _ = Real.sqrt (max C2 1) * Real.sqrt (metricScalarAt g z) := Real.sqrt_mul hBpos.le _
      _ ≤ _ := mul_le_mul_of_nonneg_right hsB (Real.sqrt_nonneg _)
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hRz) (Real.sqrt_pos.mpr W.Q_pos)).mpr
  nlinarith

/-- The cap tube supplies a nearby genuine spatial neck, with a controlled scale. -/
theorem canonical_cap_neck_CX10 (W : SpatialCanonicalWitness g eps C1 C2 q)
    (hchart : W.capTubeHasNeckChart eps)
    (cap : SpatialLocalCap g eps q W.domain.carrier)
    (depth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (metricScalarAt g q) ≤ metricDistance g q y)
    (halt : W.alternative = SpatialCanonicalAlternative.cap cap depth) :
    ∃ z : M, Nonempty (SpatialNeck g eps z) ∧
      riemannianEDistOf g q z + ENNReal.ofReal (30 / Real.sqrt (metricScalarAt g z)) ≤
        ENNReal.ofReal ((2 * max C1 1 + 30 * max C2 1) /
          Real.sqrt (metricScalarAt g q)) := by
  obtain ⟨z, nk, hmap⟩ := hchart cap depth halt
  have htube : z ∈ cap.tube := by
    rw [← cap.tube_eq]
    refine ⟨(nk.center, 0), ⟨mem_univ _, by simp⟩, ?_⟩
    exact (hmap _).trans nk.center_eq
  have hz : z ∈ W.domain.carrier := by
    rw [cap.union_eq]
    exact Or.inr htube
  have hdist : riemannianEDistOf g q z < ENNReal.ofReal (2 * W.radius) := W.inside_ball hz
  have hrad := canonical_neck_radius_le_CX10 W hz nk.Q_pos
  have hs : 0 < Real.sqrt (metricScalarAt g q) := Real.sqrt_pos.mpr W.Q_pos
  have hWrad : 0 < W.radius := (inv_pos.mpr hs).trans_le W.radius_lower
  have htotal : 2 * W.radius + 30 / Real.sqrt (metricScalarAt g z) ≤
      (2 * max C1 1 + 30 * max C2 1) / Real.sqrt (metricScalarAt g q) := by
    have hradW : W.radius ≤ max C1 1 / Real.sqrt (metricScalarAt g q) :=
      W.radius_upper.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
    calc
      _ ≤ 2 * (max C1 1 / Real.sqrt (metricScalarAt g q)) +
          30 * max C2 1 / Real.sqrt (metricScalarAt g q) :=
        add_le_add (mul_le_mul_of_nonneg_left hradW (by norm_num)) hrad
      _ = _ := by ring
  refine ⟨z, ⟨nk⟩, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2 * W.radius) +
        ENNReal.ofReal (30 / Real.sqrt (metricScalarAt g z)) := add_le_add hdist.le le_rfl
    _ = ENNReal.ofReal (2 * W.radius + 30 / Real.sqrt (metricScalarAt g z)) := by
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hWrad.le)
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal htotal

/-- Fixed volume deficit, with explicit constants and an ambient extended-distance buffer. -/
theorem canonical_volume_deficit_explicit_CX10
    (W : SpatialCanonicalWitness g eps C1 C2 q)
    (heps : eps ≤ 1 / 100) (hchart : W.capTubeHasNeckChart eps)
    (hneg : ∃ y ∈ connectedComponent q, ¬ SectionalBoundedBelowAt g y 0) :
    ∃ z : M, ∃ b : ℝ, 0 < b ∧
      riemannianEDistOf g q z + ENNReal.ofReal b ≤
        ENNReal.ofReal ((2 * max C1 1 + 30 * max C2 1) /
          Real.sqrt (metricScalarAt g q)) ∧
      ballVolume g z b ≤ ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume * b ^ 3) := by
  have heps100 : eps ≤ 1 / 100 := by linarith
  cases halt : W.alternative with
  | neck data =>
    refine ⟨q, 30 / Real.sqrt (metricScalarAt g q),
      div_pos (by norm_num) (Real.sqrt_pos.mpr W.Q_pos), ?_,
      spatialNeck_volume_deficit_CX10 data.neck heps100⟩
    have hA : (30 : ℝ) ≤ 2 * max C1 1 + 30 * max C2 1 := by
      nlinarith [le_max_right C1 1, le_max_right C2 1]
    simp only [riemannianEDistOf_self, zero_add]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hA (Real.sqrt_nonneg _))
  | cap data depth =>
    obtain ⟨z, ⟨nk⟩, hdist⟩ := canonical_cap_neck_CX10 W hchart data depth halt
    exact ⟨z, 30 / Real.sqrt (metricScalarAt g z),
      div_pos (by norm_num) (Real.sqrt_pos.mpr nk.Q_pos), hdist,
      spatialNeck_volume_deficit_CX10 nk heps100⟩
  | positive whole _ hsec =>
    exact (canonical_positive_excluded_CX10 W hneg whole hsec).elim
  | round whole data =>
    exact (canonical_round_excluded_CX10 W heps hneg whole data).elim

/-- The real-distance formulation of the same buffer; finiteness comes from the
extended-distance estimate, so no connectedness of the ambient manifold is assumed. -/
theorem canonical_volume_deficit_metricDistance_CX10
    (W : SpatialCanonicalWitness g eps C1 C2 q)
    (heps : eps ≤ 1 / 100) (hchart : W.capTubeHasNeckChart eps)
    (hneg : ∃ y ∈ connectedComponent q, ¬ SectionalBoundedBelowAt g y 0) :
    ∃ z : M, ∃ b : ℝ, 0 < b ∧
      metricDistance g q z + b ≤
        (2 * max C1 1 + 30 * max C2 1) / Real.sqrt (metricScalarAt g q) ∧
      ballVolume g z b ≤ ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume * b ^ 3) := by
  obtain ⟨z, b, hb, hd, hv⟩ := canonical_volume_deficit_explicit_CX10 W heps hchart hneg
  have hfinite : riemannianEDistOf g q z ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (le_add_of_nonneg_right (show 0 ≤ ENNReal.ofReal b from bot_le)).trans hd
  have hA : 0 < 2 * max C1 1 + 30 * max C2 1 := by
    nlinarith [le_max_right C1 1, le_max_right C2 1]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hb.le,
    ENNReal.toReal_ofReal (div_nonneg hA.le (Real.sqrt_nonneg _))] at h
  exact ⟨z, b, hb, h, hv⟩

/-- CH12-R2 Q4(b): the canonical deficit constants are chosen before the manifold,
the point, and the canonical witness. They do not depend on a noncollapsing parameter. -/
theorem canonical_volume_deficit_R2 (eps C1 C2 : ℝ) (heps : eps ≤ 1 / 100) :
    ∃ A_can η_can : ℝ, 0 < A_can ∧ 0 < η_can ∧ η_can < 1 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {g : SmoothRiemannianMetric I3 M} {q : M}
        (W : SpatialCanonicalWitness g eps C1 C2 q),
        W.capTubeHasNeckChart eps →
        (∃ y ∈ connectedComponent q, ¬ SectionalBoundedBelowAt g y 0) →
        ∃ z : M, ∃ b : ℝ, 0 < b ∧
          riemannianEDistOf g q z + ENNReal.ofReal b ≤
            ENNReal.ofReal (A_can / Real.sqrt (metricScalarAt g q)) ∧
          ballVolume g z b ≤
            ENNReal.ofReal ((1 - η_can) * euclideanThreeUnitBallVolume * b ^ 3) := by
  refine ⟨2 * max C1 1 + 30 * max C2 1, 1 / 2, ?_, by norm_num, by norm_num, ?_⟩
  · nlinarith [le_max_right C1 1, le_max_right C2 1]
  · intro M _ _ _ _ _ g q W hchart hneg
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      canonical_volume_deficit_explicit_CX10 W heps hchart hneg

end GC.LongTime.Ch12
