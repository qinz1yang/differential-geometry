import DifferentialGeometry.Geometry.Collapse.FixtureCT.KleinMetric

/-!
# Consumers of the edge carrier `S¹_a × K_{b,L}` (lane O-FIXTURE-CT, K-C, file 3)

* `kleinGlide_OFT`: the glide reflection `ι = (0, 0, 1)` of the group;
* `kleinPi_glide_OFT`: `π(x, y, t) = π(x, -y, t + L/2)` — the reflection identification that makes
  the lines `y ∈ (b/2)ℤ` edges of the collapsed annulus (non-vacuity: the two lifts differ when
  `y ≠ 0`, `kleinGlide_lifts_ne_OFT`);
* `dist_kleinPi_le_OFT`, `le_dist_kleinPi_OFT`, `dist_kleinPi_le_smul_OFT`: the two distance
  bounds in the metric-space form of `kleinMS_OFT`;
* `kleinUnit_OFT` and closed examples at periods `(1, 1, 1)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] kleinMS_OFT

/-- The glide reflection `ι(x, y, t) = (x, -y, t + L/2)`. -/
def kleinGlide_OFT (P : KleinPeriods_OFT) : KleinGroup_OFT P := ⟨0, 0, 1⟩

theorem kleinGlide_smul_OFT (P : KleinPeriods_OFT) (x y t : ℝ) :
    kleinGlide_OFT P • (WithLp.toLp 2 ![x, y, t] : E3) =
      (WithLp.toLp 2 ![x, -y, t + P.L / 2] : E3) := by
  have hs : (kSign_OFT 1 : ℝ) = -1 := by simp [kSign_OFT]
  ext i
  fin_cases i <;> simp [kleinSmul_def_OFT, kleinLin_apply_OFT, kleinVec_OFT, kleinGlide_OFT, hs]

/-- **The reflection identification.** -/
theorem kleinPi_glide_OFT (P : KleinPeriods_OFT) (x y t : ℝ) :
    kleinPi_OFT P (WithLp.toLp 2 ![x, y, t]) =
      kleinPi_OFT P (WithLp.toLp 2 ![x, -y, t + P.L / 2]) :=
  kleinPi_eq_iff_OFT.mpr ⟨kleinGlide_OFT P, (kleinGlide_smul_OFT P x y t).symm⟩

theorem kleinGlide_lifts_ne_OFT (P : KleinPeriods_OFT) (x y t : ℝ) :
    (WithLp.toLp 2 ![x, y, t] : E3) ≠ WithLp.toLp 2 ![x, -y, t + P.L / 2] := by
  intro h
  have h2 := congrArg (fun v : E3 => v 2) h
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  linarith [half_pos P.L_pos]

/-- The covering map does not increase distance (metric-space form). -/
theorem dist_kleinPi_le_OFT (P : KleinPeriods_OFT) (x y : E3) :
    dist (kleinPi_OFT P x) (kleinPi_OFT P y) ≤ ‖x - y‖ := by
  have h := edist_kleinPi_le_OFT P x y
  rw [kleinMS_hmetric_OFT P] at h
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp h

/-- The distance is at most the distance to every lift. -/
theorem dist_kleinPi_le_smul_OFT (P : KleinPeriods_OFT) (x y : E3) (g : KleinGroup_OFT P) :
    dist (kleinPi_OFT P x) (kleinPi_OFT P y) ≤ ‖x - g • y‖ := by
  have hy : kleinPi_OFT P y = kleinPi_OFT P (g • y) := kleinPi_eq_iff_OFT.mpr ⟨g, rfl⟩
  rw [hy]
  exact dist_kleinPi_le_OFT P x (g • y)

/-- Path lifting lower bound (metric-space form). -/
theorem le_dist_kleinPi_OFT (P : KleinPeriods_OFT) (x y : E3) (r : ℝ)
    (h : ∀ g : KleinGroup_OFT P, r ≤ ‖x - g • y‖) :
    r ≤ dist (kleinPi_OFT P x) (kleinPi_OFT P y) := by
  have h' := le_edist_kleinPi_OFT P x y r h
  rw [kleinMS_hmetric_OFT P] at h'
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h'

/-- The unit periods `(1, 1, 1)`. -/
def kleinUnit_OFT : KleinPeriods_OFT := ⟨1, 1, 1, one_pos, one_pos, one_pos⟩

/-- **Closed example**: on `S¹_1 × K_{1,1}` the points `π(0, 1/4, 0)` and `π(0, -1/4, 1/2)` are
equal although their lifts differ. -/
example : kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 1 / 4, 0]) =
      kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, -(1 / 4), 0 + 1 / 2]) ∧
    (WithLp.toLp 2 ![0, 1 / 4, 0] : E3) ≠ WithLp.toLp 2 ![0, -(1 / 4), 0 + 1 / 2] :=
  ⟨kleinPi_glide_OFT kleinUnit_OFT 0 (1 / 4) 0, kleinGlide_lifts_ne_OFT kleinUnit_OFT 0 (1 / 4) 0⟩

example : CompactSpace (Klein_OFT kleinUnit_OFT) := inferInstance
example : IsManifold 𝓘(ℝ, E3) ∞ (Klein_OFT kleinUnit_OFT) := inferInstance

end DifferentialGeometry.Geometry.Collapse
