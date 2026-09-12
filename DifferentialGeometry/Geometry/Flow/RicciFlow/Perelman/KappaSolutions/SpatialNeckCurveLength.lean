import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderLength

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance neckLengthSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance neckLengthC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

private theorem neck_speed_bilipschitz (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : x ∈ spatialNeckClosedCore epsilon)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
    (11 / 12 * spatialNeckScale h p) * Real.sqrt (gRef.inner x v v) ≤
        Real.sqrt (h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)) ∧
      Real.sqrt (h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)) ≤
        (13 / 12 * spatialNeckScale h p) * Real.sqrt (gRef.inner x v v) := by
  let a := spatialNeckScale h p
  let q := (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)).inner x v v
  let Q := h.inner (W.embedding x)
    (mfderiv SpatialNeckCylinderModel I W.embedding x v)
    (mfderiv SpatialNeckCylinderModel I W.embedding x v)
  have ha : 0 < a := spatialNeckScale_pos h p W.scalar_pos
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hi := W.normalized_inner_bilipschitz hsmall x hx v
  change (11 / 12 : ℝ) ^ 2 * q ≤ (a ^ 2)⁻¹ * Q ∧
    (a ^ 2)⁻¹ * Q ≤ (13 / 12 : ℝ) ^ 2 * q at hi
  have hlower : (11 / 12 * a) ^ 2 * q ≤ Q := by
    calc
      _ = a ^ 2 * ((11 / 12 : ℝ) ^ 2 * q) := by ring
      _ ≤ a ^ 2 * ((a ^ 2)⁻¹ * Q) := mul_le_mul_of_nonneg_left hi.1 ha2.le
      _ = Q := by rw [← mul_assoc, mul_inv_cancel₀ ha2.ne', one_mul]
  have hupper : Q ≤ (13 / 12 * a) ^ 2 * q := by
    calc
      Q = a ^ 2 * ((a ^ 2)⁻¹ * Q) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha2.ne', one_mul]
      _ ≤ a ^ 2 * ((13 / 12 : ℝ) ^ 2 * q) := mul_le_mul_of_nonneg_left hi.2 ha2.le
      _ = _ := by ring
  change (11 / 12 * a) * Real.sqrt q ≤ Real.sqrt Q ∧
    Real.sqrt Q ≤ (13 / 12 * a) * Real.sqrt q
  constructor
  · calc
      _ = Real.sqrt ((11 / 12 * a) ^ 2 * q) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      _ ≤ _ := Real.sqrt_le_sqrt hlower
  · calc
      _ ≤ Real.sqrt ((13 / 12 * a) ^ 2 * q) := Real.sqrt_le_sqrt hupper
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem pathELength_bilipschitz (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {γ : ℝ → spatialNeckBuffer epsilon} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b))
    (hcore : ∀ t ∈ Icc a b, γ t ∈ spatialNeckClosedCore epsilon) :
    let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p) *
        metricPathELength (I := SpatialNeckCylinderModel) gRef γ a b ≤
      metricPathELength (I := I) h ((W.embedding : spatialNeckBuffer epsilon → N) ∘ γ) a b ∧
      metricPathELength (I := I) h ((W.embedding : spatialNeckBuffer epsilon → N) ∘ γ) a b ≤
        ENNReal.ofReal (13 / 12 * spatialNeckScale h p) *
          metricPathELength (I := SpatialNeckCylinderModel) gRef γ a b := by
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hspeed (t : ℝ) (ht : t ∈ Ioo a b) :=
    W.neck_speed_bilipschitz hsmall (γ t) (hcore t ⟨ht.1.le, ht.2.le⟩)
      (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1)
  have hder (t : ℝ) (ht : t ∈ Ioo a b) :
      mfderiv 𝓘(ℝ, ℝ) I ((W.embedding : spatialNeckBuffer epsilon → N) ∘ γ) t 1 =
        mfderiv SpatialNeckCylinderModel I W.embedding (γ t)
          (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1) := by
    have hγd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact mfderiv_comp_apply t
      (W.smooth_embedding.contMDiff.mdifferentiable (by simp) (γ t)) hγd 1
  constructor
  · rw [metricPathELength_eq, metricPathELength_eq, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 11 / 12 * spatialNeckScale h p), hder t ht]
    exact ENNReal.ofReal_le_ofReal (hspeed t ht).1
  · rw [metricPathELength_eq, metricPathELength_eq, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 13 / 12 * spatialNeckScale h p), hder t ht]
    exact ENNReal.ofReal_le_ofReal (hspeed t ht).2

theorem axial_displacement_le_pathELength (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {γ : ℝ → spatialNeckBuffer epsilon} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b))
    (hcore : ∀ t ∈ Icc a b, γ t ∈ spatialNeckClosedCore epsilon) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * |(γ b).val.2 - (γ a).val.2|) ≤
      metricPathELength (I := I) h ((W.embedding : spatialNeckBuffer epsilon → N) ∘ γ) a b := by
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 11 / 12 * spatialNeckScale h p)]
  exact (mul_le_mul_of_nonneg_left
    (unitCylinder_axial_length_lower_on_open (spatialNeckBuffer epsilon) hab hγ)
    (zero_le : 0 ≤ ENNReal.ofReal (11 / 12 * spatialNeckScale h p))).trans
      (W.pathELength_bilipschitz hsmall hγ hcore).1

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
