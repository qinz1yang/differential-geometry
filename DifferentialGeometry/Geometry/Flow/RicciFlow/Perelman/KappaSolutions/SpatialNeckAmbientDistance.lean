import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompleteMetricMinimizingCurve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreCurves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderSphereLength

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance ambientNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance ambientNeckC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

theorem exists_minimizing_core_lift (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi) :
    ∃ β : ℝ → spatialNeckBuffer epsilon,
      ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (Icc 0 1) ∧
      β 0 = x ∧ β 1 = y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, β t ∈ spatialNeckClosedCore epsilon) ∧
      metricPathELength (I := I) h ((W.embedding : spatialNeckBuffer epsilon → N) ∘ β) 0 1 =
        riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  have hfin : riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) ≠ ⊤ :=
    ne_of_lt ((W.band_edist_lt hsmall x y hx hy).trans_le le_top)
  obtain ⟨γ, hγ, hγ0, hγ1, hlength⟩ :=
    completeMetric_exists_minimizing_curve h W.complete (W.embedding x) (W.embedding y) hfin
  have hcore := W.minimizing_curve_stays_core hsmall x y hx hy hγ hγ0 hlength
  obtain ⟨β, hβ, hβcore, hβeq⟩ := W.lift_core_curve hγ hcore
  have hβ0 : β 0 = x := W.smooth_embedding.isEmbedding.injective
    ((hβeq 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hβ1 : β 1 = y := W.smooth_embedding.isEmbedding.injective
    ((hβeq 1 ⟨zero_le_one, le_rfl⟩).trans hγ1)
  have hsame : metricPathELength (I := I) h
      ((W.embedding : spatialNeckBuffer epsilon → N) ∘ β) 0 1 =
      metricPathELength (I := I) h γ 0 1 := by
    let _ : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_congr hβeq
  exact ⟨β, hβ, hβ0, hβ1, hβcore, hsame.trans hlength⟩

theorem band_axial_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * |y.val.2 - x.val.2|) ≤
      riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  obtain ⟨β, hβ, hβ0, hβ1, hcore, hlength⟩ := W.exists_minimizing_core_lift hsmall x y hx hy
  have hlower := W.axial_displacement_le_pathELength hsmall zero_le_one hβ hcore
  rw [hβ0, hβ1, hlength] at hlower
  exact hlower

theorem band_antipodal_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi)
    (hanti : y.val.1 = -x.val.1) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
      riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) := by
  obtain ⟨β, hβ, hβ0, hβ1, hcore, hlength⟩ := W.exists_minimizing_core_lift hsmall x y hx hy
  have hanti' : (β 1).val.1 = -(β 0).val.1 := by rw [hβ0, hβ1]; exact hanti
  have hsphere := unitCylinder_antipodal_length_lower_on_open
    (spatialNeckBuffer epsilon) zero_le_one hβ hanti'
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hlower := (mul_le_mul_of_nonneg_left hsphere
    (zero_le : 0 ≤ ENNReal.ofReal (11 / 12 * spatialNeckScale h p))).trans
      (W.pathELength_bilipschitz hsmall hβ hcore).1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 11 / 12 * spatialNeckScale h p),
    hlength] at hlower
  exact hlower

omit [I.Boundaryless] in
theorem slice_edist_upper (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x ∈ spatialNeckClosedCore epsilon) (hy : y ∈ spatialNeckClosedCore epsilon)
    (hslice : y.val.2 = x.val.2) :
    riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y) ≤
      ENNReal.ofReal (13 / 12 * spatialNeckScale h p * Real.pi) := by
  have hupper := W.core_edist_upper hsmall x y hx hy
  simpa only [hslice, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq Real.pi_pos.le] using hupper

theorem band_axial_length_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : |x.val.2| ≤ 5 * Real.pi) (hy : |y.val.2| ≤ 5 * Real.pi)
    {γ : ℝ → N} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hγa : γ a = W.embedding x) (hγb : γ b = W.embedding y) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * |y.val.2 - x.val.2|) ≤
      metricPathELength (I := I) h γ a b := by
  let _ : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
  exact (W.band_axial_edist_lower hsmall x y hx hy).trans
    (Manifold.riemannianEDist_le_pathELength hγ hγa hγb hab)

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
