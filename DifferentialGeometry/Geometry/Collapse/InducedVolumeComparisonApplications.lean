import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.Manifold.ClosedOriented

/-!
# Volume at the curvature scale on closed three-manifolds

Consumer of `InducedVolumeComparison.lean` combining the curvature-scale toolkit (A1), the first
volume scale (X67) and the three-dimensional local Bishop–Gromov kernels (X68), bound to an
arbitrary metric `g` through the induced-metric package (A2).

On a closed connected three-manifold whose metric has somewhere negative sectional curvature,
every curvature scale `R = R_p` is finite and positive. For `0 < w < 4π/3` and
`r = r_p(w)` (`firstVolumeScale`), with `I₁ = ∫₀¹ sinh²`:

* always `Vol B(p, R) / R³ ≤ 4π I₁` (absolute Bishop–Gromov at the curvature scale);
* if `R < r`, then `w < Vol B(p, R) / R³` (LC01);
* if `r ≤ R`, then `Vol B(p, R) / R³ ≤ 3 I₁ w` (LC03 with `2ρ = R`);
* if `r ≤ R ≤ 2r`, then `w / (24 I₁) ≤ Vol B(p, R) / R³` (LC04 with `u = r`, `ρ = R`).

`curvatureScale_ballVolume_bounds` is the statement for a compact connected boundaryless
manifold; `closedManifold_curvatureScale_ballVolume_bounds` (a
`ConnectedClosedOrientedManifold 3`) and `compactCarrier_curvatureScale_ballVolume_bounds`
(a boundaryless connected `GC.Endpoint.CompactCarrier`) are its instances on actual carriers.
In terms of the collapse predicate, `volumeCollapsedAtCurvatureScale g w p` forces `r ≤ R`, and
`r ≤ R` gives `volumeCollapsedAtCurvatureScale g (3 I₁ w) p`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian

universe u

section Closed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]

/-- At every point, the volume of the curvature-scale ball is bounded above by the absolute
Bishop–Gromov constant, and above and below by the LC03/LC04 constants at the first volume
scale `r_p(w)` in the corresponding regimes. -/
theorem curvatureScale_ballVolume_bounds (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) (hneg : ¬ SectionalBoundedBelow g 0) {w : ℝ}
    (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) (p : M) :
    curvatureRadius g p ≠ ⊤ ∧ 0 < (curvatureRadius g p).toReal ∧ 0 < firstVolumeScale g p w ∧
      (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
        4 * Real.pi * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 ∧
      ((curvatureRadius g p).toReal < firstVolumeScale g p w →
        w < (ballVolume g p (curvatureRadius g p).toReal).toReal /
          (curvatureRadius g p).toReal ^ 3) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
          (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (curvatureRadius g p).toReal ≤ 2 * firstVolumeScale g p w →
        w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
          (ballVolume g p (curvatureRadius g p).toReal).toReal /
            (curvatureRadius g p).toReal ^ 3) := by
  have hfin : curvatureRadius g p ≠ ⊤ :=
    fun htop => hneg ((curvatureRadius_eq_top_iff p).mp htop)
  have hR : 0 < (curvatureRadius g p).toReal :=
    ENNReal.toReal_pos (curvatureRadius_pos g p).ne' hfin
  have hRp : ENNReal.ofReal (curvatureRadius g p).toReal ≤ curvatureRadius g p :=
    (ENNReal.ofReal_toReal hfin).le
  have hg := RiemannianMetricComplete.of_compact (I := I) g
  obtain ⟨hr, -, hbefore⟩ := firstVolumeScale_spec g hdim p hw hwc
  have hvol := ballVolume_firstVolumeScale g hdim p hw hwc
  refine ⟨hfin, hR, hr, ballVolume_div_cube_le_of_le_curvatureRadius g hg hdim p hR hRp,
    fun hlt => (lt_div_iff₀ (pow_pos hR 3)).mpr (hbefore _ hR hlt), fun hle => ?_,
    fun hle hle2 => ?_⟩
  · have htwo : 2 * ((curvatureRadius g p).toReal / 2) = (curvatureRadius g p).toReal := by ring
    have h := ballVolume_twice_scale_le_of_le_curvatureRadius g hg hdim p hw hr
      (half_pos hR) (htwo.symm ▸ hle) hvol (htwo.symm ▸ hRp)
    rwa [htwo] at h
  · exact (ballVolume_scale_lower_of_le_curvatureRadius g hg hdim p hw hr hR hle2 hvol
      ((ENNReal.ofReal_le_ofReal hle).trans hRp)).2

omit [ConnectedSpace M] in
/-- Volume collapse at the curvature scale forces the first volume scale below the curvature
scale. -/
theorem firstVolumeScale_le_of_volumeCollapsedAtCurvatureScale (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) {p : M}
    (hfin : curvatureRadius g p ≠ ⊤) (hcol : volumeCollapsedAtCurvatureScale g w p) :
    firstVolumeScale g p w ≤ (curvatureRadius g p).toReal := by
  have hR : 0 < (curvatureRadius g p).toReal :=
    ENNReal.toReal_pos (curvatureRadius_pos g p).ne' hfin
  by_contra hlt
  have hbefore := (firstVolumeScale_spec g hdim p hw hwc).2.2 _ hR (not_le.mp hlt)
  have hupper := ENNReal.toReal_le_of_le_ofReal (mul_pos hw (pow_pos hR 3)).le
    (hcol _ hR (ENNReal.ofReal_toReal hfin).symm)
  linarith

/-- If the first volume scale lies below the curvature scale, then the curvature-scale ball is
volume collapsed with the LC03 constant `3 I₁ w`. -/
theorem volumeCollapsedAtCurvatureScale_of_firstVolumeScale_le (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) {p : M}
    (hle : firstVolumeScale g p w ≤ (curvatureRadius g p).toReal) :
    volumeCollapsedAtCurvatureScale g ((3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w) p := by
  intro R hR hRp
  have hreal : (curvatureRadius g p).toReal = R := by
    rw [hRp, ENNReal.toReal_ofReal hR.le]
  have hg := RiemannianMetricComplete.of_compact (I := I) g
  have htwo : 2 * (R / 2) = R := by ring
  have h := ballVolume_twice_scale_le_of_le_curvatureRadius g hg hdim p hw
    (firstVolumeScale_spec g hdim p hw hwc).1 (half_pos hR) (htwo.symm ▸ hreal ▸ hle)
    (ballVolume_firstVolumeScale g hdim p hw hwc) (htwo.symm ▸ hRp.ge)
  rw [htwo, div_le_iff₀ (pow_pos hR 3)] at h
  rw [← ENNReal.ofReal_toReal (ballVolume_ne_top g p R)]
  exact ENNReal.ofReal_le_ofReal (by linarith only [h])

end Closed

/-! ### Actual carriers -/

/-- The curvature-scale volume bounds on a closed connected oriented three-manifold. -/
theorem closedManifold_curvatureScale_ballVolume_bounds
    (N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    (p : N.Carrier) :
    curvatureRadius g p ≠ ⊤ ∧ 0 < (curvatureRadius g p).toReal ∧ 0 < firstVolumeScale g p w ∧
      (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
        4 * Real.pi * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 ∧
      ((curvatureRadius g p).toReal < firstVolumeScale g p w →
        w < (ballVolume g p (curvatureRadius g p).toReal).toReal /
          (curvatureRadius g p).toReal ^ 3) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
          (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (curvatureRadius g p).toReal ≤ 2 * firstVolumeScale g p w →
        w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
          (ballVolume g p (curvatureRadius g p).toReal).toReal /
            (curvatureRadius g p).toReal ^ 3) :=
  curvatureScale_ballVolume_bounds g (by simp) hneg hw hwc p

/-- The curvature-scale volume bounds on a boundaryless connected compact carrier. -/
theorem compactCarrier_curvatureScale_ballVolume_bounds (W : GC.Endpoint.CompactCarrier.{u})
    [W.model.Boundaryless] [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    (p : W.Carrier) :
    curvatureRadius g p ≠ ⊤ ∧ 0 < (curvatureRadius g p).toReal ∧ 0 < firstVolumeScale g p w ∧
      (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
        4 * Real.pi * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 ∧
      ((curvatureRadius g p).toReal < firstVolumeScale g p w →
        w < (ballVolume g p (curvatureRadius g p).toReal).toReal /
          (curvatureRadius g p).toReal ^ 3) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (ballVolume g p (curvatureRadius g p).toReal).toReal / (curvatureRadius g p).toReal ^ 3 ≤
          (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w) ∧
      (firstVolumeScale g p w ≤ (curvatureRadius g p).toReal →
        (curvatureRadius g p).toReal ≤ 2 * firstVolumeScale g p w →
        w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
          (ballVolume g p (curvatureRadius g p).toReal).toReal /
            (curvatureRadius g p).toReal ^ 3) :=
  curvatureScale_ballVolume_bounds g (by simp) hneg hw hwc p

end DifferentialGeometry.Geometry.Collapse
