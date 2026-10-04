import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleGeneral

/-!
# First volume scales at interior centres of a compact carrier (BSA03, interior centres)

On a compact carrier `W` (possibly with boundary) and a centre `p` with `0 < d(p, ∂W)`, the first
volume scale `r_p(w)` is positive and attained exactly, for every `0 < w < ω₃ = 4π/3`
(`firstVolumeScale_spec_of_distanceToBoundary_pos`); this is BSA03.a (blueprint 207B, B:7764) at
interior centres, listed as provable but not done by lane W4-BSA. Boundary centres need the
half-ball asymptotics F-c.

Route (lane B2's complete extension, `BishopGromovBoundaryBuffer.lean`): on the open ball
`U = B(p, ρ)`, `ρ ≤ d(p, ∂W)`, with the interior atlas, a complete metric `g'` agrees with `g` near
`B̄(p, ρ/2)`; the inverse inclusion is isometric there and carries the small balls and their
volumes (`ballVolume_eq_of_isometricOn`); on the complete boundaryless `(U, g')` the sharp
small-ball estimate `exists_ballVolume_euclidean_ratio` applies. The generic transfer is
`exists_ballVolume_gt_cube_of_isometricOn`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal NNReal Manifold Topology
namespace DifferentialGeometry.Geometry.Collapse
universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

/-- Small balls are above every subcritical cubic barrier, transported along a partial
diffeomorphism `Φ : N ⇀ M`, isometric on its source, from a compact manifold `N` (any model)
into a complete connected three-dimensional manifold with boundaryless model. -/
theorem exists_ballVolume_gt_cube_of_isometricOn
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (hg : RiemannianMetricComplete (I := J) g) (hdim : Module.finrank ℝ F = 3)
    (Φ : PartialDiffeomorph I J N M ∞)
    (hmetric : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (p : N) {R : ℝ} (hR : 0 < R) (hball : riemannianBallOf h p R ⊆ Φ.source)
    {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < (ballVolume h p r).toReal := by
  let : NeZero (Module.finrank ℝ F) := ⟨by rw [hdim]; norm_num⟩
  let : IsManifold J 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace J M
  let : RiemannianBundle (fun x : M => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (fun x : M => TangentSpace J x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric J M
  have : CompleteSpace M := hg.complete
  have : IsRiemannianManifold J M := ⟨fun _ _ => rfl⟩
  have : T2Space (TangentBundle J M) := inferInstance
  have hEnorm : IsMetricNorm (I := J) g := isMetricNorm_of_riemannianBundle (I := J) g
  let c := euclideanUnitBallVolume 3
  have hc : 0 < c := euclideanUnitBallVolume_pos 3
  have hwc' : w < c := by simpa only [c, euclideanUnitBallVolume_three_eq] using hwc
  let b := (c + w) / 2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hwb : w < b := by dsimp only [b]; linarith
  have hbc : b < c := by dsimp only [b]; linarith
  let ε := 1 - b / c
  have hε : 0 < ε := sub_pos.mpr ((div_lt_one hc).mpr hbc)
  have hε1 : ε < 1 := by dsimp only [ε]; linarith [div_pos hb hc]
  obtain ⟨ρ, hρ, hsmall⟩ := exists_ballVolume_euclidean_ratio (I := J) g hEnorm (Φ p) ε hε hε1
  refine ⟨min (ρ / 2) R, lt_min (half_pos hρ) hR, ?_⟩
  intro r hr hra
  have hrρ : r < ρ := (hra.trans (min_le_left _ _)).trans_lt (half_lt_self hρ)
  have hrR : r ≤ R := hra.trans (min_le_right _ _)
  have hballr : riemannianBallOf h p r ⊆ Φ.source :=
    (riemannianBallOf_mono h p hrR).trans hball
  have hvol : ballVolume g (Φ p) r = ballVolume h p r :=
    ballVolume_eq_of_isometricOn h g Φ hmetric hballr
  have hlow := (hsmall hr hrρ).1
  have hfin : ballVolume h p r ≠ ⊤ := (ballVolume_lt_top_of_compactSpace h p r).ne
  change _ ≤ ballVolume g (Φ p) r at hlow
  rw [hvol] at hlow
  have hreal := ENNReal.toReal_mono hfin hlow
  rw [volume_unitBall_eq_ofReal_euclideanUnitBallVolume (E := F), hdim] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hε1.le),
    ENNReal.toReal_ofReal (pow_nonneg hr.le 3),
    ENNReal.toReal_ofReal (euclideanUnitBallVolume_pos 3).le] at hreal
  have hcoeff : (1 - ε) * c = b := by
    dsimp only [ε]
    rw [sub_sub_cancel, div_mul_cancel₀ b hc.ne']
  have hlower : b * r ^ 3 ≤ (ballVolume h p r).toReal := by
    calc
      b * r ^ 3 = (1 - ε) * (r ^ 3 * c) := by rw [← hcoeff]; ring
      _ ≤ (ballVolume h p r).toReal := hreal
  exact (mul_lt_mul_of_pos_right hwb (pow_pos hr 3)).trans_le hlower

end Transfer

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- At a centre with positive distance to the boundary, small balls of a compact carrier are above
every subcritical cubic barrier `w r³`, `0 < w < 4π/3`. -/
theorem exists_ballVolume_gt_cube_of_distanceToBoundary_pos (p : W.Carrier)
    (hd : 0 < distanceToBoundary W g p) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < (ballVolume g p r).toReal := by
  have hd' : ENNReal.ofReal 0 < distanceToBoundary W g p := by simpa using hd
  obtain ⟨ρ, -, hρ0', hρd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hd'
  have hρ : 0 < ρ := (ENNReal.ofReal_lt_ofReal_iff'.mp hρ0').1
  let R : ℝ := ρ / 2
  have hR : 0 < R := half_pos hρ
  have hRρ : R < ρ := half_lt_self hρ
  have hRρ' : ENNReal.ofReal R < ENNReal.ofReal ρ :=
    (ENNReal.ofReal_lt_ofReal_iff hρ).mpr hRρ
  -- the open set `U = B(p, ρ)` in the interior
  let U : TopologicalSpace.Opens W.Carrier :=
    ⟨riemannianBallOf g p ρ, isOpen_lt (continuous_riemannianEDist g p) continuous_const⟩
  have hUint : (U : Set W.Carrier) ⊆ W.model.interior W.Carrier :=
    riemannianBallOf_subset_interior W g hρd.le
  have hpU : p ∈ U := by
    change riemannianEDistOf g p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hcloU : riemannianClosedBallOf g p R ⊆ U := fun x hx =>
    lt_of_le_of_lt (show riemannianEDistOf g p x ≤ ENNReal.ofReal R from hx) hRρ'
  have : BoundarylessManifold W.model U :=
    ⟨fun x => W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr (hUint x.property)⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) U := Manifold.interiorChartedSpace W.model ∞
  have : IsManifold (𝓡 3) ∞ U := Manifold.interiorIsManifold W.model ∞
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen W.model U.isOpen)
  have : ConnectedSpace U :=
    isConnected_iff_connectedSpace.mp (isPathConnected_riemannianBallOf g p hρ).isConnected
  have : Nonempty U := ⟨⟨p, hpU⟩⟩
  have hι : IsLocalDiffeomorph (𝓡 3) W.model ∞ (Subtype.val : U → W.Carrier) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := W.model) U)
      (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := U)).symm.isLocalDiffeomorph
  let gU : SmoothRiemannianMetric (𝓡 3) U := localPullMetric g Subtype.val hι
  let K : Set U := Subtype.val ⁻¹' riemannianClosedBallOf g p R
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    change IsCompact (Subtype.val '' (Subtype.val ⁻¹' riemannianClosedBallOf g p R))
    rw [Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hcloU hx⟩, rfl⟩)]
    exact (Geometry.Metric.isClosed_riemannianClosedBallOf g p R).isCompact
  obtain ⟨g', O, hg', hO, hKO, hg'O, -⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := 𝓡 3) gU hK
  let O' : TopologicalSpace.Opens U := ⟨O, hO⟩
  have hF : IsLocalDiffeomorph (𝓡 3) W.model ∞ (fun x : O' => (x : U).val) :=
    isLocalDiffeomorph_comp hι (isLocalDiffeomorph_subtype_val (I := 𝓡 3) O')
  let Ψ : PartialDiffeomorph (𝓡 3) W.model U W.Carrier ∞ :=
    partialDiffeomorphOfInjOn Subtype.val O' hι.contMDiff.contMDiffOn hF
      Subtype.val_injective.injOn
  have hmetric := isometricOn_symm g g' Ψ (fun z hz a b => by
    rw [hg'O z hz]
    exact localPullMetric_inner g Subtype.val hι z a b)
  have hball : riemannianBallOf g p R ⊆ Ψ.symm.source := by
    intro y hy
    have hyc : y ∈ riemannianClosedBallOf g p R :=
      show riemannianEDistOf g p y ≤ ENNReal.ofReal R from le_of_lt hy
    exact ⟨⟨y, hcloU hyc⟩, hKO hyc, rfl⟩
  exact exists_ballVolume_gt_cube_of_isometricOn g g' hg' finrank_euclideanSpace_fin Ψ.symm
    hmetric p hR hball hw hwc

/-- BSA03.a at interior centres: on a compact carrier, at a centre with `0 < d(p, ∂W)`, the first
volume scale `r_p(w)` is positive for `0 < w < 4π/3`, attained exactly, and strictly below the
volume at every smaller radius. -/
theorem firstVolumeScale_spec_of_distanceToBoundary_pos (p : W.Carrier)
    (hd : 0 < distanceToBoundary W g p) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    0 < firstVolumeScale g p w ∧
      (ballVolume g p (firstVolumeScale g p w)).toReal = w * firstVolumeScale g p w ^ 3 ∧
      ∀ r, 0 < r → r < firstVolumeScale g p w → w * r ^ 3 < (ballVolume g p r).toReal :=
  Real.firstPositiveCrossing_cube_spec_of_bounded
    ((ballVolume_toReal_monotone g p).monotoneOn (Ioi 0))
    (fun r _ => ballVolume_toReal_continuousWithinAt_left g p r) hw
    (exists_ballVolume_gt_cube_of_distanceToBoundary_pos W g p hd hw hwc)
    ⟨(Integral.Measure.riemannianVolumeMeasure (I := W.model) (M := W.Carrier) g univ).toReal,
      fun r _ => ballVolume_toReal_le_total g p r⟩

/-- BSA03.a positivity at interior centres, in the units of the static hypotheses
(`w < euclideanThreeUnitBallVolume`). -/
theorem firstVolumeScale_pos_of_distanceToBoundary_pos (p : W.Carrier)
    (hd : 0 < distanceToBoundary W g p) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume) : 0 < firstVolumeScale g p w :=
  (firstVolumeScale_spec_of_distanceToBoundary_pos W g p hd hw hwc).1

end Carrier

end DifferentialGeometry.Geometry.Collapse
