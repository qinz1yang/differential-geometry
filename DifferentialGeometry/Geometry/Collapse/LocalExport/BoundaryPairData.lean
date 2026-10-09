import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorLocalModel
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02SequenceBinding
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# LC88 / BCP04, packet P3 start: LFR14's inputs at eligible pairs of the completion (BDRY-2, G11)

Review 45 §1.5 and §4.2 (LPA02 row): the first paragraph of LPA02 for the completed interior
`(W°, d_ĝ)` (cut height `4`) of a boundary counterexample sequence, at ELIGIBLE pairs only:
centres `q` with `D(q) > 5` and radii `0 < r ≤ 2 r_q^g(w')` of the ORIGINAL first volume scale.
* `bsa06_pair_BDRY2`: BSA06 and BCP04.a at ONE pair `(p, r)` of the original carrier (the proof of
  `bsa06_clauses_of_scale` without a scale function);
* `completion_pair_data_BDRY2`: at an eligible pair, every normalized ball of radius `R ≤ n/8` of
  `r⁻² ĝ` is the normalized ball of `r⁻² g` and inherits its sectional, derivative and volume data;
* `lpa02_normalized_sequence_hypotheses_boundary_BDRY2` (consumer): LFR14's eventual hypotheses
  (the form of `lpa02_normalized_sequence_hypotheses`) for every sequence of eligible pairs, with
  the
  derivative profile `2^{K+2} A'(2R+2, w')`, `A' = boundaryDerivativeConstant A K`, and the growing
  sectional radius `n/8` (`∀ R, eventually` — review 45 §1.5).
The scale is never recomputed on the completion; no curvature radius is transferred.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Real Bundle
open scoped ENNReal Manifold Topology ContDiff
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The volume of the unit ball of `ρ⁻² g` is `vol_g B(p, ρ)/ρ³` (dimension three). -/
theorem ballVolume_normalizedCenterMetric_one_BDRY2 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) (p : M) :
    (ballVolume (normalizedCenterMetric g ρ hρ) p 1).toReal =
      (ballVolume g p ρ).toReal / ρ ^ 3 := by
  have hs : Real.sqrt ((ρ ^ 2)⁻¹) = ρ⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  have he : Real.sqrt ((ρ ^ 2)⁻¹) * ρ = 1 := by rw [hs, inv_mul_cancel₀ hρ.ne']
  have hv := ballVolume_scaleMetric hdim (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g p ρ
  rw [he] at hv
  unfold normalizedCenterMetric
  rw [hv, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hs]
  simp only [div_eq_mul_inv, inv_pow, mul_comm]

end Volume

/-! ### BSA06 and BCP04.a at one pair -/

/-- **BSA06 and BCP04.a at one pair `(p, r)`, `0 < r ≤ 2 r_p(w')`** (the proof of
`bsa06_clauses_of_scale`, read at one radius instead of a scale function). -/
theorem bsa06_pair_BDRY2 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ → ∀ {A : ℝ → ℝ}, curvatureDerivativesControlled g K A δ →
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {n w' : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
        w' < euclideanThreeUnitBallVolume →
      ∀ (p : W.Carrier) {r : ℝ} (hr : 0 < r), r ≤ 2 * firstVolumeScale g p w' →
        w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p r).toReal / r ^ 3 ∧
        (∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p (n / 4),
          SectionalBoundedBelowAt (normalizedCenterMetric g r hr) y (-((n / 4) ^ 2)⁻¹)) ∧
        (∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R,
            curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤
              (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w') ∧
        (0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / r) := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row.{u}
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  refine ⟨min δS δG, lt_min hδS hδG, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll A hderiv hA n w' hn hδn hwn hwc p r hr hru
  have hnpos : 0 < n := by linarith
  have hstand := (h4 W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B hcoll hderiv hn hδn p).1
  have hn4 : 0 ≤ n ^ 4 := pow_nonneg hnpos.le 4
  have hδn' : δ * n ^ 4 ≤ 1 := by nlinarith [mul_nonneg hδ0 hn4]
  obtain ⟨hdtop, hR⟩ := (hG W g K δ hK hδ0 (hδ.trans (min_le_right _ _)) B).2 ‹_› p
  set D := (distanceToBoundary W g p).toReal with hDdef
  have hdeq : distanceToBoundary W g p = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal hdtop.ne).symm
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  obtain ⟨hRtop, hRD⟩ := toReal_curvatureRadius_le_of_le_add_three W g hD0 hdeq hR
  have h2nu := two_mul_firstVolumeScale_lt_toReal_of_standing W g p hnpos hstand hwn hRtop
  refine ⟨(volume_lower_at_modified_scale_of_standing_everywhere W g p (by linarith) hwn hr
      hru).2,
    normalizedCenterMetric_sectional_of_standing g p hnpos hstand hwn hr hru,
    normalizedCenterMetric_derivative_bounds_of_standing g p hderiv hA (by linarith) hδn'
      hstand hwn hwc hr hru, fun hd => ?_⟩
  have hD : 0 < D := by
    rw [hdeq] at hd
    exact ENNReal.ofReal_pos.mp hd
  exact mul_div_add_three_lt_distance_div_scale hD hRD h2nu hr hru

/-! ### The completion at an eligible pair -/

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- The interior of a connected carrier, as a local instance (G2's connectedness). -/
local instance connectedSpace_interior_BDRY2 (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] :
    ConnectedSpace (W.pieceInterior ⊤) :=
  connectedSpace_pieceInterior_top_BDRY1 W

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- A complete completion makes the interior a complete metric space for `d_ĝ`. -/
theorem completeSpace_completion_BDRY2 (hcomplete : RiemannianMetricComplete (I := 𝓡 3) ĝ) :
    @CompleteSpace (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toUniformSpace := by
  let : RiemannianBundle (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
    ⟨ĝ.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact hcomplete.complete

/-- **The completion at an eligible pair (P3).** For `ĝ = g°` on `{D ≥ 4}`, a centre `q` with
`D(q) > 5` and a radius `r > 0` with BCP04.a at `(q, r)`: for `0 ≤ R ≤ n/8` the normalized ball of
radius `R` of `r⁻² ĝ` is that of `r⁻² g` on `W` (inside `{D > 4}`), and every sectional lower bound,
every curvature-derivative bound and the ball volume of `r⁻² g` there hold for `r⁻² ĝ`. -/
theorem completion_pair_data_BDRY2
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 5 < distanceToBoundary W g q)
    {r n : ℝ} (hr : 0 < r)
    (hbcp : n * (distanceToBoundary W g q).toReal / ((distanceToBoundary W g q).toReal + 3) <
      (distanceToBoundary W g q).toReal / r)
    {R : ℝ} (hR : 0 ≤ R) (hRn : 8 * R ≤ n) :
    Subtype.val '' riemannianBallOf (normalizedCenterMetric ĝ r hr) q R =
        riemannianBallOf (normalizedCenterMetric g r hr) q.val R ∧
      (∀ κ : ℝ, (∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) q.val R,
          SectionalBoundedBelowAt (normalizedCenterMetric g r hr) y κ) →
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) q R,
          SectionalBoundedBelowAt (normalizedCenterMetric ĝ r hr) y κ) ∧
      (∀ (K : ℕ) (bound : ℝ), (∀ k ≤ K, ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr)
          q.val R, curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤ bound) →
        ∀ k ≤ K, ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) q R,
          curvatureDerivativeNorm (normalizedCenterMetric ĝ r hr) k y ≤ bound) ∧
      ballVolume (normalizedCenterMetric ĝ r hr) q R =
        ballVolume (normalizedCenterMetric g r hr) q.val R := by
  have hpos : 0 < distanceToBoundary W g q := lt_of_le_of_lt zero_le hq
  have htop : distanceToBoundary W g q ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hbcp
    simp at hbcp
  have hd : 5 < (distanceToBoundary W g q).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) htop).mp hq
  have hC : (0 : ℝ) ≤ R / 3 := by positivity
  have hbud' := buffer_lt_of_bcp04a_BDRY1 hd hr (show 24 * (R / 3) ≤ n by linarith) hbcp
  have hbud : ENNReal.ofReal (R * r + 4) ≤ distanceToBoundary W g q := by
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have himg := image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq q
    (mul_nonneg hR hr.le) hbud
  have hsub := riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g
    (mul_nonneg hR hr.le) (by norm_num) hbud
  rw [← normalizedCenterMetric_ball ĝ hr q R, ← normalizedCenterMetric_ball g hr q.val R] at himg
  rw [← normalizedCenterMetric_ball g hr q.val R] at hsub
  have hdata := completion_cut_local_data_BDRY1 W g ĝ (by norm_num) heq hr
  have hmem : ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) q R,
      y.val ∈ riemannianBallOf (normalizedCenterMetric g r hr) q.val R ∧
        ENNReal.ofReal 4 < distanceToBoundary W g y := fun y hy => by
    have hy' : y.val ∈ riemannianBallOf (normalizedCenterMetric g r hr) q.val R :=
      himg ▸ ⟨y, hy, rfl⟩
    exact ⟨hy', hsub hy'⟩
  refine ⟨himg, fun κ hsec y hy => ?_, fun K bound hder k hk y hy => ?_, ?_⟩
  · obtain ⟨hy', hd4⟩ := hmem y hy
    exact ((hdata.1 y hd4 κ).2).mpr (hsec _ hy')
  · obtain ⟨hy', hd4⟩ := hmem y hy
    rw [(hdata.2.1 y hd4 k).2]
    exact hder k hk _ hy'
  · exact (hdata.2.2 q hR hbud).2

omit [ConnectedSpace W.Carrier] in
/-- **LPA02, first paragraph, on the completed interiors (consumer).** For a boundary counterexample
sequence, completions `ĝ_n` at cut height `4`, and ANY sequence of eligible pairs `(z_j, r_j)` at
indices `a j → ∞` (`D(z_j) > 5`, `0 < r_j ≤ 2 r_{z_j}(w')` for the ORIGINAL metric), the normalized
sources `((W_{a j})°, r_j⁻² ĝ, z_j)` satisfy LFR14's eventual hypotheses: aligned distances, volume
`≥ v_*` of the unit ball, the derivative profile `2^{K+2} A'(2R+2, w')` on every fixed ball
eventually, and `sec ≥ -(a_j/4)⁻²` on the ball of radius `a_j/8 → ∞`. -/
theorem lpa02_normalized_sequence_hypotheses_boundary_BDRY2 :
    ∃ δStar > 0, ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {w' : ℝ}, 0 < w' → w' < euclideanThreeUnitBallVolume →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∀ (a : ℕ → ℕ), Tendsto a atTop atTop →
      ∀ (z : ∀ j, (W (a j)).pieceInterior ⊤),
        (∀ j, ENNReal.ofReal 5 < distanceToBoundary (W (a j)) (g (a j)) (z j)) →
      ∀ (r : ℕ → ℝ) (hr : ∀ j, 0 < r j),
        (∀ j, r j ≤ 2 * firstVolumeScale (g (a j)) (z j) w') →
      (∀ j a' b', riemannianEDistOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) a' b' =
        ENNReal.ofReal (@dist _ ((inducedMetricSpace (ĝ (a j))).rescale (r j)⁻¹
          (inv_pos.mpr (hr j))).toDist a' b')) ∧
      0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      (∀ᶠ j in atTop, ENNReal.ofReal (w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2)) ≤
        riemannianVolumeMeasure (𝓡 3) ((W (a j)).pieceInterior ⊤)
          (normalizedCenterMetric (ĝ (a j)) (r j) (hr j))
          (riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) 1)) ∧
      (∀ R > 0, ∀ᶠ j in atTop, ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) R,
          curvDerivNorm k (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) y ≤
            (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w') ∧
      Tendsto (fun j => (((a j : ℝ) / 4) ^ 2)⁻¹) atTop (𝓝 0) ∧
      Tendsto (fun j => (a j : ℝ) / 8) atTop atTop ∧
      (∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j))
          (z j) ((a j : ℝ) / 8),
        SectionalBoundedBelowAt (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) y
          (-(((a j : ℝ) / 4) ^ 2)⁻¹)) := by
  obtain ⟨δS, hδS, hpair⟩ := bsa06_pair_BDRY2.{u}
  refine ⟨δS, hδS, ?_⟩
  intro K hK A hA w' hw' hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ heq a ha z hz r hr hrz
  have haR : Tendsto (fun j => (a j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ha
  have hev : ∀ᶠ j in atTop, 3 ≤ (a j : ℝ) ∧ ((a j : ℝ))⁻¹ ≤ w' := by
    filter_upwards [haR.eventually_ge_atTop 3, haR.eventually_ge_atTop w'⁻¹] with j h3 hw
    have h0 : 0 < (a j : ℝ) := by linarith
    exact (inv_le_comm₀ h0 hw').mpr hw |> fun h => ⟨h3, h⟩
  have hdat : ∀ j, 3 ≤ (a j : ℝ) → ((a j : ℝ))⁻¹ ≤ w' → _ := fun j h3 hw => by
    have h1 : 1 ≤ a j := by exact_mod_cast (show (1 : ℝ) ≤ a j by linarith)
    exact hpair (W (a j)) (g (a j)) K _ hK (boundaryCounterexampleRatio_pos hδ₀ h1).le
      ((boundaryCounterexampleRatio_le δ₀ (a j)).trans hδ₀S) (B (a j)) (hcoll (a j)) (hder (a j))
      hA h3 (boundaryCounterexampleRatio_mul_le δ₀ h1) hw hwc (z j).val (hr j) (hrz j)
  have hpd : ∀ j, 3 ≤ (a j : ℝ) → ((a j : ℝ))⁻¹ ≤ w' → ∀ {R : ℝ}, 0 ≤ R → 8 * R ≤ (a j : ℝ) →
      _ := fun j h3 hw R hR hRn =>
    completion_pair_data_BDRY2 (W (a j)) (g (a j)) (ĝ (a j)) (heq (a j)) (z j) (hz j) (hr j)
      ((hdat j h3 hw).2.2.2 (lt_of_le_of_lt zero_le (hz j))) hR hRn
  have hv0 : 0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    (volume_lower_at_modified_scale_of_pos (g (a 0)) (z 0).val hw' (hr 0) (hrz 0)).1
  refine ⟨fun j a' b' => ?_, hv0, ?_, fun R hR => ?_, ?_, haR.atTop_div_const (by norm_num), ?_⟩
  · let := inducedMetricSpace (ĝ (a j))
    exact riemannianEDistOf_normalizedCenterMetric (ĝ (a j)) (inducedMetricSpace_hmetric (ĝ (a j)))
      (hr j) a' b'
  · filter_upwards [hev, haR.eventually_ge_atTop 8] with j ⟨h3, hw⟩ h8
    have hvol := (hdat j h3 hw).1
    have heqv := (hpd j h3 hw zero_le_one (by linarith)).2.2.2
    have hid := ballVolume_normalizedCenterMetric_one_BDRY2 finrank_euclideanSpace_fin (g (a j))
      (hr j) (z j).val
    change ENNReal.ofReal _ ≤ ballVolume (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) 1
    rw [heqv]
    refine (ENNReal.ofReal_le_ofReal (hid ▸ hvol)).trans ENNReal.ofReal_toReal_le
  · filter_upwards [hev, haR.eventually_gt_atTop (8 * R + 2)] with j ⟨h3, hw⟩ hR8 k hk y hy
    have hder' := (hdat j h3 hw).2.2.1 R hR (by linarith)
    have h := (hpd j h3 hw hR.le (by linarith)).2.2.1 K _ hder' k hk y hy
    rwa [curvatureDerivativeNorm_eq_curvDerivNorm] at h
  · have hsq : Tendsto (fun j => ((a j : ℝ) / 4) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (haR.atTop_div_const (by norm_num))
    exact tendsto_inv_atTop_zero.comp hsq
  · filter_upwards [hev] with j ⟨h3, hw⟩ y hy
    have hsec := (hdat j h3 hw).2.1
    refine (hpd j h3 hw (by positivity) (by linarith)).2.1 _ (fun y' hy' => hsec y' ?_) y hy
    exact riemannianBallOf_mono _ _ (by linarith) hy'

end DifferentialGeometry.Geometry.Collapse
