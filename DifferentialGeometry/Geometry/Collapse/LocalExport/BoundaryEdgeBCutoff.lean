import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsProducer
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap

/-!
# The actual edge cutoffs of the revised edge family `edgeB` on a complete carrier (BAUG-A, G2)

Draft 61 §2.2 (P0-A: every boundary construction consumes `edgeB`): the weak-edge block (WB) reads
`Σ_{i ∈ I_e^B} ζ_i^B`, the actual LC87 edge cutoffs of the REVISED edge charts. The closed cutoff
`EdgeFamily.cutoff` is defined on a compact carrier; here the same formula
`ζ_j = Φ(η_j/Δ) ψ(F/(Δρ))` (extended by zero off the normalized chart ball `B(j, 100Δ)`) on an
`EdgeFamilyOn` over a complete carrier, with the closed proofs re-run (only `complete_of_compact`
is replaced by the carrier's completeness):

* `EdgeFamilyOn.coord_BAUGA` (`= coord_BCG1` at centres, `0` elsewhere),
  `EdgeFamilyOn.cutoff_BAUGA`;
* `contMDiffOn_coord_BAUGA`, `cutoff_eq_formula_BAUGA`, `contMDiffAt_height_of_collar_BAUGA`
  (`F/ρ` smooth near collar points, LFR38), `contMDiff_cutoff_of_margin_BAUGA`,
  `mem_of_cutoff_ne_zero_BAUGA`, `cutoff_mem_Icc_BAUGA`;
* on `LocalPacketsOnB` (the composite `edgeB_coarse`): `LocalPacketsOnB.exists_edgeB_link_BAUGA`
  (LC87 packet (iv) for `edgeB`) and `LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA`
  (FC18 (ii):
  `tsupport ζ_j^B ⊆ B̄(j, 14Δρ(j)) ⊆ B(j, 100Δρ(j))` — the zero-extension margin, unconditional);
* consumer `LocalPacketsOnB.contMDiff_edgeB_cutoff_BAUGA`: every actual `edgeB` cutoff is smooth.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section EdgeOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

namespace EdgeFamilyOn

open Classical in
/-- The tangential coordinate `η_j` of the edge chart at `j` (`coord_BCG1` at a centre, zero off
the centres). -/
def coord_BAUGA (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (j : X) :
    X → ℝ :=
  if hj : j ∈ F.centres then F.coord_BCG1 j hj else 0

theorem coord_BAUGA_of_mem (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {j : X} (hj : j ∈ F.centres) : F.coord_BAUGA j = F.coord_BCG1 j hj := by
  unfold coord_BAUGA
  rw [dite_eq_left hj]

open Classical in
/-- The actual edge cutoff `Φ(η_j/Δ) ψ(F/(Δρ))` of the chart at `j` (normalized at `j`, extended
by zero off the normalized chart ball `B(j, 100Δ)`; zero off the centres). -/
def cutoff_BAUGA (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (j : X) :
    X → ℝ :=
  if hj : j ∈ F.centres then
    let C := F.chart j hj
    let Fs := F.smoothing
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun x => edgeCoordinateProfile (C.coord x.val / Δ) *
        edgeHeightProfile (Fs x.val / ρ j / (Δ * (ρ x.val / ρ j)))) 0
  else 0

variable (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)

/-- The actual edge coordinate is smooth on the physical chart ball `B(j, 100Δρ(j))`. -/
theorem contMDiffOn_coord_BAUGA {j : X} (hj : j ∈ F.centres) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.coord_BAUGA j) (ball j (100 * Δ * ρ j)) := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hsub : ∀ x ∈ ball j (100 * Δ * ρ j), (ρ j)⁻¹ * @dist X mX.toDist x j ≤ 100 * Δ := by
    intro x hx
    exact (inv_mul_dist_lt_of_mem_ball_LC87 hrj hx).le
  rw [F.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  refine C.contMDiffOn_coord.mono fun x hx => C.closedBall_subset_domain ?_
  rw [hc']
  exact hsub x hx

/-- On the physical chart ball the actual edge cutoff is its formula `f(η_j/Δ) · g(F/(ρΔ))`. -/
theorem cutoff_eq_formula_BAUGA {j : X} (hj : j ∈ F.centres) {x : X}
    (hx : x ∈ ball j (100 * Δ * ρ j)) :
    F.cutoff_BAUGA j x = edgeCoordinateProfile (F.coord_BAUGA j x / Δ) *
      edgeHeightProfile (F.smoothing x / ρ x / Δ) := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  rw [F.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  unfold EdgeFamilyOn.cutoff_BAUGA
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  change (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun y => edgeCoordinateProfile (C.coord y.val / Δ) *
        edgeHeightProfile (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0
      (⟨x, hmem⟩ : ball C.center (100 * Δ)).val =
    edgeCoordinateProfile (C.coord x / Δ) * edgeHeightProfile (Fs x / ρ x / Δ)
  rw [Subtype.val_injective.extend_apply]
  simp only [hq]

/-- The actual normalized height `F/ρ` is smooth near every collar point of a revised edge chart
(LFR38's collar recorded in `EdgeChart.collar`). -/
theorem contMDiffAt_height_of_collar_BAUGA {j : X} (hj : j ∈ F.centres) {x : X}
    (hx : x ∈ ball j (100 * Δ * ρ j)) (hcoord : |F.coord_BAUGA j x| ≤ 10 * Δ)
    (h1 : Δ / 10 ≤ F.smoothing x / ρ x) (h2 : F.smoothing x / ρ x ≤ 10 * Δ) :
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => F.smoothing y / ρ y) x := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : ∀ y, Fs y / ρ j / (ρ y / ρ j) = Fs y / ρ y := fun y => by
    have := hρ y
    field_simp
  rw [F.coord_BAUGA_of_mem hj] at hcoord
  unfold EdgeFamilyOn.coord_BCG1 at hcoord
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  have hcoord' : |C.coord x| ≤ 10 * Δ := hcoord
  have h1' : Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) := by rw [hq]; exact h1
  have h2' : Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by rw [hq]; exact h2
  obtain ⟨-, -, hJ, -⟩ := C.collar x hmem hcoord' h1' h2'
  have hpos : (0 : ℝ) < 300 * (ρ x / ρ j) := by positivity
  have hopen : IsOpen (ball x (300 * (ρ x / ρ j))) := isOpen_ball
  have hJx := hJ.contMDiffAt (hopen.mem_nhds (mem_ball_self hpos))
  have hproj := ContMDiffAt.comp x
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contMDiff.contMDiffAt)
    hJx
  refine hproj.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  change Fs y / ρ y = Fs y / ρ j / (ρ y / ρ j)
  exact (hq y).symm

/-- Where an actual `edgeB` cutoff is nonzero: `x` lies in the normalized chart ball `B(j, 100Δ)`,
`|η_j(x)| < 9Δ` and `F(x)/ρ(x) < 9Δ`. -/
theorem mem_of_cutoff_ne_zero_BAUGA (hΔ : 0 < Δ) {j x : X} (h : F.cutoff_BAUGA j x ≠ 0) :
    j ∈ F.centres ∧ (ρ j)⁻¹ * dist x j < 100 * Δ ∧ |F.coord_BAUGA j x| < 9 * Δ ∧
      F.smoothing x / ρ x < 9 * Δ := by
  by_cases hj : j ∈ F.centres
  swap
  · exfalso
    apply h
    unfold EdgeFamilyOn.cutoff_BAUGA
    rw [dite_eq_right hj]
    rfl
  refine ⟨hj, ?_⟩
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  rw [F.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  unfold EdgeFamilyOn.cutoff_BAUGA at h
  rw [dite_eq_left hj] at h
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  change (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun y => edgeCoordinateProfile (C.coord y.val / Δ) *
        edgeHeightProfile (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0 x ≠ 0 at h
  by_cases hmem : x ∈ ball C.center (100 * Δ)
  swap
  · exfalso
    apply h
    rw [Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hmem (ha ▸ a.property))]
    rfl
  have hval := h
  rw [show x = ((⟨x, hmem⟩ : ball C.center (100 * Δ)) : X) from rfl,
    Subtype.val_injective.extend_apply] at hval
  have hball : (ρ j)⁻¹ * @dist X mX.toDist x j < 100 * Δ := by
    have hm : x ∈ ball C.center (100 * Δ) := hmem
    rw [hc'] at hm
    exact hm
  have hcoord : edgeCoordinateProfile (C.coord x / Δ) ≠ 0 := left_ne_zero_of_mul hval
  have hheight : edgeHeightProfile (Fs x / ρ j / (Δ * (ρ x / ρ j))) ≠ 0 :=
    right_ne_zero_of_mul hval
  refine ⟨hball, ?_, ?_⟩
  · change |C.coord x| < 9 * Δ
    rw [abs_lt]
    constructor
    · by_contra hle
      apply hcoord
      refine intervalPlateauProfile_zero_left (by norm_num) ?_
      rw [div_le_iff₀ hΔ]
      linarith
    · by_contra hle
      apply hcoord
      refine intervalPlateauProfile_zero_right (by norm_num) ?_
      rw [le_div_iff₀ hΔ]
      linarith
  · by_contra hle
    apply hheight
    rw [hq]
    refine descendingIntervalProfile_zero (by norm_num) ?_
    rw [le_div_iff₀ hΔ]
    linarith

/-- An actual `edgeB` cutoff vanishes outside the physical chart ball `B(j, 100Δρ(j))`. -/
theorem cutoff_eq_zero_of_notMem_ball_BAUGA (hΔ : 0 < Δ) {j x : X}
    (hx : x ∉ ball j (100 * Δ * ρ j)) : F.cutoff_BAUGA j x = 0 := by
  by_contra h
  obtain ⟨-, hball, -, -⟩ := F.mem_of_cutoff_ne_zero_BAUGA hΔ h
  apply hx
  have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
  rw [mem_ball]
  linarith

/-- The actual `edgeB` cutoffs take values in `[0, 1]`. -/
theorem cutoff_mem_Icc_BAUGA (hΔ : 0 < Δ) (j x : X) : F.cutoff_BAUGA j x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : F.cutoff_BAUGA j x = 0
  · rw [h]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨hj, hball, -, -⟩ := F.mem_of_cutoff_ne_zero_BAUGA hΔ h
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [F.cutoff_eq_formula_BAUGA hj hx]
  have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (F.coord_BAUGA j x / Δ)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 (F.smoothing x / ρ x / Δ)
  change intervalPlateauProfile (-9) (-8) 8 9 (F.coord_BAUGA j x / Δ) *
    descendingIntervalProfile 8 9 (F.smoothing x / ρ x / Δ) ∈ Icc (0 : ℝ) 1
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **The actual `edgeB` cutoff is smooth** once its closed support lies in the OPEN chart ball
`B(j, 100Δρ(j))`; the height factor is smooth through the collar charts where it varies. -/
theorem contMDiff_cutoff_of_margin_BAUGA (hΔ : 0 < Δ) (hρc : Continuous ρ) {j : X}
    (hm : tsupport (F.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.cutoff_BAUGA j) := by
  by_cases hj : j ∈ F.centres
  swap
  · have h0 : F.cutoff_BAUGA j = fun _ => 0 := by
      funext x
      unfold EdgeFamilyOn.cutoff_BAUGA
      rw [dite_eq_right hj]
      rfl
    rw [h0]
    exact contMDiff_const
  intro x
  by_cases hx : x ∈ tsupport (F.cutoff_BAUGA j)
  swap
  · have h0 : F.cutoff_BAUGA j =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  have hxb := hm hx
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have heq : F.cutoff_BAUGA j =ᶠ[𝓝 x] fun y => edgeCoordinateProfile (F.coord_BAUGA j y / Δ) *
      edgeHeightProfile (F.smoothing y / ρ y / Δ) := by
    filter_upwards [hball] with y hy
    exact F.cutoff_eq_formula_BAUGA hj hy
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hcoordAt : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.coord_BAUGA j) x :=
    (F.contMDiffOn_coord_BAUGA hj).contMDiffAt hball
  have hprof : ContDiff ℝ ∞ fun t : ℝ => edgeCoordinateProfile (t / Δ) :=
    edgeProfiles_contDiff.1.comp (contDiff_id.div_const Δ)
  have hhprof : ContDiff ℝ ∞ fun t : ℝ => edgeHeightProfile (t / Δ) :=
    edgeProfiles_contDiff.2.1.comp (contDiff_id.div_const Δ)
  have hA : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => edgeCoordinateProfile (F.coord_BAUGA j y / Δ)) x :=
    hprof.contMDiff.contMDiffAt.comp x hcoordAt
  have hsc : Continuous fun y => F.smoothing y / ρ y / Δ :=
    (F.lipschitz_smoothing.continuous.div hρc fun y => (hρ y).ne').div_const Δ
  by_cases h8 : F.smoothing x / ρ x / Δ < 8
  · have hB : (fun y => edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [hsc.continuousAt.eventually (gt_mem_nhds h8)] with y hy
      exact descendingIntervalProfile_one (by norm_num) hy.le
    exact hA.mul (contMDiffAt_const.congr_of_eventuallyEq hB)
  by_cases h9 : 9 < F.smoothing x / ρ x / Δ
  · have hB : (fun y => edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hsc.continuousAt.eventually (lt_mem_nhds h9)] with y hy
      exact descendingIntervalProfile_zero (by norm_num) hy.le
    exact hA.mul (contMDiffAt_const.congr_of_eventuallyEq hB)
  rw [not_lt] at h8 h9
  by_cases hcx : |F.coord_BAUGA j x| ≤ 9 * Δ
  · have hFx : F.smoothing x / ρ x = Δ * (F.smoothing x / ρ x / Δ) := by
      field_simp
    have hH := F.contMDiffAt_height_of_collar_BAUGA hj hxb (by linarith)
      (by rw [hFx]; nlinarith) (by rw [hFx]; nlinarith)
    exact hA.mul (hhprof.contMDiff.contMDiffAt.comp x hH)
  · rw [not_le] at hcx
    have hcc : ContinuousAt (F.coord_BAUGA j) x := hcoordAt.continuousAt
    have hA0 : (fun y => edgeCoordinateProfile (F.coord_BAUGA j y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      rcases lt_abs.mp hcx with hpos | hneg
      · filter_upwards [hcc.eventually (lt_mem_nhds hpos)] with y hy
        refine intervalPlateauProfile_zero_right (by norm_num) ?_
        rw [le_div_iff₀ hΔ]
        linarith
      · have hneg' : F.coord_BAUGA j x < -(9 * Δ) := by linarith
        filter_upwards [hcc.eventually (gt_mem_nhds hneg')] with y hy
        refine intervalPlateauProfile_zero_left (by norm_num) ?_
        rw [div_le_iff₀ hΔ]
        linarith
    have hprod0 : (fun y => edgeCoordinateProfile (F.coord_BAUGA j y / Δ) *
        edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hA0] with y hy
      rw [hy, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hprod0

end EdgeFamilyOn

end EdgeOn

section LinkB

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

namespace LocalPacketsOnB

variable (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
  V vs U₁ U₂ Ue₁ Ue₂)

/-- **The `edgeB` link in the physical form of FC17/FC18** (LC87 packet (iv) for the revised edge
charts, from the composite `edgeB_coarse` and the chart's value clause). -/
theorem exists_edgeB_link_BAUGA (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ < 1 / 10) {j : X}
    (hj : j ∈ F.edgeB.centres) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ z ∈ closure {y : X | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10) ∧
      (∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |F.edgeB.coord_BAUGA j x - (Q x).fst| ≤ Δ / 100) := by
  have hco := F.edgeB_coarse j hj
  have hcen := F.edgeB.chart_center j hj
  have hcoordeq := F.edgeB.coord_BAUGA_of_mem hj
  let C := F.edgeB.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  obtain ⟨h0, hdist, hnn, -, hlow, -⟩ := hco
  let Qn : X → WithLp 2 (ℝ × ℝ) := C.Qn
  let Q : X → WithLp 2 (ℝ × ℝ) := fun x => WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd)
  have hQ : ∀ x, (ρ j)⁻¹ * @dist X mX.toDist x j < 200 * Δ → Q x = Qn x := by
    intro x hx
    have h := hnn x hx
    change WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd) = Qn x
    rw [max_eq_right h]
    rfl
  have hτΔ : τ * Δ < Δ / 10 := by nlinarith
  refine ⟨Q, ?_, fun x => le_max_left _ _, ?_, ?_, ?_⟩
  · rw [hQ j (by rw [@dist_self X mX.toPseudoMetricSpace j, mul_zero]; positivity)]
    exact h0
  · intro x y hx hy
    rw [hQ x hx, hQ y hy]
    exact hdist x hx y hy
  · intro z hz hzj
    have hz' : (ρ j)⁻¹ * @dist X mX.toDist z j < 200 * Δ := by linarith
    rw [hQ z hz']
    exact (hlow z ⟨hz, show (ρ j)⁻¹ * @dist X mX.toDist z j < 190 * Δ by linarith⟩).trans_lt hτΔ
  · intro x hx
    have hx' : (ρ j)⁻¹ * @dist X mX.toDist x j < 200 * Δ := by linarith
    rw [hQ x hx', hcoordeq]
    unfold EdgeFamilyOn.coord_BCG1
    have hxc : x ∈ @ball X mR.toPseudoMetricSpace C.center (100 * Δ) := by
      rw [hcen']
      exact hx
    have hv := C.value x hxc
    rw [← C.Qn_fst x] at hv
    have hμΔ : μ * Δ ≤ Δ / 100 := by nlinarith
    change |C.coord x - (Qn x).fst| ≤ Δ / 100
    linarith

/-- **FC18 (ii) for `edgeB`** (the zero-extension margin, unconditional on the family): the closed
support of every actual `edgeB` cutoff lies in `B̄(j, 14Δρ(j)) ⊆ B(j, 20Δρ(j)) ⊆ B(j, 100Δρ(j))`. -/
theorem tsupport_edgeB_cutoff_subset_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ F.edgeB.centres) :
    tsupport (F.edgeB.cutoff_BAUGA j) ⊆ closedBall j (14 * Δ * ρ j) ∧
      closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j) ∧
      tsupport (F.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j) := by
  obtain ⟨Q, hQ0, hQnn, hQdist, hQlow, hlink⟩ :=
    F.exists_edgeB_link_BAUGA hΔ hμ (by linarith) hj
  have hrj := hρ j
  have hpE := F.edgeB.mem_closure_weakEdge_BDRY5 hj
  have hpt : ∀ x, F.edgeB.cutoff_BAUGA j x ≠ 0 → dist x j ≤ 14 * Δ * ρ j := by
    intro x hx
    obtain ⟨-, hball, hcoord, hheight⟩ := F.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hx
    have hrx := hρ x
    have hdxj : dist x j < 100 * Δ * ρ j := by
      rw [inv_mul_lt_iff₀ hrj] at hball
      linarith
    have hρx : ρ x ≤ 101 / 100 * ρ j := by
      have hlip := F.lipschitz_scale.dist_le_mul x j
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
      have h1 : Λ * dist x j ≤ Λ * (100 * Δ * ρ j) := mul_le_mul_of_nonneg_left hdxj.le hΛ
      have h2 : Λ * (100 * Δ * ρ j) ≤ 1 / 100 * ρ j := by nlinarith
      linarith [(abs_le.mp hlip).2]
    have hval := F.edgeB.smoothing_value j hj x
    have hFx : F.edgeB.smoothing x < 9 * Δ * ρ x := by
      rwa [div_lt_iff₀ hrx] at hheight
    have hinf : infDist x (closure {y : X | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) < 46 * Δ / 5 * ρ j := by
      have h9 : 9 * Δ * ρ x ≤ 9 * Δ * (101 / 100 * ρ j) :=
        mul_le_mul_of_nonneg_left hρx (by positivity)
      have hμ' : μ * (Δ * ρ j) ≤ 1 / 10 * (Δ * ρ j) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have := mul_pos hΔ hrj
      linarith [(abs_lt.mp hval).1]
    obtain ⟨z, hz, hxz⟩ := (infDist_lt_iff ⟨j, hpE⟩).mp hinf
    have hk := @fc18_edge_support_kernel X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace
      Q (F.edgeB.coord_BAUGA j) (closure {y : X | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) j Δ (τ * Δ) hΔ
      (by nlinarith) hQ0 hQnn (fun x hx y hy => hQdist x y hx hy)
      (fun z hz => hQlow z hz.1 hz.2) (fun x hx => hlink x hx) x hball hcoord
      ⟨z, hz, (show (ρ j)⁻¹ * dist x z < 46 * Δ / 5 by
        rw [inv_mul_lt_iff₀ hrj]; linarith)⟩
    have hk' : (ρ j)⁻¹ * dist x j < 14 * Δ := hk
    rw [inv_mul_lt_iff₀ hrj] at hk'
    linarith
  have hS : tsupport (F.edgeB.cutoff_BAUGA j) ⊆ closedBall j (14 * Δ * ρ j) :=
    closure_minimal (fun x hx => mem_closedBall.mpr (hpt x hx)) isClosed_closedBall
  have hpos := mul_pos hΔ hrj
  have hB : closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j) :=
    closedBall_subset_ball (by nlinarith)
  exact ⟨hS, hB, hS.trans (hB.trans (ball_subset_ball (by nlinarith)))⟩

/-- **Consumer**: every actual `edgeB` cutoff is smooth on the carrier. -/
theorem contMDiff_edgeB_cutoff_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : X) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.edgeB.cutoff_BAUGA j) := by
  by_cases hj : j ∈ F.edgeB.centres
  · exact F.edgeB.contMDiff_cutoff_of_margin_BAUGA hΔ F.contMDiff_scale.continuous
      (F.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).2.2
  · have h0 : F.edgeB.cutoff_BAUGA j = fun _ => 0 := by
      funext x
      unfold EdgeFamilyOn.cutoff_BAUGA
      rw [dite_eq_right hj]
      rfl
    rw [h0]
    exact contMDiff_const

end LocalPacketsOnB

end LinkB

end DifferentialGeometry.Geometry.Collapse
