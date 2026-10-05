import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight

/-!
# Boundary port (lane B-PORT-A): TCP02 raw coordinates, circle exclusion, curvature buffer

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualRawAlignment.lean` by `build-logs/scratch/B-PORT-A/gen_shared.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section RealLine

variable (Y : Type*) [MetricSpace Y]

end RealLine

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

section Raw

open Classical in
/-- TCP02's ORIGINAL raw circle coordinate `u_j`: the Euclidean factor of the circle adapted
packet's normalized `(2, β₂)`-splitting at `j` (zero off the circle centres). -/
def circleRaw_KA3_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (j : X) : X → ℝ² :=
  if hj : j ∈ P.circle.centres then fun x =>
    letI := (P.circleAdapted j hj).instY
    (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
      (P.circleAdapted j hj).split x).fst
  else 0

open Classical in
/-- TCP02's ORIGINAL raw slim coordinate `u_j`: the real factor of the slim centre's normalized
`(1, β₁)`-splitting at `j` (zero off the slim centres). -/
def slimRaw_KA3_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (j : X) : X → ℝ :=
  if hj : j ∈ L.slim.centres then fun x =>
    letI := (L.slim.centre j hj).instZ
    (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
      (L.slim.centre j hj).split x).fst
  else 0

open Classical in
/-- TCP02's ORIGINAL raw edge coordinate `u_j`: the real factor of the edge chart's normalized
`(1, b)`-splitting at `j` (zero off the edge centres). -/
def edgeRaw_KA3_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (j : X) : X → ℝ :=
  if hj : j ∈ L.edgeB.centres then
    let C := L.edgeB.chart j hj
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    letI := C.instY
    fun x => (C.split.toFun x).fst
  else 0

/-- The edge chart's splitting as a normalized rank-one splitting at `j` with the raw coordinate
`edgeRaw_KA3_BAUGP`. -/
theorem exists_edge_split_KA3_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.edgeB.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI _y := mY
      ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 (0, q)) b,
        ∀ x, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
          f x).fst = edgeRaw_KA3_BAUGP L j x := by
  have hcen := L.edgeB.chart_center j hj
  unfold edgeRaw_KA3_BAUGP
  rw [dite_eq_left hj]
  let C := L.edgeB.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : C.center = j := hcen
  let _ := C.instY
  obtain ⟨f, hf⟩ := exists_kla_basepoint_KA3 hcen' C.split
  exact ⟨C.Y, C.instY, C.q, f, fun x => by rw [hf x]⟩

theorem circleRaw_KA3_eq_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ P.circle.centres) (x : X) :
    circleRaw_KA3_BAUGP P j x = letI := (P.circleAdapted j hj).instY
      (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
        (P.circleAdapted j hj).split x).fst := by
  unfold circleRaw_KA3_BAUGP
  rw [dite_eq_left hj]

theorem slimRaw_KA3_eq_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.slim.centres) (x : X) :
    slimRaw_KA3_BAUGP L j x = letI := (L.slim.centre j hj).instZ
      (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
        (L.slim.centre j hj).split x).fst := by
  unfold slimRaw_KA3_BAUGP
  rw [dite_eq_left hj]

end Raw

omit [CompleteSpace X] [SigmaCompactSpace X] in
/-- At a circle centre `i` (two-stratum), no normalized `(3, ν)`-splitting exists when
`3ν ≤ β₃ < 1` (the rank-two stratum excludes `(3, β₃)`-splittings). -/
theorem circle_no_three_KA3_BAUGP (Cf : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) {i : X}
    (hi : i ∈ Cf.centres) {ν : ℝ} (hν : 3 * ν ≤ β 3) (hβ3 : β 3 < 1) :
    ¬ ∃ (W : Type) (mW : MetricSpace W), letI _w := mW
      ∃ w : W, Nonempty (@KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin (2 + 1)) × W))
        (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 (0, w)) ν) := by
  rintro ⟨W, mW, w, ⟨f⟩⟩
  have hrank : scaledSplittingRank ρ hρ β i = ((2 : Fin 4) : ℕ) := (Cf.centres_subset hi).2
  have h := (scaledSplittingRank_eq_iff.mp hrank).2.2 3 (by decide) le_rfl
  exact h ⟨W, mW, w, ⟨@KleinerLottApprox.weaken X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i)))
    _ _ _ _ _ _ f hν hβ3⟩⟩

/-- The curvature buffer of `LocalChartPackets` at a reference centre in the form of TCP02's
kernel: `sec ≥ −σ/ρ(i)²` on `B(i, σ⁻¹ρ(i))` when `σ⁻¹ ≤ Lmax`, `0 < σ ≤ 1`. -/
theorem tcp02_sectional_KA3_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : σ⁻¹ ≤ Lmax) (i : X) (hiU : i ∈ U₁) :
    ∀ y, dist y i < σ⁻¹ * ρ i → SectionalBoundedBelowAt g y (-(σ * (ρ i ^ 2)⁻¹)) := by
  intro y hy
  have h := P.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hL i hiU y (by rw [mem_ball]; exact hy)
  refine h.mono ?_
  have hri := hρ i
  have he : ((σ⁻¹ * ρ i) ^ 2)⁻¹ = σ ^ 2 * (ρ i ^ 2)⁻¹ := by
    field_simp
  rw [he]
  have hr2 : 0 < (ρ i ^ 2)⁻¹ := by positivity
  nlinarith [mul_nonneg (mul_nonneg hσ.le hr2.le) (sub_nonneg.mpr hσ1)]


end DifferentialGeometry.Geometry.Collapse
