import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedWeakEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutoffOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalSlimValue
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

/-!
# Kernels of the interior layer of the augmented map on `W` (lane BAUG-A, G3)

Draft 61 §2.2–§2.3, disposition D61-4 ("factor `cgpGlobalMap` into a finite-active-family formula
layer plus a local proof layer; no `CompactSpace`, no closed-family parameter"). The local proof
layer:

* `contMDiff_blockSlot_BAUGA`, `tsupport_blockSlot_subset_BAUGA`: one block
  `p ↦ ((R ζ) η, R ζ)` of FC01's block map is smooth when the cutoff's CLOSED support lies in an
  open set where the coordinate is smooth, and its closed support lies in that of the cutoff;
* `CircleFamilyOn.coord_BAUGA`, `CircleFamilyOn.contMDiffOn_coord_BAUGA`: the circle chart
  coordinate (normalized at `j`) on a complete carrier, smooth on `B(j, 200ρ(j))`;
* `SlimCentreOn.contMDiffOn_coord_BAUGA`: the slim coordinate `coord_BCG2` is smooth on
  `B(j, 10⁶Δρ(j))` (complete carrier);
* `contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA`: a smooth function on `W°` whose
  closed support lies in a `ĝ`-ball `B(j, r)` that is transported to `W` (`ι B_ĝ(j, R) = B_g(j, R)`
  with `r < R`, `d_g = d_ĝ` on `B_ĝ(j, R')`, `r ≤ R'`; T3B's consumer-ball and zero-ball clauses)
  extends by zero to a smooth function on `W` (its closed support lies in the closed `g`-ball
  `B̄_g(j, r)`, compact in `W` and contained in `W°`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Analysis DifferentialGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Slot

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **One block of FC01's map is smooth** when the cutoff is smooth, the radius is smooth, and the
coordinate is smooth on an open set containing the cutoff's closed support. -/
theorem contMDiff_blockSlot_BAUGA {R ζ : M → ℝ} {η : M → V} {U : Set M} (hU : IsOpen U)
    (hη : ContMDiffOn I 𝓘(ℝ, V) ∞ η U) (hζ : ContMDiff I 𝓘(ℝ) ∞ ζ)
    (hR : ContMDiff I 𝓘(ℝ) ∞ R) (hsupp : tsupport ζ ⊆ U) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (V × ℝ)) ∞
      (fun p => WithLp.toLp 2 ((R p * ζ p) • η p, R p * ζ p)) := by
  have hmark : ContMDiff I 𝓘(ℝ) ∞ fun p => R p * ζ p := hR.smul hζ
  have hvec : ContMDiff I 𝓘(ℝ, V) ∞ fun p => (R p * ζ p) • η p := by
    intro p
    by_cases hp : p ∈ tsupport ζ
    · exact ContMDiffAt.smul (hmark p) ((hη).contMDiffAt (hU.mem_nhds (hsupp hp)))
    · have hev : (fun q => (R q * ζ q) • η q) =ᶠ[𝓝 p] fun _ => (0 : V) := by
        filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hp] with q hq
        rw [image_eq_zero_of_notMem_tsupport hq, mul_zero, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm :
    (V × ℝ) →L[ℝ] WithLp 2 (V × ℝ)).contMDiff.comp (hvec.prodMk_space hmark)

/-- The closed support of one block lies in the closed support of its cutoff. -/
theorem tsupport_blockSlot_subset_BAUGA (R ζ : M → ℝ) (η : M → V) :
    tsupport (fun p => WithLp.toLp 2 ((R p * ζ p) • η p, R p * ζ p)) ⊆ tsupport ζ := by
  refine closure_mono fun p hp => ?_
  rw [mem_support] at hp ⊢
  intro h0
  apply hp
  rw [h0, mul_zero, zero_smul]
  rfl

end Slot

section Coordinates

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

omit [CompleteSpace X] [SigmaCompactSpace X] in
open Classical in
/-- The circle chart coordinate `η_j` (normalized at `j`; `0` off the centres). -/
def CircleFamilyOn.coord_BAUGA {β : ℕ → ℝ} {U₁ U₂ : Set X}
    (C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) (j : X) : X → ℝ² :=
  if hj : j ∈ C.centres then
    (let c := C.chart j hj
     letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
     c.coord)
  else 0

omit [CompleteSpace X] [SigmaCompactSpace X] in
/-- The circle chart coordinate is smooth on the physical chart ball `B(j, 200ρ(j))`. -/
theorem CircleFamilyOn.contMDiffOn_coord_BAUGA {β : ℕ → ℝ} {U₁ U₂ : Set X}
    (C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) {j : X} (hj : j ∈ C.centres) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (C.coord_BAUGA j) (ball j (200 * ρ j)) := by
  have hc := C.chart_center j hj
  have hrj := hρ j
  unfold CircleFamilyOn.coord_BAUGA
  rw [dite_eq_left hj]
  let c := C.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  change ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ c.coord (@ball X mX.toPseudoMetricSpace j (200 * ρ j))
  refine c.contMDiffOn_coord.mono fun x hx => ?_
  have hd := @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j x 200 hrj hx
  change (ρ j)⁻¹ * @dist X mX.toDist x c.center < 200
  rw [hc']
  exact hd

/-- The slim coordinate `coord_BCG2` is smooth on the physical ball `B(j, 10⁶Δρ(j))`. -/
theorem SlimCentreOn.contMDiffOn_coord_BAUGA {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ c.coord_BCG2 (ball j (10 ^ 6 * Δ * ρ j)) := by
  have hr := hρ j
  have hsub : ball j (10 ^ 6 * Δ * ρ j) ⊆
      {x | (ρ j)⁻¹ * dist x j ≤ 10 ^ 6 * Δ} := fun x hx =>
    (inv_mul_dist_lt_of_mem_ball_LC87 hr hx).le
  unfold SlimCentreOn.coord_BCG2
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.contMDiffOn_coord.mono (hsub.trans P.closedBall_subset_domain)

end Coordinates

section Transport

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Zero extension through a transported ball.** For a smooth function on `(W°, d_ĝ)` whose
closed support lies in `B_ĝ(j, r)`, where `ι B_ĝ(j, R) = B_g(j, R)` (`r < R`) and `d_g = d_ĝ` on
`B_ĝ(j, R')` (`r ≤ R'`), the zero extension is smooth on `W`. -/
theorem contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) {f : W.pieceInterior ⊤ → V}
    {j : W.pieceInterior ⊤} {r R R' : ℝ} (hr : 0 < r) (hrR : r < R) (hrR' : r ≤ R') :
    letI := inducedMetricSpace ĝ
    Subtype.val '' Metric.ball j R = riemannianBallOf g j.val R →
    (∀ y ∈ Metric.ball j R', ∀ z ∈ Metric.ball j R',
      riemannianEDistOf g y.val z.val = edist y z) →
    tsupport f ⊆ Metric.ball j r →
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, V) ∞ f →
    ContMDiff W.model 𝓘(ℝ, V) ∞ (Subtype.val.extend f 0) := by
  let _ := inducedMetricSpace ĝ
  intro hball hdist hsupp hf
  have hKc : IsClosed (riemannianClosedBallOf g j.val r) :=
    Geometry.Metric.isClosed_riemannianClosedBallOf g j.val r
  have hKsub : riemannianClosedBallOf g j.val r ⊆ (W.pieceInterior ⊤ : Set W.Carrier) := by
    intro y hy
    have hy' : y ∈ riemannianBallOf g j.val R :=
      lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR)).mpr hrR)
    rw [← hball] at hy'
    obtain ⟨x, -, rfl⟩ := hy'
    exact x.2
  have hsupp' : tsupport f ⊆ Subtype.val ⁻¹' riemannianClosedBallOf g j.val r := by
    intro x hx
    have hxr : dist x j < r := hsupp hx
    have hx' : x ∈ Metric.ball j R' := lt_of_lt_of_le hxr hrR'
    have hj' : j ∈ Metric.ball j R' := mem_ball_self (lt_of_lt_of_le hr hrR')
    have hd := hdist j hj' x hx'
    change riemannianEDistOf g j.val x.val ≤ ENNReal.ofReal r
    rw [hd, edist_dist, dist_comm]
    exact ENNReal.ofReal_le_ofReal hxr.le
  exact Manifold.contMDiff_extend_zero_pieceInterior_BAUGA W hKc.isCompact
    (W.pieceInterior ⊤).isOpen hKsub subset_rfl hsupp' hf.contMDiffOn

end Transport

end DifferentialGeometry.Geometry.Collapse
