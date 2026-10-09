import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedSupplyRows
import DifferentialGeometry.Geometry.Metric.Cfs15BoundaryConstantsBLOC

/-!
# BCG05 on the boundary chain, part 1: the marker contributor halves (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG05 (B:9202, "exact boundary marker at every contributing plane");
frozen target E3 of `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` with
the
register clause `0 ≤ Λ`, `1 ≤ Δ`, `1000000 * Δ * Λ < 1 / 100000` and `θ < 1 / 100` (approved by the
lead 2026-10-05). Contributor halves taken over from BAUG-C's G3; review 69 D69-8: EVERY actual
contributing centre of the window and its plane are checked, not only the input point.

* `window_dist_le_BGR` (BCG05.a: a window contributor is within `ℓ_x/100`), `model_error_lt_BGR`
  ((BA) in model form), `Cfs15StageOutput.stage_marker_generic_BGR` (one active blend keeps a scalar
  marker, abstractly; the scale functional only Lipschitz on the cloud, ready for slot v2's (MCb)).
* `BoundaryInteriorSlots_BIF.augmentedBoundaryCoord_stageProj_BGR`,
`orthogonal_stageQ_le_ker_marker_BGR`.
* On a stage table: `pre_band_BGR` (marker division: `31 < η_b(pre y) < 79`),
  `plane_le_ker_marker_of_listed_BGR` (the (BM) marker is locally constant `1/R_a`),
  **`contributor_boundary_marker_BGR`** (`v_b y = 1`, `L_y ≤ ker v_b`; `b ∈ J_∂(ref y)`, `R_a <
  2r_∂`,
  (BA) puts the model height in `(30, 80)`); on the three stored tables
  `BoundaryAugmentedData.contributor_boundary_marker_BGR` (BAUG-C's (BA) value lemmas).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2
/-- The window arithmetic of BCG05.a: `d ≤ 80aℓ_y + 8aℓ_x`, `ℓ_y ≤ ℓ_x + d`, `0 ≤ a ≤ 10⁻⁴` give
`d ≤ ℓ_x/100`. -/
theorem window_dist_le_BGR {d ly lx a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 10000) (hlx : 0 ≤ lx)
    (hd : d ≤ 80 * a * ly + 8 * a * lx) (hl : ly ≤ lx + d) : d ≤ lx / 100 := by
  have h1 : d ≤ 80 * a * (lx + d) + 8 * a * lx := by
    have : 80 * a * ly ≤ 80 * a * (lx + d) := by
      have h80 : 0 ≤ 80 * a := by positivity
      exact mul_le_mul_of_nonneg_left hl h80
    linarith
  have h2 : d * (1 - 80 * a) ≤ 88 * a * lx := by linarith
  have h3 : 88 * a * lx ≤ 88 / 10000 * lx := by
    have : 88 * a ≤ 88 / 10000 := by linarith
    exact mul_le_mul_of_nonneg_right this hlx
  have h4 : 992 / 1000 ≤ 1 - 80 * a := by linarith
  by_cases hd0 : d ≤ 0
  · have : 0 ≤ lx / 100 := by positivity
    linarith
  · have hd0 : 0 < d := lt_of_not_ge hd0
    have h5 : d * (992 / 1000) ≤ d * (1 - 80 * a) := mul_le_mul_of_nonneg_left h4 hd0.le
    linarith

/-- (BA) in model form: `|(η_q − η_a)/R − (r_q − r_a)| < θ` gives `|η_a + R(r_q − r_a) − η_q| < Rθ`.
-/
theorem model_error_lt_BGR {ηq ηa R rq ra θ : ℝ} (hR : 0 < R)
    (h : |(ηq - ηa) / R - (rq - ra)| < θ) : |ηa + R * (rq - ra) - ηq| < R * θ := by
  have h1 : ηa + R * (rq - ra) - ηq = -(R * ((ηq - ηa) / R - (rq - ra))) := by
    field_simp
    ring
  rw [h1, abs_neg, abs_mul, abs_of_pos hR]
  exact mul_lt_mul_of_pos_left h hR

section Value

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **One active blend step keeps a scalar marker** (BCG05 at one stage, abstractly): the radius
`r = σℓ` on the cloud, an anchor `u` with `ℓ(πu) = l` whose projection is in the cloud when
`z ∈ tsupport ψ`, `‖z − u‖ < σl`; if every cloud point within `l/100` of `πu` has `v y = 1` and
`P y ≤ ker v`, `Qᗮ ≤ ker v` and `v z = 1`, then `v(Ψz) = 1`. -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.stage_marker_generic_BGR
    (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (pr : H →L[ℝ] H) (hπ : ∀ v, Q.starProjection v = pr v) (ψ : H → ℝ) (v : H →L[ℝ] ℝ)
    (hQv : Qᗮ ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) (ℓ : H → ℝ)
    (hℓ : ∀ x ∈ S, ∀ y ∈ S, |ℓ y - ℓ x| ≤ dist y x) (hℓS : ∀ y ∈ S, 0 ≤ ℓ y) {σ : ℝ}
    (hσε : σ ≤ ε / 10000) (hr : ∀ y ∈ S, r y = σ * ℓ y) (u z : H) {l : ℝ}
    (hℓu : ℓ (pr u) = l) (hloc : z ∈ tsupport ψ → pr u ∈ S) (hz : ‖z - u‖ < σ * l)
    (hcontrib : ∀ y ∈ S, dist y (pr u) ≤ l / 100 →
      v y = 1 ∧ P y ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ))
    (hz1 : v z = 1) :
    v (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = 1 := by
  have hε := O.eps_pos
  have hσl : 0 < σ * l := lt_of_le_of_lt (norm_nonneg _) hz
  refine O.adjustment_level_BLOC Q v hQv ψ (x := pr u) hz1 fun hz0 => ?_
  have hx := hloc hz0
  have hrx : r (pr u) = σ * l := by rw [hr _ hx, hℓu]
  have hdist : dist (Q.starProjection z) (pr u) ≤ ‖z - u‖ := by
    rw [dist_eq_norm, ← hπ u, ← map_sub]
    exact Submodule.norm_starProjection_apply_le _ _
  have hw : Q.starProjection z ∈ ball (pr u) (r (pr u)) := by
    rw [mem_ball, hrx]
    exact lt_of_le_of_lt hdist hz
  refine ⟨hx, hw, fun y hyI hwin => ?_⟩
  have hy : y ∈ S := O.I_subset hyI
  obtain ⟨w, hw1, hw2⟩ := hwin
  have hdyx : dist y (pr u) ≤ 80 * (ε⁻¹ * σ) * ℓ y + 8 * (ε⁻¹ * σ) * l := by
    have h1 : dist w y ≤ 80 * ε⁻¹ * r y := mem_closedBall.mp hw1
    have h2 : dist w (pr u) < 8 * ε⁻¹ * r (pr u) := mem_ball.mp hw2
    rw [hr y hy] at h1
    rw [hrx] at h2
    have h3 := dist_triangle_left y (pr u) w
    have e1 : 80 * ε⁻¹ * (σ * ℓ y) = 80 * (ε⁻¹ * σ) * ℓ y := by ring
    have e2 : 8 * ε⁻¹ * (σ * l) = 8 * (ε⁻¹ * σ) * l := by ring
    linarith
  have hlip : ℓ y ≤ l + dist y (pr u) := by
    have h1 : |ℓ y - l| ≤ dist y (pr u) := by
      rw [← hℓu]
      exact hℓ _ hx y hy
    linarith [(abs_le.mp h1).2]
  have hl0 : 0 ≤ l := hℓu ▸ hℓS _ hx
  have hσ : 0 < σ := by
    by_contra h
    have : σ * l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hl0
    linarith
  have ha0 : 0 ≤ ε⁻¹ * σ := by positivity
  have ha : ε⁻¹ * σ ≤ 1 / 10000 := by
    rw [inv_mul_le_iff₀ hε]
    linarith
  exact hcontrib y hy (window_dist_le_BGR ha0 ha hl0 hdyx hlip)

end Value

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryInteriorSlots_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S)

/-- `J_b ∘ π_j = J_b` in the coordinates `(u_b, v_b)`. -/
theorem augmentedBoundaryCoord_stageProj_BGR (st : Fin 3)
    (v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (i : Fin S.packet.cusp.count) :
    augmentedBoundaryCoord_BC7C i (Φ.stageProj st v) = augmentedBoundaryCoord_BC7C i v := by
  simp only [augmentedBoundaryCoord_BC7C, Φ.stageProj_inr_BGR st v i]

/-- `(Q_j^∂)ᗮ ≤ ker v_b`. -/
theorem orthogonal_stageQ_le_ker_marker_BGR (st : Fin 3) (i : Fin S.packet.cusp.count) :
    (Φ.stageQ st)ᗮ ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := fun w hw => by
  have h := slot_eq_zero_of_mem_orthogonal_BC7C
    (Submodule.orthogonal_le (Φ.boundarySubmodule_le_stageQ_BGR st) hw) i
  change (w (Sum.inr i)).snd = 0
  rw [h]
  rfl

end BoundaryInteriorSlots_BIF

namespace BoundaryStageReferences_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}
  (R : BoundaryStageReferences_BIF Φ st E eta row) {Γ sg eg : ℝ}

/-- **BCG05.a, marker division** at a cloud point `y` within `r_∂/100` of `x = π_j F_∂ p`,
`p ∈ Safe_b`: the model preimage `q = pre y` is in the collar band with `31 < η_b(q) < 79`, where
the
marker profile is `1`. -/
theorem pre_band_BGR
    {rd : ℝ} (hrd4 : rd < 1 / 10000) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap p)) < rd / 100) :
    (R.planes.pre ⟨y, hy⟩).val ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i ∧
      31 < S.packet.height i (R.planes.pre ⟨y, hy⟩).val ∧
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val < 79 ∧
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) = 1 := by
  have hpre := R.pre_spec ⟨y, hy⟩
  -- the coordinates of `y` are the actual block of `q = pre y`
  have hcy : S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val =
      augmentedBoundaryCoord_BC7C i y := by
    have h := congrArg (augmentedBoundaryCoord_BC7C i) hpre.1
    rwa [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
      at h
  have hcx : augmentedBoundaryCoord_BC7C i (Φ.stageProj st (S.boundaryOriginalMap p)) =
      (S.packet.height i p, 1) := by
    rw [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
    exact S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp
  have hd1 := abs_augmentedBoundaryCoord_fst_sub_le_BGR y
    (Φ.stageProj st (S.boundaryOriginalMap p)) i
  have hd2 := abs_augmentedBoundaryCoord_snd_sub_le_BGR y
    (Φ.stageProj st (S.boundaryOriginalMap p)) i
  rw [← dist_eq_norm, ← hcy, hcx] at hd1 hd2
  have hu : |(S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).1 -
      S.packet.height i p| < rd / 100 := lt_of_le_of_lt hd1 hyx
  have hv : |(S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).2 - 1| <
      rd / 100 := lt_of_le_of_lt hd2 hyx
  have hvpos : 0 < (S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).2 := by
    have := (abs_lt.mp hv).1
    linarith
  -- `q` is in the collar band
  have hband : (R.planes.pre ⟨y, hy⟩).val ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i := by
    by_contra hnot
    have h0 := S.packet.toBoundaryCollarPacket.block_eq_zero_of_notMem_collarBand_BAUGA i hnot
    rw [h0] at hvpos
    exact lt_irrefl _ hvpos
  have hblk := S.packet.toBoundaryCollarPacket.block_eq_of_mem_collarBand_BAUGA i hband
  rw [hblk, boundaryBlock_fst] at hu
  rw [hblk, boundaryBlock_snd] at hv hvpos
  -- marker division
  have hη0 : 0 ≤ S.packet.height i p := by linarith [hp.2.1]
  have hr1 : rd / 100 < 1 := by linarith
  have hdivr := marker_division_BLOC hu hv hη0 hp.2.2 hr1
  have hq : S.packet.height i (R.planes.pre ⟨y, hy⟩).val *
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) /
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) =
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val := mul_div_cancel_right₀ _ hvpos.ne'
  rw [hq] at hdivr
  have hshift := height_shift_lt_BLOC (r := rd / 100) (by linarith)
  have hηq := height_band_BLOC hp.2.1 hp.2.2 (hdivr.trans hshift)
  have hχ : boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) = 1 :=
    boundaryProfile_eq_one ⟨by linarith [hηq.1], by linarith [hηq.2]⟩
  exact ⟨hband, hηq.1, hηq.2, hχ⟩

/-- **The plane of a listed contributor lies in `ker v_b`** when the model height of `q = pre y`
is in `(30, 80)` (the (BM) marker is locally constant `1/R_a` there; the pruning keeps the slot). -/
theorem plane_le_ker_marker_of_listed_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    {i : Fin S.packet.cusp.count}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hi : i ∈ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩))
    (hh : 30 < boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) ∧
      boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) < 80) :
    R.planes.plane y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  have ha := R.ref_mem ⟨y, hy⟩
  have hpl : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune R.planes.coord
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) := R.planes.plane_of_mem hy
  have hcoord := R.coord_eq _ ha
  have hcont : ContinuousAt (boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
      (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩)))
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) :=
    (hasFDerivAt_boundaryModelHeight_BCG8b _ _ _ _ _).continuousAt
  have hev := hcont.eventually (boundaryProfile_eventuallyEq_one ⟨hh.1, hh.2⟩)
  have hval : ∀ u, ((⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i)).snd =
      (S.rho (R.planes.ref ⟨y, hy⟩))⁻¹ * boundaryProfile (boundaryModelHeight_BCG8b
        (S.packet.height i (R.planes.ref ⟨y, hy⟩)) (S.rho (R.planes.ref ⟨y, hy⟩))
        (row (R.planes.ref ⟨y, hy⟩) i) (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩)) u) :=
    fun u => by
      have h1 := (hR.prune_slot (R.planes.ref ⟨y, hy⟩) (R.planes.model (R.planes.ref ⟨y, hy⟩) u)
        i).trans (R.model_listed _ ha i hi u)
      have h2 := congrArg (fun v : WithLp 2 (ℝ² × ℝ) => v.snd) h1
      refine h2.trans ?_
      simp only [planeBlockEmbed_snd_BAUGA, boundaryModel_BCG8b, Prod.smul_snd, boundaryBlock_snd,
        smul_eq_mul]
  have hloc0 : ∀ᶠ u in 𝓝 (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)),
      ((⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
        R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i)).snd =
        (S.rho (R.planes.ref ⟨y, hy⟩))⁻¹ :=
    hev.mono fun u hu => by rw [hval u, hu, mul_one]
  have hc := congrFun hcoord (R.planes.pre ⟨y, hy⟩)
  have hpl2 : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune eta
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) := by
    rw [hpl]
    simp only [stagePlane_PLN, hc]
  rw [hpl2]
  by_cases hd : DifferentiableAt ℝ (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩))
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩))
  · exact stagePlane_le_ker_marker_PLN
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      R.planes.model R.planes.prune eta _ _ (Sum.inr i) hd hloc0
  · have h0 := fderiv_zero_of_not_differentiableAt hd
    intro v hv
    obtain ⟨u, hu⟩ := hv
    subst hu
    simp only [ContinuousLinearMap.coe_coe, h0, zero_apply, Submodule.zero_mem]


/-- **BCG05's contributor half** at one cloud point `y` of a stage table (blueprint B:9218–9288):
if `y` is within `r_∂/100` of `x = π_j F_∂ p`, `p ∈ Safe_b`, then (marker division) the model
preimage `q = pre y` has `31 < η_b(q) < 79`, so `v_b(y) = 1`; `b` is in the whole list of
`a = ref y` (`q ∈ D_a`), `R_a < 2r_∂`, (BA) puts the model height `h_b(η_a q)` in `(30, 80)`, the
model marker is locally constant `1/R_a` there and `L_y ≤ ker v_b`. -/
theorem contributor_boundary_marker_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    (hBA : letI := inducedMetricSpace S.completion.metric
      ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a, ∀ y : W.pieceInterior ⊤,
        dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a - row a i (eta a y - eta a a)| < θ)
    (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap p)) < rd / 100) :
    S.boundaryMarkerCLM_BAUGC i y = 1 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  let _ := inducedMetricSpace S.completion.metric
  have hpre := R.pre_spec ⟨y, hy⟩
  have ha := R.ref_mem ⟨y, hy⟩
  obtain ⟨hband, hη1, hη2, hχ⟩ := R.pre_band_BGR hrd4 hp hy hyx
  have hηq : 31 < S.packet.height i (R.planes.pre ⟨y, hy⟩).val ∧
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val < 79 := ⟨hη1, hη2⟩
  have hblk := S.packet.toBoundaryCollarPacket.block_eq_of_mem_collarBand_BAUGA i hband
  have hcy : S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val =
      augmentedBoundaryCoord_BC7C i y := by
    have h := congrArg (augmentedBoundaryCoord_BC7C i) hpre.1
    rwa [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
      at h
  refine ⟨?_, ?_⟩
  · change (augmentedBoundaryCoord_BC7C i y).2 = 1
    rw [← hcy, hblk, boundaryBlock_snd, hχ]
  -- `i` is listed at `a = ref y`
  have hsupp : (R.planes.pre ⟨y, hy⟩).val ∈ tsupport (S.packet.toBoundaryCollarPacket.block i) := by
    refine subset_tsupport _ (Function.mem_support.mpr fun h0 => ?_)
    have := congrArg Prod.snd h0
    rw [hblk, boundaryBlock_snd, hχ] at this
    exact one_ne_zero this
  have hCpos : 0 < stageDomain_BIF Δ st * S.rho (R.planes.ref ⟨y, hy⟩) :=
    lt_of_le_of_lt dist_nonneg hpre.2
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g (R.planes.ref ⟨y, hy⟩).val x <
        ENNReal.ofReal (stageDomain_BIF Δ st * S.rho (R.planes.ref ⟨y, hy⟩)) := by
    refine ⟨_, hsupp, ?_⟩
    have h1 := riemannianEDistOf_val_le_completion_BDRY1 W g S.completion.metric
      S.completion.inner_le (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)
    rw [inducedMetricSpace_hmetric S.completion.metric, dist_comm] at h1
    exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff hCpos).mpr hpre.2)
  have hi : i ∈ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mpr hmeet
  have hRa := S.toBoundarySupplyCore.rho_lt_two_of_meets_BGR hrd hprem hΛ hΛC hmeet
  have hRpos := S.rho_pos (R.planes.ref ⟨y, hy⟩).val
  -- (BA) at `q`: the model height is within `R_aθ` of `η_b(q)`
  have hba := hBA _ ha i hi _ hpre.2
  have hθ0 : 0 < θ := lt_of_le_of_lt (abs_nonneg _) hba
  have hmodel : |boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) -
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val| <
      S.rho (R.planes.ref ⟨y, hy⟩) * θ := by
    simp only [boundaryModelHeight_BCG8b, map_sub]
    simp only [map_sub] at hba
    exact model_error_lt_BGR hRpos hba
  have hRθ : S.rho (R.planes.ref ⟨y, hy⟩) * θ ≤ 1 := by
    have : S.rho (R.planes.ref ⟨y, hy⟩) * θ ≤ 2 * rd * (1 / 100) :=
      mul_le_mul hRa.le hθ.le hθ0.le (by positivity)
    linarith
  have hh := model_height_band_BLOC hηq.1 hηq.2 hmodel hRθ
  exact R.plane_le_ker_marker_of_listed_BGR hR hy hi hh

end BoundaryStageReferences_BIF

namespace BoundaryAugmentedData

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} (D : BoundaryAugmentedData S Φ)
  {Γc Γe Γs ec ee es : ℝ} {Sg : Fin 3 → ℝ}

/-- **BCG05's contributor half on the three stored tables** (the rows are `S.ba_spec`'s, BAUG-C's
(BA) value lemmas): a cloud point within `r_∂/100` of `π_j F_∂ p`, `p ∈ Safe_b`, has `v_b = 1` and
`L_y ≤ ker v_b`. -/
theorem contributor_boundary_marker_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) (hθ : θ < 1 / 100) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    {i : Fin S.packet.cusp.count} {p : W.Carrier}
    (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap p)) < rd / 100) :
    S.boundaryMarkerCLM_BAUGC i y = 1 ∧
      D.stagePlane st y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  have hΛC := lambda_mul_stageDomain_le_BGR hΛ hΔ hΛΔ st
  fin_cases st
  · exact D.circle.contributor_boundary_marker_BGR hc
      (fun _ ha _ hi y hy => S.circleRow_BIF_value_BAUGC ha hi y hy) hθ hrd hrd4 hprem hΛ hΛC hp
      hy hyx
  · exact D.edge.contributor_boundary_marker_BGR he
      (fun _ ha _ hi y hy => (S.edgeRow_BIF_value_deriv_BAUGC ha hi).1 y hy) hθ hrd hrd4 hprem hΛ
      hΛC hp hy hyx
  · exact D.slim.contributor_boundary_marker_BGR hs
      (fun _ ha _ hi y hy => (S.slimRow_BIF_value_deriv_BAUGC ha hi).1 y hy) hθ hrd hrd4 hprem hΛ
      hΛC hp hy hyx

end BoundaryAugmentedData

end DifferentialGeometry.Geometry.Collapse
