import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketApplications

/-!
# EDP04's original whole-disk / rim coverage from the LFR28 edge disk packet

Lane C14-EDP3. Blueprint `master207B.tex`, EDP04 (`thm:fibration-actual-whole-edge-disk-bundle`,
B:6949–7038): "The initial fiber is exactly the original `{η_i = a, t ≤ 4Δ}` in its radius-`100Δ`
domain, by LFR27. It is LFR28's closed smooth disk." External review 53 §2.3: the original whole
closed-disk fibre, the whole rim and the original disk trivialization's coverage equalities come
from `edgeDisk` (no new disk family); the transport along the adjusted `(g_i, T)` is not here.

The packet (`EdgeDiskPacket`, normalized) records the disk model of the ZERO fibre only, and a
trivialization `Θ'` over every interval `(a₀, b₀) ∋ 0` of `(-4Δ, 4Δ)` with a smooth retraction and
the rim clause R2 (a flow translating `η` and preserving `H` near the rim). From these, with
`H = Δψ(t/Δ)` and `Fib c = {y ∈ B(center, 100Δ) : η y = c, H y ≤ 4Δ}` (subspaces of `M`):

* `EdgeDiskPacket.slab_homeomorph_EDP3`: `Fib 0 × (a₀, b₀)` is homeomorphic to the WHOLE slab
  `{y ∈ B(center, 100Δ) : η y ∈ (a₀, b₀), H y ≤ 4Δ}` by a map with `η ∘ Φ = pr₂`, `Φ(x, 0) = x`, and
  rim onto rim: `H(Φ(x, s)) = 4Δ ↔ H x = 4Δ`.
* `EdgeDiskPacket.fibre_homeomorph_EDP3`: for every `|a| < 4Δ`, `Fib 0 ≃ₜ Fib a` matching the rims.
* `EdgeDiskPacket.fibre_closedCell_EDP3`: every whole fibre `Fib a`, `|a| < 4Δ`, is homeomorphic to
  the closed disk, compact and connected.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_EDP3 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

/-- **The whole slab over `(a₀, b₀)` is the original trivialization's image** (LFR28.1 with R2):
`Fib 0 × (a₀, b₀) ≃ₜ {y ∈ B(center, 100Δ) : η y ∈ (a₀, b₀), H y ≤ 4Δ}`, with `η ∘ Φ = pr₂`,
`Φ(x, 0) = x`, and `H(Φ(x, s)) = 4Δ ↔ H x = 4Δ` (rim onto rim). -/
theorem EdgeDiskPacket.slab_homeomorph_EDP3 (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    (hΔ : 0 < Δ) {a₀ b₀ : ℝ} (ha₀ : -(4 * Δ) < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀)
    (hb₀ : b₀ < 4 * Δ) :
    ∃ Φ : {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
          edgeRowHeight Δ F ρ y ≤ 4 * Δ} × Ioo a₀ b₀ ≃ₜ
        {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y ∈ Ioo a₀ b₀ ∧
          edgeRowHeight Δ F ρ y ≤ 4 * Δ},
      (∀ p, P.coord (Φ p : M) = p.2) ∧ (∀ x, (Φ (x, ⟨0, h0⟩) : M) = x) ∧
      ∀ p, edgeRowHeight Δ F ρ (Φ p : M) = 4 * Δ ↔ edgeRowHeight Δ F ρ (p.1 : M) = 4 * Δ := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  obtain ⟨Θ', hΘs, hΘmem, hΘ0, hΘinj, ⟨r', hr', hrH, U, hU, D, -, hD0, hDadd, hΘD, -, hDH⟩,
    O', -, hO'mem, R, hRs, hRret⟩ := P.trivial a₀ b₀ ha₀ h0 hb₀
  let T := slabFibreHomeomorph P.slabOpen (B := ball P.center (100 * Δ)) (f := P.coord)
    (H := edgeRowHeight Δ F ρ) (c := 4 * Δ)
    (fun y hy => ball_subset_ball (by linarith) (P.slabOpen_subset hy))
    (fun y hy hf hH => P.slab_subset y hy (by rw [hf, abs_zero]; positivity) hH)
  have hsub : ∀ y : P.slabOpen, (y : M) ∈ ball P.center (100 * Δ) := fun y =>
    ball_subset_ball (by linarith) (P.slabOpen_subset y.2)
  have hcoordc : Continuous P.coord := P.lipschitz.continuous
  -- the forward map
  let θ : {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
      edgeRowHeight Δ F ρ y ≤ 4 * Δ} × Ioo a₀ b₀ → P.slabOpen :=
    fun p => Θ' (T.symm p.1, ⟨p.2.1, p.2.2⟩)
  have hθc : Continuous θ := hΘs.continuous.comp
    ((T.symm.continuous.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _))
  have hθcoord : ∀ p, P.coord (θ p : M) = p.2 := fun p => (hΘmem _).1
  have hθH : ∀ p, edgeRowHeight Δ F ρ (θ p : M) ≤ 4 * Δ := fun p => by
    linarith [(hΘmem (T.symm p.1, ⟨p.2.1, p.2.2⟩)).2]
  -- the backward map
  have habs : ∀ y : {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y ∈ Ioo a₀ b₀ ∧
      edgeRowHeight Δ F ρ y ≤ 4 * Δ}, |P.coord y| ≤ 4 * Δ := fun y => by
    rw [abs_le]
    constructor <;> linarith [y.2.2.1.1, y.2.2.1.2]
  let y' : {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y ∈ Ioo a₀ b₀ ∧
      edgeRowHeight Δ F ρ y ≤ 4 * Δ} → P.slabOpen :=
    fun y => ⟨y.1, P.slab_subset y.1 y.2.1 (habs y) y.2.2.2⟩
  have hy'c : Continuous y' := continuous_subtype_val.subtype_mk _
  have hy'H : ∀ y, 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (y' y : M) := fun y => by
    linarith [y.2.2.2]
  have hRmem := fun y => (hRret (y' y) y.2.2.1 (hy'H y)).fst
  have hRc : Continuous fun y => R (y' y) :=
    hRs.continuousOn.comp_continuous hy'c (fun y => hO'mem _ y.2.2.1 (hy'H y))
  refine ⟨{ toFun := fun p => ⟨(θ p : M), hsub (θ p), by rw [hθcoord]; exact p.2.2, hθH p⟩
            invFun := fun y => (T ⟨R (y' y), hRmem y⟩, ⟨P.coord y.1, y.2.2.1⟩)
            left_inv := fun p => ?_
            right_inv := fun y => ?_
            continuous_toFun := (continuous_subtype_val.comp hθc).subtype_mk _
            continuous_invFun := (T.continuous.comp (hRc.subtype_mk _)).prodMk
              ((hcoordc.comp continuous_subtype_val).subtype_mk _) }, fun p => hθcoord p,
    fun x => ?_, fun p => ?_⟩
  · -- left inverse: injectivity of `Θ'`
    have hz := (hRret (θ p) (by rw [hθcoord]; exact p.2.2) (by linarith [hθH p])).snd
    have hinj := hΘinj (hz.trans rfl)
    have h1 : (⟨R (θ p), (hRret (θ p) (by rw [hθcoord]; exact p.2.2)
        (by linarith [hθH p])).fst⟩ : {y : P.slabOpen // P.coord y = 0 ∧
          0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y}) = T.symm p.1 := congrArg Prod.fst hinj
    have h2 := congrArg (fun q => (q.2 : ℝ)) hinj
    refine Prod.ext ?_ (Subtype.ext h2)
    change T ⟨R (θ p), _⟩ = p.1
    rw [h1, Homeomorph.apply_symm_apply]
  · -- right inverse: the retraction
    apply Subtype.ext
    have hz := (hRret (y' y) y.2.2.1 (hy'H y)).snd
    change ((Θ' (T.symm (T ⟨R (y' y), hRmem y⟩), ⟨P.coord y.1, y.2.2.1⟩) : P.slabOpen) : M) = y.1
    rw [Homeomorph.symm_apply_apply, hz]
  · -- `Φ(x, 0) = x`
    change ((Θ' (T.symm x, ⟨0, h0⟩) : P.slabOpen) : M) = x
    rw [hΘ0]
    rfl
  · -- rim onto rim (R2)
    change edgeRowHeight Δ F ρ (θ p : M) = 4 * Δ ↔ edgeRowHeight Δ F ρ (p.1 : M) = 4 * Δ
    have hp1 : edgeRowHeight Δ F ρ ((T.symm p.1 : P.slabOpen) : M) =
        edgeRowHeight Δ F ρ (p.1 : M) := rfl
    constructor
    · intro h
      obtain ⟨hp, he⟩ := hΘD (T.symm p.1, ⟨p.2.1, p.2.2⟩)
      set z := D (p.2 : ℝ) ⟨(T.symm p.1 : P.slabOpen), hp⟩ with hzdef
      have hz : ((z : P.slabOpen) : M) = (θ p : M) := by
        change ((z : P.slabOpen) : M) = ((Θ' (T.symm p.1, ⟨p.2.1, p.2.2⟩) : P.slabOpen) : M)
        rw [he]
      have hzH : edgeRowHeight Δ F ρ ((z : P.slabOpen) : M) = 4 * Δ := by rw [hz, h]
      have hback : D (-(p.2 : ℝ)) z = ⟨(T.symm p.1 : P.slabOpen), hp⟩ := by
        have h2 := DFunLike.congr_fun (hDadd (p.2 : ℝ) (-(p.2 : ℝ)))
          (⟨(T.symm p.1 : P.slabOpen), hp⟩ : (⟨U, hU⟩ : TopologicalSpace.Opens P.slabOpen))
        simp only [Diffeomorph.coe_trans, Function.comp_apply, add_neg_cancel, hD0,
          Diffeomorph.coe_refl, id_eq] at h2
        rw [hzdef, h2]
      have hHD := hDH z (-(p.2 : ℝ)) (by rw [hzH, sub_self, abs_zero]; exact hr')
      rw [hback, hzH] at hHD
      rw [← hp1]
      exact hHD
    · intro h
      have hH := hrH (T.symm p.1, ⟨p.2.1, p.2.2⟩) (by rw [hp1, h, sub_self]; exact hr')
      change edgeRowHeight Δ F ρ ((Θ' (T.symm p.1, ⟨p.2.1, p.2.2⟩) : P.slabOpen) : M) = 4 * Δ
      rw [hH, hp1, h]

/-- **Every whole fibre is the zero fibre transported** (EDP04's initial fibre): for `|a| < 4Δ`,
`Fib 0 ≃ₜ Fib a` with the rims matched (`H = 4Δ`). -/
theorem EdgeDiskPacket.fibre_homeomorph_EDP3 (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    (hΔ : 0 < Δ) {a : ℝ} (ha : |a| < 4 * Δ) :
    ∃ φ : {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
          edgeRowHeight Δ F ρ y ≤ 4 * Δ} ≃ₜ
        {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = a ∧ edgeRowHeight Δ F ρ y ≤ 4 * Δ},
      ∀ x, edgeRowHeight Δ F ρ (φ x : M) = 4 * Δ ↔ edgeRowHeight Δ F ρ (x : M) = 4 * Δ := by
  have hab := abs_nonneg a
  have h0 : (0 : ℝ) ∈ Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2) :=
    ⟨by linarith, by linarith⟩
  have haI : a ∈ Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2) :=
    ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
  obtain ⟨Φ, hcoord, -, hrim⟩ := P.slab_homeomorph_EDP3 hΔ (by linarith) h0 (by linarith)
  refine ⟨{ toFun := fun x => ⟨(Φ (x, ⟨a, haI⟩) : M), (Φ (x, ⟨a, haI⟩)).2.1, hcoord _,
              (Φ (x, ⟨a, haI⟩)).2.2.2⟩
            invFun := fun y => (Φ.symm ⟨y.1, y.2.1, by rw [y.2.2.1]; exact haI, y.2.2.2⟩).1
            left_inv := fun x => by simp
            right_inv := fun y => ?_
            continuous_toFun := ((continuous_subtype_val.comp Φ.continuous).comp
              (continuous_id.prodMk continuous_const)).subtype_mk _
            continuous_invFun := continuous_fst.comp
              (Φ.symm.continuous.comp (continuous_subtype_val.subtype_mk _)) },
    fun x => hrim _⟩
  apply Subtype.ext
  set q := Φ.symm ⟨y.1, y.2.1, by rw [y.2.2.1]; exact haI, y.2.2.2⟩ with hq
  have hq2 : (q.2 : ℝ) = a := by
    have h := hcoord q
    rw [hq, Homeomorph.apply_symm_apply] at h
    rw [← h]
    exact y.2.2.1
  have he : (q.1, (⟨a, haI⟩ : Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2))) = q :=
    Prod.ext rfl (Subtype.ext hq2.symm)
  change (Φ (q.1, ⟨a, haI⟩) : M) = y.1
  rw [he, hq, Homeomorph.apply_symm_apply]

/-- **Every whole fibre is a closed disk** (LFR28's disk at every `|a| < 4Δ`): `Fib a` is
homeomorphic to `ClosedCell 2`, compact and connected. -/
theorem EdgeDiskPacket.fibre_closedCell_EDP3 (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    (hΔ : 0 < Δ) {a : ℝ} (ha : |a| < 4 * Δ) :
    Nonempty ({y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = a ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = a ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ∧
      ConnectedSpace {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = a ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} := by
  obtain ⟨φ, -⟩ := P.fibre_homeomorph_EDP3 hΔ ha
  obtain ⟨⟨ψ⟩, hc, hconn⟩ := P.fibre_homeomorph_closedCell hΔ
  exact ⟨⟨φ.symm.trans ψ⟩, φ.compactSpace, φ.connectedSpace_iff.mp hconn⟩

end DifferentialGeometry.Geometry.Collapse
