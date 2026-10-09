import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEExits
import DifferentialGeometry.Analysis.Calculus.AdjustmentStepPointwise
import DifferentialGeometry.Geometry.Fibration.ActualStageNearest

/-!
# BCG03: A3c — the derivative errors of the enhanced boundary chain (BAUG-Dd)

Target A3c `stage_derivative_lt_BAUGD` of `TargetsBoundary-A-v3.1.lean.txt` (review 69 D69-5: `bder`
really bounds `‖DF_∂‖`, `C.deriv_bound`; the normal error is the V3 field `normal` at `eg`): for
`C : BoundaryGaf02ChainE DP …`, `‖(Dg_{k+1} − DF_∂)v‖ ≤ H_k |v|_g` with `H_k < c_k`, on all of `W`,
original metric. Route = CFS20's pointwise derivative step `adjustmentMap_step_deriv_GAF3` with the
comparison operator `π_{L_x}` at the current input:

* `BoundaryStageSlot_BIF.map_deriv_BAUGD` (`‖D a_j − π_{L_x}‖ ≤ Ξ` on `B(x, r_x)`),
  `BoundaryAugmentedDataPV3.normal_BAUGD` (the V3 field `normal` per stage);
* `deriv_step_core_BAUGD` (the step at an interior stage-core point) and `deriv_step_BAUGD` (on
  all of `W`; identity off `tsupport ψ_st`);
* `BoundaryGaf02ChainE.stage_derivative_lt_BAUGD` (A3c).
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryStageSlot_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {st : Fin 3} {Kj : ℕ} {Ξ sg cw : ℝ}

/-- The slot's smoothing map has derivative within `Ξ` of `π_{L_x}` on every `B(x, r_x)`. -/
theorem map_deriv_BAUGD (σ : BoundaryStageSlot_BIF D st Kj Ξ sg cw) {x : _}
    (hx : x ∈ Φ.stageCloud st) {z : _} (hz : z ∈ ball x (D.stageRadius st sg x)) :
    ‖fderiv ℝ σ.map z - (D.stagePlane st x).starProjection‖ ≤ Ξ := by
  cases σ with
  | active O => exact (O.ambient_value_deriv hx hz).2.2
  | inactive hc he =>
    rw [(stageCloud_eq_empty_of_inactive hc he).1] at hx
    exact absurd hx (Set.notMem_empty x)

end BoundaryStageSlot_BIF

namespace BoundaryAugmentedDataPV3

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}

/-- The V3 field `normal` at every stage, on the stage planes of the data. -/
theorem normal_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
      ∀ v : TangentSpace W.model q.val,
        ‖(DP.stagePlane st x)ᗮ.starProjection (Φ.stageProj st
            (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
          eg st * Real.sqrt (g.inner q.val v v) := by
  fin_cases st
  · exact DP.circle_spec.normal
  · exact DP.edge_spec.normal
  · exact DP.slim_spec.normal

/-- `L_x ≤ Q_j` at every stage-cloud point (the V3 field `dimension`). -/
theorem plane_le_stageQ_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    ∀ x ∈ Φ.stageCloud st, DP.stagePlane st x ≤ Φ.stageQ st := by
  fin_cases st
  · exact fun x hx => (DP.circle_spec.dimension x hx).2
  · exact fun x hx => (DP.edge_spec.dimension x hx).2
  · exact fun x hx => (DP.slim_spec.dimension x hx).2

end BoundaryAugmentedDataPV3

/-- `‖id − π_L‖ ≤ 1` and `‖(id − π_L) u‖ ≤ ‖u‖` for a finite-dimensional `L`. -/
theorem norm_id_sub_starProjection_le_BAUGD {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (L : Submodule ℝ H) [L.HasOrthogonalProjection] :
    ‖ContinuousLinearMap.id ℝ H - L.starProjection‖ ≤ 1 := by
  have h : ContinuousLinearMap.id ℝ H - L.starProjection = Lᗮ.starProjection := by
    rw [L.id_eq_sum_starProjection_self_orthogonalComplement, add_sub_cancel_left]
  rw [h]
  exact Lᗮ.starProjection_norm_le

/-- **The abstract stage step** (CFS20 at a current input in the tube; fast to elaborate): for a
smoothing map `a` with `‖a w − (x + π_L(w − x))‖ ≤ Ξr` and `‖Da w − π_L‖ ≤ Ξ` at `w = π_Q y`
(`L ≤ Q`), `‖π_Q y − x‖ ≤ Eρ`, `Ξr + Eρ ≤ a'ρ`, the cutoff bound `‖Dψ(y)‖ ≤ b/ρ`, the original
derivative `‖DF w‖ ≤ L_c N`, the normal error `‖π_{L⊥}π_Q DF w‖ ≤ νN` and the prior error
`‖Df w − DF w‖ ≤ H₀N`: the adjustment is differentiable at `y` and
`‖DΨ(y)(Df w) − DF w‖ ≤ (a' b (L_c + H₀) + Ξ(L_c + H₀) + ν + 2H₀)N`. -/
theorem adjust_step_deriv_abstract_BAUGD {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Q L : Submodule ℝ H) (hLQ : L ≤ Q) (a : H → H) (ψ : H → ℝ) (y x : H)
    {r Ξ E ρ a' b Lc H₀ N ν : ℝ}
    (hval : ‖a (Q.starProjection y) - (x + L.starProjection (Q.starProjection y - x))‖ ≤ Ξ * r)
    (hda : DifferentiableAt ℝ a (Q.starProjection y))
    (hder : ‖fderiv ℝ a (Q.starProjection y) - L.starProjection‖ ≤ Ξ)
    (hπ : ‖Q.starProjection y - x‖ ≤ E * ρ) (ha' : Ξ * r + E * ρ ≤ a' * ρ)
    (hψd : DifferentiableAt ℝ ψ y) (hψI : ψ y ∈ Icc (0 : ℝ) 1) (hcut : ‖fderiv ℝ ψ y‖ ≤ b / ρ)
    (hb : 0 ≤ b) (hΞ : 0 ≤ Ξ) (hL : 0 ≤ Lc) (hH : 0 ≤ H₀) (hρ : 0 < ρ) (hN : 0 ≤ N)
    (u u₀ : H) (hfirst : ‖u₀‖ ≤ Lc * N)
    (hnormal : ‖Lᗮ.starProjection (Q.starProjection u₀)‖ ≤ ν * N)
    (hprior : ‖u - u₀‖ ≤ H₀ * N) :
    DifferentiableAt ℝ (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ) y ∧
      ‖fderiv ℝ (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ) y u - u₀‖ ≤
        (a' * b * (Lc + H₀) + Ξ * (Lc + H₀) + ν + 2 * H₀) * N := by
  obtain ⟨hPd, hcomp⟩ := norm_fderiv_starProjection_comp_sub_le_GAF3 Q L hda hLQ hder
  have hId : ContinuousLinearMap.id ℝ H - L.starProjection = Lᗮ.starProjection := by
    rw [L.id_eq_sum_starProjection_self_orthogonalComplement, add_sub_cancel_left]
  have hmem : Q.starProjection y ∈ Q := Submodule.starProjection_apply_mem _ _
  have hvalue : ‖(fun z => Q.starProjection (a z)) (Q.starProjection y) - Q.starProjection y‖ ≤
      a' * ρ := by
    have h1 : (fun z => Q.starProjection (a z)) (Q.starProjection y) - Q.starProjection y =
        Q.starProjection (a (Q.starProjection y) - Q.starProjection y) := by
      simp only
      rw [map_sub, Submodule.starProjection_eq_self_iff.mpr hmem]
    rw [h1]
    refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
    have hsplit : a (Q.starProjection y) - Q.starProjection y =
        (a (Q.starProjection y) - (x + L.starProjection (Q.starProjection y - x))) -
          Lᗮ.starProjection (Q.starProjection y - x) := by
      rw [Submodule.starProjection_orthogonal_val]
      abel
    rw [hsplit]
    have h2 : ‖Lᗮ.starProjection (Q.starProjection y - x)‖ ≤ E * ρ :=
      (Submodule.norm_starProjection_apply_le _ _).trans hπ
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ Ξ * r + E * ρ := add_le_add hval h2
      _ ≤ a' * ρ := ha'
  have hA : ‖ContinuousLinearMap.id ℝ H - L.starProjection‖ ≤ 1 := by
    rw [hId]; exact Lᗮ.starProjection_norm_le
  have hDf : (ContinuousLinearMap.id ℝ ℝ).smulRight u (1 : ℝ) = u := by simp
  have hDF : (ContinuousLinearMap.id ℝ ℝ).smulRight u₀ (1 : ℝ) = u₀ := by simp
  have hnormal' : ‖(ContinuousLinearMap.id ℝ H - L.starProjection)
      (Q.starProjection ((ContinuousLinearMap.id ℝ ℝ).smulRight u₀ (1 : ℝ)))‖ ≤ ν * N := by
    rw [hDF, hId]; exact hnormal
  have h := adjustmentMap_step_deriv_GAF3 Q hPd hψd L.starProjection
    ((ContinuousLinearMap.id ℝ ℝ).smulRight u) ((ContinuousLinearMap.id ℝ ℝ).smulRight u₀) 1
    hb hΞ hL hH hρ hN hψI hA hvalue hcut hcomp (by rw [hDF]; exact hfirst) hnormal'
    (by rw [hDf, hDF]; exact hprior)
  rw [hDf, hDF] at h
  exact ⟨(hasFDerivAt_adjustmentMap_GAF3 Q hPd hψd).differentiableAt, h⟩

/-- The stage adjustment of a slot map as an `adjustmentMap` (definitional). -/
theorem adjust_eq_adjustmentMap_BAUGD {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    Φ.adjust st a = adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (a y))
      (Φ.cutoff st) :=
  rfl

section Step

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- The tube facts of the derivative step at an interior stage-core point `q`: `π_st y q` is
within `Eρ(q)` of `x = π_st F_∂(q)` and lies in `B(x, r_x)`; `Ξ r_x + Eρ(q) ≤ a ρ(q)` with
`a = 5/3 ΞΣ + (1 + Ξ)E`. -/
theorem deriv_step_tube_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {Ξs : ℝ} (hΞ : 0 ≤ Ξs) (hsg : 0 < Sg st)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (q : W.pieceInterior ⊤) (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 3 * Sg st / 10)
    (hyv : ‖y - S.boundaryOriginalMap q.val‖ ≤ E * S.rho q.val) :
    ‖((actualSlotsV2_BAUGD S).stageQ st).starProjection y -
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤ E * S.rho q.val ∧
      ((actualSlotsV2_BAUGD S).stageQ st).starProjection y ∈
        ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
          (DP.stageRadius st (Sg st)
            ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))) ∧
      Ξs * DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) +
          E * S.rho q.val ≤ (5 / 3 * Ξs * Sg st + (1 + Ξs) * E) * S.rho q.val := by
  have hr := stageRadius_bounds_V2_BAUGD DP hsg.le hcore
  have hρ := S.rho_pos q.val
  have hπy : ((actualSlotsV2_BAUGD S).stageQ st).starProjection y =
      (actualSlotsV2_BAUGD S).stageProj st y :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) y
  have hwx : ‖((actualSlotsV2_BAUGD S).stageQ st).starProjection y -
      (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤ E * S.rho q.val :=
    (congrArg (fun u => ‖u - (actualSlotsV2_BAUGD S).stageProj st
      (S.boundaryOriginalMap q.val)‖) hπy).trans_le
      ((norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) st _ _).trans hyv)
  have hpos : 0 < Sg st * S.rho q.val := mul_pos hsg hρ
  refine ⟨hwx, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have h3 := mul_le_mul_of_nonneg_right hE hρ.le
    have h4 : 3 * Sg st / 10 * S.rho q.val = 3 / 10 * (Sg st * S.rho q.val) := by ring
    linarith [hr.1]
  · have h5 : Ξs * DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
        Ξs * (5 / 3 * (Sg st * S.rho q.val)) := mul_le_mul_of_nonneg_left hr.2 hΞ
    have h6 : (5 / 3 * Ξs * Sg st + (1 + Ξs) * E) * S.rho q.val =
        Ξs * (5 / 3 * (Sg st * S.rho q.val)) + E * S.rho q.val + Ξs * (E * S.rho q.val) := by
      ring
    have h7 : 0 ≤ Ξs * (E * S.rho q.val) := mul_nonneg hΞ (mul_nonneg hE0 hρ.le)
    linarith

/-- The normal error of the derivative step at an interior stage-core point (V3 `normal`). -/
theorem deriv_step_normal_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} (q : W.pieceInterior ⊤) (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    (v : TangentSpace W.model q.val) :
    ‖(DP.stagePlane st ((actualSlotsV2_BAUGD S).stageProj st
      (S.boundaryOriginalMap q.val)))ᗮ.starProjection
      (((actualSlotsV2_BAUGD S).stageQ st).starProjection
        (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
      eg st * Real.sqrt (g.inner q.val v v) := by
  have e1 : ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (mvfderiv W.model S.boundaryOriginalMap q.val v) =
      (actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val v) :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _
  exact (congrArg (fun u => ‖(DP.stagePlane st ((actualSlotsV2_BAUGD S).stageProj st
    (S.boundaryOriginalMap q.val)))ᗮ.starProjection u‖) e1).trans_le
    (DP.normal_BAUGD st _ ⟨q, hcore, rfl⟩ q rfl v)

/-- **CFS20's derivative step at an interior stage-core point** `q`: with the cutoff bound
`‖Dψ_st(y q)‖ ≤ b/ρ(q)`, `‖DF_∂ w‖ ≤ L|w|_g`, the prior error `‖(Dy − DF_∂)w‖ ≤ H₀|w|_g` and
`‖y q − F_∂ q‖ ≤ Eρ(q)` (`E ≤ 3Σ/10`): `‖(D(Ψ_st ∘ y) − DF_∂)w‖ ≤ (a b (L + H₀) + Ξ(L + H₀) + e_st +
2H₀)|w|_g` with `a = 5/3 ΞΣ + (1 + Ξ)E` (comparison operator `π_{L_x}`, V3 `normal`). -/
theorem deriv_step_core_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {Kj : ℕ} {Ξs cws : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 ≤ Ξs) (hsg : 0 < Sg st)
    (hψI : ∀ z, (actualSlotsV2_BAUGD S).cutoff st z ∈ Icc (0 : ℝ) 1)
    (y : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (q : W.pieceInterior ⊤) (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    (hy : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) y q.val)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 3 * Sg st / 10)
    (hyv : ‖y q.val - S.boundaryOriginalMap q.val‖ ≤ E * S.rho q.val)
    (hψd : DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff st) (y q.val)) {bcut : ℝ}
    (hbcut : 0 ≤ bcut)
    (hcut : ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff st) (y q.val)‖ ≤ bcut / S.rho q.val)
    {L : ℝ} (hL : 0 ≤ L)
    (hfirst : ∀ v : TangentSpace W.model q.val,
      ‖mvfderiv W.model S.boundaryOriginalMap q.val v‖ ≤ L * Real.sqrt (g.inner q.val v v))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hprior : ∀ v : TangentSpace W.model q.val,
      ‖mvfderiv W.model y q.val v - mvfderiv W.model S.boundaryOriginalMap q.val v‖ ≤
        H₀ * Real.sqrt (g.inner q.val v v))
    (v : TangentSpace W.model q.val) :
    ‖mvfderiv W.model ((actualSlotsV2_BAUGD S).adjust st σ.map ∘ y) q.val v -
        mvfderiv W.model S.boundaryOriginalMap q.val v‖ ≤
      ((5 / 3 * Ξs * Sg st + (1 + Ξs) * E) * bcut * (L + H₀) + Ξs * (L + H₀) + eg st +
        2 * H₀) * Real.sqrt (g.inner q.val v v) := by
  have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud st := ⟨q, hcore, rfl⟩
  obtain ⟨hwx, hball, ha'⟩ := deriv_step_tube_BAUGD DP hΞ hsg (y q.val) q hcore hE0 hE hyv
  have hk := adjust_step_deriv_abstract_BAUGD ((actualSlotsV2_BAUGD S).stageQ st)
    (DP.stagePlane st ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)))
    (DP.plane_le_stageQ_BAUGD st _ hx) σ.map ((actualSlotsV2_BAUGD S).cutoff st) (y q.val)
    ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
    (σ.map_value_BAUGD hx hball) ((σ.map_contDiffAt_BAUGD hx hball).differentiableAt (by simp))
    (σ.map_deriv_BAUGD hx hball) hwx ha' hψd (hψI _) hcut hbcut hΞ hL hH₀ (S.rho_pos q.val)
    (Real.sqrt_nonneg _) (mvfderiv W.model y q.val v)
    (mvfderiv W.model S.boundaryOriginalMap q.val v) (hfirst v)
    (deriv_step_normal_BAUGD DP q hcore v) (hprior v)
  have hΨd : DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).adjust st σ.map) (y q.val) := hk.1
  have hc := mvfderiv_comp_apply_of_differentiableAt_GAF3 hy hΨd v
  exact (congrArg (fun u => ‖u - mvfderiv W.model S.boundaryOriginalMap q.val v‖) hc).trans_le hk.2

/-- **The derivative step on all of `W`** (identity off `tsupport ψ_st`; CFS20 at an interior
stage-core point on it). -/
theorem deriv_step_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {Kj : ℕ} {Ξs cws : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 ≤ Ξs) (hsg : 0 < Sg st)
    (hψI : ∀ z, (actualSlotsV2_BAUGD S).cutoff st z ∈ Icc (0 : ℝ) 1)
    (y : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (p : W.Carrier)
    (hy : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) y p)
    (hloc : y p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 3 * Sg st / 10)
    (hyv : ‖y p - S.boundaryOriginalMap p‖ ≤ E * S.rho p)
    (hψd : DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff st) (y p)) {bcut : ℝ}
    (hbcut : 0 ≤ bcut)
    (hcut : ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff st) (y p)‖ ≤ bcut / S.rho p)
    {L : ℝ} (hL : 0 ≤ L)
    (hfirst : ∀ v : TangentSpace W.model p,
      ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ L * Real.sqrt (g.inner p v v))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hprior : ∀ v : TangentSpace W.model p,
      ‖mvfderiv W.model y p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        H₀ * Real.sqrt (g.inner p v v))
    (heg : 0 ≤ eg st) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model ((actualSlotsV2_BAUGD S).adjust st σ.map ∘ y) p v -
        mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      ((5 / 3 * Ξs * Sg st + (1 + Ξs) * E) * bcut * (L + H₀) + Ξs * (L + H₀) + eg st +
        2 * H₀) * Real.sqrt (g.inner p v v) := by
  by_cases hz : y p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st)
  · obtain ⟨q, hq, hcore⟩ := hloc hz
    subst hq
    exact deriv_step_core_BAUGD DP σ hΞ hsg hψI y q hcore hy hE0 hE hyv hψd hbcut hcut hL hfirst
      hH₀ hprior v
  · have hev : (actualSlotsV2_BAUGD S).adjust st σ.map =ᶠ[𝓝 (y p)] id :=
      Filter.eventually_of_mem ((isClosed_tsupport _).isOpen_compl.mem_nhds hz)
        fun z hz' => adjust_eq_of_notMem_BAUGD st _ hz'
    have hΨd : DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).adjust st σ.map) (y p) :=
      differentiableAt_id.congr_of_eventuallyEq hev
    have hf : fderiv ℝ ((actualSlotsV2_BAUGD S).adjust st σ.map) (y p) =
        ContinuousLinearMap.id ℝ _ := by
      rw [hev.fderiv_eq, fderiv_id]
    have hc := mvfderiv_comp_apply_of_differentiableAt_GAF3 hy hΨd v
    have hc2 : fderiv ℝ ((actualSlotsV2_BAUGD S).adjust st σ.map) (y p)
        (mvfderiv W.model y p v) = mvfderiv W.model y p v := by
      rw [hf]; rfl
    have ha : 0 ≤ 5 / 3 * Ξs * Sg st + (1 + Ξs) * E := by positivity
    have hbig : H₀ ≤ (5 / 3 * Ξs * Sg st + (1 + Ξs) * E) * bcut * (L + H₀) + Ξs * (L + H₀) +
        eg st + 2 * H₀ := by
      have h1 := mul_nonneg (mul_nonneg ha hbcut) (add_nonneg hL hH₀)
      have h2 := mul_nonneg hΞ (add_nonneg hL hH₀)
      linarith only [h1, h2, heg, hH₀]
    exact (congrArg (fun u => ‖u - mvfderiv W.model S.boundaryOriginalMap p v‖)
      (hc.trans hc2)).trans_le
      ((hprior v).trans (mul_le_mul_of_nonneg_right hbig (Real.sqrt_nonneg _)))

end Step

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- `(1 − 1)•a + 1•b = b`. -/
theorem segment_one_BAUGD (a b' : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ((1 : ℝ) - 1) • a + (1 : ℝ) • b' = b' := by
  simp

include C in
/-- `ψ₀` at `F_∂ p`: differentiable, `‖Dψ₀‖ ≤ b_cut/ρ`. -/
theorem cutoff_deriv_zero_V2_BAUGD (p : W.Carrier) :
    DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap p) ∧
      ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap p)‖ ≤
        bcut / S.rho p := by
  have hB := C.cutoff_bindings
  exact ⟨(hB.1.1.differentiable (by simp)) _, hB.1.2.2.2.2 p⟩

/-- `ψ₁` at `g₁ p`: differentiable, `‖Dψ₁‖ ≤ b_cut/ρ`. -/
theorem cutoff_deriv_one_V2_BAUGD (p : W.Carrier) :
    DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff 1)
        ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p)) ∧
      ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 1)
        ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p))‖ ≤
        bcut / S.rho p := by
  have hB := C.cutoff_bindings.2.1
  have h := hB.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  have e := segment_one_BAUGD (S.boundaryOriginalMap p)
    ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p))
  have hpos : 0 < S.scaleMarker_BIF
      ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p)) :=
    (congrArg (fun z => 0 < S.scaleMarker_BIF z) e).mp h.1
  have hd : ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 1)
      ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p))‖ ≤
      bcut / S.rho p :=
    (congrArg (fun z => ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 1) z‖ ≤ bcut / S.rho p) e).mp
      h.2
  have hopen : IsOpen {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
      0 < S.scaleMarker_BIF z} :=
    isOpen_lt continuous_const S.scaleMarker_BIF.continuous
  exact ⟨(hB.1.contDiffAt (hopen.mem_nhds hpos)).differentiableAt (by simp), hd⟩

/-- `ψ₂` at `g₂ p`: differentiable, `‖Dψ₂‖ ≤ b_cut/ρ`. -/
theorem cutoff_deriv_two_V2_BAUGD (p : W.Carrier) :
    DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff 2)
        ((actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map
          ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p))) ∧
      ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 2)
        ((actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map
          ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p)))‖ ≤
        bcut / S.rho p := by
  have hB := C.cutoff_bindings.2.2
  have h := hB.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  have e := segment_one_BAUGD (S.boundaryOriginalMap p)
    ((actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map
      ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p)))
  exact ⟨(hB.1.differentiable (by simp)) _,
    (congrArg (fun z => ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 2) z‖ ≤ bcut / S.rho p) e).mp h⟩

/-- The chain's cutoff `ψ_st` at its own input `g_st`: differentiable, `‖Dψ_st‖ ≤ b_cut/ρ`. -/
theorem cutoff_deriv_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    DifferentiableAt ℝ ((actualSlotsV2_BAUGD S).cutoff st) (C.stage st.castSucc p) ∧
      ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff st) (C.stage st.castSucc p)‖ ≤ bcut / S.rho p := by
  fin_cases st
  · exact C.cutoff_deriv_zero_V2_BAUGD p
  · change DifferentiableAt ℝ _ (C.g₁ p) ∧ ‖fderiv ℝ _ (C.g₁ p)‖ ≤ _
    rw [C.g₁_apply_V2_BAUGD]
    exact C.cutoff_deriv_one_V2_BAUGD p
  · change DifferentiableAt ℝ _ (C.g₂ p) ∧ ‖fderiv ℝ _ (C.g₂ p)‖ ≤ _
    rw [C.g₂_apply_V2_BAUGD, C.g₁_apply_V2_BAUGD]
    exact C.cutoff_deriv_two_V2_BAUGD p

end BoundaryGaf02Chain

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- `b_der ≥ 0` (the derivative clause at a nonzero tangent vector of any point). -/
theorem bder_nonneg_BAUGD (p : W.Carrier) : 0 ≤ bder := by
  by_contra h
  have h : bder < 0 := lt_of_not_ge h
  have hv : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : TangentSpace W.model p) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun u : EuclideanSpace ℝ (Fin 3) => u 0) h0
    simp at h1
  have hpos := g.pos p _ hv
  have h2 : 0 < Real.sqrt (g.inner p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := Real.sqrt_pos.mpr hpos
  have h3 := C.deriv_bound p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
  have h4 := mul_neg_of_neg_of_pos h h2
  linarith [norm_nonneg (mvfderiv W.model S.boundaryOriginalMap p
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))]

include C in
/-- `b_cut ≥ 0` (the cutoff clause of `ψ₀` at any point). -/
theorem bcut_nonneg_BAUGD (p : W.Carrier) : 0 ≤ bcut := by
  have h := (norm_nonneg _).trans (C.toChain.cutoff_deriv_zero_V2_BAUGD p).2
  have h2 := mul_nonneg h (S.rho_pos p).le
  rwa [div_mul_cancel₀ _ (S.rho_pos p).ne'] at h2

/-- **One derivative stage on the chain** (generic `st`): with the prior error `H₀` of the input
`g_st`, `‖(Dg_{st+1} − DF_∂)v‖ ≤ (a b_cut (b_der + H₀) + Ξ_st(b_der + H₀) + e_st + 2H₀)|v|_g`,
`a = 5/3 Ξ_stΣ_st + (1 + Ξ_st)E_st`, `E_st = 0, c₀, c₁`. -/
theorem deriv_stage_BAUGD (st : Fin 3) (p : W.Carrier) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hprior : ∀ v : TangentSpace W.model p,
      ‖mvfderiv W.model (C.toChain.stage st.castSucc) p v -
          mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ H₀ * Real.sqrt (g.inner p v v))
    (v : TangentSpace W.model p) :
    ‖mvfderiv W.model (C.toChain.stage st.succ) p v -
        mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      ((5 / 3 * Ξ st * Sg st + (1 + Ξ st) * ![0, c 0, c 1] st) * bcut * (bder + H₀) +
        Ξ st * (bder + H₀) + eg st + 2 * H₀) * Real.sqrt (g.inner p v v) := by
  have hN := C.toChain.numbers
  have hie := C.toChain.input_error_V2_BAUGD st p
  have hE0 : 0 ≤ ![0, c 0, c 1] st := by
    have hc := C.toChain.budgets_V2_BAUGD
    fin_cases st
    · exact le_rfl
    · exact hc.1
    · exact hc.2.2.1
  have hcd := C.toChain.cutoff_deriv_V2_BAUGD st p
  have hk := deriv_step_BAUGD DP (C.toChain.slot st) (hN.1 st).1.le (hN.1 st).2.1
    (C.toChain.cutoff_mem_Icc_V2_BAUGD st) (C.toChain.stage st.castSucc) p
    ((C.stage_smooth_BAUGD st.castSucc).mdifferentiableAt (by simp))
    (C.toChain.loc_V2_BAUGD st p) hE0 hie.2 hie.1 hcd.1 (C.bcut_nonneg_BAUGD p) hcd.2
    (C.bder_nonneg_BAUGD p) (C.deriv_bound p) hH₀ hprior (hN.1 st).2.2.2.1 v
  have hfun : C.toChain.stage st.succ =
      (actualSlotsV2_BAUGD S).adjust st (C.toChain.slot st).map ∘ C.toChain.stage st.castSucc :=
    funext fun q => C.toChain.stage_succ_eq_V2_BAUGD st q
  exact (congrArg (fun f => ‖mvfderiv W.model f p v -
    mvfderiv W.model S.boundaryOriginalMap p v‖) hfun).trans_le hk

/-- A3c at stage one: `‖(Dg₁ − DF_∂)v‖ ≤ (5/3 Ξ₀Σ₀ b_cut b_der + Ξ₀ b_der + e₀)|v|_g`. -/
theorem deriv_lt_zero_BAUGD (p : W.Carrier) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model (C.toChain.stage (Fin.succ 0)) p v -
        mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      (5 / 3 * Ξ 0 * Sg 0 * bcut * bder + Ξ 0 * bder + eg 0) * Real.sqrt (g.inner p v v) := by
  have h := C.deriv_stage_BAUGD 0 p le_rfl (fun v => by
    change ‖mvfderiv W.model S.boundaryOriginalMap p v -
      mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ 0 * Real.sqrt (g.inner p v v)
    simp) v
  refine h.trans (le_of_eq ?_)
  simp only [Matrix.cons_val_zero, mul_zero, add_zero]

/-- A3c at stage two: `‖(Dg₂ − DF_∂)v‖ ≤ H₁|v|_g` with GAF01's `H₁` (prior `c₀`). -/
theorem deriv_lt_one_BAUGD (p : W.Carrier) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model (C.toChain.stage (Fin.succ 1)) p v -
        mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (bder + c 0) + Ξ 1 * (bder + c 0) + eg 1 +
        2 * c 0) * Real.sqrt (g.inner p v v) := by
  have hN := C.toChain.numbers
  have hd0 : 5 / 3 * Ξ 0 * Sg 0 * bcut * bder + Ξ 0 * bder + eg 0 < c 0 := hN.2.2.2.1
  have hc := C.toChain.budgets_V2_BAUGD
  have h := C.deriv_stage_BAUGD 1 p hc.1 (fun v =>
    (C.deriv_lt_zero_BAUGD p v).trans (mul_le_mul_of_nonneg_right hd0.le (Real.sqrt_nonneg _))) v
  refine h.trans (le_of_eq ?_)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]

/-- A3c at stage three: `‖(DE − DF_∂)v‖ ≤ H₂|v|_g` with GAF01's `H₂` (prior `c₁`). -/
theorem deriv_lt_two_BAUGD (p : W.Carrier) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model (C.toChain.stage (Fin.succ 2)) p v -
        mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) + Ξ 2 * (bder + c 1) + eg 2 +
        2 * c 1) * Real.sqrt (g.inner p v v) := by
  have hN := C.toChain.numbers
  have hd1 : (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (bder + c 0) + Ξ 1 * (bder + c 0) +
      eg 1 + 2 * c 0 < c 1 := hN.2.2.2.2.2.2.2.2.1
  have hc := C.toChain.budgets_V2_BAUGD
  have h := C.deriv_stage_BAUGD 2 p hc.2.2.1 (fun v =>
    (C.deriv_lt_one_BAUGD p v).trans (mul_le_mul_of_nonneg_right hd1.le (Real.sqrt_nonneg _))) v
  refine h.trans (le_of_eq ?_)
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **A3c** derivative errors `‖(Dg_{k+1} − DF_∂)v‖ ≤ H_k |v|_g`, `H_k < c_k` (`bder` from
`C.deriv_bound`; the normal error from `DP.*_spec.normal` at `eg`). -/
theorem stage_derivative_lt_BAUGD :
    ∀ k : Fin 3, ∃ Hd : ℝ, Hd < c k ∧ ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model (C.toChain.stage k.succ) p v -
          mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ Hd * Real.sqrt (g.inner p v v) := by
  have hN := C.toChain.numbers
  intro k
  fin_cases k
  · exact ⟨_, hN.2.2.2.1, C.deriv_lt_zero_BAUGD⟩
  · exact ⟨_, hN.2.2.2.2.2.2.2.2.1, C.deriv_lt_one_BAUGD⟩
  · exact ⟨_, hN.2.2.2.2.2.2.2.2.2.2.2.2.2, C.deriv_lt_two_BAUGD⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
