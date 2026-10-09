import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovedRegionBufferBGR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPieces
import DifferentialGeometry.Topology.Manifold.RatioCompatibleDefiner
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankKernel74

/-!
# BCG07 clause 07.b2: `M₁` is a compact smooth manifold with boundary (S-BCG-ROWS3, G37)

`M₁ = W ∖ int(Z ∪ C)` is the superlevel set `{∏ t_i ≥ 0}` of the product of the defining
functions `t_i` of the pairwise disjoint regular faces (the actual zero domains
`Z_k = {F_k ≤ 0}` and the cusp cores `C_b = {G_b − 40 ≤ 0}`): at most one factor is `≤ 0` at a
point, so `∏ t_i ≥ 0` iff no factor is negative iff the point is outside every interior, and at a
zero of the product exactly one factor vanishes and `d(∏ t_i) = (∏_{j ≠ i} t_j) dt_i ≠ 0`. The
tree's regular-sublevel kernel for carriers of both kinds
(`GC.GraphManifold.Assembly.carrierSublevel*`) then gives the manifold-with-boundary structure.

* generic: `interior_sublevel_eq_BGR`, `compl_interior_iUnion_sublevel_BGR`,
  `exists_isManifold_of_sublevel_set_BGR`, **`isManifold_compl_interior_union_BGR`**;
* **`BoundaryGaf02ChainE.M₁_isManifold_BGR`** (07.b2): a `𝓡∂ 3`-structure on `↥M₁` for which
  `M₁` is a compact smooth 3-manifold with boundary, the inclusion into `W` is smooth with
  bijective differential, and its boundary points are exactly the actual zero faces and the cusp
  fronts `H_b` (`M₁ ⊆ {D ≥ 35}`, so no point of `∂W` occurs).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2


section Carrier

variable {W : CompactCarrier.{0}} {ι : Type*}

/-- **The interior of a regular sublevel is the strict sublevel** (Fermat at the interior points
of the level). -/
theorem interior_sublevel_eq_BGR {t : W.Carrier → ℝ} (ht : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ x, t x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) t x ≠ 0)
    (hint : ∀ x, t x = 0 → W.model.IsInteriorPoint x) :
    interior {x | t x ≤ 0} = {x | t x < 0} := by
  refine Subset.antisymm (fun x hx => ?_) (interior_maximal (fun y (hy : t y < 0) => hy.le)
    (isOpen_lt ht.continuous continuous_const))
  have hle' : x ∈ {x | t x ≤ 0} := interior_subset hx
  have hle : t x ≤ 0 := hle'
  rcases hle.lt_or_eq with hlt | h0
  · exact hlt
  · exfalso
    have hd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) t x := (ht x).mdifferentiableAt (by simp)
    have hne : mfderiv W.model 𝓘(ℝ, ℝ) (fun y => 0 - t y) x ≠ 0 := by
      intro h0'
      apply hreg x h0
      have h := DifferentialGeometry.Manifold.mfderiv_const_sub_real hd 0
      have h' : -(show E3 →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) t x) = 0 := h.symm.trans h0'
      exact neg_eq_zero.mp h'
    have hcl := mem_closure_lt_of_mfderiv_ne_zero_BGR (f := fun y => 0 - t y) (hint x h0) hne
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨y, hyU, hy⟩ := hcl _ (mem_interior_iff_mem_nhds.mp hx)
    have h1 : t y ≤ 0 := hyU
    have h2 : 0 - t y < 0 - t x := hy
    rw [h0] at h2
    linarith

/-- **`M₁` as a superlevel set of the product**: for pairwise disjoint regular sublevels
`{t_i ≤ 0}`, `(int ⋃ {t_i ≤ 0})ᶜ = {∏ t_i ≥ 0}`. -/
theorem compl_interior_iUnion_sublevel_BGR [Fintype ι] {t : ι → W.Carrier → ℝ}
    (hsm : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (t i))
    (hreg : ∀ i x, t i x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (t i) x ≠ 0)
    (hint : ∀ i x, t i x = 0 → W.model.IsInteriorPoint x)
    (hdisj : Pairwise (Disjoint on fun i => {x | t i x ≤ 0})) :
    (interior (⋃ i, {x | t i x ≤ 0}))ᶜ = {x | 0 ≤ ∏ i, t i x} := by
  classical
  have hI : ∀ i, interior {x | t i x ≤ 0} = {x | t i x < 0} := fun i =>
    interior_sublevel_eq_BGR (hsm i) (hreg i) (hint i)
  rw [interior_iUnion_of_disjoint_closed_BGR
    (fun i => isClosed_le (hsm i).continuous continuous_const) hdisj]
  simp_rw [hI]
  ext x
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_lt]
  constructor
  · intro h
    exact Finset.prod_nonneg fun i _ => h i
  · intro h i
    by_contra hneg
    rw [not_le] at hneg
    have hpos : ∀ j ∈ Finset.univ.erase i, 0 < t j x := fun j hj => by
      by_contra hle
      rw [not_lt] at hle
      exact Set.disjoint_left.mp (hdisj (Finset.ne_of_mem_erase hj))
        (show x ∈ {x | t j x ≤ 0} from hle) (show x ∈ {x | t i x ≤ 0} from hneg.le)
    have hprod : ∏ j, t j x = t i x * ∏ j ∈ Finset.univ.erase i, t j x :=
      (Finset.mul_prod_erase Finset.univ (fun j => t j x) (Finset.mem_univ i)).symm
    have : ∏ j, t j x < 0 := by
      rw [hprod]
      exact mul_neg_of_neg_of_pos hneg (Finset.prod_pos hpos)
    linarith

/-- **A regular sublevel set of a carrier is a manifold with boundary** (the tree's kernel,
`carrierSublevel*`, stated for a set equal to the sublevel). -/
theorem exists_isManifold_of_sublevel_set_BGR {S : Set W.Carrier} (f : W.Carrier → ℝ)
    (hS : S = {x | f x ≤ 0}) (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x, f x = 0 → x ∈ W.interior) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥S,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ ↥S ∧ ContMDiff (𝓡∂ 3) W.model ∞ (fun x : ↥S => x.1) ∧
      (∀ x : ↥S, Function.Bijective
        (mfderiv (𝓡∂ 3) W.model (fun y : ↥S => y.1) x)) ∧
      (∀ x : ↥S, (𝓡∂ 3).IsBoundaryPoint x ↔ (W.model.IsBoundaryPoint x.1 ∨ f x.1 = 0)) := by
  subst hS
  exact ⟨GC.GraphManifold.Assembly.carrierSublevelChartedSpace W f 0 hf hreg hint,
    GC.GraphManifold.Assembly.carrierSublevel_isManifold W f 0 hf hreg hint,
    GC.GraphManifold.Assembly.carrierSublevel_contMDiff_val W f 0 hf hreg hint,
    fun x => GC.GraphManifold.Assembly.carrierSublevel_mfderiv_val_bijective W f 0 hf hreg hint x,
    fun x => GC.GraphManifold.Assembly.carrierSublevel_isBoundaryPoint_iff hf hreg hint
      (x := x)⟩

/-- **The removed-region complement of pairwise disjoint regular sublevels is a manifold with
boundary**: for finitely many smooth `t_i` with nonzero differential at their zeros, zeros in the
interior of `W`, and pairwise disjoint sublevels `{t_i ≤ 0}`, the set `(int ⋃ {t_i ≤ 0})ᶜ` is a
smooth 3-manifold with boundary `(∂W ∩ S) ∪ ⋃ {t_i = 0}` (the inclusion is smooth with bijective
differential). -/
theorem isManifold_compl_interior_union_BGR [Finite ι] {t : ι → W.Carrier → ℝ}
    (hsm : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (t i))
    (hreg : ∀ i x, t i x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (t i) x ≠ 0)
    (hint : ∀ i x, t i x = 0 → W.model.IsInteriorPoint x)
    (hdisj : Pairwise (Disjoint on fun i => {x | t i x ≤ 0})) {S : Set W.Carrier}
    (hS : S = (interior (⋃ i, {x | t i x ≤ 0}))ᶜ) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥S,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ ↥S ∧ ContMDiff (𝓡∂ 3) W.model ∞ (fun x : ↥S => x.1) ∧
      (∀ x : ↥S, Function.Bijective
        (mfderiv (𝓡∂ 3) W.model (fun y : ↥S => y.1) x)) ∧
      (∀ x : ↥S, (𝓡∂ 3).IsBoundaryPoint x ↔
        (W.model.IsBoundaryPoint x.1 ∨ ∃ i, t i x.1 = 0)) := by
  classical
  let _ := Fintype.ofFinite ι
  have hset : S = {x | 0 - ∏ i, t i x ≤ 0} := by
    rw [hS, compl_interior_iUnion_sublevel_BGR hsm hreg hint hdisj]
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  have hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x => 0 - ∏ i, t i x) :=
    contMDiff_const.sub (contMDiff_finsetProd (fun i _ => hsm i))
  have hzero : ∀ x, (0 - ∏ i, t i x) = 0 → ∃ j, t j x = 0 := fun x hx => by
    have h : ∏ i, t i x = 0 := by linarith
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨j, hj⟩
  have hreg' : ∀ x, (0 - ∏ i, t i x) = 0 →
      mfderiv W.model 𝓘(ℝ, ℝ) (fun y => 0 - ∏ i, t i y) x ≠ 0 := by
    intro x hx
    obtain ⟨j, hj⟩ := hzero x hx
    have hpos : ∀ i ∈ Finset.univ.erase j, 0 < t i x := fun i hi => by
      by_contra hle
      rw [not_lt] at hle
      exact Set.disjoint_left.mp (hdisj (Finset.ne_of_mem_erase hi))
        (show x ∈ {x | t i x ≤ 0} from hle) (show x ∈ {x | t j x ≤ 0} from hj.le)
    have hR : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun y => ∏ i ∈ Finset.univ.erase j, t i y) :=
      contMDiff_finsetProd (fun i _ => hsm i)
    have hPeq : (fun y => ∏ i, t i y) =
        fun y => t j y * ∏ i ∈ Finset.univ.erase j, t i y :=
      funext fun y => (Finset.mul_prod_erase Finset.univ (fun i => t i y)
        (Finset.mem_univ j)).symm
    have hP : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => ∏ i, t i y) x :=
      ((contMDiff_finsetProd (fun i _ => hsm i)) x).mdifferentiableAt (by simp)
    have hmul := mfderiv_mul_of_eq_zero_ZSP35 ((hsm j x).mdifferentiableAt (by simp))
      ((hR x).mdifferentiableAt (by simp)) hj
    have hne : mfderiv W.model 𝓘(ℝ, ℝ) (fun y => ∏ i, t i y) x ≠ 0 := by
      rw [hPeq, hmul]
      exact smul_ne_zero (Finset.prod_pos hpos).ne' (hreg j x hj)
    intro h0
    apply hne
    have h := DifferentialGeometry.Manifold.mfderiv_const_sub_real hP 0
    have h' : -(show E3 →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun y => ∏ i, t i y) x) = 0 :=
      h.symm.trans h0
    exact neg_eq_zero.mp h'
  have hint' : ∀ x, (0 - ∏ i, t i x) = 0 → x ∈ W.interior := fun x hx => by
    obtain ⟨j, hj⟩ := hzero x hx
    exact hint j x hj
  obtain ⟨cs, h1, h2, h3, h4⟩ := exists_isManifold_of_sublevel_set_BGR _ hset hf hreg' hint'
  refine ⟨cs, ?_⟩
  let _ := cs
  refine ⟨h1, h2, h3, fun x => (h4 x).trans (or_congr_right ⟨hzero x.1, fun ⟨j, hj⟩ => ?_⟩)⟩
  have : ∏ i, t i x.1 = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
  linarith

end Carrier

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Each cusp core is the regular sublevel `{G_b − 40 ≤ 0}`** of BCG06's modified level `G_b`
(smooth, no critical point on `{G_b ≤ 40}`, level `40` in the interior of `W`), and its front is
the level `{G_b − 40 = 0}`. -/
theorem cuspLevel_data_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun y => S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) y - 40) ∧
    (∀ x, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x - 40 = 0 →
      mfderiv W.model 𝓘(ℝ, ℝ) (fun y => S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) y - 40) x ≠ 0) ∧
    (∀ x, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x - 40 = 0 → W.model.IsInteriorPoint x) ∧
    {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x - 40 ≤ 0} = C.toChain.cuspCore_BIF i ∧
    {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x - 40 = 0} = C.toChain.cuspFront_BIF i := by
  have hεd := epsBoundary_lt_BGR hrd hrdc
  have hBI := (C.bcg04_row_BGR hrd hprem).2.1 3 i
  have hBFM := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3 i
  have hc₃ := C.validity.c_two_lt_E4
  have hR := BoundaryCollarPacket.register_R_BCG6K hεd hc₃
  have hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) :=
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  have hcore : C.toChain.cuspCore_BIF i = {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x ≤ 40} :=
    S.packet.toBoundaryCollarPacket.cuspCore_eq_BCG6K hεd hBI hBFM
  have hfront : C.toChain.cuspFront_BIF i = {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x = 40} :=
    S.packet.toBoundaryCollarPacket.cuspFront_eq_BCG6K hεd hBI hBFM
  refine ⟨(S.packet.toBoundaryCollarPacket.contMDiff_coreLevel_BCG6K i hu).sub contMDiff_const,
    fun x hx => ?_, fun x hx => ?_, ?_, ?_⟩
  · have hx40 : S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x = 40 := by linarith
    rw [GC.GraphManifold.Assembly.FC39P0.mfderiv_sub_const_JN74]
    exact S.packet.toBoundaryCollarPacket.mfderiv_coreLevel_ne_zero_BCG6K i
      (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu C.toChain.c_two_pos_BCG6K.le hR
      (fun y _ => (hBI y).1) (C.bcg04_derivative_on_boundary_chain_BGR i) (le_of_eq hx40)
  · have hx40 : S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) x = 40 := by linarith
    have hxF : x ∈ S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) := by
      change x ∈ C.toChain.cuspFront_BIF i
      rw [hfront]
      exact hx40
    exact (S.packet.toBoundaryCollarPacket.mem_strip_of_mem_front_BCG6K hεd hBI hxF).2
  · rw [hcore]
    ext x
    simp only [mem_ofPred_eq, sub_nonpos]
  · rw [hfront]
    ext x
    simp only [mem_ofPred_eq, sub_eq_zero]

/-- **BCG07 clause 07.b2: `M₁` is a compact smooth manifold with boundary.** `↥M₁` carries a
`𝓡∂ 3`-structure for which the inclusion into `W` is smooth with bijective differential, and its
boundary points are exactly the actual zero faces and the cusp fronts `H_b` (no point of `∂W`
occurs, `M₁ ⊆ {D ≥ 35}`). Premises: `εr < 1/2` (ZSP02's defining functions) and E4's block. -/
theorem M₁_isManifold_BGR (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥C.toChain.M₁_BIFc,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ ↥C.toChain.M₁_BIFc ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun x : ↥C.toChain.M₁_BIFc => x.1) ∧
      (∀ x : ↥C.toChain.M₁_BIFc, Function.Bijective
        (mfderiv (𝓡∂ 3) W.model (fun y : ↥C.toChain.M₁_BIFc => y.1) x)) ∧
      (∀ x : ↥C.toChain.M₁_BIFc, (𝓡∂ 3).IsBoundaryPoint x ↔
        x.1 ∈ (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i) ∧
      CompactSpace ↥C.toChain.M₁_BIFc := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hcusp := C.cuspLevel_data_BGR hrd hrd4 hrdc hprem hθ
  let t : S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count → W.Carrier → ℝ :=
    Sum.elim Zd.defFn (fun i y => S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) y - 40)
  have hsm : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (t i) := by
    rintro (k | i)
    · exact Zd.defFn_smooth k
    · exact (hcusp i).1
  have hreg : ∀ i x, t i x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (t i) x ≠ 0 := by
    rintro (k | i) x hx
    · exact Zd.defFn_regular k x hx
    · exact (hcusp i).2.1 x hx
  have hint : ∀ i x, t i x = 0 → W.model.IsInteriorPoint x := by
    rintro (k | i) x hx
    · apply C.isInteriorPoint_of_mem_actualZeroFace_BGR k
      rw [Zd.face_eq k]
      exact hx
    · exact (hcusp i).2.2.1 x hx
  have hsub : ∀ i, {x | t i x ≤ 0} =
      Sum.elim C.toChain.actualZeroDomain_BIFc C.toChain.cuspCore_BIF i := by
    rintro (k | i)
    · exact (Zd.domain_eq k).symm
    · exact (hcusp i).2.2.2.1
  have hdisj : Pairwise (Disjoint on fun i => {x | t i x ≤ 0}) := by
    rintro (k | i) (k' | i') hne
    · rw [Function.onFun, hsub, hsub]
      exact C.actualZeroDomain_pairwise_disjoint_BGR fun h => hne (congrArg Sum.inl h)
    · rw [Function.onFun, hsub, hsub]
      exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i' k).symm
    · rw [Function.onFun, hsub, hsub]
      exact C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k'
    · rw [Function.onFun, hsub, hsub]
      exact hspec.pairwise_disjoint i i' fun h => hne (congrArg Sum.inr h)
  have hM : C.toChain.M₁_BIFc = (interior (⋃ i, {x | t i x ≤ 0}))ᶜ := by
    rw [iUnion_congr hsub, iUnion_sum]
    rfl
  obtain ⟨cs, h1, h2, h3, h4⟩ := isManifold_compl_interior_union_BGR hsm hreg hint hdisj hM
  refine ⟨cs, ?_⟩
  let _ := cs
  refine ⟨h1, h2, h3, fun x => ?_,
    isCompact_iff_compactSpace.mp C.toChain.isClosed_M₁_BCF.isCompact⟩
  have hnb : ¬ W.model.IsBoundaryPoint x.1 := fun hb => by
    have hbuf := C.toChain.M₁_subset_buffer_BGR (⋃ k, C.toChain.actualZeroDomain_BIFc k) x.2
    have hdist : distanceToBoundary W g x.1 = 0 := by
      refine le_antisymm ?_ bot_le
      calc distanceToBoundary W g x.1
          ≤ riemannianEDistOf g x.1 ((⟨x.1, hb⟩ : W.model.boundary W.Carrier) : W.Carrier) :=
            iInf_le (fun q : W.model.boundary W.Carrier => riemannianEDistOf g x.1 q)
              ⟨x.1, hb⟩
        _ = 0 := riemannianEDistOf_self _ _
    have h35 : ENNReal.ofReal 35 ≤ distanceToBoundary W g x.1 := hbuf
    rw [hdist] at h35
    have : (35 : ℝ) ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm h35 bot_le)
    linarith
  rw [h4 x]
  constructor
  · rintro (hb | ⟨i, hi⟩)
    · exact absurd hb hnb
    · rcases i with k | i
      · refine Or.inl (mem_iUnion.mpr ⟨k, ?_⟩)
        rw [Zd.face_eq k]
        exact hi
      · refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
        rw [← (hcusp i).2.2.2.2]
        exact hi
  · rintro (hx | hx)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      rw [Zd.face_eq k] at hk
      exact Or.inr ⟨Sum.inl k, hk⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [← (hcusp i).2.2.2.2] at hi
      exact Or.inr ⟨Sum.inr i, hi⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
