import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFaceParamConsumerOCX
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefiningApplicationsBGR

/-!
# BCG07 F3 and F5z with `face_param` delivered (S-BCG-ROWS2 G32)

O-CROSS G4 delivers `face_param_OCX` (the standard `S²` / `T²` smooth embedding of every actual zero
face into `W`, premise `εr < 1/2`) and `actualZeroFace_isConnected_OCX`. With it:

* **`exists_boundaryActualZeroDomains_BGR`** (F3):
  `Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs)` on the enhanced chain — analytic half
  (G22), placement fields (G14), `face_param` (O-CROSS G4) and `face_saturated` (G25 / G31, from the
  whole-fibre layer v2b `WF`);
* **`zeroFace_eq_slimFibre_direct_V2b_BGR`** (F5z): a zero face meeting `X₃` is ONE whole slim
  fibre, directly from the analytic half (the fibre lies in the face by the zero-block retention
  `zeroFace_saturated_BGR`), the connectedness of the face and the v2b layer — no `Z`;
* **`frontier_M₁_image_finite_V2b_BGR`**: `f₃(∂M₁ ∩ X₃)` is finite (F4c + F5 + F5z), BCF01 G1a input
  (a), with inputs `hεr`, `WF` (v2b), E4's premises only.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

/-- **BCG07 F3: the actual zero domains of `C.E`** on the enhanced chain and a v2b A4 output.
Premises: `εr < 1/2` (FAMZ), `e ≤ 1/1000` (N76-6, the `zero_cover` field), E4's `r_∂` block and
`θ < 1/100` (for `face_saturated`). DEVIATION from the frozen v3.1 F3 (which has only `hεr`):
`WF` and the E4 premises enter through `face_saturated` (the saturation of `M₁` needs the connected
whole fibres), `e ≤ 1/1000` through `zero_cover`. -/
theorem exists_boundaryActualZeroDomains_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs) := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact ⟨{ toBoundaryZeroDefining_BIFc := Zd
           domain_subset_ball := C.actualZeroDomain_subset_ball_BGR
           zero_cover := fun k q hq => C.actualZeroDomain_cover_BGR he k q hq
           isCompact_domain := C.isCompact_actualZeroDomain_BGR
           pairwise_disjoint := C.actualZeroDomain_pairwise_disjoint_BGR
           face_param := C.face_param_OCX hεr
           face_saturated := C.face_saturated_actual_V2b_BGR WF Zd hrd hrd4 hrdc hprem hθ }⟩

/-- **BCG07 F5z: a zero face meeting `X₃` is ONE whole slim fibre** (frozen v3.1 F5z), directly. -/
theorem zeroFace_eq_slimFibre_direct_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) :
    ∀ k : S.ZeroIdx_BAUGC, (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.actualZeroFace_BIFc k = Bs.fibre 2 y := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  rintro k ⟨p, hp, hpX⟩
  have hface := Zd.face_eq k
  have hF0 : Zd.defFn k p = 0 := by
    have h : p ∈ {q | Zd.defFn k q = 0} := hface ▸ hp
    exact h
  have hSX : C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 = Bs.source 2 ∩
      C.toChain.stageMap 2 ⁻¹' (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩
        Bs.source 2)) := by
    ext q
    constructor
    · rintro ⟨hq, hqX⟩
      exact ⟨hqX, q, ⟨hq, hqX⟩, rfl⟩
    · rintro ⟨hqX, p', ⟨hp', hpX'⟩, hpq⟩
      exact ⟨C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 2 k) hp' hpq.symm,
        hqX⟩
  have hfibsub : Bs.fibre 2 (C.toChain.stageMap 2 p) ⊆ C.toChain.actualZeroFace_BIFc k :=
    fun q hq => C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 2 k) hp hq.2
  obtain ⟨O, hO, hOD⟩ := C.slim_isolation_V2b_BGR WF (Zd.defFn_smooth k) hpX (cc := 0)
    (fun q hq hqp => by
      have h : q ∈ C.toChain.actualZeroFace_BIFc k := hfibsub ⟨hq, hqp⟩
      rw [hface] at h
      exact h)
    (fun q hq q' hq' hqq' hq0 => by
      have hqf : q ∈ C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 :=
        ⟨by rw [hface]; exact hq0, hq⟩
      have h : q' ∈ C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 := by
        rw [hSX]
        exact ⟨hq', q, hqf, hqq'⟩
      have h' : q' ∈ C.toChain.actualZeroFace_BIFc k := h.1
      rw [hface] at h'
      exact h')
    (Zd.defFn_regular k p hF0)
  rw [← hface] at hOD
  refine ⟨C.toChain.stageMap 2 p, Bs.image_eq 2 ▸ mem_image_of_mem _ hpX, ?_⟩
  exact DifferentialGeometry.Topology.eq_fiber_of_isPreconnected_of_isolated
    (C.toChain.stageMap 2) (Bs.source 2) (C.toChain.actualZeroFace_BIFc k)
    (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2))
    (Bs.isOpen_source 2 (by decide)) (Bs.continuousOn_stageMap_BCF 2)
    (C.actualZeroFace_isConnected_OCX hεr k).isPreconnected hSX ⟨O, hO, hOD⟩
    (Bs.proper 2 {C.toChain.stageMap 2 p}
      (singleton_subset_iff.mpr (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX)) isCompact_singleton)
    ⟨p, hpX, rfl⟩

/-- **`f₃(∂M₁ ∩ X₃)` is finite** (F4c + F5 + F5z; BCF01 G1a input (a)): inputs `hεr`, the v2b layer
and E4's premises only. -/
theorem frontier_M₁_image_finite_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2)).Finite := by
  have hF := C.frontier_M₁_unconditional_BGR hεr hrd hrd4 hrdc hprem hθ
  have hpiece : ∀ T : Set W.Carrier, (T ∩ Bs.source 2).Nonempty →
      (∃ y ∈ Bs.base 2, T = Bs.fibre 2 y) → (C.toChain.stageMap 2 '' (T ∩ Bs.source 2)).Finite :=
    fun T _ ⟨y, _, hy⟩ => by
      refine (Set.finite_singleton y).subset ?_
      rintro _ ⟨q, ⟨hqT, hqX⟩, rfl⟩
      rw [hy] at hqT
      exact hqT.2
  have hz : ∀ k : S.ZeroIdx_BAUGC,
      (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2)).Finite :=
    fun k => by
    by_cases hne : (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty
    · exact hpiece _ hne (C.zeroFace_eq_slimFibre_direct_V2b_BGR WF hεr k hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact Set.finite_empty
  have hc : ∀ i : Fin S.packet.cusp.count,
      (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2)).Finite := fun i => by
    by_cases hne : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty
    · exact hpiece _ hne (C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ i hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact Set.finite_empty
  rw [hF, Set.union_inter_distrib_right, Set.iUnion_inter, Set.iUnion_inter, image_union,
    image_iUnion, image_iUnion]
  exact (Set.finite_iUnion hz).union (Set.finite_iUnion hc)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
