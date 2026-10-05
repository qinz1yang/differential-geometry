import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap
import DifferentialGeometry.Topology.Manifold.InteriorZeroExtension

/-!
# BCG03: the boundary blocks of the augmented map on the original carrier `W` (lane BAUG-A, G1)

Draft 61 §2.1–§2.3, disposition D61-4. The augmented target is `H^∂ = H_int ⊕ ⊕_b ℝ²_b` in the
`planeAxis` encoding of `BlockSpace`: the tags are `ι ⊕ κ` (interior tags `ι`, boundary components
`κ`), every slot is `ℝ² ⊕ ℝ`, and the two-dimensional boundary block `(u_b, v_b)` sits in the slot
of `b` as `(planeAxis u_b, v_b)` (the fixed linear isometric encoding of `cgpGlobalMap`).

* `BoundaryCollarPacket.collarBand_BAUGA`, `…safeBand_BAUGA`: the original smooth collar band
  `e_b(2 < z < 98)` (the indicator set of `P.block b`) and `Safe_b = band ∩ {32 ≤ η_b ≤ 78}` — the
  height condition is never stated without the band;
* `BoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA`: on `Safe_b` the ACTUAL boundary block
  `F_{∂,b} := P.block b` is `(η_b, 1)` (BCG05's scalar marker `v_b = 1`);
* `boundaryAugmentedMap_BAUGA Fint B`: the augmented map from ANY interior part
  `Fint : M → H_int` and boundary blocks `B b : M → ℝ × ℝ`; `…_inl`, `…_boundary_block`,
  `…_interior_projection` (`pr_{H_int} F_∂ = Fint`), `…_eq_interior_off_support` (off every
  boundary closed support `F_∂ = ι_int Fint`), `contMDiff_boundaryAugmentedMap_BAUGA`;
* `boundaryOriginalMap_BAUGA P Fint`: the map with the packet's actual collar blocks
  (`P.toBoundaryCollarPacket.block b`, collar-band restricted, zero outside — never the unrestricted
  `𝓑(P.height b)`); `boundaryOriginalMap_boundary_block_BAUGA`, `…_safe_BAUGA`,
  `…_interior_projection_BAUGA`, `…_eq_interior_extension_off_collar_support_BAUGA`,
  `…_smooth_BAUGA`. The interior part `F_int^W` of the active family is built in G3.
* Consumer: `contMDiff_extend_zero_of_tsupport_subset_distanceToBoundary_BAUGA` — a function on
  `W°` smooth in the interior atlas with closed support in `{D ≥ c}` (`c > 0`) extends by zero to a
  smooth function on `W` (the fixed buffer domains of the interior blocks).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

section Encoding

/-- The plane encoding `(u, v) ↦ (planeAxis u, v)` of a two-dimensional block in a `BlockSpace`
slot `ℝ² ⊕ ℝ`, as a continuous linear map. -/
def planeBlockEmbed_BAUGA : ℝ × ℝ →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm : (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).comp
    (planeAxis.prodMap (ContinuousLinearMap.id ℝ ℝ))

theorem planeBlockEmbed_apply_BAUGA (B : ℝ × ℝ) :
    planeBlockEmbed_BAUGA B = WithLp.toLp 2 (planeAxis B.1, B.2) :=
  rfl

theorem planeBlockEmbed_snd_BAUGA (B : ℝ × ℝ) : (planeBlockEmbed_BAUGA B).snd = B.2 :=
  rfl

theorem planeBlockEmbed_fst_BAUGA (B : ℝ × ℝ) : (planeBlockEmbed_BAUGA B).fst = planeAxis B.1 :=
  rfl

end Encoding

section Augmented

variable {ι κ : Type*} {M : Type*}

/-- **The augmented map** `F_∂ : M → H_int ⊕ ⊕_b ℝ²_b` from an interior part `Fint` and boundary
blocks `B b`: the interior slots are those of `Fint`, the slot of `b` is the plane encoding of
`B b`. -/
def boundaryAugmentedMap_BAUGA (Fint : M → BlockSpace (fun _ : ι => ℝ²)) (B : κ → M → ℝ × ℝ)
    (p : M) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  WithLp.toLp 2 (Sum.elim (fun i => Fint p i) (fun b => planeBlockEmbed_BAUGA (B b p)))

/-- The orthogonal projection `pr_{H_int}` onto the interior slots. -/
def augmentedInteriorProj_BAUGA (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    BlockSpace (fun _ : ι => ℝ²) :=
  WithLp.toLp 2 fun i => x (Sum.inl i)

/-- The inclusion `ι_int` of the interior slots (boundary slots zero). -/
def augmentedInteriorIncl_BAUGA (y : BlockSpace (fun _ : ι => ℝ²)) :
    BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  WithLp.toLp 2 (Sum.elim (fun i => y i) fun _ => 0)

variable (Fint : M → BlockSpace (fun _ : ι => ℝ²)) (B : κ → M → ℝ × ℝ)

theorem boundaryAugmentedMap_inl_BAUGA (p : M) (i : ι) :
    boundaryAugmentedMap_BAUGA Fint B p (Sum.inl i) = Fint p i :=
  rfl

/-- The slot of the boundary component `b` is the plane encoding of the boundary block. -/
theorem boundaryAugmentedMap_boundary_block_BAUGA (p : M) (b : κ) :
    boundaryAugmentedMap_BAUGA Fint B p (Sum.inr b) = planeBlockEmbed_BAUGA (B b p) :=
  rfl

/-- `pr_{H_int} F_∂ = Fint`. -/
theorem boundaryAugmentedMap_interior_projection_BAUGA (p : M) :
    augmentedInteriorProj_BAUGA (boundaryAugmentedMap_BAUGA Fint B p) = Fint p :=
  rfl

/-- Where every boundary block vanishes, `F_∂ = ι_int Fint`. -/
theorem boundaryAugmentedMap_eq_interior_of_block_eq_zero_BAUGA {p : M}
    (hp : ∀ b, B b p = 0) :
    boundaryAugmentedMap_BAUGA Fint B p = augmentedInteriorIncl_BAUGA (Fint p) := by
  refine congrArg (WithLp.toLp 2) (funext fun t => ?_)
  rcases t with i | b
  · rfl
  · change planeBlockEmbed_BAUGA (B b p) = 0
    rw [hp b, map_zero]

/-- Off the closed supports of all boundary blocks, `F_∂ = ι_int Fint`. -/
theorem boundaryAugmentedMap_eq_interior_off_support_BAUGA [TopologicalSpace M] {p : M}
    (hp : p ∉ ⋃ b, tsupport (B b)) :
    boundaryAugmentedMap_BAUGA Fint B p = augmentedInteriorIncl_BAUGA (Fint p) := by
  refine boundaryAugmentedMap_eq_interior_of_block_eq_zero_BAUGA Fint B fun b => ?_
  exact image_eq_zero_of_notMem_tsupport fun h => hp (mem_iUnion.mpr ⟨b, h⟩)

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- The augmented map is smooth when the interior part and every boundary block are smooth. -/
theorem contMDiff_boundaryAugmentedMap_BAUGA [Fintype ι] [Fintype κ]
    {Fint : M → BlockSpace (fun _ : ι => ℝ²)} {B : κ → M → ℝ × ℝ}
    (hF : ContMDiff I 𝓘(ℝ, BlockSpace (fun _ : ι => ℝ²)) ∞ Fint)
    (hB : ∀ b, ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (B b)) :
    ContMDiff I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ∞ (boundaryAugmentedMap_BAUGA Fint B) := by
  have hFpi := ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => WithLp 2 (ℝ² × ℝ) :
    BlockSpace (fun _ : ι => ℝ²) →L[ℝ] ∀ _ : ι, WithLp 2 (ℝ² × ℝ))).contMDiff.comp hF
  have hpi : ContMDiff I 𝓘(ℝ, ∀ _ : ι ⊕ κ, WithLp 2 (ℝ² × ℝ)) ∞
      (fun p => Sum.elim (fun i => Fint p i) (fun b => planeBlockEmbed_BAUGA (B b p))) := by
    refine contMDiff_pi_space.2 fun t => ?_
    rcases t with i | b
    · exact contMDiff_pi_space.1 hFpi i
    · exact planeBlockEmbed_BAUGA.contMDiff.comp (hB b)
  exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)).symm :
    (∀ _ : ι ⊕ κ, WithLp 2 (ℝ² × ℝ)) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)).contMDiff.comp hpi

end Augmented

section Collar

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)

/-- The original smooth collar band `e_b(2 < z < 98)` of the boundary component `b` (the set on
which `P.block b` is `𝓑(P.height b)`). -/
def collarBand_BAUGA : Set W.Carrier :=
  (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}

/-- `Safe_b`: points of the original collar band with `32 ≤ η_b ≤ 78`. -/
def safeBand_BAUGA : Set W.Carrier :=
  {x | x ∈ P.collarBand_BAUGA b ∧ 32 ≤ P.height b x ∧ P.height b x ≤ 78}

theorem block_eq_indicator_BAUGA :
    P.block b = (P.collarBand_BAUGA b).indicator (fun x => boundaryBlock (P.height b x)) :=
  rfl

theorem block_eq_of_mem_collarBand_BAUGA {x : W.Carrier} (hx : x ∈ P.collarBand_BAUGA b) :
    P.block b x = boundaryBlock (P.height b x) :=
  indicator_of_mem hx _

theorem block_eq_zero_of_notMem_collarBand_BAUGA {x : W.Carrier}
    (hx : x ∉ P.collarBand_BAUGA b) : P.block b x = 0 :=
  indicator_of_notMem hx _

theorem isOpen_collarBand_BAUGA : IsOpen (P.collarBand_BAUGA b) :=
  (P.cusp.collar b).isOpen_image ((isOpen_lt continuous_const continuous_cusp_height).inter
    (isOpen_lt continuous_cusp_height continuous_const))
    fun p hp => cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le

/-- **BCG05's marker on `Safe_b`**: there the actual boundary block is `(η_b, 1)`. -/
theorem block_eq_of_mem_safeBand_BAUGA {x : W.Carrier} (hx : x ∈ P.safeBand_BAUGA b) :
    P.block b x = (P.height b x, 1) := by
  rw [P.block_eq_of_mem_collarBand_BAUGA b hx.1, boundaryBlock,
    boundaryProfile_eq_one ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩, mul_one]

theorem cutoff_eq_one_of_mem_safeBand_BAUGA {x : W.Carrier} (hx : x ∈ P.safeBand_BAUGA b) :
    P.cutoff b x = 1 := by
  change (P.block b x).2 = 1
  rw [P.block_eq_of_mem_safeBand_BAUGA b hx]

theorem safeBand_subset_collarBand_BAUGA : P.safeBand_BAUGA b ⊆ P.collarBand_BAUGA b :=
  fun _ hx => hx.1

end BoundaryCollarPacket

variable {ι : Type*}

/-- **The augmented map on the original carrier** with the packet's ACTUAL collar blocks
`F_{∂,b} = P.block b` (collar-band restricted, zero outside) and an interior part `Fint`. -/
def boundaryOriginalMap_BAUGA (P : BoundaryCollarPacket W g K A w₀ ε)
    (Fint : W.Carrier → BlockSpace (fun _ : ι => ℝ²)) :
    W.Carrier → BlockSpace (fun _ : ι ⊕ Fin P.cusp.count => ℝ²) :=
  boundaryAugmentedMap_BAUGA Fint P.block

variable (P : BoundaryCollarPacket W g K A w₀ ε) (Fint : W.Carrier → BlockSpace (fun _ : ι => ℝ²))

/-- The slot of `b` is the plane encoding of `P.block b`. -/
theorem boundaryOriginalMap_boundary_block_BAUGA (p : W.Carrier) (b : Fin P.cusp.count) :
    boundaryOriginalMap_BAUGA P Fint p (Sum.inr b) = planeBlockEmbed_BAUGA (P.block b p) :=
  rfl

/-- On `Safe_b` the slot of `b` is `(planeAxis η_b, 1)`. -/
theorem boundaryOriginalMap_safe_BAUGA {p : W.Carrier} {b : Fin P.cusp.count}
    (hp : p ∈ P.safeBand_BAUGA b) :
    boundaryOriginalMap_BAUGA P Fint p (Sum.inr b) =
      WithLp.toLp 2 (planeAxis (P.height b p), (1 : ℝ)) := by
  rw [boundaryOriginalMap_boundary_block_BAUGA, P.block_eq_of_mem_safeBand_BAUGA b hp]
  rfl

theorem boundaryOriginalMap_interior_projection_BAUGA (p : W.Carrier) :
    augmentedInteriorProj_BAUGA (boundaryOriginalMap_BAUGA P Fint p) = Fint p :=
  rfl

/-- Off every closed boundary-collar support, `F_∂ = ι_int Fint`. -/
theorem boundaryOriginalMap_eq_interior_extension_off_collar_support_BAUGA {p : W.Carrier}
    (hp : p ∉ ⋃ b, tsupport (P.block b)) :
    boundaryOriginalMap_BAUGA P Fint p = augmentedInteriorIncl_BAUGA (Fint p) :=
  boundaryAugmentedMap_eq_interior_off_support_BAUGA Fint P.block hp

/-- The augmented map is smooth on `W` once the interior part is. -/
theorem boundaryOriginalMap_smooth_BAUGA [Fintype ι]
    (hF : ContMDiff W.model 𝓘(ℝ, BlockSpace (fun _ : ι => ℝ²)) ∞ Fint) :
    ContMDiff W.model 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ Fin P.cusp.count => ℝ²)) ∞
      (boundaryOriginalMap_BAUGA P Fint) :=
  contMDiff_boundaryAugmentedMap_BAUGA hF P.contMDiff_block

end Collar

section Consumer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Consumer of the zero-extension lemma**: a function on `W°`, smooth in the interior atlas,
whose closed support lies in `{D ≥ c}` with `c > 0`, extends by zero to a smooth function on the
original carrier `W` (the set `{D ≥ c}` is closed, hence compact, in `W` and lies in `W°`). -/
theorem contMDiff_extend_zero_of_tsupport_subset_distanceToBoundary_BAUGA
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier) {c : ℝ} (hc : 0 < c)
    {f : W.pieceInterior ⊤ → V}
    (hsupp : tsupport f ⊆ {x | ENNReal.ofReal c ≤ distanceToBoundary W g x})
    (hf : letI := interiorCharted_BDRY1 W
      ContMDiff (𝓡 3) 𝓘(ℝ, V) ∞ f) :
    ContMDiff W.model 𝓘(ℝ, V) ∞ (Subtype.val.extend f 0) := by
  have hKc : IsClosed {y : W.Carrier | ENNReal.ofReal c ≤ distanceToBoundary W g y} :=
    (upperSemicontinuous_distanceToBoundary_BDRY1 W g).isClosed_preimage (ENNReal.ofReal c)
  have hsub : {y : W.Carrier | ENNReal.ofReal c ≤ distanceToBoundary W g y} ⊆
      (W.pieceInterior ⊤ : Set W.Carrier) := by
    intro y hy
    rw [coe_pieceInterior_top_BDRY1]
    exact mem_interior_of_distanceToBoundary_pos_BDRY1 W g
      (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hy)
  let _ := interiorCharted_BDRY1 W
  exact Manifold.contMDiff_extend_zero_pieceInterior_BAUGA W hKc.isCompact
    (W.pieceInterior ⊤).isOpen hsub subset_rfl hsupp hf.contMDiffOn

end Consumer

end DifferentialGeometry.Geometry.Collapse
