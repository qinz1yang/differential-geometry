import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

/-!
# Zero extension from an open subset with closed support in the ambient manifold (lane BAUG-A)

Draft 61 §2.3 / disposition D61-4: ONE general zero-extension lemma for the boundary augmented
map. A function `f` on an open subset `O` of a manifold `M` whose closed support lies in a set `K`
that is compact IN `M`, with `K ⊆ U ⊆ O`, `U` open, and `f` smooth on `U`, extends by zero to a
smooth function on `M` that equals `f` on `O` (in particular on `U`). The hypothesis is closed
support in the AMBIENT manifold: a set that is only closed in `O` may accumulate at the frontier of
`O`, and its zero extension need not be smooth.

* `extend_zero_val_BAUGA`: the zero extension `Subtype.val.extend f 0` equals `f` on `O`;
* `extend_zero_eq_zero_of_notMem_BAUGA`: it vanishes off `O`;
* `contMDiff_extend_zero_of_tsupport_subset_BAUGA`: the smoothness lemma (any model, any `O`);
* `contMDiff_extend_zero_pieceInterior_BAUGA`: the same for the open interior
  `W° = W.pieceInterior ⊤` of a compact carrier with its interior atlas (model `𝓡 3`), the form
  used on the boundary family.
-/

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

section General

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [TopologicalSpace M] [NormedSpace ℝ V] in
/-- The zero extension equals the function on the open subset. -/
theorem extend_zero_val_BAUGA {O : Set M} (f : O → V) (x : O) :
    Subtype.val.extend f 0 (x : M) = f x :=
  Subtype.val_injective.extend_apply f 0 x

omit [TopologicalSpace M] [NormedSpace ℝ V] in
/-- The zero extension vanishes off the open subset. -/
theorem extend_zero_eq_zero_of_notMem_BAUGA {O : Set M} (f : O → V) {y : M} (hy : y ∉ O) :
    Subtype.val.extend f 0 y = 0 :=
  extend_apply' f (0 : M → V) y fun ⟨a, ha⟩ => hy (ha ▸ a.2)

omit [NormedSpace ℝ V] in
/-- The zero extension vanishes at every point outside `K` when the closed support of `f` lies in
`Subtype.val ⁻¹' K`. -/
theorem extend_zero_eq_zero_of_notMem_of_tsupport_BAUGA {O : Set M} {f : O → V} {K : Set M}
    (hsupp : tsupport f ⊆ Subtype.val ⁻¹' K) {y : M} (hy : y ∉ K) :
    Subtype.val.extend f 0 y = 0 := by
  by_cases hyO : y ∈ O
  · have h0 : f ⟨y, hyO⟩ = 0 := by
      by_contra hne
      exact hy (hsupp (subset_tsupport f hne))
    rw [show y = ((⟨y, hyO⟩ : O) : M) from rfl, extend_zero_val_BAUGA, h0]
  · exact extend_zero_eq_zero_of_notMem_BAUGA f hyO

/-- **Zero extension with closed support in the ambient manifold.** If the closed support of
`f : O → V` lies in `K`, `K` is compact in `M`, `K ⊆ U ⊆ O` with `U` open, and `f` is smooth on
`U`, then the zero extension of `f` is smooth on `M`. -/
theorem contMDiff_extend_zero_of_tsupport_subset_BAUGA [T2Space M] {n : ℕ∞ω} {O : Opens M}
    {f : O → V} {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUO : U ⊆ O) (hsupp : tsupport f ⊆ Subtype.val ⁻¹' K)
    (hf : ContMDiffOn I 𝓘(ℝ, V) n f (Subtype.val ⁻¹' U)) :
    ContMDiff I 𝓘(ℝ, V) n (Subtype.val.extend f 0) := by
  intro x
  by_cases hx : x ∈ K
  · lift x to O using hUO (hKU hx)
    rw [← contMDiffAt_subtype_iff]
    have hfun : (fun y : O => Subtype.val.extend f 0 (y : M)) = f :=
      funext (extend_zero_val_BAUGA f)
    rw [hfun]
    exact hf.contMDiffAt ((hU.preimage continuous_subtype_val).mem_nhds (hKU hx))
  · refine (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact extend_zero_eq_zero_of_notMem_of_tsupport_BAUGA hsupp hy

end General

section PieceInterior

open GC.Endpoint

universe u

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Zero extension from the open interior of a compact carrier** (interior atlas, model `𝓡 3`):
if the closed support of `f : W° → V` lies in `K`, `K` compact in `W`, `K ⊆ U ⊆ W°` with `U` open
in `W`, and `f` is smooth on `U` in the interior atlas, then the zero extension of `f` is smooth on
the carrier `W` and equals `f` on `W°` (`extend_zero_val_BAUGA`). -/
theorem contMDiff_extend_zero_pieceInterior_BAUGA (W : CompactCarrier.{u})
    {f : W.pieceInterior ⊤ → V} {K U : Set W.Carrier} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUO : U ⊆ W.pieceInterior ⊤) (hsupp : tsupport f ⊆ Subtype.val ⁻¹' K)
    (hf : letI := interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      ContMDiffOn (𝓡 3) 𝓘(ℝ, V) ∞ f (Subtype.val ⁻¹' U)) :
    ContMDiff W.model 𝓘(ℝ, V) ∞ (Subtype.val.extend f 0) := by
  refine contMDiff_extend_zero_of_tsupport_subset_BAUGA hK hU hKU hUO hsupp ?_
  let _ := interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hid := contMDiff_id_interiorAtlas W.model ∞ (M := W.pieceInterior ⊤)
  exact hf.comp hid.contMDiffOn fun _ hx => hx

end PieceInterior

end DifferentialGeometry.Manifold
