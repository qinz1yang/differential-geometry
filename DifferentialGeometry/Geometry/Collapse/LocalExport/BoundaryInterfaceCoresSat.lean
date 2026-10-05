import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceInhabitants

/-!
# Boundary route interfaces: zero cores with saturated faces (lane B-BCF134, lead decision 13:4x)

`BoundaryInitialCoresSpec C` (BIFACE) stores the actual zero cores `Z_k` as ABSTRACT compact sets
(inside the original zero balls, covering the `.38`-balls, pairwise disjoint, with an `S²` or `T²`
frontier). Nothing ties their faces to the whole fibres of the stage maps `f_j = π_j ∘ C.E`, so the
statements of BCF01 (G3) and BCF03 that use `S ⊆ M₁` are not consequences of the interface.

**Counterexample to the frozen G3 on the plain structure** (minimal description): take any instance
in which a zero core `Z_k` meets the slim source `X₃` and replace `Z_k` by a core `Z_k'` inside the
same zero ball, still containing `B(z, .38 r_z)` in its interior and with a torus frontier, whose
torus face CUTS a slim fibre `F = X₃ ∩ f₃⁻¹{y}` (part of `F` in `int Z_k'`, part outside). Then
`y ∈ D₃ = f₃(M₁ ∩ X₃)` and, if `y ∈ K₃`, the whole fibre `F` lies in `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`
although part of `F` lies in `int Z_k' ⊆ W \ M₁`; a point of `∂S` inside `int Z_k'` lies in
`∂S \ ∂M₁` but not in `S ∩ M₂ ⊆ M₁`, so `S ∩ M₂ = ∂S \ ∂M₁` fails.

**The extension.** `BoundaryInitialCoresSpecSat C Bs` adds one field, in the weakest form BCF01-G3
(the ZSP05 premise `S ⊆ M₁`) and BCF03 consume: for the circle and slim stages (`st ≠ 1`) the
complement of `int_W(Z ∪ C_∂)`, i.e. `M₁`, is saturated by the whole fibres of `f_st` inside `X_st`
(draft 61 §5.4 (F4d)). Its PRODUCER (canonical cores := the zero-block sublevels of `C.E`, as in
the closed `Gaf02Chain.zero_face_saturated_ZSP35` / `zero_base_function_ZSP35`, together with the
cusp saturation `cuspFront_saturated_BIF`) is lane B-BCG-ROWS's.

* `BoundaryInitialCoresSpecSat.M₁_saturated_BCF`: F4d's set form
  `M₁ ∩ X_st = X_st ∩ f_st⁻¹(f_st(M₁ ∩ X_st))` (`st ≠ 1`).
* Inhabitants: `BoundaryInitialCoresSpec.toSat_of_source_empty_BCF` (any cores over bases whose
  circle and slim sources are empty) and `BoundaryGaf02Chain.emptyInitialCoresSat_BCF` (the
  empty-family chain of BIFACE's inhabitants).
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The actual zero cores with saturated faces** (lead decision 13:4x; draft 61 §5.4 (F4d)):
`BoundaryInitialCoresSpec C` together with the saturation of `M₁ = W \ int_W(Z ∪ C_∂)` by the whole
fibres of the circle and slim stage maps inside their source domains: a point of `X_st` in the same
`f_st`-fibre as a point of `M₁ ∩ X_st` lies in `M₁` (`st ≠ 1`). -/
structure BoundaryInitialCoresSpecSat (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (Bs : BoundaryGaf02Bases C) : Type extends BoundaryInitialCoresSpec C where
  /-- (F4d) `M₁ ∩ X_st` is a union of whole `f_st`-fibres (`st ≠ 1`). -/
  face_saturated : ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
    C.stageMap st q = C.stageMap st p →
    p ∉ interior ((⋃ k, core k) ∪ C.cuspCores_BIF) →
    q ∉ interior ((⋃ k, core k) ∪ C.cuspCores_BIF)

namespace BoundaryInitialCoresSpecSat

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}
  (Z : BoundaryInitialCoresSpecSat C Bs)

/-- The saturation field on `M₁` of the underlying cores. -/
theorem mem_M₁_of_stageMap_eq_BCF {st : Fin 3} (hst : st ≠ 1) {p q : W.Carrier}
    (hp : p ∈ Z.M₁) (hpX : p ∈ Bs.source st) (hqX : q ∈ Bs.source st)
    (hpq : C.stageMap st q = C.stageMap st p) : q ∈ Z.M₁ :=
  Z.face_saturated st hst p hpX q hqX hpq hp

/-- **F4d on the saturated cores**: `M₁ ∩ X_st = X_st ∩ f_st⁻¹(f_st(M₁ ∩ X_st))` for the circle and
slim stages. -/
theorem M₁_saturated_BCF (st : Fin 3) (hst : st ≠ 1) :
    Z.M₁ ∩ Bs.source st =
      Bs.source st ∩ C.stageMap st ⁻¹' (C.stageMap st '' (Z.M₁ ∩ Bs.source st)) := by
  ext q
  constructor
  · rintro ⟨hqM, hqX⟩
    exact ⟨hqX, q, ⟨hqM, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hpM, hpX⟩, hpq⟩
    exact ⟨Z.mem_M₁_of_stageMap_eq_BCF hst hpM hpX hqX hpq.symm, hqX⟩

end BoundaryInitialCoresSpecSat

/-- **Inhabitant**: any cores over bases whose circle and slim source domains are empty carry the
(vacuous) saturation. -/
def BoundaryInitialCoresSpec.toSat_of_source_empty_BCF
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}
    (ZC : BoundaryInitialCoresSpec C) (h : ∀ st, st ≠ 1 → Bs.source st = ∅) :
    BoundaryInitialCoresSpecSat C Bs where
  toBoundaryInitialCoresSpec := ZC
  face_saturated := fun st hst p hp => by
    rw [h st hst] at hp
    exact (notMem_empty p hp).elim

/-- The underlying cores of `toSat_of_source_empty_BCF` are the given ones. -/
theorem BoundaryInitialCoresSpec.toSat_of_source_empty_toSpec_BCF
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}
    (ZC : BoundaryInitialCoresSpec C) (h : ∀ st, st ≠ 1 → Bs.source st = ∅) :
    (ZC.toSat_of_source_empty_BCF h).toBoundaryInitialCoresSpec = ZC :=
  rfl

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
  {bcut bder κ : ℝ} (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
  (hz0 : letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.family.zero.centres = ∅)

/-- **Inhabitant on the empty-family chain** (BIFACE's `emptyBases_BIF`, `emptyInitialCores_BIF`):
the empty cores with saturated faces. -/
def emptyInitialCoresSat_BCF : BoundaryInitialCoresSpecSat C (C.emptyBases_BIF hc hF) :=
  (C.emptyInitialCores_BIF hz0).toSat_of_source_empty_BCF fun _ _ => rfl

/-- The saturated empty cores are BIFACE's empty cores. -/
theorem emptyInitialCoresSat_toSpec_BCF :
    (C.emptyInitialCoresSat_BCF hc hF hz0).toBoundaryInitialCoresSpec =
      C.emptyInitialCores_BIF hz0 :=
  rfl

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
