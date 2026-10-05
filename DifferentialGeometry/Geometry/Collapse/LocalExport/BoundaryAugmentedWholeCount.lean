import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedSupportSlot
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryTransport
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterValidity

/-!
# BCG03: the ACTUAL augmented whole lists `#J_aug(a) ≤ N_TCP + 1` (lane B-COUNT, G3)

Blueprint BCG.0 (`B:8700–8726`: "Add one to the early whole-list and multiplicity constants") and
BCG03 (`B:8960–9131`), draft 61 §2.4 / D61-5, merged with lane BCG-8b's G11
(`BoundaryAugmentedSupportSlot`). G11 proved `#J_aug(a) ≤ N + 1` for ANY interior list of at most
`N` entries; here the interior list is the ACTUAL whole list of the boundary family, so the bound
is the early `N_TCP + 1 = gafMultiplicity` with no parameter `N_int`.

For an original reference `a` (circle, ACTIVE edge `edgeB`, slim centre `j`) the reference domain is
the `g`-ball of `W`, `D_a = B_g(j, C_aρ(j))`, `C_a = 10, 20Δ, 950000Δ = .95L` — the SAME set as in
G11's `J_∂(a) = P.boundarySupportList_BCG8b j C_aρ(j)`. The interior lists are taken in the meeting
form of `D_a` (`imageMeetingList_BCNT Subtype.val`: an interior closed support `S ⊆ W°` meets `D_a`
iff `val '' S ∩ D_a ≠ ∅`), with BCG01's row lists: TCP01 (circle, `edgeB`, slim) at circle
references, EGP02 (`edgeB`, slim) at edge references, SGP01 (slim) at slim references, and the zero
list. By T2/T3's consumer-domain transport (`consumer_domain_completion_BDRY5`: `ĝ = g°` on
`{D ≥ 4}`, BCP04.a, `8C_a ≤ n`), `val '' B_ĝ(j, C_aρ(j)) = D_a`, so these lists ARE the lists of
G1/G2 (`imageMeetingList_eq_BCNT`), hence have at most `N_TCP` entries, and the zero list at most
one. The boundary slot takes the zero slot's place (G11 `ncard_augmentedSupportList_zero_le_BCG8b`:
a member of `J_∂(a)` puts `D_a` off every zero ball, T3's separation): the WHOLE augmented list
`(J_int(a) ⊕ J_0(a)) ⊕ J_∂(a)` has at most `N_TCP + max(#J_0, 1) ≤ N_TCP + 1` entries.

* `imageMeetingList_BCNT`, `imageMeetingList_eq_BCNT` (lists in the meeting form of a set of the
  ambient space), `zeroImageMeetingList_BCNT`, `zeroImageMeetingList_eq_BCNT`;
* `tcp01AugInteriorList_BCNT`, `egp02AugInteriorList_BCNT`, `sgp01AugInteriorList_BCNT` (the
  tagged row lists in `X ⊕ (X ⊕ X)`, `X ⊕ X`, `X`) and their counts
  `LocalPacketsOnB.ncard_tcp01AugInteriorList_BCNT`, `…egp02…`, `…sgp01…`;
* **G3** `bcg03_actual_augmented_count_BFRZ`: on T3B's family `F : LocalPacketsOnBFRZ` on
  `(W°, d_ĝ)` with T3B's tail clauses (nonproduct branch), at every circle / `edgeB` / slim centre,
  `#((J_int(a) ⊕ J_0(a)) ⊕ J_∂(a)) ≤ N_TCP + 1`;
* consumer `bcg03_actual_augmented_count_le_N_BCNT`: under the boundary threshold validity
  (`BoundaryThresholdValidity.N_ge : gafMultiplicity ≤ D.N`) the actual augmented lists are bounded
  by the register's early `N` itself (`N_TCP + 1 = gafMultiplicity`,
  `tcp01SupportBound_add_one_CNT`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### Lists in the meeting form of an ambient set -/

/-- The indices `k ∈ J` whose set `S k` meets `D` after the map `f` (the meeting form of an ambient
reference domain, e.g. `f = Subtype.val : W° → W`, `D = B_g(j, r)`). -/
def imageMeetingList_BCNT {X M : Type*} (f : X → M) (J : Set X) (S : X → Set X) (D : Set M) :
    Set X :=
  {k | k ∈ J ∧ (f '' S k ∩ D).Nonempty}

/-- For injective `f` and `D = f '' B`, the meeting form of `D` is the meeting form of `B`. -/
theorem imageMeetingList_eq_BCNT {X M : Type*} {f : X → M} (hf : Injective f) (J : Set X)
    (S : X → Set X) {B : Set X} {D : Set M} (hD : f '' B = D) :
    imageMeetingList_BCNT f J S D = {k | k ∈ J ∧ (S k ∩ B).Nonempty} := by
  ext k
  simp only [imageMeetingList_BCNT, ← hD, ← image_inter hf, image_nonempty, mem_ofPred_eq]

/-- A meeting list of a finite index set is finite. -/
theorem imageMeetingList_finite_BCNT {X M : Type*} (f : X → M) {J : Set X} (hJ : J.Finite)
    (S : X → Set X) (D : Set M) : (imageMeetingList_BCNT f J S D).Finite :=
  hJ.subset fun _ hk => hk.1

/-- The tagged union of two finite lists is finite. -/
theorem augmentedSupportList_finite_BCNT {α β : Type*} {A : Set α} {B : Set β} (hA : A.Finite)
    (hB : B.Finite) : (augmentedSupportList_BCG8b A B).Finite :=
  (hA.image _).union (hB.image _)

section ZeroImage

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X} {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set X}

/-- The zero centres whose LC31 cutoff support meets `D` after the map `f`. -/
def zeroImageMeetingList_BCNT (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    {M : Type*} (f : X → M) (D : Set M) : Set X :=
  {k | ∃ hk : k ∈ Z.centres, (f '' tsupport (fun y => Calculus.annularCutoff
    Calculus.cutoffProfile ((Z.zero k hk).radial y)) ∩ D).Nonempty}

/-- For injective `f` and `D = f '' B(p, ℓρ(p))`, the zero meeting form of `D` is the zero list of
`B(p, ℓρ(p))`. -/
theorem zeroImageMeetingList_eq_BCNT
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) {M : Type*} {f : X → M}
    (hf : Injective f) {p : X} {ℓ : ℝ} {D : Set M} (hD : f '' ball p (ℓ * ρ p) = D) :
    zeroImageMeetingList_BCNT Z f D = zeroMeetingListOn_BCNT Z p ℓ := by
  ext k
  simp only [zeroImageMeetingList_BCNT, zeroMeetingListOn_BCNT, ← hD, ← image_inter hf,
    image_nonempty, mem_ofPred_eq]

/-- The closed support of an LC31 zero cutoff lies in its zero ball. -/
theorem zero_tsupport_subset_ball_BCNT
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (he : e < 1 / 40)
    {k : X} (hk : k ∈ Z.centres) :
    tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile ((Z.zero k hk).radial y)) ⊆
      ball k (Z.zero k hk).radius := by
  intro x hx
  have h := (zero_cutoff_tsupport_band_BCNT Z he hk hx).2
  have hR := (Z.zero k hk).radius_pos
  rw [mem_ball, dist_comm]
  linarith

end ZeroImage

/-! ### The tagged row lists of a boundary family -/

section RowLists

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- TCP01's interior whole list of a reference domain `D` (meeting form after `f`): circle, `edgeB`
and slim supports, tagged in `X ⊕ (X ⊕ X)`. -/
def tcp01AugInteriorList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {M : Type*} (f : X → M) (D : Set M) : Set (X ⊕ (X ⊕ X)) :=
  augmentedSupportList_BCG8b
    (imageMeetingList_BCNT f F.circle.centres (fun k => tsupport (F.circle.cutoff k)) D)
    (augmentedSupportList_BCG8b
      (imageMeetingList_BCNT f F.edgeB.centres (fun k => tsupport (F.edgeB.cutoff_BAUGA k)) D)
      (imageMeetingList_BCNT f F.slim.centres (fun k => tsupport (F.slim.cutoff_BCNT k)) D))

/-- EGP02's interior whole list of a reference domain `D`: `edgeB` and slim supports, tagged in
`X ⊕ X`. -/
def egp02AugInteriorList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {M : Type*} (f : X → M) (D : Set M) : Set (X ⊕ X) :=
  augmentedSupportList_BCG8b
    (imageMeetingList_BCNT f F.edgeB.centres (fun k => tsupport (F.edgeB.cutoff_BAUGA k)) D)
    (imageMeetingList_BCNT f F.slim.centres (fun k => tsupport (F.slim.cutoff_BCNT k)) D)

/-- SGP01's interior whole list of a reference domain `D`: slim supports. -/
def sgp01AugInteriorList_BCNT
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {M : Type*} (f : X → M) (D : Set M) : Set X :=
  imageMeetingList_BCNT f F.slim.centres (fun k => tsupport (F.slim.cutoff_BCNT k)) D

namespace LocalPacketsOnB

variable (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
  V vs U₁ U₂ Ue₁ Ue₂)

/-- On `D = f '' B(p, r)` (`f` injective) TCP01's tagged interior list has
`|J₂(p, r)| + |J_e(p, r)| + |J_s(p, r)|` entries. -/
theorem ncard_tcp01AugInteriorList_BCNT {M : Type*} {f : X → M} (hf : Injective f) {p : X}
    {r : ℝ} {D : Set M} (hD : f '' ball p r = D) :
    (tcp01AugInteriorList_BCNT F f D).ncard = (bdCircleList_BCNT F p r).ncard +
      (bdEdgeBList_BCNT F p r).ncard + (bdSlimList_BCNT F p r).ncard := by
  have hc := imageMeetingList_eq_BCNT hf F.circle.centres (fun k => tsupport (F.circle.cutoff k)) hD
  have he := imageMeetingList_eq_BCNT hf F.edgeB.centres
    (fun k => tsupport (F.edgeB.cutoff_BAUGA k)) hD
  have hs := imageMeetingList_eq_BCNT hf F.slim.centres
    (fun k => tsupport (F.slim.cutoff_BCNT k)) hD
  unfold tcp01AugInteriorList_BCNT
  rw [hc, he, hs]
  change (augmentedSupportList_BCG8b (bdCircleList_BCNT F p r)
    (augmentedSupportList_BCG8b (bdEdgeBList_BCNT F p r) (bdSlimList_BCNT F p r))).ncard = _
  rw [ncard_augmentedSupportList_BCG8b (F.bdCircleList_finite_BCNT p r)
      (augmentedSupportList_finite_BCNT (F.bdEdgeBList_finite_BCNT p r)
        (F.bdSlimList_finite_BCNT p r)),
    ncard_augmentedSupportList_BCG8b (F.bdEdgeBList_finite_BCNT p r)
      (F.bdSlimList_finite_BCNT p r)]
  ring

/-- On `D = f '' B(p, r)` EGP02's tagged interior list has `|J_e(p, r)| + |J_s(p, r)|` entries. -/
theorem ncard_egp02AugInteriorList_BCNT {M : Type*} {f : X → M} (hf : Injective f) {p : X}
    {r : ℝ} {D : Set M} (hD : f '' ball p r = D) :
    (egp02AugInteriorList_BCNT F f D).ncard =
      (bdEdgeBList_BCNT F p r).ncard + (bdSlimList_BCNT F p r).ncard := by
  have he := imageMeetingList_eq_BCNT hf F.edgeB.centres
    (fun k => tsupport (F.edgeB.cutoff_BAUGA k)) hD
  have hs := imageMeetingList_eq_BCNT hf F.slim.centres
    (fun k => tsupport (F.slim.cutoff_BCNT k)) hD
  unfold egp02AugInteriorList_BCNT
  rw [he, hs]
  exact ncard_augmentedSupportList_BCG8b (F.bdEdgeBList_finite_BCNT p r)
    (F.bdSlimList_finite_BCNT p r)

/-- On `D = f '' B(p, r)` SGP01's interior list is the slim list of `B(p, r)`. -/
theorem sgp01AugInteriorList_eq_BCNT {M : Type*} {f : X → M} (hf : Injective f) {p : X}
    {r : ℝ} {D : Set M} (hD : f '' ball p r = D) :
    sgp01AugInteriorList_BCNT F f D = bdSlimList_BCNT F p r :=
  imageMeetingList_eq_BCNT hf F.slim.centres (fun k => tsupport (F.slim.cutoff_BCNT k)) hD

end LocalPacketsOnB

end RowLists

/-! ### G3 on T3B's family -/

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

/-- **The augmented count at one reference domain, abstract form.** A finite interior list `S`
with at most `N` entries, a zero list `Z` with at most one entry, and a boundary list `Jb` that is
a subsingleton and empties `Z` when occupied: `#((S ⊕ Z) ⊕ Jb) ≤ N + 1`. -/
theorem ncard_augmented_zero_slot_le_BCNT {α γ κ : Type*} {S : Set α} {Z : Set γ} {Jb : Set κ}
    {N : ℕ} (hS : S.Finite) (hSN : S.ncard ≤ N) (hZ : Z.Finite) (hZ1 : Z.ncard ≤ 1)
    (hB : Jb.Subsingleton) (hZB : Jb.Nonempty → Z = ∅) :
    (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b S Z) Jb).ncard ≤ N + 1 := by
  have h := ncard_augmentedSupportList_zero_le_BCG8b hS hZ hB hZB
  have hm : max Z.ncard 1 = 1 := max_eq_right hZ1
  omega

/-- **G3: the ACTUAL augmented whole lists on T3B's family** (BCG03 with BCG.0's "add one"; D61-5
merged with G11). For T3B's final boundary family `F : LocalPacketsOnBFRZ` on `(W°, d_ĝ, ρ)` (its
regions `{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}`) and T3B's tail clauses — `ĝ = g°` on `O ⊇
{D ≥ 4}`, BCP04.a at the member's index `n` (requested `8·950000Δ ≤ n`), the zero balls are actual
`g`-balls, and the nonproduct branch (collar images `{z < 92}` pairwise disjoint and missing every
zero ball) — with G11's and G1's parameter requests: at every circle centre (`D_a = B_g(j, 10ρ(j))`,
TCP01 list), `edgeB` centre (`D_a = B_g(j, 20Δρ(j))`, EGP02 list) and slim centre
(`D_a = B_g(j, 950000Δρ(j))`, SGP01 list), the WHOLE augmented list `(J_int(a) ⊕ J_0(a)) ⊕ J_∂(a)`
of ACTUAL closed supports meeting `D_a` (interior row list, zero list, boundary blocks `F_b`) has at
most `N_TCP + 1` entries. -/
theorem bcg03_actual_augmented_count_BFRZ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {Kc : ℕ} {Ac : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g Kc Ac w₀ εB) (hεB : εB ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz n : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 8 * (950000 * Δ) ≤ n)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) (O : Set (W.pieceInterior ⊤))
    (hO4 : {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary W g x} ⊆ O)
    (hOeq : ∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤))
      (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3)
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM),
      (∀ z (hz : z ∈ F.zero.centres),
        Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
          riemannianBallOf g z.val (F.zero.zero z hz).radius) →
      (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
        Disjoint (riemannianBallOf g z.val (F.zero.zero z hz).radius)
          ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) →
      (∀ j ∈ F.circle.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (tcp01AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (10 * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val (riemannianBallOf g j.val (10 * ρ j))))
          (P.boundarySupportList_BCG8b j.val (10 * ρ j))).ncard ≤ tcp01SupportBound + 1) ∧
      (∀ j ∈ F.edgeB.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (egp02AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (20 * Δ * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val
              (riemannianBallOf g j.val (20 * Δ * ρ j))))
          (P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j))).ncard ≤ tcp01SupportBound + 1) ∧
      ∀ j ∈ F.slim.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (sgp01AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (950000 * Δ * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val
              (riemannianBallOf g j.val (950000 * Δ * ρ j))))
          (P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j))).ncard ≤
            tcp01SupportBound + 1 := by
  intro _ oM F hzball hsep
  let instM_BCNT : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x := fun x hx => hOeq x (hO4 hx)
  -- consumer-domain transport: `val '' B_ĝ(j, Cρ(j)) = B_g(j, Cρ(j))` for `C ≤ 950000Δ`, `j ∈ U₁`
  have hball : ∀ (Ca : ℝ), 0 ≤ Ca → Ca ≤ 950000 * Δ → ∀ j : W.pieceInterior ⊤,
      j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} →
      Subtype.val '' Metric.ball j (Ca * ρ j) = riemannianBallOf g j.val (Ca * ρ j) := by
    intro Ca hCa hCaΔ j hj
    have hj5 : ENNReal.ofReal 5 < distanceToBoundary W g j :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num)) hj
    have h := (consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ (C := Ca / 4) (by positivity) hbcp
      (by linarith) j hj5).1
    rwa [show 4 * (Ca / 4) * ρ j = Ca * ρ j by ring] at h
  -- the zero list is emptied by an occupied boundary slot
  have hzero : ∀ (Ca : ℝ), Ca ≤ 95 / 100 * (1000000 * Δ) → ∀ j : W.pieceInterior ⊤,
      (P.boundarySupportList_BCG8b j.val (Ca * ρ j)).Nonempty →
      zeroImageMeetingList_BCNT F.zero Subtype.val (riemannianBallOf g j.val (Ca * ρ j)) = ∅ := by
    rintro Ca hCa j ⟨bb, hbb⟩
    have hD := (P.bcg03_mem_boundarySupportList_BCG8b hεB hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq hCa
      (fun z : {z // z ∈ F.zero.centres} => z.1.val) (fun z => (F.zero.zero z.1 z.2).radius)
      (fun z i => hsep z.1 z.2 i) hbb).2.2
    rw [Set.eq_empty_iff_forall_notMem]
    rintro k ⟨hk, y, ⟨x, hx, rfl⟩, hyD⟩
    have hxb : x ∈ Metric.ball k (F.zero.zero k hk).radius :=
      zero_tsupport_subset_ball_BCNT F.zero he hk hx
    have hxg : x.val ∈ riemannianBallOf g k.val (F.zero.zero k hk).radius := by
      rw [← hzball k hk]
      exact ⟨x, hxb, rfl⟩
    exact Set.disjoint_left.mp (hD ⟨k, hk⟩) hyD hxg
  -- the zero list of `D_a` has at most one entry
  have hzone : ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 950000 * Δ → ∀ j : W.pieceInterior ⊤,
      j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} →
      (zeroImageMeetingList_BCNT F.zero Subtype.val
          (riemannianBallOf g j.val (ℓ * ρ j))).ncard ≤ 1 ∧
        (zeroImageMeetingList_BCNT F.zero Subtype.val
          (riemannianBallOf g j.val (ℓ * ρ j))).Finite := by
    intro ℓ hℓ hℓΔ j hj
    rw [zeroImageMeetingList_eq_BCNT F.zero Subtype.val_injective (hball ℓ hℓ.le hℓΔ j hj)]
    exact ⟨zero_list_le_one_BFRZ F hΛ.le hΔ hLΛ he hT j hℓ hℓΔ,
      F.zero.finite_centres.subset fun k hk => hk.choose⟩
  have hsub : ∀ (Ca : ℝ), Ca ≤ 95 / 100 * (1000000 * Δ) → ∀ j : W.pieceInterior ⊤,
      (P.boundarySupportList_BCG8b j.val (Ca * ρ j)).Subsingleton := fun Ca hCa j =>
    P.boundarySupportList_subsingleton_BCG8b hεB hdisj hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq hCa j.val
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have hjU : j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} :=
      (F.circle.centres_subset hj).1
    have hD := hball 10 (by norm_num) (by linarith) j hjU
    have hS := F.toLocalPacketsOnB.ncard_tcp01AugInteriorList_BCNT Subtype.val_injective hD
    have hcount := (tcp01_support_count_BFRZ F hΛ.le hΔ hLΛ hLmax he hT j).1
    obtain ⟨hZ1, hZf⟩ := hzone 10 (by norm_num) (by linarith) j hjU
    refine ncard_augmented_zero_slot_le_BCNT ?_ (hS.symm ▸ hcount) hZf hZ1
      (hsub 10 (by linarith) j) (hzero 10 (by linarith) j)
    exact augmentedSupportList_finite_BCNT
      (imageMeetingList_finite_BCNT _ F.circle.finite_centres _ _)
      (augmentedSupportList_finite_BCNT (imageMeetingList_finite_BCNT _ F.edgeB.finite_centres _ _)
        (imageMeetingList_finite_BCNT _ F.slim.finite_centres _ _))
  · have hjU : j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} := by
      have h20 := F.edgeB.centres_subset hj
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num)) h20
    have hD := hball (20 * Δ) (by positivity) (by linarith) j hjU
    have hS := F.toLocalPacketsOnB.ncard_egp02AugInteriorList_BCNT Subtype.val_injective hD
    have hcount := (egp02_whole_count_BFRZ F hΛ.le hΔ hLΛ hLmax he hT j).1
    obtain ⟨hZ1, hZf⟩ := hzone (20 * Δ) (by positivity) (by linarith) j hjU
    refine ncard_augmented_zero_slot_le_BCNT ?_ (hS.symm ▸ hcount) hZf hZ1
      (hsub (20 * Δ) (by linarith) j) (hzero (20 * Δ) (by linarith) j)
    exact augmentedSupportList_finite_BCNT
      (imageMeetingList_finite_BCNT _ F.edgeB.finite_centres _ _)
      (imageMeetingList_finite_BCNT _ F.slim.finite_centres _ _)
  · have hjU : j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} :=
      (F.slim.centres_subset hj).1
    have hD := hball (950000 * Δ) (by positivity) le_rfl j hjU
    have hS := F.toLocalPacketsOnB.sgp01AugInteriorList_eq_BCNT Subtype.val_injective hD
    have hcount := (sgp01_whole_count_BFRZ F hΛ.le hΔ hLΛ hLmax he hT j).1
    obtain ⟨hZ1, hZf⟩ := hzone (950000 * Δ) (by positivity) le_rfl j hjU
    refine ncard_augmented_zero_slot_le_BCNT ?_ (hS.symm ▸ hcount) hZf hZ1
      (hsub (950000 * Δ) (by linarith) j) (hzero (950000 * Δ) (by linarith) j)
    exact imageMeetingList_finite_BCNT _ F.slim.finite_centres _ _

/-- **Consumer: the register's early `N` bounds the ACTUAL augmented lists.** Under the boundary
threshold validity (`BoundaryThresholdValidity.N_ge : gafMultiplicity ≤ D.N`, PR01 on the augmented
constants), G3's whole augmented lists at every circle / `edgeB` / slim reference of T3B's family
have at most `D.N` entries (`N_TCP + 1 = gafMultiplicity`, `tcp01SupportBound_add_one_CNT`). -/
theorem bcg03_actual_augmented_count_le_N_BCNT {Kv : ℕ} {Av : ℝ → ℝ} {Dr : BoundaryEarlyData}
    {Tr : BoundaryThresholds Dr} (hv : BoundaryThresholdValidity.{u} Kv Av Dr Tr)
    (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {Kc : ℕ} {Ac : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g Kc Ac w₀ εB) (hεB : εB ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz n : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 8 * (950000 * Δ) ≤ n)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) (O : Set (W.pieceInterior ⊤))
    (hO4 : {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary W g x} ⊆ O)
    (hOeq : ∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤))
      (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3)
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM),
      (∀ z (hz : z ∈ F.zero.centres),
        Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
          riemannianBallOf g z.val (F.zero.zero z hz).radius) →
      (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
        Disjoint (riemannianBallOf g z.val (F.zero.zero z hz).radius)
          ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) →
      (∀ j ∈ F.circle.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (tcp01AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (10 * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val (riemannianBallOf g j.val (10 * ρ j))))
          (P.boundarySupportList_BCG8b j.val (10 * ρ j))).ncard ≤ Dr.N) ∧
      (∀ j ∈ F.edgeB.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (egp02AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (20 * Δ * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val
              (riemannianBallOf g j.val (20 * Δ * ρ j))))
          (P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j))).ncard ≤ Dr.N) ∧
      ∀ j ∈ F.slim.centres,
        (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b
            (sgp01AugInteriorList_BCNT F.toLocalPacketsOnB Subtype.val
              (riemannianBallOf g j.val (950000 * Δ * ρ j)))
            (zeroImageMeetingList_BCNT F.zero Subtype.val
              (riemannianBallOf g j.val (950000 * Δ * ρ j))))
          (P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j))).ncard ≤ Dr.N := by
  intro hc oM F hzball hsep
  have hN : tcp01SupportBound + 1 ≤ Dr.N := tcp01SupportBound_add_one_CNT ▸ hv.N_ge
  obtain ⟨h1, h2, h3⟩ := bcg03_actual_augmented_count_BFRZ W g P hεB hdisj ρ hρ hΛ hΔ hβ₁ hlip
    hcol hΛΔ hreq hLΛ hLmax he hT hbcp hn ĝ O hO4 hOeq hc oM F hzball hsep
  exact ⟨fun j hj => (h1 j hj).trans hN, fun j hj => (h2 j hj).trans hN,
    fun j hj => (h3 j hj).trans hN⟩

end DifferentialGeometry.Geometry.Collapse
