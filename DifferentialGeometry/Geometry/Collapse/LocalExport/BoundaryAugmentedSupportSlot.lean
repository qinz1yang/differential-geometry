import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsZero
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFR
import DifferentialGeometry.Geometry.Fibration.ActualWholeSupportCount

/-!
# BCG03: the whole boundary support lists and the augmented count `N + 1` (lane BCG-8b, G11)

Blueprint 207B, BCG.0 (`B:8700–8726`: "Add one to the early whole-list and multiplicity
constants"), BCG01 (`B:8727–8820`) and BCG03 (`B:8960–9131`: "Square summation with one extra
block proves the same early modulus formulas with augmented `N, P`"); external draft 61 §2.4 and
disposition D61-5. For an original reference `a` (circle, ACTIVE edge `edgeB`, slim) the reference
domain is `D_a = B_g(p_a, C_a R_a)`, `R_a = ρ(p_a)`, `C_a = 10, 20Δ, .95L`, `L = 10⁶Δ` (BCG01.a),
and

  `J_∂(a) = {b | tsupport(P.block b) ∩ D_a ≠ ∅}`

with `P.block b = F_b = 𝓑(η_b)` the LC88 collar block (BCG.0). The list is a DEFINITION with
two-sided membership (`mem_boundarySupportList_BCG8b`), never a chosen finite subset; its members
are exactly the `b` for which BCG02's joint value-and-differential clauses (BCG-8 G10,
`lc88_boundary_values_differential_BFR_BCG8`, meeting form
`∃ x ∈ tsupport F_b, d_g(p_a, x) < C_aR_a`,
`mem_boundarySupportList_iff_edist_BCG8b`) supply the row `A_{a,b}`. It counts closed supports
meeting the WHOLE `D_a` (support end points where the cutoff vanishes included), not a pointwise
multiplicity and not the number of boundary components.

* `BoundaryCollarPacket.boundarySupportList_BCG8b`, `augmentedSupportList_BCG8b` (`J_aug(a)`, the
  interior whole list and `J_∂(a)` in `α ⊕ Fin P.cusp.count`), their membership lemmas, and the
  counting kernels `ncard_augmentedSupportList_BCG8b`, `ncard_augmentedSupportList_le_succ_BCG8b`,
  `ncard_augmentedSupportList_zero_le_BCG8b` (with a zero list that is empty whenever `J_∂(a)` is
  occupied: `≤ |S| + max |Z| 1`).
* LC88 boundary data, nonproduct case, `r_∂ = β₁³/1000`, request `β₁³·10⁶Δ < 1`, `C ≤ .95L`:
  `BoundaryCollarPacket.boundarySupportList_subsingleton_BCG8b`,
  `BoundaryCollarPacket.ncard_boundarySupportList_le_one_BCG8b` (`#J_∂(a) ≤ 1`),
  `BoundaryCollarPacket.bcg03_mem_boundarySupportList_BCG8b` (`b ∈ J_∂(a)` ⇒ `R_a < 2r_∂`,
  `D_a ⊆ e_b{19 < z < 91} ∩ {19 < η_b < 91}`, `D_a` misses every zero ball missing the enlarged
  collars — hence every zero support), `BoundaryCollarPacket.ncard_augmented_le_BCG8b`
  (`#J_aug(a) ≤ N + 1`), `BoundaryCollarPacket.ncard_augmented_zero_le_BCG8b` (zero-slot form).
  Uses BCG01's kernels `subsingleton_supports_meeting_reference_domain`,
  `bcg01_zero_exclusion_BCG1`, `bcg01_parameters_BCG1`.
* `LocalPacketsOnB.bcg03_boundary_support_lists_BCG8b`: the instance at the three reference
  families of a boundary family on `W°` (circle `C = 10`, `F.edgeB` `C = 20Δ`, slim
  `C = 950000Δ = .95L`), the zero balls `B_g(z, r_z)` of `F.zero`.
* Consumer `bcg03_augmented_count_BFR_BCG8b`: on the final boundary family `F : LocalPacketsOnBFR`
  (T3B_IDX2's family), with `N_int := tcp01SupportBound` (`N_TCP`, lane C14-COUNTb), every interior
  whole list of at most `N_TCP` entries gives `#J_aug(a) ≤ N_TCP + 1` at every reference.

Hypotheses are those of T3B_IDX2's tail (`lc88_boundary_packets_BFR_BCG5_IDX2`: `Λ`-Lipschitz `ρ`,
collar smallness `ρ ≤ β₁³/2000` on `z ≤ 96`, `100ΔΛ ≤ 10⁻⁶`, the nonproduct separation branch) plus
BCG01's request `β₁³·10⁶Δ < 1` (a request of BCG-8 G10's sequence statement already).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The augmented list and its counting kernels -/

/-- **The augmented whole support list** `J_aug(a)`: the interior whole list `Jint` and the boundary
list `Jb`, as one set of `α ⊕ β`. -/
def augmentedSupportList_BCG8b {α β : Type*} (Jint : Set α) (Jb : Set β) : Set (α ⊕ β) :=
  Sum.inl '' Jint ∪ Sum.inr '' Jb

/-- An interior index is in `J_aug(a)` exactly when it is in the interior list. -/
theorem inl_mem_augmentedSupportList_BCG8b {α β : Type*} {Jint : Set α} {Jb : Set β} {i : α} :
    Sum.inl i ∈ augmentedSupportList_BCG8b Jint Jb ↔ i ∈ Jint := by
  constructor
  · rintro (⟨i', hi', hii'⟩ | ⟨b, -, hb⟩)
    · rwa [← Sum.inl_injective hii']
    · exact absurd hb Sum.inr_ne_inl
  · exact fun hi => Or.inl ⟨i, hi, rfl⟩

/-- A boundary index is in `J_aug(a)` exactly when it is in the boundary list. -/
theorem inr_mem_augmentedSupportList_BCG8b {α β : Type*} {Jint : Set α} {Jb : Set β} {b : β} :
    Sum.inr b ∈ augmentedSupportList_BCG8b Jint Jb ↔ b ∈ Jb := by
  constructor
  · rintro (⟨i, -, hi⟩ | ⟨b', hb', hbb'⟩)
    · exact absurd hi Sum.inl_ne_inr
    · rwa [← Sum.inr_injective hbb']
  · exact fun hb => Or.inr ⟨b, hb, rfl⟩

/-- `#J_aug(a) = #Jint + #Jb` for finite lists. -/
theorem ncard_augmentedSupportList_BCG8b {α β : Type*} {Jint : Set α} {Jb : Set β}
    (hJ : Jint.Finite) (hB : Jb.Finite) :
    (augmentedSupportList_BCG8b Jint Jb).ncard = Jint.ncard + Jb.ncard := by
  have hdisj : Disjoint (Sum.inl '' Jint : Set (α ⊕ β)) (Sum.inr '' Jb) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    exact Sum.inr_ne_inl hb
  rw [augmentedSupportList_BCG8b, Set.ncard_union_eq hdisj (hJ.image _) (hB.image _),
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

/-- **The augmented count `N + 1`.** An interior list of at most `N` entries and a boundary list
with at most ONE entry give `#J_aug(a) ≤ N + 1`. -/
theorem ncard_augmentedSupportList_le_succ_BCG8b {α β : Type*} {Jint : Set α} {Jb : Set β}
    {N : ℕ} (hJ : Jint.Finite) (hJN : Jint.ncard ≤ N) (hB : Jb.Subsingleton) :
    (augmentedSupportList_BCG8b Jint Jb).ncard ≤ N + 1 := by
  rw [ncard_augmentedSupportList_BCG8b hJ hB.finite]
  have h1 : Jb.ncard ≤ 1 := (Set.ncard_le_one hB.finite).mpr fun a ha b hb => hB ha hb
  omega

/-- **The boundary slot takes the zero slot's place.** With a zero list `Z` that is empty whenever
the (at most one) boundary slot is occupied, `J_aug(a) = (S ⊕ Z) ⊕ Jb` has at most
`#S + max #Z 1` entries. -/
theorem ncard_augmentedSupportList_zero_le_BCG8b {α γ β : Type*} {S : Set α} {Z : Set γ}
    {Jb : Set β} (hS : S.Finite) (hZ : Z.Finite) (hB : Jb.Subsingleton)
    (hZB : Jb.Nonempty → Z = ∅) :
    (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b S Z) Jb).ncard ≤
      S.ncard + max Z.ncard 1 := by
  have hSZ : (augmentedSupportList_BCG8b S Z).Finite := (hS.image _).union (hZ.image _)
  rw [ncard_augmentedSupportList_BCG8b hSZ hB.finite, ncard_augmentedSupportList_BCG8b hS hZ]
  rcases Jb.eq_empty_or_nonempty with hB0 | hB0
  · rw [hB0, Set.ncard_empty]
    have := le_max_left Z.ncard 1
    omega
  · rw [hZB hB0, Set.ncard_empty]
    have h1 : Jb.ncard ≤ 1 := (Set.ncard_le_one hB.finite).mpr fun a ha b hb => hB ha hb
    have := le_max_right (0 : ℕ) 1
    omega

/-! ## The whole boundary support list of one reference domain (LC88 boundary data) -/

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **The whole boundary support list** `J_∂` of the reference domain `D = B_g(p, r)`: every
boundary component whose closed support `tsupport F_b` meets `D` (draft 61 §2.4, D61-5). -/
def boundarySupportList_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε) (p : W.Carrier) (r : ℝ) :
    Set (Fin P.cusp.count) :=
  {b | (tsupport (P.block b) ∩ riemannianBallOf g p r).Nonempty}

/-- Two-sided membership of `J_∂`: `b ∈ J_∂` iff `tsupport F_b ∩ D ≠ ∅`. -/
theorem mem_boundarySupportList_BCG8b {P : BoundaryCollarPacket W g K A w₀ ε} {p : W.Carrier}
    {r : ℝ} {b : Fin P.cusp.count} :
    b ∈ P.boundarySupportList_BCG8b p r ↔
      (tsupport (P.block b) ∩ riemannianBallOf g p r).Nonempty :=
  Iff.rfl

/-- Two-sided membership of `J_∂` in the meeting form of BCG02 (BCG-7 G6, BCG-8 G8–G10). -/
theorem mem_boundarySupportList_iff_edist_BCG8b {P : BoundaryCollarPacket W g K A w₀ ε}
    {p : W.Carrier} {r : ℝ} {b : Fin P.cusp.count} :
    b ∈ P.boundarySupportList_BCG8b p r ↔
      ∃ x ∈ tsupport (P.block b), riemannianEDistOf g p x < ENNReal.ofReal r :=
  ⟨fun ⟨x, hx, hxD⟩ => ⟨x, hx, hxD⟩, fun ⟨x, hx, hxD⟩ => ⟨x, hx, hxD⟩⟩

/-- **At most ONE boundary slot** (BCG01): in the nonproduct case, with `r_∂ = β₁³/1000`,
`L = 10⁶Δ`, `C ≤ .95L`, the whole boundary support list of `D = B_g(p, Cρ(p))` is a subsingleton. -/
theorem boundarySupportList_subsingleton_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ Δ β₁ C : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ)
    (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) (p : W.Carrier) :
    (P.boundarySupportList_BCG8b p (C * ρ p)).Subsingleton := by
  obtain ⟨hL, hΛC, hr, -⟩ := bcg01_parameters_BCG1 hΛ hΔ hβ₁ hΛΔ hC hreq (le_refl _)
  have hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < β₁ ^ 3 / 1000 := fun i q hq =>
    (bcg01_parameters_BCG1 hΛ hΔ hβ₁ hΛΔ hC hreq (hcol i q hq)).2.2.2
  intro i hi j hj
  exact P.subsingleton_supports_meeting_reference_domain hε hdisj hρ hΛ.le hlip hsmall hL hC hΛC
    hr p ((mem_boundarySupportList_iff_edist_BCG8b (P := P)).mp hi)
    ((mem_boundarySupportList_iff_edist_BCG8b (P := P)).mp hj)

/-- **`#J_∂(a) ≤ 1`** under the hypotheses of `boundarySupportList_subsingleton_BCG8b`. -/
theorem ncard_boundarySupportList_le_one_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ Δ β₁ C : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ)
    (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) (p : W.Carrier) :
    (P.boundarySupportList_BCG8b p (C * ρ p)).ncard ≤ 1 :=
  (Set.ncard_le_one (Set.toFinite _)).mpr fun _ ha _ hb =>
    P.boundarySupportList_subsingleton_BCG8b hε hdisj hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq hC p ha hb

/-- **A member of `J_∂(a)`** (BCG01.b with BCP05): with `r_∂ = β₁³/1000`, `C ≤ .95L`, if `b ∈ J_∂`
of `D = B_g(p, Cρ(p))` then `ρ(p) < 2r_∂ = β₁³/500`, `D` lies in `e_b{19 < z < 91}` and in
`{19 < η_b < 91}` (the SAME height `P.height b`), and `D` misses every zero ball `B_g(c_k, R_k)`
that misses the enlarged collars `e_i{z < 92}`. -/
theorem bcg03_mem_boundarySupportList_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 4) {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ Δ β₁ C : ℝ} (hΛ : 0 < Λ)
    (hΔ : 0 < Δ) (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) {ι : Type*} (c : ι → W.Carrier) (R : ι → ℝ)
    (hsep : ∀ k (i : Fin P.cusp.count), Disjoint (riemannianBallOf g (c k) (R k))
      ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) {p : W.Carrier}
    {b : Fin P.cusp.count} (hb : b ∈ P.boundarySupportList_BCG8b p (C * ρ p)) :
    ρ p < β₁ ^ 3 / 500 ∧
      (∀ y ∈ riemannianBallOf g p (C * ρ p), ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧
        19 < q.2.val 0 ∧ q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91) ∧
      ∀ k, Disjoint (riemannianBallOf g p (C * ρ p)) (riemannianBallOf g (c k) (R k)) := by
  obtain ⟨hL, hΛC, hr, -⟩ := bcg01_parameters_BCG1 hΛ hΔ hβ₁ hΛΔ hC hreq (le_refl _)
  have hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < β₁ ^ 3 / 1000 := fun i q hq =>
    (bcg01_parameters_BCG1 hΛ hΔ hβ₁ hΛΔ hC hreq (hcol i q hq)).2.2.2
  obtain ⟨hρp, hband, hzero⟩ := P.bcg01_zero_exclusion_BCG1 hε hρ hΛ.le hlip hsmall hL hC hΛC hr
    ((mem_boundarySupportList_iff_edist_BCG8b (P := P)).mp hb) c R (fun k => hsep k b)
  exact ⟨by linarith only [hρp], hband, hzero⟩

/-- **`#J_aug(a) ≤ N + 1`** at one reference domain `D = B_g(p, Cρ(p))`: under the hypotheses of
`boundarySupportList_subsingleton_BCG8b`, every interior whole list of at most `N` entries has an
augmented list (with `J_∂(a)`) of at most `N + 1` entries. -/
theorem ncard_augmented_le_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ Δ β₁ C : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ)
    (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) (p : W.Carrier) {α : Type*} {Jint : Set α} {N : ℕ}
    (hJ : Jint.Finite) (hJN : Jint.ncard ≤ N) :
    (augmentedSupportList_BCG8b Jint (P.boundarySupportList_BCG8b p (C * ρ p))).ncard ≤ N + 1 :=
  ncard_augmentedSupportList_le_succ_BCG8b hJ hJN
    (P.boundarySupportList_subsingleton_BCG8b hε hdisj hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq hC p)

/-- **`#J_aug(a)` with the zero slot.** Under the hypotheses of
`boundarySupportList_subsingleton_BCG8b`, for finitely many zero balls `B_g(c_k, R_k)` missing the
enlarged collars and every finite list `S`: the augmented list `(S ⊕ Z_D) ⊕ J_∂`, `Z_D` the zero
balls meeting `D = B_g(p, Cρ(p))`, has at most `#S + max #Z_D 1` entries. -/
theorem ncard_augmented_zero_le_BCG8b (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ Δ β₁ C : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ)
    (hβ₁ : 0 < β₁)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β₁ ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β₁ ^ 3 * (1000000 * Δ) < 1)
    (hC : C ≤ 95 / 100 * (1000000 * Δ)) {ι : Type*} [Finite ι] (c : ι → W.Carrier) (R : ι → ℝ)
    (hsep : ∀ k (i : Fin P.cusp.count), Disjoint (riemannianBallOf g (c k) (R k))
      ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) (p : W.Carrier)
    {α : Type*} {S : Set α} (hS : S.Finite) :
    (augmentedSupportList_BCG8b (augmentedSupportList_BCG8b S {k : ι |
        (riemannianBallOf g (c k) (R k) ∩ riemannianBallOf g p (C * ρ p)).Nonempty})
      (P.boundarySupportList_BCG8b p (C * ρ p))).ncard ≤
      S.ncard + max {k : ι |
        (riemannianBallOf g (c k) (R k) ∩ riemannianBallOf g p (C * ρ p)).Nonempty}.ncard 1 := by
  refine ncard_augmentedSupportList_zero_le_BCG8b hS (Set.toFinite _)
    (P.boundarySupportList_subsingleton_BCG8b hε hdisj hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq hC p)
    fun ⟨b, hb⟩ => ?_
  have hzero := (P.bcg03_mem_boundarySupportList_BCG8b hε hρ hΛ hΔ hβ₁ hlip hcol hΛΔ hreq hC c R
    hsep hb).2.2
  rw [Set.eq_empty_iff_forall_notMem]
  rintro k ⟨y, hyk, hyD⟩
  exact Set.disjoint_left.mp (hzero k) hyD hyk

end BoundaryCollarPacket

/-! ## The instance at the three reference families of a boundary family -/

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG03's whole boundary support lists at the references of a boundary family.** For a boundary
family `F : LocalPacketsOnB` on `(W°, d_ĝ, ρ)` and the LC88 data of T3B's tail (nonproduct case,
`F`'s zero balls `B_g(z, r_z)` missing the enlarged collars), at every circle centre
(`D = B_g(j, 10ρ(j))`), every ACTIVE edge centre of `F.edgeB` (`D = B_g(j, 20Δρ(j))`) and every slim
centre (`D = B_g(j, 950000Δρ(j))`): `J_∂` is a subsingleton, and every member `b` has
`ρ(j) < 2r_∂ = β₁³/500`, `D ⊆ {19 < η_b < 91}` and `D` missing every zero ball of `F`. -/
theorem LocalPacketsOnB.bcg03_boundary_support_lists_BCG8b (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ εB) (hεB : εB ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤))
      (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
      (letI := F.instMetricN
       letI := F.instChartedN
       letI := F.instMetricC
       ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
        Disjoint (riemannianBallOf g z.val (F.zero.zero z hz).radius)
          ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) →
      letI := F.instMetricN
      letI := F.instChartedN
      letI := F.instMetricC
      (∀ j ∈ F.circle.centres,
        (P.boundarySupportList_BCG8b j.val (10 * ρ j)).Subsingleton ∧
        ∀ bb ∈ P.boundarySupportList_BCG8b j.val (10 * ρ j),
          ρ j < β 1 ^ 3 / 500 ∧
          (∀ y ∈ riemannianBallOf g j.val (10 * ρ j), 19 < P.height bb y ∧ P.height bb y < 91) ∧
          ∀ z (hz : z ∈ F.zero.centres),
            Disjoint (riemannianBallOf g j.val (10 * ρ j))
              (riemannianBallOf g z.val (F.zero.zero z hz).radius)) ∧
      (∀ j ∈ F.edgeB.centres,
        (P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j)).Subsingleton ∧
        ∀ bb ∈ P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j),
          ρ j < β 1 ^ 3 / 500 ∧
          (∀ y ∈ riemannianBallOf g j.val (20 * Δ * ρ j),
            19 < P.height bb y ∧ P.height bb y < 91) ∧
          ∀ z (hz : z ∈ F.zero.centres),
            Disjoint (riemannianBallOf g j.val (20 * Δ * ρ j))
              (riemannianBallOf g z.val (F.zero.zero z hz).radius)) ∧
      ∀ j ∈ F.slim.centres,
        (P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j)).Subsingleton ∧
        ∀ bb ∈ P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j),
          ρ j < β 1 ^ 3 / 500 ∧
          (∀ y ∈ riemannianBallOf g j.val (950000 * Δ * ρ j),
            19 < P.height bb y ∧ P.height bb y < 91) ∧
          ∀ z (hz : z ∈ F.zero.centres),
            Disjoint (riemannianBallOf g j.val (950000 * Δ * ρ j))
              (riemannianBallOf g z.val (F.zero.zero z hz).radius) := by
  intro _ U₁ U₂ Ue₁ Ue₂ F hsep
  let instM_BCG8b : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  let _ := F.instMetricN
  let _ := F.instChartedN
  let _ := F.instMetricC
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have key : ∀ (C : ℝ), C ≤ 95 / 100 * (1000000 * Δ) → ∀ p : W.pieceInterior ⊤,
      (P.boundarySupportList_BCG8b p.val (C * ρ p)).Subsingleton ∧
      ∀ bb ∈ P.boundarySupportList_BCG8b p.val (C * ρ p),
        ρ p < β 1 ^ 3 / 500 ∧
        (∀ y ∈ riemannianBallOf g p.val (C * ρ p), 19 < P.height bb y ∧ P.height bb y < 91) ∧
        ∀ z (hz : z ∈ F.zero.centres),
          Disjoint (riemannianBallOf g p.val (C * ρ p))
            (riemannianBallOf g z.val (F.zero.zero z hz).radius) := by
    intro C hC p
    refine ⟨P.boundarySupportList_subsingleton_BCG8b hεB hdisj hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq hC
      p.val, fun bb hbb => ?_⟩
    obtain ⟨h1, h2, h3⟩ := P.bcg03_mem_boundarySupportList_BCG8b hεB hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ
      hreq hC (fun z : {z // z ∈ F.zero.centres} => z.1.val)
      (fun z => (F.zero.zero z.1 z.2).radius) (fun z i => hsep z.1 z.2 i) hbb
    refine ⟨h1, fun y hy => ?_, fun z hz => h3 ⟨z, hz⟩⟩
    obtain ⟨q, -, -, -, -, hy1, hy2⟩ := h2 y hy
    exact ⟨hy1, hy2⟩
  refine ⟨fun j _ => key 10 (by linarith only [hΔ]) j,
    fun j _ => key (20 * Δ) (by linarith only [hΔ]) j,
    fun j _ => key (950000 * Δ) (by linarith only [hΔ]) j⟩

/-- **Consumer: `#J_aug(a) ≤ N_TCP + 1` at every reference of the final boundary family.** For the
final boundary family `F : LocalPacketsOnBFR` (T3B_IDX2's family) on `(W°, d_ĝ, ρ)` and the LC88
data of T3B's tail, with `N_int := tcp01SupportBound` (`N_TCP`, lane C14-COUNTb): at every circle
centre, ACTIVE edge centre and slim centre, every interior whole list of at most `N_TCP` entries has
`#J_aug(a) ≤ N_TCP + 1`. -/
theorem bcg03_augmented_count_BFR_BCG8b (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
    (P : BoundaryCollarPacket W g K A w₀ εB) (hεB : εB ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ₁ : 0 < β 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hcol : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤))
      (F : LocalPacketsOnBFR (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          U₁ U₂ Ue₁ Ue₂)
      {α : Type} {Jint : Set α}, Jint.Finite → Jint.ncard ≤ tcp01SupportBound →
      (∀ j ∈ F.circle.centres,
        (augmentedSupportList_BCG8b Jint (P.boundarySupportList_BCG8b j.val (10 * ρ j))).ncard ≤
          tcp01SupportBound + 1) ∧
      (∀ j ∈ F.edgeB.centres,
        (augmentedSupportList_BCG8b Jint
          (P.boundarySupportList_BCG8b j.val (20 * Δ * ρ j))).ncard ≤ tcp01SupportBound + 1) ∧
      ∀ j ∈ F.slim.centres,
        (augmentedSupportList_BCG8b Jint
          (P.boundarySupportList_BCG8b j.val (950000 * Δ * ρ j))).ncard ≤
            tcp01SupportBound + 1 := by
  intro _ U₁ U₂ Ue₁ Ue₂ F α Jint hJ hJN
  let instM_BCG8b : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  refine ⟨fun j _ => ?_, fun j _ => ?_, fun j _ => ?_⟩
  · exact P.ncard_augmented_le_BCG8b hεB hdisj hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq
      (by linarith only [hΔ]) j.val hJ hJN
  · exact P.ncard_augmented_le_BCG8b hεB hdisj hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq
      (by linarith only [hΔ]) j.val hJ hJN
  · exact P.ncard_augmented_le_BCG8b hεB hdisj hρ hΛ hΔ0 hβ₁ hlip hcol hΛΔ hreq
      (by linarith only [hΔ]) j.val hJ hJN

end DifferentialGeometry.Geometry.Collapse
