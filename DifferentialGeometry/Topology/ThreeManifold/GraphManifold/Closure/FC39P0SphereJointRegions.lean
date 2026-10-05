import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointShell

/-!
# FC39 producer, packet P0 (gate 1): the joint S³ configuration, regions and the cover

The set clauses of `JunctionsV2` (§5.6, §5.7) that join the edge kind and the circle kind of the
S³ data, on top of the slim / zero clauses of `FC39P0SphereSlimRegions.lean`:

* `sphere_relInt_edge`: `int_{M₂} P = P \ M₃`, hence `sphere_region_eq` (`region_eq`:
  `M₃ = M₂ \ int_{M₂} P = R`);
* `sphere_horizontalDisks_eq`: the horizontal disks are `P ∩ ∂M₂`; `sphere_relInt_horizontal`:
  `int_{∂M₂} H = H \ M₃`, hence `sphere_region_boundary` (`region_boundary`:
  `M₃ ∩ ∂M₂ = ∂M₂ \ int_{∂M₂} H`);
* `sphere_cover` (`cover`) and `sphere_interiors_disjoint` (`interiors_disjoint`).

Tool: `relInt_eq_diff_region_JOINT` — a relative interior against the closed region `M₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## Relative interiors against the circle region -/

/-- **A relative interior against the closed region `M₃`**: for `X ⊆ A` with `A \ M₃ ⊆ X` and every
point of `X ∩ M₃` a limit of `A \ X`, the relative interior of `X` in `A` is `X \ M₃`. -/
theorem relInt_eq_diff_region_JOINT {A X : Set sphereW.Carrier} (hXA : X ⊆ A)
    (hcov : A \ sphereCircleBundle.region ⊆ X)
    (hlim : ∀ p ∈ X ∩ sphereCircleBundle.region, p ∈ closure (A \ X)) :
    relInt A X = X \ sphereCircleBundle.region := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hpX : p.1 ∈ X := interior_subset (s := Subtype.val ⁻¹' X) hp
    refine ⟨hpX, fun hpR => ?_⟩
    obtain ⟨U, hU, hUX⟩ := (mem_nhds_subtype _ _ _).1 (mem_interior_iff_mem_nhds.1 hp)
    obtain ⟨z, hzU, hzA, hzX⟩ := mem_closure_iff_nhds.1 (hlim p.1 ⟨hpX, hpR⟩) U hU
    exact hzX (hUX (show (⟨z, hzA⟩ : A) ∈ Subtype.val ⁻¹' U from hzU))
  · rintro p ⟨hpX, hpR⟩
    refine ⟨⟨p, hXA hpX⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds]
    refine (mem_nhds_subtype _ _ _).2 ⟨sphereCircleBundle.regionᶜ,
      isClosed_sphereCircleRegion.isOpen_compl.mem_nhds hpR, ?_⟩
    rintro ⟨z, hzA⟩ (hz : z ∉ sphereCircleBundle.region)
    exact hcov ⟨hzA, hz⟩

/-- The complement of such a relative interior is `M₃ ∩ A`. -/
theorem diff_relInt_eq_JOINT {A X : Set sphereW.Carrier}
    (hcov : A \ sphereCircleBundle.region ⊆ X)
    (hrel : relInt A X = X \ sphereCircleBundle.region) :
    A \ relInt A X = sphereCircleBundle.region ∩ A := by
  rw [hrel]
  ext z
  constructor
  · rintro ⟨hzA, hz⟩
    by_cases hR : z ∈ sphereCircleBundle.region
    · exact ⟨hR, hzA⟩
    · exact absurd ⟨hcov ⟨hzA, hR⟩, hR⟩ hz
  · rintro ⟨hR, hzA⟩
    exact ⟨hzA, fun h => h.2 hR⟩

/-! ## `region_eq` -/

/-- The band minus the region lies in the edge piece. -/
theorem band_diff_region_subset_edge {x : sphereW.Carrier}
    (hx : -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5)
    (hxR : x ∉ sphereCircleBundle.region) : x ∈ sphereEdgeBundle.edgePiece := by
  rcases band_subset_edge_union_region hx.1 hx.2 with h | h
  · exact h
  · exact absurd h hxR

/-- **`int_{M₂} P = P \ M₃`** for the S³ data. -/
theorem sphere_relInt_edge :
    relInt (regionM2 sphereSlimPieces) sphereEdgeBundle.edgePiece =
      sphereEdgeBundle.edgePiece \ sphereCircleBundle.region := by
  rw [sphere_regionM2]
  refine relInt_eq_diff_region_JOINT (fun x hx => sphereHeight_edgePiece hx)
    (fun x hx => band_diff_region_subset_edge hx.1 hx.2) ?_
  rintro p ⟨hpE, hpR⟩
  have hpV : p ∈ sphereEdgeBundle.vertical := by
    rw [← sphere_edge_region]
    exact ⟨hpE, hpR⟩
  have hpB := sphereHeight_edgePiece hpE
  refine closure_mono ?_ (vertical_mem_closure_JOINT hpV)
  rintro z ⟨hz, hzE⟩
  refine ⟨⟨?_, ?_⟩, hzE⟩
  · rw [hz]
    exact hpB.1
  · rw [hz]
    exact hpB.2

/-- **`region_eq` for the S³ data**: `M₃ = M₂ \ int_{M₂} P` is the circle region. -/
theorem sphere_region_eq :
    regionM3 sphereSlimPieces sphereEdgeBundle = sphereCircleBundle.region := by
  have hcov : regionM2 sphereSlimPieces \ sphereCircleBundle.region ⊆
      sphereEdgeBundle.edgePiece := by
    rw [sphere_regionM2]
    exact fun x hx => band_diff_region_subset_edge hx.1 hx.2
  rw [regionM3, diff_relInt_eq_JOINT hcov sphere_relInt_edge, inter_eq_left, sphere_regionM2]
  exact sphereCircleRegion_subset_band

/-! ## `region_boundary` -/

/-- **The horizontal disks are `P ∩ ∂M₂`** (from `edge_faces`, face by face). -/
theorem sphere_horizontalDisks_eq :
    sphereEdgeBundle.horizontalDisks =
      sphereEdgeBundle.edgePiece ∩ sphereSlimPieces.boundaryM2 := by
  ext x
  simp only [EdgeBundle.horizontalDisks, SlimPiecesV2.boundaryM2, mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨e, he⟩
    have h : x ∈ sphereEdgeBundle.edgePiece ∩
        sphereSlimPieces.residualSet (sphereHorizontal e) := by
      rw [sphere_edge_faces]
      exact mem_iUnion₂.2 ⟨e, rfl, he⟩
    exact ⟨h.1, sphereHorizontal e, h.2⟩
  · rintro ⟨hxE, F, hxF⟩
    have h : x ∈ sphereEdgeBundle.edgePiece ∩ sphereSlimPieces.residualSet F := ⟨hxE, hxF⟩
    rw [sphere_edge_faces] at h
    obtain ⟨e, -, he⟩ := mem_iUnion₂.1 h
    exact ⟨e, he⟩

theorem sphere_boundaryM2_subset_band {x : sphereW.Carrier}
    (hx : x ∈ sphereSlimPieces.boundaryM2) :
    -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5 := by
  rw [sphere_boundaryM2] at hx
  rcases hx with h | h
  · change sphereHeight x = -3 / 5 at h
    rw [h]
    norm_num
  · change sphereHeight x = 3 / 5 at h
    rw [h]
    norm_num

/-- **`int_{∂M₂} H = H \ M₃`** for the S³ data. -/
theorem sphere_relInt_horizontal :
    relInt sphereSlimPieces.boundaryM2 sphereEdgeBundle.horizontalDisks =
      sphereEdgeBundle.horizontalDisks \ sphereCircleBundle.region := by
  rw [sphere_horizontalDisks_eq]
  refine relInt_eq_diff_region_JOINT inter_subset_right ?_ ?_
  · rintro x ⟨hxB, hxR⟩
    exact ⟨band_diff_region_subset_edge (sphere_boundaryM2_subset_band hxB) hxR, hxB⟩
  · rintro p ⟨⟨hpE, hpBd⟩, hpR⟩
    have hpV : p ∈ sphereEdgeBundle.vertical := by
      rw [← sphere_edge_region]
      exact ⟨hpE, hpR⟩
    refine closure_mono ?_ (vertical_mem_closure_JOINT hpV)
    rintro z ⟨hz, hzE⟩
    refine ⟨?_, fun h => hzE h.1⟩
    rw [sphere_boundaryM2] at hpBd ⊢
    rcases hpBd with h | h
    · left
      change sphereHeight z = -3 / 5
      rw [hz]
      exact h
    · right
      change sphereHeight z = 3 / 5
      rw [hz]
      exact h

/-- **`region_boundary` for the S³ data**: `M₃ ∩ ∂M₂ = ∂M₂ \ int_{∂M₂} H`. -/
theorem sphere_region_boundary :
    sphereCircleBundle.region ∩ sphereSlimPieces.boundaryM2 =
      sphereSlimPieces.boundaryM2 \
        relInt sphereSlimPieces.boundaryM2 sphereEdgeBundle.horizontalDisks := by
  have hcov : sphereSlimPieces.boundaryM2 \ sphereCircleBundle.region ⊆
      sphereEdgeBundle.horizontalDisks := by
    rw [sphere_horizontalDisks_eq]
    rintro x ⟨hxB, hxR⟩
    exact ⟨band_diff_region_subset_edge (sphere_boundaryM2_subset_band hxB) hxR, hxB⟩
  rw [diff_relInt_eq_JOINT hcov sphere_relInt_horizontal]

/-! ## `cover` -/

theorem mem_sphereZminus_iff {x : sphereW.Carrier} :
    x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle (.inl (.inl (0 : Fin 2))) ↔
      sphereHeight x ≤ -15 / 17 := by
  change x ∈ range (sphereZeroDomains.piece (0 : Fin 2)).map ↔ _
  rw [sphereZeroDomains.range_eq (0 : Fin 2)]
  change sphereHeight x + 15 / 17 ≤ 0 ↔ _
  constructor <;> intro h <;> linarith

theorem mem_sphereZplus_iff {x : sphereW.Carrier} :
    x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle (.inl (.inl (1 : Fin 2))) ↔
      3 / 5 ≤ sphereHeight x := by
  change x ∈ range (sphereZeroDomains.piece (1 : Fin 2)).map ↔ _
  rw [sphereZeroDomains.range_eq (1 : Fin 2)]
  change 3 / 5 - sphereHeight x ≤ 0 ↔ _
  constructor <;> intro h <;> linarith

theorem mem_sphereSlimRow_iff {x : sphereW.Carrier} :
    x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle
        (.inl (.inr (.inr (0 : Fin 1)))) ↔
      -15 / 17 ≤ sphereHeight x ∧ sphereHeight x ≤ -3 / 5 := by
  change x ∈ range slimMap ↔ _
  rw [range_slimMap]
  rfl

/-- **`cover` for the S³ data**: `Z₋ ∪ S ∪ Z₊ ∪ P ∪ M₃ = S³`. -/
theorem sphere_cover :
    (⋃ a, allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle a) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  by_cases h1 : sphereHeight x ≤ -15 / 17
  · exact ⟨_, mem_sphereZminus_iff.2 h1⟩
  by_cases h2 : sphereHeight x ≤ -3 / 5
  · exact ⟨_, mem_sphereSlimRow_iff.2 ⟨by linarith, h2⟩⟩
  by_cases h3 : 3 / 5 ≤ sphereHeight x
  · exact ⟨_, mem_sphereZplus_iff.2 h3⟩
  rcases band_subset_edge_union_region (x := x) (by linarith) (by linarith) with h | h
  · exact ⟨.inr true, h⟩
  · exact ⟨.inr false, h⟩

/-! ## `interiors_disjoint` -/

/-- Two sets on the two sides of a height level `c` (`|c| < 1`) have disjoint interiors. -/
theorem disjoint_interior_of_height_JOINT {A B : Set sphereW.Carrier} {c : ℝ} (hc : |c| < 1)
    (hA : ∀ x ∈ A, sphereHeight x ≤ c) (hB : ∀ x ∈ B, c ≤ sphereHeight x) :
    Disjoint (interior A) (interior B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  have hx : sphereHeight x = c :=
    le_antisymm (hA x (interior_subset hxA)) (hB x (interior_subset hxB))
  have hx1 : |sphereHeight x| < 1 := by
    rw [hx]
    exact hc
  refine not_mem_interior_of_mem_closure
    (mem_closure_height_above hx1 (c := 1) (abs_lt.1 hx1).2) ?_ hxA
  rw [Set.disjoint_left]
  rintro z hzA ⟨hz1, -⟩
  have := hA z hzA
  linarith

/-- The edge piece and the circle region have disjoint interiors. -/
theorem disjoint_interior_edge_region :
    Disjoint (interior sphereEdgeBundle.edgePiece) (interior sphereCircleBundle.region) := by
  rw [Set.disjoint_left]
  intro x hxE hxR
  have hxV : x ∈ sphereEdgeBundle.vertical := by
    rw [← sphere_edge_region]
    exact ⟨interior_subset hxE, interior_subset hxR⟩
  refine not_mem_interior_of_mem_closure (vertical_mem_closure_JOINT hxV) ?_ hxE
  rw [Set.disjoint_left]
  rintro z hz ⟨-, hz'⟩
  exact hz' hz

/-- **`interiors_disjoint` for the S³ data.** -/
theorem sphere_interiors_disjoint :
    Pairwise fun a a' : sphereSlimPieces.RowIndex ⊕ Bool =>
      Disjoint (interior (allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle a))
        (interior (allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle a')) := by
  have hZm : ∀ x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle
      (.inl (.inl (0 : Fin 2))), sphereHeight x ≤ -15 / 17 :=
    fun x hx => mem_sphereZminus_iff.1 hx
  have hZp : ∀ x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle
      (.inl (.inl (1 : Fin 2))), 3 / 5 ≤ sphereHeight x :=
    fun x hx => mem_sphereZplus_iff.1 hx
  have hS : ∀ x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle
      (.inl (.inr (.inr (0 : Fin 1)))), -15 / 17 ≤ sphereHeight x ∧ sphereHeight x ≤ -3 / 5 :=
    fun x hx => mem_sphereSlimRow_iff.1 hx
  have hE : ∀ x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle (.inr true),
      -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5 :=
    fun x hx => sphereHeight_edgePiece hx
  have hR : ∀ x ∈ allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle (.inr false),
      -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5 :=
    fun x hx => sphereCircleRegion_subset_band hx
  have c1 : |(-15 / 17 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have c2 : |(-3 / 5 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have c3 : |(3 / 5 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have d01 := disjoint_interior_of_height_JOINT c1 hZm (fun x hx => by linarith [hZp x hx])
  have d0S := disjoint_interior_of_height_JOINT c1 hZm (fun x hx => (hS x hx).1)
  have d0E := disjoint_interior_of_height_JOINT c1 hZm (fun x hx => by linarith [(hE x hx).1])
  have d0R := disjoint_interior_of_height_JOINT c1 hZm (fun x hx => by linarith [(hR x hx).1])
  have dS1 := disjoint_interior_of_height_JOINT c3 (fun x hx => by linarith [(hS x hx).2]) hZp
  have dE1 := disjoint_interior_of_height_JOINT c3 (fun x hx => (hE x hx).2) hZp
  have dR1 := disjoint_interior_of_height_JOINT c3 (fun x hx => (hR x hx).2) hZp
  have dSE := disjoint_interior_of_height_JOINT c2 (fun x hx => (hS x hx).2)
    (fun x hx => (hE x hx).1)
  have dSR := disjoint_interior_of_height_JOINT c2 (fun x hx => (hS x hx).2)
    (fun x hx => (hR x hx).1)
  have dER := disjoint_interior_edge_region
  intro a a' hne
  rcases a with (i | b | j) | e
  · fin_cases i <;> rcases a' with (i' | b' | j') | e'
    all_goals try fin_cases i'
    all_goals try fin_cases j'
    all_goals try exact b'.elim0
    all_goals try cases e'
    all_goals first
      | exact absurd rfl hne
      | exact d01 | exact d01.symm | exact d0S | exact d0E | exact d0R
      | exact dS1.symm | exact dE1.symm | exact dR1.symm
  · exact b.elim0
  · fin_cases j
    rcases a' with (i' | b' | j') | e'
    all_goals try fin_cases i'
    all_goals try fin_cases j'
    all_goals try exact b'.elim0
    all_goals try cases e'
    all_goals first
      | exact absurd rfl hne
      | exact d0S.symm | exact dS1 | exact dSE | exact dSR
  · cases e <;> rcases a' with (i' | b' | j') | e'
    all_goals try fin_cases i'
    all_goals try fin_cases j'
    all_goals try exact b'.elim0
    all_goals try cases e'
    all_goals first
      | exact absurd rfl hne
      | exact d0E.symm | exact d0R.symm | exact dE1 | exact dR1 | exact dSE.symm
      | exact dSR.symm | exact dER | exact dER.symm

end GC.GraphManifold.Assembly.FC39P0
