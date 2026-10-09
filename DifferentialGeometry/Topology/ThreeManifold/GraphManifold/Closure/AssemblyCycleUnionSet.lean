import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionRounding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionGraph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleThirdPiece

/-!
# FC42 packet H3a, part 2: the rounded union of one cycle as a set

For a complete cycle partition `P : D.CyclePartition` (packet H2) and a cycle `j`, the rounded
union `unionSet j` = the balls, the oriented handles and the fillets
`cycleRimChart j k b '' {0 < x, 0 < y, (x, y) ∈ rimBox 1, ψ_std ≤ 0}` (the shape of
`BallHandleCycle.range_union_eq`). Proved here, without any input beyond the certificate:

* `union_rim` at the level of sets: inside a rim chart of a cycle handle the union is exactly the
  `ψ_std ≤ 0` side (`mem_unionSet_rim_iff`; the inclusion `⊆` uses lane ASM-CYC2's G2: a rim chart
  target meets no other vertex and no other handle), and `union_away`: away from the rim targets the
  union is the balls and handles (`unionSet_diff_rimTargets`);
* `unionSet j` is closed (closed fillet band `x, y ≥ 0, x + y ≤ 3/4, ψ_std ≤ 0`) and connected (a
  chain of balls and handles around the cycle; each fillet point slides along the diagonal, where
  `ψ_std` decreases at unit speed, into a ball or a handle);
* `unionSet j` lies in the closed complement `roundedComplement` of the open rounded circle region
  and in `W.interior`.

The relative openness in `roundedComplement` (exclusion of the other closed pieces, lane ASM-CYC2's
packet H1) and the `PieceEmbedding` are part 3 (`AssemblyCycleUnionPiece.lean`). Note (review 42 §2.3): the existence of a cycle
partition does not by itself encode the termination of the FC42 normalization.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsS_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothS_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsS_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothS_ASMCYC3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace EdgeHandle

variable {W : CompactCarrier.{u}}

theorem endDisk_nonempty (H : EdgeHandle W) (b : Bool) : (H.endDisk b).Nonempty :=
  ⟨_, ⟨⟨0, by simp⟩, rfl⟩⟩

theorem isPreconnected_range_map (H : EdgeHandle W) : IsPreconnected (range H.map) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
  let _ : PreconnectedSpace (ClosedCell 2) := Subtype.preconnectedSpace hconv.isPreconnected
  let _ : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  exact isPreconnected_range H.smooth.continuous

end EdgeHandle

namespace DecompositionCertificate

namespace CyclePartition

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  (P : D.CyclePartition)

/-- The rim chart of cycle `j` at `(k, b)`: the certificate rim chart at the oriented end. -/
def cycleRimChart (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞ :=
  D.rimChart (P.handle j k) (xor b (P.orientation j k))

/-- The fillet parameters of a rim chart. -/
def filletParam : Set (Circle × (ℝ × ℝ)) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2 ∈ rimBox 1 ∧ standardRimRounding p.2 ≤ 0}

/-- Balls and handles of cycle `j`. -/
def coreSet (j : Fin P.cnt) : Set W.Carrier :=
  (⋃ k, range (P.ballPiece j k).map) ∪ ⋃ k, range (P.cycleHandle j k).map

/-- **The rounded union of cycle `j`**: balls, handles and fillets. -/
def unionSet (j : Fin P.cnt) : Set W.Carrier :=
  P.coreSet j ∪ ⋃ k, ⋃ b, P.cycleRimChart j k b '' filletParam

/-- The rim chart targets of cycle `j`. -/
def rimTargets (j : Fin P.cnt) : Set W.Carrier :=
  ⋃ k, ⋃ b, (P.cycleRimChart j k b).target

theorem range_ballPiece (j : Fin P.cnt) (k : Fin (P.len j)) :
    range (P.ballPiece j k).map = (D.vertex (P.ball j k)).image := by
  rw [P.vertex_ball j k]
  rfl

theorem range_cycleHandle (j : Fin P.cnt) (k : Fin (P.len j)) :
    range (P.cycleHandle j k).map = range (D.handle (P.handle j k)).map :=
  EdgeHandle.orient_range _ _

theorem xor_xor_orientation (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    xor (xor b (P.orientation j k)) (P.orientation j k) = b := by
  cases b <;> cases P.orientation j k <;> rfl

/-- The end vertices of a cycle handle are balls of the same cycle. -/
theorem handleEnd_handle_eq (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    D.handleEnd (P.handle j k) b =
      P.ball j (rimBall (P.len j) k (xor b (P.orientation j k))) := by
  have h := P.handleEnd_handle j k (xor b (P.orientation j k))
  rwa [P.xor_xor_orientation] at h

/-- The certificate rim chart `(P.handle j k, b)` is the cycle rim chart `(k, xor b σ)`. -/
theorem rimChart_handle_eq (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    D.rimChart (P.handle j k) b = P.cycleRimChart j k (xor b (P.orientation j k)) := by
  rw [cycleRimChart, P.xor_xor_orientation]

/-- A handle with an end on a ball of cycle `j` is a handle of cycle `j`. -/
theorem exists_handle_eq_of_handleEnd_eq (j : Fin P.cnt) (k : Fin (P.len j))
    {h : Fin D.handleCount} {b : Bool} (hb : D.handleEnd h b = P.ball j k) :
    ∃ k', P.handle j k' = h := by
  have h1 := P.handle_handleIdx_symm h
  set j' := (P.handleIdx.symm h).1
  set k'' := (P.handleIdx.symm h).2
  rw [← h1, P.handleEnd_handle_eq] at hb
  have h2 := P.ball_eq_ball_iff.mp hb
  have hj : j' = j := congrArg Sigma.fst h2
  subst hj
  exact ⟨k'', h1⟩

theorem ball_mem_vertex_image {j : Fin P.cnt} {k : Fin (P.len j)} {x : W.Carrier}
    (hx : x ∈ range (P.ballPiece j k).map) : x ∈ (D.vertex (P.ball j k)).image := by
  rwa [← P.range_ballPiece]

theorem ball_subset_coreSet (j : Fin P.cnt) (k : Fin (P.len j)) :
    (D.vertex (P.ball j k)).image ⊆ P.coreSet j := by
  rw [← P.range_ballPiece]
  exact fun x hx => Or.inl (mem_iUnion.mpr ⟨k, hx⟩)

theorem handle_subset_coreSet (j : Fin P.cnt) (k : Fin (P.len j)) :
    range (D.handle (P.handle j k)).map ⊆ P.coreSet j := by
  rw [← P.range_cycleHandle]
  exact fun x hx => Or.inr (mem_iUnion.mpr ⟨k, hx⟩)

theorem coreSet_subset_unionSet (j : Fin P.cnt) : P.coreSet j ⊆ P.unionSet j :=
  subset_union_left

/-- Inside a rim chart of a cycle handle, the `ψ ≤ 0` side lies in the rounded union. -/
theorem mem_unionSet_of_rim (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart (P.handle j k) b).source)
    (hψ : standardRimRounding p.2 ≤ 0) : D.rimChart (P.handle j k) b p ∈ P.unionSet j := by
  rcases standardRimRounding_nonpos_iff_or_fillet.mp hψ with hy | hx | hf
  · apply P.coreSet_subset_unionSet
    have h := (D.rim_vertex _ _ hp).mpr hy
    rw [P.handleEnd_handle_eq] at h
    exact P.ball_subset_coreSet j _ h
  · apply P.coreSet_subset_unionSet
    by_cases hy : 0 ≤ p.2.2
    · exact P.handle_subset_coreSet j k ((D.rim_handle _ _ hp).mpr ⟨hy, hx⟩)
    · have h := (D.rim_vertex _ _ hp).mpr (le_of_not_ge hy)
      rw [P.handleEnd_handle_eq] at h
      exact P.ball_subset_coreSet j _ h
  · refine Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨xor b (P.orientation j k), ?_⟩⟩)
    rw [← P.rimChart_handle_eq]
    exact ⟨p, hf, rfl⟩

/-- Inside a rim chart of a cycle handle, the rounded union lies on the `ψ ≤ 0` side. -/
theorem nonpos_of_mem_unionSet_rim (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart (P.handle j k) b).source)
    (hmem : D.rimChart (P.handle j k) b p ∈ P.unionSet j) : standardRimRounding p.2 ≤ 0 := by
  have hT : D.rimChart (P.handle j k) b p ∈ (D.rimChart (P.handle j k) b).target :=
    (D.rimChart _ _).map_source hp
  rcases hmem with (hB | hH) | hF
  · obtain ⟨k', hk'⟩ := mem_iUnion.mp hB
    have hv := P.ball_mem_vertex_image hk'
    by_cases he : P.ball j k' = D.handleEnd (P.handle j k) b
    · rw [he] at hv
      exact standardRimRounding_nonpos_of _ (Or.inl ((D.rim_vertex _ _ hp).mp hv))
    · exact (Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target _ _ _ he) hv hT).elim
  · obtain ⟨k', hk'⟩ := mem_iUnion.mp hH
    rw [P.range_cycleHandle] at hk'
    by_cases he : P.handle j k' = P.handle j k
    · rw [he] at hk'
      exact standardRimRounding_nonpos_of _ (Or.inr ((D.rim_handle _ _ hp).mp hk').2)
    · exact (Set.disjoint_left.mp (D.disjoint_handle_rimChart_target _ _ _ he) hk' hT).elim
  · obtain ⟨k', hk'⟩ := mem_iUnion.mp hF
    obtain ⟨b', q, hq, hqp⟩ := mem_iUnion.mp hk'
    have hqs : q ∈ (P.cycleRimChart j k' b').source :=
      (D.rim_source _ _).mpr (rimBox_mono (by norm_num) hq.2.2.1)
    by_cases he : (P.handle j k', xor b' (P.orientation j k')) = (P.handle j k, b)
    · simp only [Prod.mk.injEq] at he
      have hq' : q ∈ (D.rimChart (P.handle j k) b).source := by
        rw [← he.1, ← he.2]
        exact hqs
      have hqp' : D.rimChart (P.handle j k) b q = D.rimChart (P.handle j k) b p := by
        rw [← hqp, cycleRimChart, he.1, he.2]
      have := (D.rimChart (P.handle j k) b).injOn hq' hp hqp'
      rw [← this]
      exact hq.2.2.2
    · have hT' : D.rimChart (P.handle j k) b p ∈ (P.cycleRimChart j k' b').target := by
        rw [← hqp]
        exact (P.cycleRimChart j k' b').map_source hqs
      exact (Set.disjoint_left.mp (D.rim_disjoint _ _ _ _ he) hT' hT).elim

/-- **`union_rim`, set level.** -/
theorem mem_unionSet_rim_iff (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (P.cycleRimChart j k b).source) :
    P.cycleRimChart j k b p ∈ P.unionSet j ↔ standardRimRounding p.2 ≤ 0 :=
  ⟨P.nonpos_of_mem_unionSet_rim j k _ hp, P.mem_unionSet_of_rim j k _ hp⟩

theorem fillet_subset_rimTargets (j : Fin P.cnt) :
    (⋃ k, ⋃ b, P.cycleRimChart j k b '' filletParam) ⊆ P.rimTargets j := by
  refine iUnion₂_subset fun k b => ?_
  rintro _ ⟨p, hp, rfl⟩
  refine mem_iUnion₂.mpr ⟨k, b, (P.cycleRimChart j k b).map_source ?_⟩
  exact (D.rim_source _ _).mpr (rimBox_mono (by norm_num) hp.2.2.1)

/-- **`union_away`, set level.** -/
theorem unionSet_diff_rimTargets (j : Fin P.cnt) :
    P.unionSet j \ P.rimTargets j = P.coreSet j \ P.rimTargets j := by
  apply Subset.antisymm
  · rintro x ⟨hx | hx, hT⟩
    · exact ⟨hx, hT⟩
    · exact (hT (P.fillet_subset_rimTargets j hx)).elim
  · exact sdiff_subset_sdiff_left (P.coreSet_subset_unionSet j)

/-- The closed fillet parameters: the corner band `{x, y ≥ 0, x + y ≤ 3/4, ψ ≤ 0}`. -/
def filletBand : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 + v.2 ≤ 3 / 4 ∧ standardRimRounding v ≤ 0}

theorem isCompact_filletBand : IsCompact filletBand := by
  have hc : Continuous standardRimRounding := contDiff_standardRimRounding.continuous
  have hcl : IsClosed filletBand := by
    have he : filletBand = {v : ℝ × ℝ | 0 ≤ v.1} ∩ ({v : ℝ × ℝ | 0 ≤ v.2} ∩
        ({v : ℝ × ℝ | v.1 + v.2 ≤ 3 / 4} ∩ {v : ℝ × ℝ | standardRimRounding v ≤ 0})) := by
      ext v
      simp [filletBand]
    rw [he]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le (continuous_fst.add continuous_snd) continuous_const).inter
          (isClosed_le hc continuous_const)))
  refine Metric.isCompact_of_isClosed_isBounded hcl ((Metric.isBounded_closedBall (x := 0)
    (r := 1)).subset ?_)
  rintro v ⟨h1, h2, h3, -⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
  constructor <;> linarith

theorem filletBand_subset_rimBox : filletBand ⊆ rimBox 1 := by
  rintro v ⟨h1, h2, h3, -⟩
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg h1]
    linarith
  · rw [abs_of_nonneg h2]
    linarith

theorem filletParam_subset : filletParam ⊆ {p : Circle × (ℝ × ℝ) | p.2 ∈ filletBand} := by
  rintro p ⟨hx, hy, -, hψ⟩
  exact ⟨hx.le, hy.le, (band_of_standardRimRounding_nonpos p.2 hx hy hψ).le, hψ⟩

/-- The rounded union with closed fillets. -/
theorem unionSet_eq_closed (j : Fin P.cnt) :
    P.unionSet j = P.coreSet j ∪
      ⋃ k, ⋃ b, P.cycleRimChart j k b '' {p | p.2 ∈ filletBand} := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨k, b, p, hp, rfl⟩ := mem_iUnion₂.mp hx
      exact Or.inr (mem_iUnion₂.mpr ⟨k, b, p, filletParam_subset hp, rfl⟩)
  · rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨k, b, p, hp, rfl⟩ := mem_iUnion₂.mp hx
      have hs : p ∈ (D.rimChart (P.handle j k) (xor b (P.orientation j k))).source :=
        (D.rim_source _ _).mpr (rimBox_mono (by norm_num) (filletBand_subset_rimBox hp))
      exact P.mem_unionSet_of_rim j k _ hs hp.2.2.2

theorem isClosed_coreSet (j : Fin P.cnt) : IsClosed (P.coreSet j) :=
  (isClosed_iUnion_of_finite fun k => (P.ballPiece j k).isClosed_range).union
    (isClosed_iUnion_of_finite fun k =>
      (isCompact_range (P.cycleHandle j k).smooth.continuous).isClosed)

theorem isClosed_unionSet (j : Fin P.cnt) : IsClosed (P.unionSet j) := by
  rw [P.unionSet_eq_closed]
  refine (P.isClosed_coreSet j).union (isClosed_iUnion_of_finite fun k =>
    isClosed_iUnion_of_finite fun b => ?_)
  have hK : IsCompact {p : Circle × (ℝ × ℝ) | p.2 ∈ filletBand} := by
    convert (isCompact_univ (X := Circle)).prod isCompact_filletBand using 1
    ext p
    simp
  refine (hK.image_of_continuousOn ((P.cycleRimChart j k b).contMDiffOn.continuousOn.mono ?_)).isClosed
  intro p hp
  exact (D.rim_source _ _).mpr (rimBox_mono (by norm_num) (filletBand_subset_rimBox hp))

/-- The handle at position `k` meets the balls at positions `k` and `k + 1`. -/
theorem cycleHandle_inter_ball_nonempty (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    (range (P.cycleHandle j k).map ∩
      range (P.ballPiece j (rimBall (P.len j) k b)).map).Nonempty := by
  obtain ⟨x, hx⟩ := EdgeHandle.endDisk_nonempty (D.handle (P.handle j k)) (xor b (P.orientation j k))
  refine ⟨x, ?_, ?_⟩
  · rw [P.range_cycleHandle]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, rfl⟩
  · rw [P.range_ballPiece, ← P.handleEnd_handle]
    exact D.endDisk_subset_vertex_image _ _ hx

theorem isPreconnected_coreSet (j : Fin P.cnt) : IsPreconnected (P.coreSet j) := by
  let s : Fin (P.len j) → Set W.Carrier := fun k =>
    range (P.ballPiece j k).map ∪ range (P.cycleHandle j k).map
  have hs : ∀ k, IsPreconnected (s k) := fun k => by
    obtain ⟨x, hx1, hx2⟩ := P.cycleHandle_inter_ball_nonempty j k false
    exact IsPreconnected.union x hx2 hx1 (P.ballPiece j k).isConnected_range.isPreconnected
      (EdgeHandle.isPreconnected_range_map _)
  have hU : P.coreSet j = ⋃ k, s k := by
    rw [coreSet, iUnion_union_distrib]
  rw [hU]
  have hR : ∀ k : Fin (P.len j), (s k ∩ s (finRotate (P.len j) k)).Nonempty := fun k => by
    obtain ⟨x, hx1, hx2⟩ := P.cycleHandle_inter_ball_nonempty j k true
    exact ⟨x, Or.inr hx1, Or.inl hx2⟩
  apply IsPreconnected.iUnion_of_reflTransGen hs
  let R : Fin (P.len j) → Fin (P.len j) → Prop := fun i i' => (s i ∩ s i').Nonempty
  have hsymm : ∀ i i', R i i' → R i' i := fun i i' h => by
    obtain ⟨x, h1, h2⟩ := h
    exact ⟨x, h2, h1⟩
  have hrev : ∀ a c, Relation.ReflTransGen R a c → Relation.ReflTransGen R c a := by
    intro a c hac
    induction hac with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (hsymm _ _ hbc)).trans ih
  have h0 : ∀ (t : ℕ) (ht : t < P.len j),
      Relation.ReflTransGen R ⟨0, P.len_pos j⟩ ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ t ih =>
      intro ht
      refine (ih (by omega)).tail ?_
      have hrot : finRotate (P.len j) ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
        ext
        rw [val_finRotate_of_pos (P.len_pos j), Nat.mod_eq_of_lt ht]
      have := hR ⟨t, by omega⟩
      rwa [hrot] at this
  intro i i'
  exact (hrev _ _ (h0 i.1 i.2)).trans (h0 i'.1 i'.2)

theorem coreSet_nonempty (j : Fin P.cnt) : (P.coreSet j).Nonempty := by
  obtain ⟨x, hx⟩ := (P.ballPiece j ⟨0, P.len_pos j⟩).range_nonempty
  exact ⟨x, Or.inl (mem_iUnion.mpr ⟨_, hx⟩)⟩

/-- A fillet point is joined to the balls and handles inside the rounded union. -/
theorem exists_isPreconnected_fillet (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ filletParam) :
    ∃ t ⊆ P.unionSet j, P.cycleRimChart j k b p ∈ t ∧ (t ∩ P.coreSet j).Nonempty ∧
      IsPreconnected t := by
  obtain ⟨hx, hy, -, hψ⟩ := hp
  set m := min p.2.1 p.2.2 with hm
  let γ : ℝ → Circle × (ℝ × ℝ) := fun t => (p.1, (p.2.1 - t, p.2.2 - t))
  have hγc : Continuous γ := continuous_const.prodMk
    ((continuous_const.sub continuous_id).prodMk (continuous_const.sub continuous_id))
  have hband : ∀ t ∈ Icc (0 : ℝ) m, (γ t).2 ∈ filletBand := by
    rintro t ⟨ht0, htm⟩
    have h1 : t ≤ p.2.1 := htm.trans (min_le_left _ _)
    have h2 : t ≤ p.2.2 := htm.trans (min_le_right _ _)
    have hb := band_of_standardRimRounding_nonpos p.2 hx hy hψ
    have hψt : standardRimRounding (γ t).2 = standardRimRounding p.2 - t := by
      have he : ((p.2.1 - t, p.2.2 - t) : ℝ × ℝ) + (t, t) = p.2 :=
        Prod.ext (by simp) (by simp)
      have := standardRimRounding_add_diag (p.2.1 - t, p.2.2 - t) t
      rw [he] at this
      change standardRimRounding (p.2.1 - t, p.2.2 - t) = _
      linarith
    refine ⟨by simp [γ]; linarith, by simp [γ]; linarith, by simp [γ]; linarith, ?_⟩
    rw [hψt]
    linarith
  have hsrc : ∀ t ∈ Icc (0 : ℝ) m, γ t ∈ (P.cycleRimChart j k b).source := fun t ht =>
    (D.rim_source _ _).mpr (rimBox_mono (by norm_num) (filletBand_subset_rimBox (hband t ht)))
  let seg := (fun t => P.cycleRimChart j k b (γ t)) '' Icc (0 : ℝ) m
  have hm0 : 0 ≤ m := le_min hx.le hy.le
  refine ⟨seg, ?_, ⟨0, ⟨le_rfl, hm0⟩, by simp [γ]⟩, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact P.mem_unionSet_of_rim j k _ (hsrc t ht) (hband t ht).2.2.2
  · refine ⟨P.cycleRimChart j k b (γ m), ⟨m, ⟨hm0, le_rfl⟩, rfl⟩, ?_⟩
    have hs := hsrc m ⟨hm0, le_rfl⟩
    rcases min_choice p.2.1 p.2.2 with h | h
    · -- `x = 0`: the handle side (`y ≥ 0`)
      have hmx : m = p.2.1 := hm.trans h
      have hx0 : (γ m).2.1 ≤ 0 := by simp only [γ]; linarith
      have hy0 : 0 ≤ (γ m).2.2 := by
        have := min_le_right p.2.1 p.2.2
        simp only [γ]
        linarith
      exact P.handle_subset_coreSet j k ((D.rim_handle _ _ hs).mpr ⟨hy0, hx0⟩)
    · have hmy : m = p.2.2 := hm.trans h
      have hy0 : (γ m).2.2 ≤ 0 := by simp only [γ]; linarith
      have hv := (D.rim_vertex _ _ hs).mpr hy0
      rw [P.handleEnd_handle_eq] at hv
      exact P.ball_subset_coreSet j _ hv
  · exact (isPreconnected_Icc.image _ ((P.cycleRimChart j k b).contMDiffOn.continuousOn.comp
      hγc.continuousOn (fun t ht => hsrc t ht)))

theorem isConnected_unionSet (j : Fin P.cnt) : IsConnected (P.unionSet j) := by
  obtain ⟨x₀, hx₀⟩ := P.coreSet_nonempty j
  refine ⟨⟨x₀, P.coreSet_subset_unionSet j hx₀⟩, isPreconnected_of_forall x₀ fun y hy => ?_⟩
  rcases hy with hy | hy
  · exact ⟨P.coreSet j, P.coreSet_subset_unionSet j, hx₀, hy, P.isPreconnected_coreSet j⟩
  · obtain ⟨k, b, p, hp, rfl⟩ := mem_iUnion₂.mp hy
    obtain ⟨t, hts, hyt, ⟨z, hzt, hzc⟩, htc⟩ := P.exists_isPreconnected_fillet j k b hp
    refine ⟨P.coreSet j ∪ t, union_subset (P.coreSet_subset_unionSet j) hts, Or.inl hx₀,
      Or.inr hyt, ?_⟩
    exact IsPreconnected.union z hzc hzt (P.isPreconnected_coreSet j) htc

theorem coreSet_subset_roundedComplement (j : Fin P.cnt) :
    P.coreSet j ⊆ D.roundedComplement := by
  rintro x (hx | hx)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hxd : x ∈ D.circ.domain
    · exact Or.inr (D.nonneg_roundedFunction_of_mem_vertex_image _ (P.ball_mem_vertex_image hk) hxd)
    · exact Or.inl hxd
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    rw [P.range_cycleHandle] at hk
    by_cases hxd : x ∈ D.circ.domain
    · exact Or.inr (D.nonneg_roundedFunction_of_mem_handle _ hk hxd)
    · exact Or.inl hxd

theorem fillet_source (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ filletParam) : p ∈ (P.cycleRimChart j k b).source :=
  (D.rim_source _ _).mpr (rimBox_mono (by norm_num) hp.2.2.1)

/-- **The rounded union lies in the closed complement** `S = {x ∉ domain ∨ ρ x ≥ 0}`. -/
theorem unionSet_subset_roundedComplement (j : Fin P.cnt) :
    P.unionSet j ⊆ D.roundedComplement := by
  rintro x (hx | hx)
  · exact P.coreSet_subset_roundedComplement j hx
  · obtain ⟨k, b, p, hp, rfl⟩ := mem_iUnion₂.mp hx
    right
    change 0 ≤ D.circ.roundedFunction (D.rimChart (P.handle j k) (xor b (P.orientation j k)) p)
    rw [D.roundedFunction_rimChart _ _ (P.fillet_source j k b hp)]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (D.circ.cornerScale_pos _).le hp.2.2.2)

/-- **The rounded union lies in the interior of `W`.** -/
theorem unionSet_subset_interior (j : Fin P.cnt) : P.unionSet j ⊆ W.interior := by
  rintro x ((hB | hH) | hF)
  · obtain ⟨k, q, rfl⟩ := mem_iUnion.mp hB
    by_cases hq : (𝓡∂ 3).IsInteriorPoint q
    · exact ((P.ballPiece j k).smooth.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
        ((P.ballPiece j k).mfderiv_bijective q).2 hq
    · -- a boundary point lies in the partitioned face: end disks and circle-region strata
      have hqb : q ∈ (𝓡∂ 3).boundary (P.ballPiece j k).Piece :=
        ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint q).mpr hq
      obtain ⟨f, hf, hpart⟩ := P.exists_partitioned_face j k
      have hface : (P.ballPiece j k).map q ∈ D.face f := by
        rw [D.face_eq_boundaryImage_of_isBall (P.ball_isBall j k) hf, P.vertex_ball j k]
        exact ⟨q, hqb, rfl⟩
      rw [← D.face_partition f hpart] at hface
      rcases hface with ((hd | ha) | hl)
      · obtain ⟨h, hd⟩ := mem_iUnion.mp hd
        obtain ⟨b, hd⟩ := mem_iUnion.mp hd
        obtain ⟨-, hz⟩ := mem_iUnion.mp hd
        obtain ⟨y, hy⟩ := hz
        exact (D.handle h).interior ⟨_, hy⟩
      · obtain ⟨a, -, hz⟩ := mem_iUnion₂.mp ha
        rw [D.arcFace_eq] at hz
        obtain ⟨w, -, hw⟩ := hz
        exact hw ▸ D.circ.domain_interior w.2
      · obtain ⟨l, -, hz⟩ := mem_iUnion₂.mp hl
        rw [D.loopFace_eq] at hz
        obtain ⟨w, -, hw⟩ := hz
        exact hw ▸ D.circ.domain_interior w.2
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hH
    rw [P.range_cycleHandle] at hk
    exact (D.handle _).interior hk
  · obtain ⟨k, b, p, hp, rfl⟩ := mem_iUnion₂.mp hF
    exact D.circ.domain_interior
      (D.mem_domain_of_mem_rimChart_target ((P.cycleRimChart j k b).map_source
        (P.fillet_source j k b hp)))

/-- The end disks of the oriented cycle handle lie in the model boundary of the labelled ball. -/
theorem cycleHandle_endDisk_subset (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    (P.cycleHandle j k).endDisk b ⊆
      (P.ballPiece j (rimBall (P.len j) k b)).map ''
        (𝓡∂ 3).boundary (P.ballPiece j (rimBall (P.len j) k b)).Piece := by
  rw [cycleHandle, EdgeHandle.orient_endDisk]
  intro x hx
  have h1 := D.face_subset_boundaryImage _ (D.handleEnd_face _ _ hx)
  rw [D.handleFace_owner, P.handleEnd_handle, P.vertex_ball] at h1
  exact h1

end CyclePartition

end DecompositionCertificate

end GC.GraphManifold.Assembly
