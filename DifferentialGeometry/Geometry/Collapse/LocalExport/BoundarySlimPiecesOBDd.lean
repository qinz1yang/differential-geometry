import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChoiceV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07RowBGR
import DifferentialGeometry.Topology.Manifold.OneManifold.ArcRegularDomainOBDd
import DifferentialGeometry.Topology.Ehresmann.ArcEndNotInteriorOBDd
import DifferentialGeometry.Topology.Ehresmann.SubArcOBDd

/-!
# The components of `D₃ = K₃ ∩ C₃` as sub-arcs of the arcs of `dec.slim` (S-BD2d, `_OBDd`), G10c

Lane O-BD1 (by S-BD2d). `dec.slim.K₃ = ⋃ arcs` (disjoint compact arcs in `B₃`),
`C₃ = slimBaseDomain_BIFc`. Along each arc the regular domain `C₃` (closed, finite frontier
`⊆ f₃(∂M₁ ∩ X₃)`, `∂K₃ ∩ ∂C₃ = ∅`) cuts out finitely many disjoint nondegenerate sub-arcs
(`exists_arc_pieces_OBDd`):

* `BoundaryGaf02ChainE.arc_end_not_relInterior_OBDd`: an arc end of `dec.slim` is not a relative
  interior point of `K₃` (`arc_end_not_mem_relInterior_OBDd`, the other arcs being disjoint
  compact sets);
* `BoundaryGaf02ChainE.exists_slimD3Arcs_OBDd`: finitely many smooth embedded base arcs `γ i`
  (sub-arcs) with pairwise disjoint images, `⋃ γ i [0,1] = K₃ ∩ C₃`, whose end values are face
  points `f₃(∂M₁ ∩ X₃)` or arc ends of `dec.slim`, and an arc end of `dec.slim` is never a face
  point of `C₃`.
-/



set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- An arc end of `dec.slim` is not a relative interior point of `K₃`. -/
theorem arc_end_not_relInterior_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (k : Fin dec.slim.arcCount) (b : Bool) :
    dec.slim.arc k (iccEnd b) ∉ relInterior_BIF (dec.bases.base 2) dec.slim.K₃ := by
  obtain ⟨At⟩ := dec.fibres.slimBase_graphAtlas_OBD
  have hc : ContinuousOn (dec.slim.arc k) (Icc 0 1) := (dec.slim.arc_smooth k).continuousOn
  have hinj := dec.slim.arc_injOn k
  have hsub : dec.slim.arc k '' Icc 0 1 ⊆ dec.slim.K₃ := fun y hy =>
    mem_iUnion.2 ⟨k, hy⟩
  have hTB : dec.slim.K₃ ⊆ dec.bases.base 2 := by
    rintro y hy
    obtain ⟨k', hk'⟩ := mem_iUnion.1 hy
    exact dec.slim.arc_subset_base k' hk'
  have hcl : IsClosed (⋃ k' ∈ ({k}ᶜ : Set (Fin dec.slim.arcCount)),
      dec.slim.arc k' '' Icc 0 1) :=
    (Set.toFinite _).isClosed_biUnion fun k' _ =>
      (isCompact_Icc.image_of_continuousOn (dec.slim.arc_smooth k').continuousOn).isClosed
  have hiso : ∀ t ∈ ({0, 1} : Set ℝ), dec.slim.arc k t ∈ (⋃ k' ∈ ({k}ᶜ :
      Set (Fin dec.slim.arcCount)), dec.slim.arc k' '' Icc 0 1)ᶜ ∧
      dec.slim.K₃ ∩ (⋃ k' ∈ ({k}ᶜ : Set (Fin dec.slim.arcCount)),
        dec.slim.arc k' '' Icc 0 1)ᶜ ⊆ dec.slim.arc k '' Icc 0 1 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
    refine ⟨?_, ?_⟩
    · intro hy
      obtain ⟨k', hk', hy'⟩ := mem_iUnion₂.1 hy
      exact Set.disjoint_left.1 (dec.slim.arc_disjoint (Ne.symm hk')) ⟨t, ht', rfl⟩ hy'
    · intro y ⟨hyK, hyN⟩
      obtain ⟨k', hk'⟩ := mem_iUnion.1 hyK
      by_cases hkk : k' = k
      · subst hkk; exact hk'
      · exact absurd (mem_iUnion₂.2 ⟨k', hkk, hk'⟩) hyN
  cases b
  · have h0 : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inl rfl
    exact arc_end_not_mem_relInterior_OBDd At hc hinj hsub hTB
      ⟨_, hcl.isOpen_compl, (hiso 0 h0).1, (hiso 0 h0).2⟩
  · have h1 : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inr rfl
    exact arc_end_one_not_mem_relInterior_OBDd At hc hinj hsub hTB
      ⟨_, hcl.isOpen_compl, (hiso 1 h1).1, (hiso 1 h1).2⟩

include C in
/-- **The components of `D₃ = K₃ ∩ C₃` as sub-arcs of the arcs of `dec.slim`.** -/
theorem exists_slimD3Arcs_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (N : ℕ) (γ : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)),
      (Pairwise fun i j => Disjoint ((γ i).toFun '' Icc 0 1) ((γ j).toFun '' Icc 0 1)) ∧
      (⋃ i, (γ i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) ∧
      (∀ (i : Fin N) (b : Bool),
        (γ i).toFun (iccEnd b) ∈ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) ∨
          ∃ (k : Fin dec.slim.arcCount) (b' : Bool),
            (γ i).toFun (iccEnd b) = dec.slim.arc k (iccEnd b')) ∧
      (∀ (k : Fin dec.slim.arcCount) (b : Bool),
        dec.slim.arc k (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) := by
  classical
  obtain ⟨At⟩ := dec.fibres.slimBase_graphAtlas_OBD
  obtain ⟨-, hfrontier, -, -, hfinite, -, hclosed⟩ :=
    C.bcg07_row_extras_BGR hεr hrd hrd4 hrdc hprem hθ dec.fibres
  have hnotface : ∀ (k : Fin dec.slim.arcCount) (b : Bool),
      dec.slim.arc k (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) :=
    fun k b hface => C.arc_end_not_relInterior_OBDd dec k b (dec.slim.faces_subset hface)
  have hCsub : dec.bases.slimBaseDomain_BIFc ⊆ dec.bases.base 2 := by
    rintro _ ⟨p, ⟨-, hp⟩, rfl⟩
    exact dec.bases.image_eq 2 ▸ mem_image_of_mem _ hp
  have hCcl : ∃ F : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsClosed F ∧ dec.bases.slimBaseDomain_BIFc = F ∩ dec.bases.base 2 := by
    obtain ⟨F, hF, hFC⟩ := isClosed_induced_iff.1 (hclosed 2 (by decide))
    refine ⟨F, hF, Set.ext fun y => ⟨fun hy => ⟨?_, hCsub hy⟩, fun hy => ?_⟩⟩
    · have : (⟨y, hCsub hy⟩ : dec.bases.base 2) ∈ Subtype.val ⁻¹' F := by
        rw [hFC]; exact hy
      exact this
    · have : (⟨y, hy.2⟩ : dec.bases.base 2) ∈ Subtype.val ⁻¹' F := hy.1
      rw [hFC] at this
      exact this
  have hreg := C.slimBaseDomain_regular_OBD dec.fibres hrd hrd4 hrdc hprem hθ
  have hpieces : ∀ k : Fin dec.slim.arcCount, ∃ (N : ℕ) (s e : Fin N → ℝ),
      (∀ i, 0 ≤ s i ∧ s i < e i ∧ e i ≤ 1) ∧
      (Icc (0 : ℝ) 1 ∩ dec.slim.arc k ⁻¹' dec.bases.slimBaseDomain_BIFc = ⋃ i, Icc (s i) (e i)) ∧
      (Pairwise fun i j => Disjoint (Icc (s i) (e i)) (Icc (s j) (e j))) ∧
      (∀ i, (s i = 0 ∨ dec.slim.arc k (s i) ∈ dec.bases.slimBaseDomain_BIFc \
          relInterior_BIF (dec.bases.base 2) dec.bases.slimBaseDomain_BIFc) ∧
        (e i = 1 ∨ dec.slim.arc k (e i) ∈ dec.bases.slimBaseDomain_BIFc \
          relInterior_BIF (dec.bases.base 2) dec.bases.slimBaseDomain_BIFc)) := by
    intro k
    refine exists_arc_pieces_OBDd At (dec.slim.arc_smooth k).continuousOn (dec.slim.arc_injOn k)
      (fun t ht => dec.slim.arc_subset_base k ⟨t, ht, rfl⟩) hCcl hreg ?_ ?_
    · exact hfinite.subset (inter_subset_left.trans hfrontier)
    · intro t ht hmem
      by_contra hnot
      have hb : ∃ b : Bool, (iccEnd b : ℝ) = t := by
        rcases ht with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
      obtain ⟨b, rfl⟩ := hb
      exact hnotface k b (hfrontier ⟨hmem, hnot⟩)
  choose N s e hle hdec hdisj hend using hpieces
  let arcE : Fin dec.slim.arcCount → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2) := fun k =>
    { toFun := dec.slim.arc k
      smooth := dec.slim.arc_smooth k
      injOn := dec.slim.arc_injOn k
      deriv_ne := dec.slim.arc_deriv k
      mapsTo := fun t ht => dec.slim.arc_subset_base k ⟨t, ht, rfl⟩ }
  let eqv : Fin (Fintype.card (Σ k : Fin dec.slim.arcCount, Fin (N k))) ≃
      (Σ k : Fin dec.slim.arcCount, Fin (N k)) := (Fintype.equivFin _).symm
  let γ : Fin (Fintype.card (Σ k : Fin dec.slim.arcCount, Fin (N k))) →
      SmoothEmbeddedBaseArc_EFE (dec.bases.base 2) := fun i =>
    subArc_OBDd (arcE (eqv i).1) (s (eqv i).1 (eqv i).2) (e (eqv i).1 (eqv i).2)
      (hle _ _).1 (hle _ _).2.1 (hle _ _).2.2
  have himg : ∀ i, (γ i).toFun '' Icc 0 1 =
      dec.slim.arc (eqv i).1 '' Icc (s (eqv i).1 (eqv i).2) (e (eqv i).1 (eqv i).2) := fun i =>
    image_subArc_OBDd (arcE (eqv i).1) (hle _ _).1 (hle _ _).2.1 (hle _ _).2.2
  have hdisjp : ∀ p q : Σ k : Fin dec.slim.arcCount, Fin (N k), p ≠ q →
      Disjoint (dec.slim.arc p.1 '' Icc (s p.1 p.2) (e p.1 p.2))
        (dec.slim.arc q.1 '' Icc (s q.1 q.2) (e q.1 q.2)) := by
    rintro ⟨k, a⟩ ⟨k', a'⟩ hpq
    by_cases hkk : k = k'
    · subst hkk
      have hne : a ≠ a' := fun h => hpq (by rw [h])
      rw [Set.disjoint_left]
      rintro _ ⟨t, ht, rfl⟩ ⟨t', ht', htt⟩
      have h1 : t ∈ Icc (0 : ℝ) 1 := ⟨(hle k a).1.trans ht.1, ht.2.trans (hle k a).2.2⟩
      have h2 : t' ∈ Icc (0 : ℝ) 1 := ⟨(hle k a').1.trans ht'.1, ht'.2.trans (hle k a').2.2⟩
      have := dec.slim.arc_injOn k h2 h1 htt
      subst this
      exact Set.disjoint_left.1 (hdisj k hne) ht ht'
    · refine Set.disjoint_of_subset
        (image_mono (fun t ht => (⟨(hle k a).1.trans ht.1, ht.2.trans (hle k a).2.2⟩ :
          t ∈ Icc (0 : ℝ) 1)))
        (image_mono (fun t ht => (⟨(hle k' a').1.trans ht.1, ht.2.trans (hle k' a').2.2⟩ :
          t ∈ Icc (0 : ℝ) 1))) (dec.slim.arc_disjoint hkk)
  refine ⟨_, γ, ?_, ?_, fun i b => ?_, hnotface⟩
  · intro i j hij
    rw [himg, himg]
    exact hdisjp _ _ (fun h => hij (eqv.injective h))
  · ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      rw [himg] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      have hmem : t ∈ Icc (0 : ℝ) 1 ∩ dec.slim.arc (eqv i).1 ⁻¹'
          dec.bases.slimBaseDomain_BIFc := by
        rw [hdec]
        exact mem_iUnion.2 ⟨(eqv i).2, ht⟩
      exact ⟨mem_iUnion.2 ⟨(eqv i).1, t, hmem.1, rfl⟩, hmem.2⟩
    · rintro ⟨hyK, hyD⟩
      obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.1 hyK
      have hmem : t ∈ Icc (0 : ℝ) 1 ∩ dec.slim.arc k ⁻¹' dec.bases.slimBaseDomain_BIFc :=
        ⟨ht, hyD⟩
      rw [hdec] at hmem
      obtain ⟨a, ha⟩ := mem_iUnion.1 hmem
      refine mem_iUnion.2 ⟨eqv.symm ⟨k, a⟩, ?_⟩
      rw [himg, Equiv.apply_symm_apply]
      exact ⟨t, ha, rfl⟩
  · have hends := hend (eqv i).1 (eqv i).2
    cases b
    · have h0 : (γ i).toFun ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) =
          dec.slim.arc (eqv i).1 (s (eqv i).1 (eqv i).2) :=
        subArc_zero_OBDd (arcE (eqv i).1) (hle _ _).1 (hle _ _).2.1 (hle _ _).2.2
      rw [h0]
      rcases hends.1 with h | h
      · exact Or.inr ⟨(eqv i).1, false, by rw [h]; rfl⟩
      · exact Or.inl (hfrontier h)
    · have h1 : (γ i).toFun ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) =
          dec.slim.arc (eqv i).1 (e (eqv i).1 (eqv i).2) :=
        subArc_one_OBDd (arcE (eqv i).1) (hle _ _).1 (hle _ _).2.1 (hle _ _).2.2
      rw [h1]
      rcases hends.2 with h | h
      · exact Or.inr ⟨(eqv i).1, true, by rw [h]; rfl⟩
      · exact Or.inl (hfrontier h)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
