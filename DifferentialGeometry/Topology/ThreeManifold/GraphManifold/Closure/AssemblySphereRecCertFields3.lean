import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertFields2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# FC42 sphere recursion, packet S4 (group G5, second module): corners, rim charts, protection

Lane ASM-SPH2b (review 40 §2.4 "third layer"). On the component `i` of the capped carrier:

* the corners of the handle rims `ccHandleCorner` (the corners of the component circle region are
  the corners centred in the component base, `CircleRegion.CornerIn`), with `handleCorner_bijective`
  and `arcBase_end`;
* the rim charts `ccRimChart` (the lifted rim charts restricted to the piece) and their fields;
* the protection fields (ports, seams, rim charts, circle region, handles);
* the rim-product clause: `D.RimProduct → ` the clause for the inherited rims and handles
  (`cc_rimProduct`: the same profiles, moved by the transport).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsF3_ASMSPH2b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothF3_ASMSPH2b : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  {c : Fin D.sphereSeamCount} {X : SphereCutCapped W (D.sphereSeam c) E} {DQ : X.Q.Components}
  {i : Fin DQ.count}

/-! ## Rim charts and corners in the certificate -/

theorem rimTarget_subset_compl (h : Fin D.handleCount) (b : Bool) :
    (D.rimChart h b).target ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.rim_sphereSeam_disjoint h b c)

theorem rimSource_eq (h : Fin D.handleCount) (b : Bool) :
    (D.rimChart h b).source = (univ : Set Circle) ×ˢ rimBox 2 := by
  ext p
  exact (D.rim_source h b).trans (by simp)

theorem isPreconnected_rimTarget (h : Fin D.handleCount) (b : Bool) :
    IsPreconnected (D.rimChart h b).target := by
  rw [← (D.rimChart h b).toPartialEquiv.image_source_eq_target, rimSource_eq]
  exact (isPreconnected_univ.prod (isPreconnected_rimBox 2)).image _
    ((D.rimChart h b).contMDiffOn.continuousOn.mono (rimSource_eq h b).ge)

theorem rimCenter_mem_source (h : Fin D.handleCount) (b : Bool) (θ : Circle) :
    (θ, ((0 : ℝ), (0 : ℝ))) ∈ (D.rimChart h b).source :=
  (D.rim_source h b).mpr (by simp [rimBox])

/-- The centre of the rim chart: a point of the handle rim over the corner centre. -/
theorem exists_rimCenter (h : Fin D.handleCount) (b : Bool) :
    ∃ y : D.circ.domain, D.circ.proj y = D.circ.cornerChart (D.handleCorner h b) (0, 0) ∧
      y.val ∈ (D.rimChart h b).target ∧ y.val ∈ range (D.handle h).map := by
  obtain ⟨hx, hp⟩ := D.rim_proj h b _ (rimCenter_mem_source h b 1)
  refine ⟨⟨_, hx⟩, hp, (D.rimChart h b).map_source (rimCenter_mem_source h b 1), ?_⟩
  have hl : D.rimChart h b (1, ((0 : ℝ), (0 : ℝ))) ∈ D.rimChart h b '' {p | p.2 = (0, 0)} :=
    ⟨_, rfl, rfl⟩
  rw [D.rim_label] at hl
  obtain ⟨x, -, hx'⟩ := hl
  exact ⟨_, hx'⟩

theorem cornerChart_mem_seamAvoiding (k : Fin D.circ.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    D.circ.cornerChart k v ∈ D.seamAvoidingBase c :=
  D.cornerChart_target_subset_seamAvoidingBase c k (D.circ.cornerChart_mem_target k hv)

/-- The rim chart target of a handle of the component lies (transported) in the piece. -/
theorem transport_rimTarget_subset {h : Fin D.handleCount} (hh : D.ccH c X DQ i h) (b : Bool) :
    X.transport '' (D.rimChart h b).target ⊆ DQ.piece i := by
  obtain ⟨y, -, hyT, p, hp⟩ := exists_rimCenter h b
  refine subset_piece_of_mem (X.isPreconnected_transport_image (isPreconnected_rimTarget h b)
    (rimTarget_subset_compl h b)) ⟨_, hyT, rfl⟩ ?_
  rw [← hp]
  exact hh ⟨p, rfl⟩

theorem liftCirc_cornerChart_val (k : Fin D.circ.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    ((D.liftCircleRegion c X).cornerChart k v).val = D.circ.cornerChart k v :=
  D.circ.restrictBase_cornerChart_val (D.cornerBase_subset_seamAvoidingBase c)
    (D.rounded_subset_seamAvoidingBase c) (D.cornerChart_target_subset_seamAvoidingBase c) k hv

/-- The corner centre of a handle of the component lies in the component base. -/
theorem center_mem_compBase {h : Fin D.handleCount} (hh : D.ccH c X DQ i h) (b : Bool) :
    (D.liftCircleRegion c X).cornerChart (D.handleCorner h b) (0, 0) ∈
      (D.liftCircleRegion c X).compBase DQ i := by
  obtain ⟨y, hy, hyT, -⟩ := exists_rimCenter h b
  have hb : D.circ.proj y ∈ D.seamAvoidingBase c := by
    rw [hy]
    exact cornerChart_mem_seamAvoiding _ (by simp [rimBox])
  have heq : (D.liftCircleRegion c X).cornerChart (D.handleCorner h b) (0, 0) = ⟨_, hb⟩ :=
    Subtype.ext ((liftCirc_cornerChart_val _ (by simp [rimBox])).trans hy.symm)
  rw [heq]
  obtain ⟨hb', -⟩ := ccCirc_proj (X := X) (DQ := DQ) (i := i)
    (x := ⟨_, transport_rimTarget_subset hh b ⟨_, hyT, rfl⟩⟩) hb rfl
  exact hb'

/-- A handle whose corner centre lies in the component base is a handle of the component. -/
theorem ccH_of_center_mem {h : Fin D.handleCount} {b : Bool}
    (hc : (D.liftCircleRegion c X).cornerChart (D.handleCorner h b) (0, 0) ∈
      (D.liftCircleRegion c X).compBase DQ i) : D.ccH c X DQ i h := by
  obtain ⟨y, hy, -, p, hp⟩ := exists_rimCenter h b
  have hb : D.circ.proj y ∈ D.seamAvoidingBase c := by
    rw [hy]
    exact cornerChart_mem_seamAvoiding _ (by simp [rimBox])
  obtain ⟨hx, hproj⟩ := liftCirc_proj_eq (X := X) hb
  have heq : (D.liftCircleRegion c X).cornerChart (D.handleCorner h b) (0, 0) = ⟨_, hb⟩ :=
    Subtype.ext ((liftCirc_cornerChart_val _ (by simp [rimBox])).trans hy.symm)
  rw [heq, ← hproj] at hc
  have hi := CircleRegion.mem_compBase_iff.mp hc
  refine ccH_of_mem (p := p) ?_
  change X.transport ((D.handle h).map p) ∈ DQ.piece i
  rw [hp]
  exact hi

theorem ccCirc_cornerChart_val (k : Fin (D.ccCirc c X DQ i).cornerCount) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    ((D.ccCirc c X DQ i).cornerChart k v).val.val = D.circ.cornerChart
      ((D.liftCircleRegion c X).cornerInEquiv ((D.liftCircleRegion c X).compBase DQ i) k).1 v :=
  (congrArg Subtype.val ((D.liftCircleRegion c X).toComponent_cornerChart_val DQ i k hv)).trans
    (liftCirc_cornerChart_val _ hv)

variable (D c X DQ i)

/-- **The rim corners of the handles of the component.** -/
def ccHandleCorner (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    Fin (D.ccCirc c X DQ i).cornerCount :=
  ((D.liftCircleRegion c X).cornerInEquiv ((D.liftCircleRegion c X).compBase DQ i)).symm
    ⟨D.handleCorner (ccEquiv _ h).1 b, center_mem_compBase (ccEquiv _ h).2 b⟩

theorem cornerInEquiv_ccHandleCorner (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    ((D.liftCircleRegion c X).cornerInEquiv ((D.liftCircleRegion c X).compBase DQ i)
      (D.ccHandleCorner c X DQ i h b)).1 = D.handleCorner (ccEquiv _ h).1 b := by
  rw [ccHandleCorner, Equiv.apply_symm_apply]

/-- **Field `handleCorner_bijective`.** -/
theorem cc_handleCorner_bijective :
    Bijective fun hb : Fin (Nat.card {h // D.ccH c X DQ i h}) × Bool =>
      D.ccHandleCorner c X DQ i hb.1 hb.2 := by
  constructor
  · rintro ⟨h, b⟩ ⟨h', b'⟩ hhb
    have h1 := congrArg (fun k => ((D.liftCircleRegion c X).cornerInEquiv
      ((D.liftCircleRegion c X).compBase DQ i) k).1) hhb
    simp only [cornerInEquiv_ccHandleCorner] at h1
    have h2 := D.handleCorner_bijective.1 (a₁ := ((ccEquiv _ h).1, b)) (a₂ := ((ccEquiv _ h').1, b')) h1
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    rw [(ccEquiv _).injective (Subtype.ext h3), h4]
  · intro k
    set kk := (D.liftCircleRegion c X).cornerInEquiv ((D.liftCircleRegion c X).compBase DQ i) k
    obtain ⟨⟨h, b⟩, hk⟩ := D.handleCorner_bijective.2 kk.1
    have hc := kk.2
    simp only at hk
    rw [← hk] at hc
    have hh : D.ccH c X DQ i h := ccH_of_center_mem hc
    refine ⟨((ccEquiv _).symm ⟨h, hh⟩, b), ?_⟩
    apply ((D.liftCircleRegion c X).cornerInEquiv ((D.liftCircleRegion c X).compBase DQ i)).injective
    apply Subtype.ext
    simp only
    rw [cornerInEquiv_ccHandleCorner, Equiv.apply_symm_apply]
    exact hk

/-- **Field `arcBase_end`.** -/
theorem cc_arcBase_end (j : Fin (Nat.card {j // D.ccA c X DQ i j})) (e : Bool) :
    D.ccArcBase c X DQ i j (iccEnd e) = (D.ccCirc c X DQ i).cornerChart
      (D.ccHandleCorner c X DQ i (D.ccArcEnd c X DQ i j e).1 (D.ccArcEnd c X DQ i j e).2) (0, 0) := by
  refine (eq_ccBaseOf_iff.mpr ?_).symm
  rw [ccCirc_cornerChart_val _ (by simp [rimBox]), cornerInEquiv_ccHandleCorner,
    ccEquiv_ccArcEnd_fst, D.arcBase_end]
  rfl

/-! ## Rim charts -/

theorem liftRimChart_target (h : Fin D.handleCount) (b : Bool) :
    (D.liftRimChart c X h b).target = X.transport '' (D.rimChart h b).target :=
  X.liftPartialDiffeomorph_target _ (rimTarget_subset_compl h b)

/-- **The rim charts of the component.** -/
def ccRimChart (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (GC.Topology.componentCarrier X.Q DQ i).model
      (Circle × (ℝ × ℝ)) (GC.Topology.componentCarrier X.Q DQ i).Carrier ∞ :=
  (codRestrictOpens (J := X.Q.model) (D.liftRimChart c X (ccEquiv _ h).1 b) (DQ.piece i)
    (nonempty_piece DQ i) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) X.Q.model (Circle × (ℝ × ℝ)) (DQ.piece i) ∞)

variable {D c X DQ i}

theorem ccRimChart_source (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (D.ccRimChart c X DQ i h b).source = (D.rimChart (ccEquiv _ h).1 b).source :=
  (codRestrictOpens_source (J := X.Q.model) (D.liftRimChart c X (ccEquiv _ h).1 b) (DQ.piece i)
    (nonempty_piece DQ i) (by
    rw [liftRimChart_target]
    exact transport_rimTarget_subset (ccEquiv _ h).2 b)).trans (D.liftRimChart_source c X _ b)

theorem ccRimChart_val (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.rimChart (ccEquiv _ h).1 b).source) :
    (D.ccRimChart c X DQ i h b p).val = X.transport (D.rimChart (ccEquiv _ h).1 b p) :=
  codRestrictOpens_apply (J := X.Q.model) (D.liftRimChart c X (ccEquiv _ h).1 b) (DQ.piece i)
    (nonempty_piece DQ i) (transport_rimTarget_subset (ccEquiv _ h).2 b ⟨_, (D.rimChart _ b).map_source hp, rfl⟩)

theorem ccRimChart_target (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (D.ccRimChart c X DQ i h b).target =
      Subtype.val ⁻¹' (X.transport '' (D.rimChart (ccEquiv _ h).1 b).target) := by
  refine (codRestrictOpens_target (J := X.Q.model) (D.liftRimChart c X (ccEquiv _ h).1 b)
    (DQ.piece i) (nonempty_piece DQ i)).trans ?_
  rw [liftRimChart_target]

variable (D c X DQ i)

/-- **Field `rim_source`.** -/
theorem cc_rim_source (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    {p : Circle × (ℝ × ℝ)} : p ∈ (D.ccRimChart c X DQ i h b).source ↔ p.2 ∈ rimBox 2 := by
  rw [ccRimChart_source]
  exact D.rim_source _ b

/-- **Field `rim_proj`.** -/
theorem cc_rim_proj (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (p : Circle × (ℝ × ℝ)) (hp : p ∈ (D.ccRimChart c X DQ i h b).source) :
    ∃ hx : D.ccRimChart c X DQ i h b p ∈ (D.ccCirc c X DQ i).domain,
      (D.ccCirc c X DQ i).proj ⟨_, hx⟩ =
        (D.ccCirc c X DQ i).cornerChart (D.ccHandleCorner c X DQ i h b) p.2 := by
  rw [ccRimChart_source] at hp
  have hv : p.2 ∈ rimBox 2 := (D.rim_source _ b).mp hp
  obtain ⟨hx0, hp0⟩ := D.rim_proj _ b p hp
  have hb : D.circ.proj ⟨_, hx0⟩ ∈ D.seamAvoidingBase c := by
    rw [hp0]
    exact cornerChart_mem_seamAvoiding _ hv
  obtain ⟨hxd, hval⟩ := ccCirc_proj_val (X := X) (DQ := DQ) (i := i) hb
    (x := D.ccRimChart c X DQ i h b p) (ccRimChart_val h b hp)
  refine ⟨hxd, Subtype.ext (Subtype.ext ?_)⟩
  rw [hval, hp0, ccCirc_cornerChart_val _ hv, cornerInEquiv_ccHandleCorner]

variable {D c X DQ i} in
theorem mem_image_ccVertex_iff (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
      D.SideSphereInterval c b) {k : Fin (Nat.card {k // D.ccV c X DQ i k})} {y : W.Carrier}
    (hyS : y ∉ (D.sphereSeam c).zeroSphere) {x : (GC.Topology.componentCarrier X.Q DQ i).Carrier}
    (hx : x.val = X.transport y) :
    x ∈ (D.ccVertex c X DQ i hcap k).image ↔ y ∈ (D.vertex (ccEquiv _ k).1).image := by
  rw [image_ccVertex]
  constructor
  · intro hmem
    have h1 : x.val ∈ X.transport '' ((D.vertex (ccEquiv _ k).1).image \
        (D.sphereSeam c).zeroSphere) ∪ D.ccCapPart c X (ccEquiv _ k).1 := hmem
    rw [hx] at h1
    rcases h1 with hy | hy
    · exact ((X.transport_mem_image_iff ((D.sphereSeam c).sdiff_zeroSphere_subset _) hyS).mp hy).1
    · exact (X.transport_notMem_capSet hyS (D.ccCapPart_subset_capSet c X _ hy)).elim
  · intro hy
    have h1 : x.val ∈ X.transport '' ((D.vertex (ccEquiv _ k).1).image \
        (D.sphereSeam c).zeroSphere) ∪ D.ccCapPart c X (ccEquiv _ k).1 := by
      rw [hx]
      exact Or.inl ⟨y, ⟨hy, hyS⟩, rfl⟩
    exact h1

end DecompositionCertificate

/-! ## Rim chart fields, protection, rim product -/

theorem image_eq_preimage_val_on {Q : CompactCarrier.{u}} {DQ : Q.Components} {i : Fin DQ.count}
    {α : Type*} {g : α → (GC.Topology.componentCarrier Q DQ i).Carrier} {g₀ : α → Q.Carrier}
    {A : Set α} (h : ∀ a ∈ A, (g a).val = g₀ a) : g '' A = Subtype.val ⁻¹' (g₀ '' A) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (h a ha).symm⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, Subtype.ext ((h a ha).trans hax)⟩

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)
  (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i → D.SideSphereInterval c b)

theorem ccEquiv_ccHandleEnd (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    (ccEquiv _ (D.ccHandleEnd c X DQ i h b)).1 = D.handleEnd (ccEquiv _ h).1 b := by
  rw [ccHandleEnd, Equiv.apply_symm_apply]

/-- **Field `rim_vertex`.** -/
theorem cc_rim_vertex (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.ccRimChart c X DQ i h b).source) :
    (D.ccRimChart c X DQ i h b p ∈ (D.ccVertex c X DQ i hcap (D.ccHandleEnd c X DQ i h b)).image ↔
      p.2.2 ≤ 0) := by
  rw [ccRimChart_source] at hp
  rw [mem_image_ccVertex_iff hcap (rimTarget_subset_compl _ b ((D.rimChart _ b).map_source hp))
    (ccRimChart_val h b hp), ccEquiv_ccHandleEnd]
  exact D.rim_vertex _ b hp

/-- **Field `rim_handle`.** -/
theorem cc_rim_handle (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.ccRimChart c X DQ i h b).source) :
    (D.ccRimChart c X DQ i h b p ∈ range (D.ccHandle c X DQ i h).map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0)) := by
  rw [ccRimChart_source] at hp
  rw [range_ccHandle]
  change (D.ccRimChart c X DQ i h b p).val ∈ X.transport '' range (D.handle (ccEquiv _ h).1).map ↔ _
  rw [ccRimChart_val h b hp, X.transport_mem_image_iff (D.handle_subset_compl _)
    (rimTarget_subset_compl _ b ((D.rimChart _ b).map_source hp))]
  exact D.rim_handle _ b hp

/-- **Field `rim_region`.** -/
theorem cc_rim_region (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (D.ccRimChart c X DQ i h b).source) :
    (D.ccRimChart c X DQ i h b p ∈ (D.ccCirc c X DQ i).region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2)) := by
  rw [ccRimChart_source] at hp
  rw [region_ccCirc]
  change (D.ccRimChart c X DQ i h b p).val ∈ X.transport '' D.circ.region ↔ _
  rw [ccRimChart_val h b hp, X.transport_mem_image_iff D.region_subset_compl
    (rimTarget_subset_compl _ b ((D.rimChart _ b).map_source hp))]
  exact D.rim_region _ b hp

/-- **Field `rim_label`.** -/
theorem cc_rim_label (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    D.ccRimChart c X DQ i h b '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => (D.ccHandle c X DQ i h).map (x, iccEnd b)) '' diskRim := by
  have hsrc : ∀ p ∈ {p : Circle × (ℝ × ℝ) | p.2 = (0, 0)}, p ∈ (D.rimChart (ccEquiv _ h).1 b).source :=
    fun p hp => (D.rim_source _ b).mpr (by rw [hp]; simp [rimBox])
  rw [image_eq_preimage_val_on (g₀ := fun p => X.transport (D.rimChart (ccEquiv _ h).1 b p))
      fun p hp => ccRimChart_val h b (hsrc p hp),
    image_eq_preimage_val (g₀ := fun x : ClosedCell 2 =>
      X.transport ((D.handle (ccEquiv _ h).1).map (x, iccEnd b))) fun x => rfl]
  have h2 := congrArg (X.transport '' ·) (D.rim_label (ccEquiv _ h).1 b)
  simp only [image_image] at h2
  rw [h2]

/-- **Field `rim_disjoint`.** -/
theorem cc_rim_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (h' : Fin (Nat.card {h // D.ccH c X DQ i h})) (b' : Bool) (hne : (h, b) ≠ (h', b')) :
    Disjoint (D.ccRimChart c X DQ i h b).target (D.ccRimChart c X DQ i h' b').target := by
  rw [ccRimChart_target, ccRimChart_target]
  refine (X.disjoint_transport_image (rimTarget_subset_compl _ _) (rimTarget_subset_compl _ _)
    (D.rim_disjoint _ _ _ _ fun he => hne ?_)).preimage _
  obtain ⟨h1, h2⟩ := Prod.mk.inj he
  rw [(ccEquiv _).injective (Subtype.ext h1), h2]

/-! ### Protection fields -/

theorem externalTarget_trace_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    {B : Set W.Carrier} (hB : B ⊆ (D.sphereSeam c).zeroSphereᶜ)
    (h : Disjoint (E.collar (Fin.cast X.hn (PortRestriction.componentPortEquiv
      X.capping.retained DQ i a).1)).target B) :
    Disjoint ((X.componentTori DQ i).collar a).target
      (Subtype.val ⁻¹' (X.transport '' B) : Set (GC.Topology.componentCarrier X.Q DQ i).Carrier) := by
  rw [componentTori_target_eq]
  exact (X.disjoint_transport_image (X.externalTarget_subset_compl _) hB h).preimage _

/-- **Field `external_region_disjoint`.** -/
theorem cc_external_region_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    Disjoint ((X.componentTori DQ i).collar a).target (D.ccCirc c X DQ i).region := by
  rw [region_ccCirc]
  exact D.externalTarget_trace_disjoint c X DQ i a D.region_subset_compl
    (D.external_region_disjoint _)

/-- **Field `external_handle_disjoint`.** -/
theorem cc_external_handle_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    (h : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    Disjoint ((X.componentTori DQ i).collar a).target (range (D.ccHandle c X DQ i h).map) := by
  rw [range_ccHandle]
  exact D.externalTarget_trace_disjoint c X DQ i a (D.handle_subset_compl _)
    (D.external_handle_disjoint _ _)

/-- **Field `external_edgeCircle_disjoint`.** -/
theorem cc_external_edgeCircle_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    (e : Fin (Nat.card {e // D.ccE c X DQ i e})) :
    Disjoint ((X.componentTori DQ i).collar a).target
      (range (D.ccEdgeCircle c X DQ i e).piece.map) := by
  rw [range_ccEdgeCircle]
  exact D.externalTarget_trace_disjoint c X DQ i a (D.edgeCircle_subset_compl _)
    (D.external_edgeCircle_disjoint _ _)

/-- **Field `external_torusSeam_disjoint`.** -/
theorem cc_external_torusSeam_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    (d : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    Disjoint ((X.componentTori DQ i).collar a).target (D.ccTorusSeam c X DQ i d).collar.target := by
  rw [ccTorusSeam_target]
  exact D.externalTarget_trace_disjoint c X DQ i a (D.torusTarget_subset_compl _)
    (D.external_torusSeam_disjoint _ _)

/-- **Field `external_sphereSeam_disjoint`.** -/
theorem cc_external_sphereSeam_disjoint
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    Disjoint ((X.componentTori DQ i).collar a).target (D.ccSphereSeam c X DQ i d).collar.target := by
  rw [ccSphereSeam_target]
  exact D.externalTarget_trace_disjoint c X DQ i a (D.sphereTarget_subset_compl (ccEquiv _ d).2.1)
    (D.external_sphereSeam_disjoint _ _)

/-- **Field `rim_external_disjoint`.** -/
theorem cc_rim_external_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))) :
    Disjoint (D.ccRimChart c X DQ i h b).target ((X.componentTori DQ i).collar a).target := by
  rw [ccRimChart_target]
  exact (D.externalTarget_trace_disjoint c X DQ i a (rimTarget_subset_compl _ _)
    (D.rim_external_disjoint _ _ _).symm).symm

/-- **Field `rim_torusSeam_disjoint`.** -/
theorem cc_rim_torusSeam_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (d : Fin (Nat.card {d // D.ccT c X DQ i d})) :
    Disjoint (D.ccRimChart c X DQ i h b).target (D.ccTorusSeam c X DQ i d).collar.target := by
  rw [ccRimChart_target, ccTorusSeam_target]
  exact (X.disjoint_transport_image (rimTarget_subset_compl _ _) (D.torusTarget_subset_compl _)
    (D.rim_torusSeam_disjoint _ _ _)).preimage _

/-- **Field `rim_sphereSeam_disjoint`.** -/
theorem cc_rim_sphereSeam_disjoint (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool)
    (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    Disjoint (D.ccRimChart c X DQ i h b).target (D.ccSphereSeam c X DQ i d).collar.target := by
  rw [ccRimChart_target, ccSphereSeam_target]
  exact (X.disjoint_transport_image (rimTarget_subset_compl _ _)
    (D.sphereTarget_subset_compl (ccEquiv _ d).2.1) (D.rim_sphereSeam_disjoint _ _ _)).preimage _

/-- **Field `sphereSeam_region_disjoint`.** -/
theorem cc_sphereSeam_region_disjoint (d : Fin (Nat.card {c' // D.ccS c X DQ i c'})) :
    Disjoint (D.ccSphereSeam c X DQ i d).collar.target (D.ccCirc c X DQ i).region := by
  rw [ccSphereSeam_target, region_ccCirc]
  exact (X.disjoint_transport_image (D.sphereTarget_subset_compl (ccEquiv _ d).2.1)
    D.region_subset_compl (D.sphereSeam_region_disjoint _)).preimage _

/-- **Field `sphereSeam_handle_disjoint`.** -/
theorem cc_sphereSeam_handle_disjoint (d : Fin (Nat.card {c' // D.ccS c X DQ i c'}))
    (h : Fin (Nat.card {h // D.ccH c X DQ i h})) :
    Disjoint (D.ccSphereSeam c X DQ i d).collar.target (range (D.ccHandle c X DQ i h).map) := by
  rw [ccSphereSeam_target, range_ccHandle]
  exact (X.disjoint_transport_image (D.sphereTarget_subset_compl (ccEquiv _ d).2.1)
    (D.handle_subset_compl _) (D.sphereSeam_handle_disjoint _ _)).preimage _

/-! ### The rim-product clause -/

/-- **The rim-product clause is inherited**: the same collar profiles, moved by the transport. -/
theorem cc_rimProduct (hR : D.RimProduct) (h : Fin (Nat.card {h // D.ccH c X DQ i h})) (b : Bool) :
    RimProductAt (D.ccRimChart c X DQ i h b) (D.ccHandle c X DQ i h) b := by
  obtain ⟨a, ha, ha', A, ρ, τ, hρ, hτ, hρ0, hτ0, hρd, hτd, heq⟩ := hR (ccEquiv _ h).1 b
  refine ⟨a, ha, ha', A, ρ, τ, hρ, hτ, hρ0, hτ0, hρd, hτd, ?_⟩
  intro θ x y w t hx hx' hy hy' hw ht
  have hp : (θ, (x, y)) ∈ (D.rimChart (ccEquiv _ h).1 b).source := by
    refine (D.rim_source _ b).mpr ⟨?_, ?_⟩
    · rw [abs_lt]
      constructor <;> linarith
    · rw [abs_lt]
      constructor <;> linarith
  apply Subtype.ext
  rw [ccRimChart_val h b hp, heq θ x y w t hx hx' hy hy' hw ht]
  rfl

end DecompositionCertificate

/-! ## Consumer (G5) -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- **Consumer (G5).** The inherited handles of a capped component carry rim charts whose rim
label is the handle rim, over corners of the component circle region labelled bijectively by the
handle ends; the rim-product clause of `D` is inherited by these rims and handles. -/
theorem exists_ccRims (hR : D.RimProduct) :
    ∃ (mh : ℕ) (H : Fin mh → EdgeHandle (GC.Topology.componentCarrier X.Q DQ i))
      (R : CircleRegion (GC.Topology.componentCarrier X.Q DQ i))
      (corner : Fin mh → Bool → Fin R.cornerCount)
      (χ : Fin mh → Bool → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
        (GC.Topology.componentCarrier X.Q DQ i).model (Circle × (ℝ × ℝ))
        (GC.Topology.componentCarrier X.Q DQ i).Carrier ∞),
      Bijective (fun hb : Fin mh × Bool => corner hb.1 hb.2) ∧
      (∀ h b, RimProductAt (χ h b) (H h) b) ∧
      ∀ h b, χ h b '' {p | p.2 = (0, 0)} =
        (fun x : ClosedCell 2 => (H h).map (x, iccEnd b)) '' diskRim :=
  ⟨_, D.ccHandle c X DQ i, D.ccCirc c X DQ i, D.ccHandleCorner c X DQ i, D.ccRimChart c X DQ i,
    D.cc_handleCorner_bijective c X DQ i, D.cc_rimProduct c X DQ i hR, D.cc_rim_label c X DQ i⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
