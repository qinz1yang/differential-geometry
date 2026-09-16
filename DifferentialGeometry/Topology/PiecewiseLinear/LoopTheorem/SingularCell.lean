import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.LoopSpace.FreeHomotopyInjection
import DifferentialGeometry.Topology.LoopSpace.FreeHomotopySurjection
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerivedNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

structure SingularTwoCell (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  domain : Set (EuclideanSpace ℝ (Fin 2))
  isPLBall_domain : IsPLBall 2 domain
  toFun : EuclideanSpace ℝ (Fin 2) → M
  isPLOn : IsPLOn 2 3 toFun domain

instance {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    CoeFun (SingularTwoCell M) (fun _ => EuclideanSpace ℝ (Fin 2) → M) :=
  ⟨SingularTwoCell.toFun⟩

namespace SingularTwoCell

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def restrict (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) : SingularTwoCell M where
  domain := P
  isPLBall_domain := hP
  toFun := D
  isPLOn := D.isPLOn.mono_of_isPolyhedron hP.isPolyhedron hPD

@[simp]
theorem restrict_domain (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    (D.restrict hP hPD).domain = P :=
  rfl

@[simp]
theorem restrict_apply (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) (x : EuclideanSpace ℝ (Fin 2)) :
    D.restrict hP hPD x = D x :=
  rfl

theorem continuousOn (D : SingularTwoCell M) : ContinuousOn D D.domain :=
  fun x hx => (D.isPLOn x hx).continuousWithinAt

theorem frontier_subset_domain (D : SingularTwoCell M) : frontier D.domain ⊆ D.domain := by
  have hclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  simpa only [hclosed.closure_eq] using
    (frontier_subset_closure : frontier D.domain ⊆ closure D.domain)

def boundary (D : SingularTwoCell M) : C(frontier D.domain, M) where
  toFun x := D x
  continuous_toFun :=
    continuousOn_iff_continuous_domRestrict.mp
      (D.continuousOn.mono D.frontier_subset_domain)

@[simp]
theorem boundary_apply (D : SingularTwoCell M) (x : frontier D.domain) :
    D.boundary x = D x :=
  rfl

theorem isPLSphere_frontier (D : SingularTwoCell M) : IsPLSphere 1 (frontier D.domain) :=
  D.isPLBall_domain.isPLSphere_frontier

def IsNonsingular (D : SingularTwoCell M) : Prop :=
  InjOn D D.domain

theorem isNonsingular_iff (D : SingularTwoCell M) :
    D.IsNonsingular ↔ InjOn D D.domain :=
  Iff.rfl

theorem range_boundary_restrict (D : SingularTwoCell M)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    Set.range (D.restrict hP hPD).boundary = D '' frontier P := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem restrict_isNonsingular_iff (D : SingularTwoCell M)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    (D.restrict hP hPD).IsNonsingular ↔ InjOn D P :=
  Iff.rfl

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology

universe u

namespace FreeLoop

variable {X : Type u} [TopologicalSpace X]

open Classical in
noncomputable def basedRepresentative [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    basedCircleLoop x :=
  Classical.choose (exists_basedCircle_free_homotopic x γ)

theorem basedRepresentative_homotopic [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    (FreeLoop.basedRepresentative γ x).val.Homotopic γ :=
  Classical.choose_spec (exists_basedCircle_free_homotopic x γ)

open Classical in
noncomputable def fundamentalGroupRepresentative [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk (circleToPath (FreeLoop.basedRepresentative γ x))

open Classical in
noncomputable def conjugacyClass [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    ConjClasses (FundamentalGroup X x) :=
  ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x)

end FreeLoop

def basedCircleFundamentalGroupClass {X : Type u} [TopologicalSpace X] {x : X}
    (γ : basedCircleLoop x) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk (circleToPath γ)

theorem isConj_circleToPath_of_freeHomotopic {X : Type u} [TopologicalSpace X] {x : X}
    (γ δ : basedCircleLoop x) (h : γ.val.Homotopic δ.val) :
    IsConj (basedCircleFundamentalGroupClass γ) (basedCircleFundamentalGroupClass δ) := by
  obtain ⟨H⟩ := h
  let r : FundamentalGroup X x :=
    Path.Homotopic.Quotient.mk (basedCircleHomotopyTrack γ δ H)
  have heq := Path.Homotopic.Quotient.eq.mpr
    (basedCircleHomotopyTrack_commutes γ δ H)
  change r * basedCircleFundamentalGroupClass γ =
    basedCircleFundamentalGroupClass δ * r at heq
  rw [isConj_iff]
  refine ⟨r, ?_⟩
  calc
    r * basedCircleFundamentalGroupClass γ * r⁻¹ =
        (basedCircleFundamentalGroupClass δ * r) * r⁻¹ :=
      congrArg (fun z => z * r⁻¹) heq
    _ = basedCircleFundamentalGroupClass δ := by
      rw [mul_assoc, mul_inv_cancel, mul_one]

theorem FreeLoop.conjugacyClass_eq_mk_circleToPath
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (δ : basedCircleLoop x)
    (hδ : δ.val.Homotopic γ) :
    FreeLoop.conjugacyClass γ x =
      ConjClasses.mk (basedCircleFundamentalGroupClass δ) := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact isConj_circleToPath_of_freeHomotopic (FreeLoop.basedRepresentative γ x) δ
    ((FreeLoop.basedRepresentative_homotopic γ x).trans hδ.symm)

theorem FreeLoop.conjugacyClass_eq_of_homotopic
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {γ δ : freeLoop X} (h : γ.Homotopic δ) (x : X) :
    FreeLoop.conjugacyClass γ x = FreeLoop.conjugacyClass δ x := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact isConj_circleToPath_of_freeHomotopic (FreeLoop.basedRepresentative γ x)
    (FreeLoop.basedRepresentative δ x) ((FreeLoop.basedRepresentative_homotopic γ x).trans
      (h.trans (FreeLoop.basedRepresentative_homotopic δ x).symm))

open Classical in
noncomputable def loopRepresentativeAlong
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q : Path x y) (γ : basedCircleLoop y) : FundamentalGroup X x :=
  DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (basedCircleFundamentalGroupClass γ)

open Classical in
theorem loopRepresentativeAlong_pathToCircle
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q : Path x y) (p : Path y y) :
    loopRepresentativeAlong q
        (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop y) =
      DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
        (Path.Homotopic.Quotient.mk p) := by
  unfold loopRepresentativeAlong basedCircleFundamentalGroupClass
  rw [show circleToPath
      (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop y) = p from
    (basedPathCircleHomeomorph y).left_inv p]

theorem loopRepresentativeAlong_connector
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q q' : Path x y) (γ : basedCircleLoop y) :
    loopRepresentativeAlong q' γ =
      MulAut.conj (DifferentialGeometry.Topology.connectorLoop q q')⁻¹
        (loopRepresentativeAlong q γ) :=
  DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint_connector q q'
    (basedCircleFundamentalGroupClass γ)

theorem loopRepresentativeAlong_isConj
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q q' : Path x y) (γ : basedCircleLoop y) :
    IsConj (loopRepresentativeAlong q γ) (loopRepresentativeAlong q' γ) := by
  rw [isConj_iff]
  refine ⟨(connectorLoop q q')⁻¹, ?_⟩
  rw [loopRepresentativeAlong_connector q q' γ, MulAut.conj_apply]

theorem FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x y : X} (q : Path x y) (γ : basedCircleLoop y) :
    FreeLoop.conjugacyClass γ.val x = ConjClasses.mk (loopRepresentativeAlong q γ) := by
  let p : Path x x := q.trans ((circleToPath γ).trans q.symm)
  let δ : basedCircleLoop x := basedPathCircleHomeomorph x p
  have hδ : δ.val.Homotopic γ.val := by
    change (pathToCircle p).Homotopic γ.val
    refine (pathToCircle_conjugate_homotopic q (circleToPath γ)).trans ?_
    rw [show pathToCircle (circleToPath γ) = γ.val from
      congrArg Subtype.val ((basedPathCircleHomeomorph y).apply_symm_apply γ)]
  calc
    FreeLoop.conjugacyClass γ.val x =
        ConjClasses.mk (basedCircleFundamentalGroupClass δ) :=
      FreeLoop.conjugacyClass_eq_mk_circleToPath γ.val x δ hδ
    _ = ConjClasses.mk (loopRepresentativeAlong q γ) := by
      congr 1
      rw [basedCircleFundamentalGroupClass,
        show circleToPath δ = p from (basedPathCircleHomeomorph x).left_inv p]
      unfold p loopRepresentativeAlong
      rw [fundamentalGroupChangeBasepoint_apply]
      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
      exact (Path.Homotopic.Quotient.trans_assoc _ _ _).symm

def conjugacyClassMeets {G : Type*} [Group G]
    (C : ConjClasses G) (N : Subgroup G) : Prop :=
  ∃ g, g ∈ C.carrier ∧ g ∈ N

theorem conjugacyClassMeets_iff_carrier_subset
    {G : Type*} [Group G] (C : ConjClasses G) (N : Subgroup G) [N.Normal] :
    conjugacyClassMeets C N ↔ C.carrier ⊆ (N : Set G) := by
  constructor
  · rintro ⟨g, hg, hgN⟩ h hh
    have hconj : IsConj g h := ConjClasses.mk_eq_mk_iff_isConj.mp
      ((ConjClasses.mem_carrier_iff_mk_eq.mp hg).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp hh).symm)
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    exact ‹N.Normal›.conj_mem g hgN c
  · intro h
    obtain ⟨g, rfl⟩ := C.exists_rep
    refine ⟨g, ?_, h ?_⟩ <;> exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl

theorem conjugacyClass_subset_or_disjoint_normal
    {G : Type*} [Group G] (C : ConjClasses G) (N : Subgroup G) [N.Normal] :
    C.carrier ⊆ (N : Set G) ∨ Disjoint C.carrier (N : Set G) := by
  classical
  by_cases h : conjugacyClassMeets C N
  · exact Or.inl ((conjugacyClassMeets_iff_carrier_subset C N).mp h)
  · right
    exact Set.disjoint_left.mpr fun g hg hgN => h ⟨g, hg, hgN⟩

def loopClassMeets {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) : Prop :=
  conjugacyClassMeets (FreeLoop.conjugacyClass γ x) N

theorem loopClassMeets_iff_carrier_subset
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    loopClassMeets γ x N ↔
      (FreeLoop.conjugacyClass γ x).carrier ⊆ (N : Set _) := by
  exact conjugacyClassMeets_iff_carrier_subset (FreeLoop.conjugacyClass γ x) N

theorem loopConjugacyClass_subset_or_disjoint_normal
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    (FreeLoop.conjugacyClass γ x).carrier ⊆ (N : Set _) ∨
      Disjoint (FreeLoop.conjugacyClass γ x).carrier (N : Set _) := by
  exact conjugacyClass_subset_or_disjoint_normal (FreeLoop.conjugacyClass γ x) N

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def vertexCollisionPairs (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) : Finset (Finset E) :=
  ((simplicialComplexVertices K).powersetCard 2).filter
    (fun s => ¬ InjOn f (s : Set E))

@[simp]
theorem mem_vertexCollisionPairs (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) (s : Finset E) :
    s ∈ vertexCollisionPairs K f ↔
      (s : Set E) ⊆ K.vertices ∧ s.card = 2 ∧ ¬ InjOn f (s : Set E) := by
  classical
  rw [vertexCollisionPairs, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hinj⟩
    exact ⟨fun v hv => mem_simplicialComplexVertices K |>.mp (hsub hv), hcard, hinj⟩
  · rintro ⟨hsub, hcard, hinj⟩
    exact ⟨⟨fun v hv => mem_simplicialComplexVertices K |>.mpr (hsub hv), hcard⟩, hinj⟩

open Classical in
noncomputable def simplicialComplexity (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) : ℕ :=
  (vertexCollisionPairs K f).card

open Classical in
theorem vertexCollisionPairs_image_subset_of_vertex_injection
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : MapsTo r L.vertices K.vertices) (hinj : InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v) :
    (vertexCollisionPairs L g).image (fun s => s.image r) ⊆
      vertexCollisionPairs K f := by
  intro s hs
  rw [Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [mem_vertexCollisionPairs] at ht ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hr (ht.1 hv)
  · calc
      (t.image r).card = t.card := Finset.card_image_of_injOn (hinj.mono ht.1)
      _ = 2 := ht.2.1
  · intro hfinj
    apply ht.2.2
    intro v hv w hw hgw
    apply hinj (ht.1 hv) (ht.1 hw)
    apply hfinj
      (by exact Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      (by exact Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    calc
      f (r v) = g v := hfactor v (ht.1 hv)
      _ = g w := hgw
      _ = f (r w) := (hfactor w (ht.1 hw)).symm

open Classical in
theorem simplicialComplexity_lt_of_vertex_injection
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : MapsTo r L.vertices K.vertices) (hinj : InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v)
    (hmissing : ∃ s ∈ vertexCollisionPairs K f,
      s ∉ (vertexCollisionPairs L g).image (fun t => t.image r)) :
    simplicialComplexity L g < simplicialComplexity K f := by
  have hsubset := vertexCollisionPairs_image_subset_of_vertex_injection
    K L f g r hr hinj hfactor
  have himageInj : InjOn (fun s : Finset F' => s.image r)
      (vertexCollisionPairs L g : Set (Finset F')) := by
    intro a ha b hb hab
    have haVertices := (mem_vertexCollisionPairs L g a).mp ha |>.1
    have hbVertices := (mem_vertexCollisionPairs L g b).mp hb |>.1
    have habInj : InjOn r ((a ∪ b : Finset F') : Set F') :=
      hinj.mono fun x hx => by
        rcases Finset.mem_union.mp hx with hxa | hxb
        · exact haVertices hxa
        · exact hbVertices hxb
    exact (Finset.image_eq_image_iff_of_injOn habInj
      Finset.subset_union_left Finset.subset_union_right).mp hab
  obtain ⟨s, hs, hsMissing⟩ := hmissing
  unfold simplicialComplexity
  calc
    (vertexCollisionPairs L g).card =
        ((vertexCollisionPairs L g).image (fun t => t.image r)).card :=
      (Finset.card_image_of_injOn himageInj).symm
    _ < (vertexCollisionPairs K f).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsubset, ?_⟩
      intro heq
      exact hsMissing (by simpa only [heq] using hs)

open Classical in
theorem simplicialComplexity_lt_of_vertex_injection_of_missing_collision
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : MapsTo r L.vertices K.vertices) (hinj : InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v)
    (hmissing : ∃ v ∈ K.vertices, ∃ w ∈ K.vertices,
      v ≠ w ∧ f v = f w ∧ w ∉ r '' L.vertices) :
    simplicialComplexity L g < simplicialComplexity K f := by
  apply simplicialComplexity_lt_of_vertex_injection K L f g r hr hinj hfactor
  obtain ⟨v, hv, w, hw, hvw, hfvw, hwRange⟩ := hmissing
  let s : Finset E' := {v, w}
  refine ⟨s, ?_, ?_⟩
  · rw [mem_vertexCollisionPairs]
    refine ⟨?_, by simp [s, hvw], ?_⟩
    · intro x hx
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · intro hfinj
      exact hvw (hfinj (by simp [s]) (by simp [s]) hfvw)
  · intro hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, hts⟩ := hs
    have hwImage : w ∈ t.image r := by
      rw [hts]
      simp [s]
    obtain ⟨z, hzt, hrz⟩ := Finset.mem_image.mp hwImage
    apply hwRange
    exact ⟨z, (mem_vertexCollisionPairs L g t).mp ht |>.1 hzt, hrz⟩

open Classical in
theorem simplicialComplexity_eq_zero_iff_injOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F) :
    simplicialComplexity K f = 0 ↔ InjOn f K.vertices := by
  constructor
  · intro h v hv w hw hvw
    by_contra hvw'
    have hp : ({v, w} : Finset E) ∈ vertexCollisionPairs K f := by
      rw [mem_vertexCollisionPairs]
      refine ⟨?_, by simp [hvw'], ?_⟩
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hw
      · intro hinj
        exact hvw' (hinj (by simp) (by simp) hvw)
    have hempty : vertexCollisionPairs K f = ∅ := Finset.card_eq_zero.mp h
    rw [hempty] at hp
    simp at hp
  · intro hinj
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hdata := (mem_vertexCollisionPairs K f s).mp hs
    exact hdata.2.2 (hinj.mono hdata.1)

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem injOn_simplicialMap_of_injOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (φ : E → F) (hφ : InjOn φ K.vertices)
    (hfaces : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    InjOn (simplicialMap K φ) K.space := by
  let ψ : F → E := Function.invFunOn φ K.vertices
  have hψφ : ∀ s ∈ K.faces, ∀ v ∈ s, ψ (φ v) = v := by
    intro s hs v hv
    apply hφ.leftInvOn_invFunOn
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  have hleft : ∀ x ∈ K.space, simplicialMap L ψ (simplicialMap K φ x) = x :=
    fun x hx => simplicialMap_simplicialMap K L φ ψ hfaces hψφ hx
  intro x hx y hy hxy
  rw [← hleft x hx, ← hleft y hy, hxy]

theorem injOn_vertices_of_injOn_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hφ : InjOn (simplicialMap K φ) K.space) : InjOn φ K.vertices := by
  intro v hv w hw hvw
  apply hφ (K.vertices_subset_space hv) (K.vertices_subset_space hw)
  rw [simplicialMap_vertex K φ hv, simplicialMap_vertex K φ hw, hvw]

open Classical in
theorem simplicialComplexity_eq_zero_iff_injOn_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) (φ : E → F)
    (hfaces : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    simplicialComplexity K φ = 0 ↔ InjOn (simplicialMap K φ) K.space := by
  rw [simplicialComplexity_eq_zero_iff_injOn_vertices]
  exact ⟨fun h => injOn_simplicialMap_of_injOn_vertices K L φ h hfaces,
    injOn_vertices_of_injOn_simplicialMap K φ⟩

open Classical in
noncomputable def normalSystemManifoldComplex
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
    Geometry.SimplicialComplex ℝ E :=
  relativeDerivedNeighborhood hL L

open Classical in
noncomputable def normalSystemBoundaryComplex
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
    Geometry.SimplicialComplex ℝ E :=
  boundaryComplex 3 (normalSystemManifoldComplex K L hL)

open Classical in
noncomputable def normalSystemBoundaryNeighborhood
    (K L C : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
    Geometry.SimplicialComplex ℝ E :=
  derivedNeighborhood (normalSystemBoundaryComplex K L hL) C

open Classical in
abbrev normalSystemBoundaryNeighborhoodSpace
    (K L C : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :=
  (normalSystemBoundaryNeighborhood K L C hL).space

open Classical in
noncomputable def normalSystemLoopConjugacyClass
    {Y : Type*} [TopologicalSpace Y] (x : Y) (γ : freeLoop Y) (q : Path x (γ 0)) :
    ConjClasses (FundamentalGroup Y x) :=
  ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))

open Classical in
structure NormalSystem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  ambientComplex : Geometry.SimplicialComplex ℝ E
  imageComplex : Geometry.SimplicialComplex ℝ E
  loopComplex : Geometry.SimplicialComplex ℝ E
  sourceComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))
  finite_ambient : ambientComplex.faces.Finite
  finite_source : sourceComplex.faces.Finite
  source_isPLBall : IsPLBall 2 sourceComplex.space
  vertexMap : EuclideanSpace ℝ (Fin 2) → E
  source_faces_map : ∀ s ∈ sourceComplex.faces, s.image vertexMap ∈ imageComplex.faces
  image_space : imageComplex.space = simplicialMap sourceComplex vertexMap '' sourceComplex.space
  image_faces_subset_ambient : imageComplex.faces ⊆ ambientComplex.faces
  isManifold : IsCombinatorialManifoldWithBoundary 3
    (normalSystemManifoldComplex ambientComplex imageComplex image_faces_subset_ambient)
  manifold_space :
    (normalSystemManifoldComplex ambientComplex imageComplex
      image_faces_subset_ambient).space =
        (derivedNeighborhood ambientComplex imageComplex).space
  loop_space : loopComplex.space =
    simplicialMap sourceComplex vertexMap '' frontier sourceComplex.space
  loop_faces_subset_boundary : loopComplex.faces ⊆
    (normalSystemBoundaryComplex ambientComplex imageComplex
      image_faces_subset_ambient).faces
  image_inter_boundary : imageComplex.space ∩
    (normalSystemBoundaryComplex ambientComplex imageComplex
      image_faces_subset_ambient).space = loopComplex.space
  basepoint : normalSystemBoundaryNeighborhoodSpace ambientComplex imageComplex loopComplex
    image_faces_subset_ambient
  boundaryLoop : freeLoop
    (normalSystemBoundaryNeighborhoodSpace ambientComplex imageComplex loopComplex
      image_faces_subset_ambient)
  boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space
  boundaryLoop_eq : ∀ θ, (boundaryLoop θ : E) =
    simplicialMap sourceComplex vertexMap (boundaryParam θ)
  connector : Path basepoint (boundaryLoop 0)
  normalSubgroup : Subgroup (FundamentalGroup
    (normalSystemBoundaryNeighborhoodSpace ambientComplex imageComplex loopComplex
      image_faces_subset_ambient) basepoint)
  normal : normalSubgroup.Normal
  loopClass_avoids_normal : ¬conjugacyClassMeets
    (normalSystemLoopConjugacyClass basepoint boundaryLoop connector) normalSubgroup

namespace NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundaryLoop_range (S : NormalSystem E) :
    Set.range (fun θ => (S.boundaryLoop θ : E)) = S.loopComplex.space := by
  rw [S.loop_space]
  apply Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    change (S.boundaryLoop θ : E) ∈ _
    rw [S.boundaryLoop_eq θ]
    exact ⟨S.boundaryParam θ, (S.boundaryParam θ).property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨θ, hθ⟩ := S.boundaryParam.surjective ⟨x, hx⟩
    refine ⟨θ, ?_⟩
    change (S.boundaryLoop θ : E) = _
    rw [S.boundaryLoop_eq θ]
    exact congrArg (simplicialMap S.sourceComplex S.vertexMap)
      (congrArg Subtype.val hθ)

open Classical in
noncomputable def manifoldComplex (S : NormalSystem E) : Geometry.SimplicialComplex ℝ E :=
  normalSystemManifoldComplex S.ambientComplex S.imageComplex S.image_faces_subset_ambient

open Classical in
noncomputable def boundaryComplex (S : NormalSystem E) : Geometry.SimplicialComplex ℝ E :=
  normalSystemBoundaryComplex S.ambientComplex S.imageComplex S.image_faces_subset_ambient

open Classical in
noncomputable def boundaryNeighborhood (S : NormalSystem E) :
    Geometry.SimplicialComplex ℝ E :=
  normalSystemBoundaryNeighborhood S.ambientComplex S.imageComplex S.loopComplex
    S.image_faces_subset_ambient

open Classical in
abbrev boundaryNeighborhoodSpace (S : NormalSystem E) :=
  normalSystemBoundaryNeighborhoodSpace S.ambientComplex S.imageComplex S.loopComplex
    S.image_faces_subset_ambient

open Classical in
noncomputable def singularMap (S : NormalSystem E) : EuclideanSpace ℝ (Fin 2) → E :=
  simplicialMap S.sourceComplex S.vertexMap

def boundaryBasedLoop (S : NormalSystem E) : basedCircleLoop (S.boundaryLoop 0) :=
  ⟨S.boundaryLoop, rfl⟩

open Classical in
noncomputable def loopRepresentative (S : NormalSystem E) :
    FundamentalGroup S.boundaryNeighborhoodSpace S.basepoint :=
  loopRepresentativeAlong S.connector S.boundaryBasedLoop

open Classical in
noncomputable def loopConjugacyClass (S : NormalSystem E) :
    ConjClasses (FundamentalGroup S.boundaryNeighborhoodSpace S.basepoint) :=
  normalSystemLoopConjugacyClass S.basepoint S.boundaryLoop S.connector

def loopClassMeetsNormal (S : NormalSystem E) : Prop :=
  conjugacyClassMeets S.loopConjugacyClass S.normalSubgroup

def IsNonsingular (S : NormalSystem E) : Prop :=
  InjOn S.singularMap S.sourceComplex.space

open Classical in
noncomputable def complexity (S : NormalSystem E) : ℕ := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  exact simplicialComplexity S.sourceComplex S.vertexMap

open Classical in
theorem complexity_eq_zero_iff_isNonsingular (S : NormalSystem E) :
    S.complexity = 0 ↔ S.IsNonsingular := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  exact simplicialComplexity_eq_zero_iff_injOn_simplicialMap
    S.sourceComplex S.imageComplex S.vertexMap S.source_faces_map

open Classical in
theorem singularMap_mapsTo_image (S : NormalSystem E) :
    MapsTo S.singularMap S.sourceComplex.space S.imageComplex.space :=
  simplicialMap_mapsTo S.sourceComplex S.imageComplex S.vertexMap S.source_faces_map

open Classical in
theorem image_faces_subset_manifoldComplex (S : NormalSystem E) :
    S.imageComplex.faces ⊆ S.manifoldComplex.faces := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact faces_subset_relativeDerivedNeighborhood S.image_faces_subset_ambient S.imageComplex
    Subset.rfl S.image_faces_subset_ambient

open Classical in
theorem image_space_subset_manifoldComplex (S : NormalSystem E) :
    S.imageComplex.space ⊆ S.manifoldComplex.space := by
  exact space_mono_of_faces_subset S.image_faces_subset_manifoldComplex

open Classical in
theorem image_space_subset_regularNeighborhood (S : NormalSystem E) :
    S.imageComplex.space ⊆
      (derivedNeighborhood S.ambientComplex S.imageComplex).space := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact subcomplex_space_subset_derivedNeighborhood S.image_faces_subset_ambient

open Classical in
theorem singularMap_mapsTo_manifoldComplex (S : NormalSystem E) :
    MapsTo S.singularMap S.sourceComplex.space S.manifoldComplex.space :=
  S.singularMap_mapsTo_image.mono_right S.image_space_subset_manifoldComplex

open Classical in
theorem manifoldComplex_faces_finite (S : NormalSystem E) : S.manifoldComplex.faces.Finite := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact relativeDerivedNeighborhood_faces_finite
    S.image_faces_subset_ambient S.imageComplex

open Classical in
theorem boundaryComplex_faces_finite (S : NormalSystem E) : S.boundaryComplex.faces.Finite := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact PiecewiseLinear.boundaryComplex_faces_finite 3 S.manifoldComplex

open Classical in
theorem boundaryNeighborhood_faces_finite (S : NormalSystem E) :
    S.boundaryNeighborhood.faces.Finite := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhood_faces_finite S.boundaryComplex S.loopComplex

open Classical in
noncomputable def imageStrongDeformationRetract [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      (derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact derivedNeighborhoodStrongDeformationRetract S.image_faces_subset_ambient

open Classical in
noncomputable def imageFundamentalGroupInclusionEquiv [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (x : derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) :
    FundamentalGroup (derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) x ≃*
      FundamentalGroup (derivedNeighborhoodSpace S.ambientComplex S.imageComplex) x.1 := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact derivedNeighborhoodFundamentalGroupInclusionEquiv
    (K := S.ambientComplex) (L := S.imageComplex)
    S.image_faces_subset_ambient x

open Classical in
noncomputable def loopStrongDeformationRetract [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      (derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhoodStrongDeformationRetract S.loop_faces_subset_boundary

open Classical in
noncomputable def loopFundamentalGroupInclusionEquiv [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (x : derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) :
    FundamentalGroup (derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) x ≃*
      FundamentalGroup (derivedNeighborhoodSpace S.boundaryComplex S.loopComplex) x.1 := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhoodFundamentalGroupInclusionEquiv
    (K := S.boundaryComplex) (L := S.loopComplex)
    S.loop_faces_subset_boundary x

open Classical in
theorem loopConjugacyClass_eq_of_connector (S : NormalSystem E)
    (q : Path S.basepoint (S.boundaryLoop 0)) :
    normalSystemLoopConjugacyClass S.basepoint S.boundaryLoop q =
      S.loopConjugacyClass := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact loopRepresentativeAlong_isConj q S.connector S.boundaryBasedLoop

open Classical in
theorem loopConjugacyClass_disjoint_normal (S : NormalSystem E) :
    Disjoint S.loopConjugacyClass.carrier (S.normalSubgroup : Set _) := by
  let _ : S.normalSubgroup.Normal := S.normal
  rcases conjugacyClass_subset_or_disjoint_normal
    S.loopConjugacyClass S.normalSubgroup with hsub | hdis
  · exact (S.loopClass_avoids_normal
      ((conjugacyClassMeets_iff_carrier_subset
        S.loopConjugacyClass S.normalSubgroup).mpr hsub)).elim
  · exact hdis

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
