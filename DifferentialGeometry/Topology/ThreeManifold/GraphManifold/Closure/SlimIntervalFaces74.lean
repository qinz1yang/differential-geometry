import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusIntervalPiece74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74
import DifferentialGeometry.Topology.Manifold.ModelTransport

/-!
# Draft 74, package S2 (arcs), part 1: the model faces of the interval pieces

Lane S-JUNCTIONS (suffix `_JN74`, group G4a). For a smooth injective full-rank map
`F : S² × [0, 1] → W` (resp. `T² × [0, 1] → W`) the piece `sphereIntervalPiece F …` (resp.
`torusIntervalPiece F …`) has the model boundary `S² × {0, 1}` (resp. `T² × {0, 1}`), whose two
actual components are the end slices. These are the generic versions (for every `F`) of the
face facts of the S³ slim piece (`FC39P0SphereSlim.lean`): the `SlimPiecesV2` fields
`endFace`, `endFace_eq`, `endFace_exhausted` of an interval slim piece are

* `sphereIntervalFace74 F … b : ModelBoundaryFace (sphereIntervalPiece F …)` with
  `sphereIntervalFace74_val` (`= slimModelEnd (.sphereInterval …) b`) and
  `sphereIntervalFace74_exhausted`;
* the same for the torus (`torusIntervalFace74 …`), `W : CompactCarrier.{0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The sphere interval piece -/

section Sphere

local instance closureSphereConnected_JN74 : ConnectedSpace ClosureSphere.{u} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

variable {W : CompactCarrier.{u}} (F : ClosureSphere.{u} × Icc (0 : ℝ) 1 → W.Carrier)
  (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ F)
  (hFb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model F p)) (hFi : Injective F)

/-- The end sphere `S² × {b}` of the model `S² × [0, 1]`. -/
def sphereEndSet74 (b : Bool) : Set (ClosureSphere.{u} × Icc (0 : ℝ) 1) :=
  range fun z => (z, iccEnd b)

theorem mem_sphereEndSet74 {b : Bool} {p : ClosureSphere.{u} × Icc (0 : ℝ) 1} :
    p ∈ sphereEndSet74 b ↔ p.2 = iccEnd b := by
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro h
    exact ⟨p.1, Prod.ext rfl h.symm⟩

/-- **The model boundary of the sphere interval piece is `S² × {0, 1}`.** -/
theorem sphereInterval_boundary_eq74 :
    (𝓡∂ 3).boundary (sphereIntervalPiece F hF hFb hFi).Piece =
      sphereEndSet74 false ∪ sphereEndSet74 true := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 := DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary
    (ClosureSphere.{u} × Icc (0 : ℝ) 1)
  have h2 : ((𝓡 2).prod (𝓡∂ 1)).boundary (ClosureSphere.{u} × Icc (0 : ℝ) 1) =
      Set.prod univ ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)) :=
    ModelWithCorners.boundary_of_boundaryless_left
  refine h1.trans (h2.trans ?_)
  rw [boundary_Icc]
  ext p
  rw [mem_union, mem_sphereEndSet74, mem_sphereEndSet74]
  have hbot : (⊥ : Icc (0 : ℝ) 1) = iccEnd false := Subtype.ext (by simp [iccEnd])
  have htop : (⊤ : Icc (0 : ℝ) 1) = iccEnd true := Subtype.ext (by simp [iccEnd])
  constructor
  · rintro ⟨-, hp | hp⟩
    · exact Or.inl (hp.trans hbot)
    · exact Or.inr (hp.trans htop)
  · rintro (hp | hp)
    · exact ⟨mem_univ _, Or.inl (hp.trans hbot.symm)⟩
    · exact ⟨mem_univ _, Or.inr (hp.trans htop.symm)⟩

/-- The actual components of `S² × {0, 1}` are the two end spheres. -/
theorem connectedComponentIn_sphereEnd74 (b : Bool) {x : ClosureSphere.{u} × Icc (0 : ℝ) 1}
    (hx : x ∈ sphereEndSet74 b) :
    connectedComponentIn (sphereEndSet74 false ∪ sphereEndSet74 true) x = sphereEndSet74 b := by
  have hpre : IsPreconnected (sphereEndSet74.{u} b) :=
    isPreconnected_range (continuous_id.prodMk continuous_const)
  have hsub : sphereEndSet74.{u} b ⊆ sphereEndSet74 false ∪ sphereEndSet74 true := by
    cases b
    exacts [subset_union_left, subset_union_right]
  refine Subset.antisymm ?_ (hpre.subset_connectedComponentIn hx hsub)
  have hcont : Continuous fun p : ClosureSphere.{u} × Icc (0 : ℝ) 1 => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hUV : Disjoint {p : ClosureSphere.{u} × Icc (0 : ℝ) 1 | (p.2 : ℝ) < 1 / 2}
      {p | 1 / 2 < (p.2 : ℝ)} :=
    Set.disjoint_left.2 fun p (h1 : (p.2 : ℝ) < 1 / 2) (h2 : 1 / 2 < (p.2 : ℝ)) =>
      lt_asymm h1 h2
  have hend : ∀ {p : ClosureSphere.{u} × Icc (0 : ℝ) 1} (c : Bool), p ∈ sphereEndSet74 c →
      (p.2 : ℝ) = bif c then 1 else 0 := by
    intro p c hp
    rw [mem_sphereEndSet74] at hp
    rw [hp]
    cases c <;> rfl
  have hcov : connectedComponentIn (sphereEndSet74 false ∪ sphereEndSet74 true) x ⊆
      {p | (p.2 : ℝ) < 1 / 2} ∪ {p | 1 / 2 < (p.2 : ℝ)} := by
    intro p hp
    rcases connectedComponentIn_subset _ _ hp with h | h
    · left
      change (p.2 : ℝ) < 1 / 2
      rw [hend false h]
      norm_num
    · right
      change 1 / 2 < (p.2 : ℝ)
      rw [hend true h]
      norm_num
  have hxmem := mem_connectedComponentIn (hsub hx)
  have hxb := hend b hx
  rcases isPreconnected_connectedComponentIn.subset_or_subset (isOpen_lt hcont continuous_const)
    (isOpen_lt continuous_const hcont) hUV hcov with h | h
  · cases b
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · exact h'
      · have h1 : (p.2 : ℝ) < 1 / 2 := h hp
        rw [hend true h'] at h1
        norm_num at h1
    · have h1 : (x.2 : ℝ) < 1 / 2 := h hxmem
      rw [hxb] at h1
      norm_num at h1
  · cases b
    · have h1 : 1 / 2 < (x.2 : ℝ) := h hxmem
      rw [hxb] at h1
      norm_num at h1
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · have h1 : 1 / 2 < (p.2 : ℝ) := h hp
        rw [hend false h'] at h1
        norm_num at h1
      · exact h'

/-- A base point of the model sphere. -/
def sphereBasePoint74 : ClosureSphere.{u} :=
  ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩

theorem sphereEnd_mem_boundary74 (b : Bool) :
    (sphereBasePoint74, iccEnd b) ∈ (𝓡∂ 3).boundary (sphereIntervalPiece F hF hFb hFi).Piece := by
  rw [sphereInterval_boundary_eq74]
  cases b
  exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]

/-- **The actual model face of the end `b` of the sphere interval piece** (`S² × {b}`). -/
def sphereIntervalFace74 (b : Bool) : ModelBoundaryFace (sphereIntervalPiece F hF hFb hFi) :=
  ⟨sphereEndSet74 b, (sphereBasePoint74, iccEnd b), sphereEnd_mem_boundary74 F hF hFb hFi b, by
    rw [sphereInterval_boundary_eq74]
    exact (connectedComponentIn_sphereEnd74 b ⟨_, rfl⟩).symm⟩

/-- The face of the end `b` is the model end slice of `SlimModel.sphereInterval`. -/
theorem sphereIntervalFace74_val (b : Bool) :
    (sphereIntervalFace74 F hF hFb hFi b).1 =
      slimModelEnd (SlimModel.sphereInterval (sphereIntervalPieceDiffeo F hF hFb hFi)) b :=
  rfl

theorem sphereIntervalFace74_exhausted (Fc : ModelBoundaryFace (sphereIntervalPiece F hF hFb hFi)) :
    ∃ b, sphereIntervalFace74 F hF hFb hFi b = Fc := by
  obtain ⟨C, x, hx, rfl⟩ := Fc
  have hx' : x ∈ sphereEndSet74 false ∪ sphereEndSet74 true := by
    rw [← sphereInterval_boundary_eq74 F hF hFb hFi]
    exact hx
  have key : ∀ b, x ∈ sphereEndSet74 b → ∃ b', sphereIntervalFace74 F hF hFb hFi b' =
      ⟨connectedComponentIn ((𝓡∂ 3).boundary (sphereIntervalPiece F hF hFb hFi).Piece) x, x, hx,
        rfl⟩ := by
    intro b hb
    refine ⟨b, Subtype.ext ?_⟩
    change sphereEndSet74 b = connectedComponentIn
      ((𝓡∂ 3).boundary (sphereIntervalPiece F hF hFb hFi).Piece) x
    rw [sphereInterval_boundary_eq74]
    exact (connectedComponentIn_sphereEnd74 b hb).symm
  rcases hx' with h | h
  exacts [key false h, key true h]

/-- The image of the end slice under the piece map is `{F (z, b)}`. -/
theorem image_sphereInterval_end74 (b : Bool) :
    (sphereIntervalPiece F hF hFb hFi).map ''
        slimModelEnd (SlimModel.sphereInterval (sphereIntervalPieceDiffeo F hF hFb hFi)) b =
      range fun z => F (z, iccEnd b) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, rfl⟩

end Sphere

/-! ## The torus interval piece -/

section Torus

variable {W : CompactCarrier.{0}} (F : Torus × Icc (0 : ℝ) 1 → W.Carrier)
  (hF : ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ F)
  (hFb : ∀ p, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model F p)) (hFi : Injective F)

/-- The end torus `T² × {b}` of the model `T² × [0, 1]`. -/
def torusEndSet74 (b : Bool) : Set (Torus × Icc (0 : ℝ) 1) :=
  range fun z => (z, iccEnd b)

theorem mem_torusEndSet74 {b : Bool} {p : Torus × Icc (0 : ℝ) 1} :
    p ∈ torusEndSet74 b ↔ p.2 = iccEnd b := by
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro h
    exact ⟨p.1, Prod.ext rfl h.symm⟩

/-- **The model boundary of the torus interval piece is `T² × {0, 1}`.** -/
theorem torusInterval_boundary_eq74 :
    (𝓡∂ 3).boundary (torusIntervalPiece F hF hFb hFi).Piece =
      torusEndSet74 false ∪ torusEndSet74 true := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 : letI := torusIccChartedSpace74
      (𝓡∂ 3).boundary (Torus × Icc (0 : ℝ) 1) =
        (torusModel.prod (𝓡∂ 1)).boundary (Torus × Icc (0 : ℝ) 1) :=
    boundary_transHomeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) torusIccHomeomorph74
      torusIccCoordinates74 torusIccHomeomorph74_compat
  have h2 : (torusModel.prod (𝓡∂ 1)).boundary (Torus × Icc (0 : ℝ) 1) =
      Set.prod univ ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)) :=
    ModelWithCorners.boundary_of_boundaryless_left
  refine h1.trans (h2.trans ?_)
  rw [boundary_Icc]
  ext p
  rw [mem_union, mem_torusEndSet74, mem_torusEndSet74]
  have hbot : (⊥ : Icc (0 : ℝ) 1) = iccEnd false := Subtype.ext (by simp [iccEnd])
  have htop : (⊤ : Icc (0 : ℝ) 1) = iccEnd true := Subtype.ext (by simp [iccEnd])
  constructor
  · rintro ⟨-, hp | hp⟩
    · exact Or.inl (hp.trans hbot)
    · exact Or.inr (hp.trans htop)
  · rintro (hp | hp)
    · exact ⟨mem_univ _, Or.inl (hp.trans hbot.symm)⟩
    · exact ⟨mem_univ _, Or.inr (hp.trans htop.symm)⟩

/-- The actual components of `T² × {0, 1}` are the two end tori. -/
theorem connectedComponentIn_torusEnd74 (b : Bool) {x : Torus × Icc (0 : ℝ) 1}
    (hx : x ∈ torusEndSet74 b) :
    connectedComponentIn (torusEndSet74 false ∪ torusEndSet74 true) x = torusEndSet74 b := by
  have hpre : IsPreconnected (torusEndSet74 b) :=
    isPreconnected_range (continuous_id.prodMk continuous_const)
  have hsub : torusEndSet74 b ⊆ torusEndSet74 false ∪ torusEndSet74 true := by
    cases b
    exacts [subset_union_left, subset_union_right]
  refine Subset.antisymm ?_ (hpre.subset_connectedComponentIn hx hsub)
  have hcont : Continuous fun p : Torus × Icc (0 : ℝ) 1 => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hUV : Disjoint {p : Torus × Icc (0 : ℝ) 1 | (p.2 : ℝ) < 1 / 2}
      {p | 1 / 2 < (p.2 : ℝ)} :=
    Set.disjoint_left.2 fun p (h1 : (p.2 : ℝ) < 1 / 2) (h2 : 1 / 2 < (p.2 : ℝ)) =>
      lt_asymm h1 h2
  have hend : ∀ {p : Torus × Icc (0 : ℝ) 1} (c : Bool), p ∈ torusEndSet74 c →
      (p.2 : ℝ) = bif c then 1 else 0 := by
    intro p c hp
    rw [mem_torusEndSet74] at hp
    rw [hp]
    cases c <;> rfl
  have hcov : connectedComponentIn (torusEndSet74 false ∪ torusEndSet74 true) x ⊆
      {p | (p.2 : ℝ) < 1 / 2} ∪ {p | 1 / 2 < (p.2 : ℝ)} := by
    intro p hp
    rcases connectedComponentIn_subset _ _ hp with h | h
    · left
      change (p.2 : ℝ) < 1 / 2
      rw [hend false h]
      norm_num
    · right
      change 1 / 2 < (p.2 : ℝ)
      rw [hend true h]
      norm_num
  have hxmem := mem_connectedComponentIn (hsub hx)
  have hxb := hend b hx
  rcases isPreconnected_connectedComponentIn.subset_or_subset (isOpen_lt hcont continuous_const)
    (isOpen_lt continuous_const hcont) hUV hcov with h | h
  · cases b
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · exact h'
      · have h1 : (p.2 : ℝ) < 1 / 2 := h hp
        rw [hend true h'] at h1
        norm_num at h1
    · have h1 : (x.2 : ℝ) < 1 / 2 := h hxmem
      rw [hxb] at h1
      norm_num at h1
  · cases b
    · have h1 : 1 / 2 < (x.2 : ℝ) := h hxmem
      rw [hxb] at h1
      norm_num at h1
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · have h1 : 1 / 2 < (p.2 : ℝ) := h hp
        rw [hend false h'] at h1
        norm_num at h1
      · exact h'

theorem torusEnd_mem_boundary74 (b : Bool) :
    ((1 : Torus), iccEnd b) ∈ (𝓡∂ 3).boundary (torusIntervalPiece F hF hFb hFi).Piece := by
  rw [torusInterval_boundary_eq74]
  cases b
  exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]

/-- **The actual model face of the end `b` of the torus interval piece** (`T² × {b}`). -/
def torusIntervalFace74 (b : Bool) : ModelBoundaryFace (torusIntervalPiece F hF hFb hFi) :=
  ⟨torusEndSet74 b, ((1 : Torus), iccEnd b), torusEnd_mem_boundary74 F hF hFb hFi b, by
    rw [torusInterval_boundary_eq74]
    exact (connectedComponentIn_torusEnd74 b ⟨_, rfl⟩).symm⟩

/-- The face of the end `b` is the model end slice of `SlimModel.torusInterval`. -/
theorem torusIntervalFace74_val (b : Bool) :
    (torusIntervalFace74 F hF hFb hFi b).1 =
      slimModelEnd (SlimModel.torusInterval (torusIntervalPieceDiffeo F hF hFb hFi)) b :=
  rfl

theorem torusIntervalFace74_exhausted (Fc : ModelBoundaryFace (torusIntervalPiece F hF hFb hFi)) :
    ∃ b, torusIntervalFace74 F hF hFb hFi b = Fc := by
  obtain ⟨C, x, hx, rfl⟩ := Fc
  have hx' : x ∈ torusEndSet74 false ∪ torusEndSet74 true := by
    rw [← torusInterval_boundary_eq74 F hF hFb hFi]
    exact hx
  have key : ∀ b, x ∈ torusEndSet74 b → ∃ b', torusIntervalFace74 F hF hFb hFi b' =
      ⟨connectedComponentIn ((𝓡∂ 3).boundary (torusIntervalPiece F hF hFb hFi).Piece) x, x, hx,
        rfl⟩ := by
    intro b hb
    refine ⟨b, Subtype.ext ?_⟩
    change torusEndSet74 b = connectedComponentIn
      ((𝓡∂ 3).boundary (torusIntervalPiece F hF hFb hFi).Piece) x
    rw [torusInterval_boundary_eq74]
    exact (connectedComponentIn_torusEnd74 b hb).symm
  rcases hx' with h | h
  exacts [key false h, key true h]

/-- The image of the end slice under the piece map is `{F (z, b)}`. -/
theorem image_torusInterval_end74 (b : Bool) :
    (torusIntervalPiece F hF hFb hFi).map ''
        slimModelEnd (SlimModel.torusInterval (torusIntervalPieceDiffeo F hF hFb hFi)) b =
      range fun z => F (z, iccEnd b) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, rfl⟩

end Torus

end GC.GraphManifold.Assembly.FC39P0
