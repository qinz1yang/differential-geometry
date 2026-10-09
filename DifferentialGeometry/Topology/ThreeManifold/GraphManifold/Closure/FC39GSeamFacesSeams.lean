import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesParams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar
import DifferentialGeometry.Topology.Manifold.HalfSpaceCenteredChart

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): the seams of the shared faces

Steps G2–G6 of the lane sheet (`build-logs/resume/sheet-FC39-G-SF.md`). For a shared face `σ` and
the GIVEN safe neighbourhoods `N` (`SharedSafe Rw N`, chosen first, D58-6):

* G2 `exists_sharedParam_sphere_GSF` / `_torus_GSF` — the ambient parametrization of `σ` from the
  slim model: `z ↦ (slim j).map (e (z, iccEnd b))`, a smooth embedding into `W` (injective
  differential by the chain rule, values in `W.interior`; `isSmoothEmbedding_of_interior_GSF`);
* G3 `exists_neighbourFn_GSF` — the defining function of the neighbour face on its `near` set: the
  zero `ratio i` (`range_eq`: the zero row is `{ratio ≤ 0}`), or the cusp function (`near_eq`);
* G4 `exists_safeOpen_GSF` — an open `V ⊇ σ` with `closure V ⊆ N σ` meeting no row set other than
  the slim owner and the neighbour (the other rows are compact and miss `σ`:
  `sharedSet_disjoint_rowSet_GSF`);
* G5–G6 `exists_sphereSeam_GSF` / `exists_torusSeam_GSF` — the seam of
  `exists_sphereSeam_of_regular_level` / `exists_torusSeam_of_regular_level` inside `V ∩ near`; its
  negative side lies in the neighbour row (`f ≤ 0`), its positive side in the slim row (`cover`:
  the edge piece and the circle region miss `closure (N σ)`, the other rows miss `V`, and `f > 0`
  excludes the neighbour), and its closed collar lies in `N σ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## G2: the ambient parametrization of a shared face -/

/-- The end point `iccEnd b` of `[0, 1]` is a model boundary point. -/
theorem isBoundaryPoint_iccEnd_GSF (b : Bool) :
    (𝓡∂ 1).IsBoundaryPoint (iccEnd b : Icc (0 : ℝ) 1) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  change (iccEnd b : Icc (0 : ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1)
  rw [boundary_Icc]
  cases b
  · left
    exact Subtype.ext (by simp [iccEnd])
  · right
    exact Subtype.ext (by simp [iccEnd])

/-- **G2 kernel.** The end slice of a product piece `S × [0, 1]`, inside `W.interior`, is a smooth
embedding of `S` into `W`. -/
theorem isSmoothEmbedding_endSlice_GSF (P : PieceEmbedding W) {ES HS : Type*}
    [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES] [Nontrivial ES]
    [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless] {S : Type*}
    [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S] [CompactSpace S]
    (e : (S × Icc (0 : ℝ) 1) ≃ₘ⟮IS.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece) (b : Bool)
    (hint : ∀ z, P.map (e (z, iccEnd b)) ∈ W.interior) :
    IsSmoothEmbedding IS W.model ∞ (fun z => P.map (e (z, iccEnd b))) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hincl : IsSmoothEmbedding IS (IS.prod (𝓡∂ 1)) ∞
      (fun z : S => (z, (iccEnd b : Icc (0 : ℝ) 1))) :=
    @isSmoothEmbedding_prodMk_boundary_point 0 (Icc (0 : ℝ) 1) _
      (inferInstance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))
      (inferInstance : IsManifold (𝓡∂ 1) ∞ (Icc (0 : ℝ) 1)) _ _ S _ _ _ _ _
      IS _ (iccEnd b) (isBoundaryPoint_iccEnd_GSF b)
  have hsm : ContMDiff IS (𝓡∂ 3) ∞ (fun z => e (z, iccEnd b)) :=
    e.contMDiff.comp hincl.contMDiff
  have hcont : Continuous fun z => P.map (e (z, iccEnd b)) :=
    P.continuous_map.comp hsm.continuous
  have hinj : Injective fun z => P.map (e (z, iccEnd b)) := fun z z' h =>
    congrArg Prod.fst (e.injective (P.injective h))
  refine isSmoothEmbedding_of_interior_GSF W (P.smooth.comp hsm)
    (hcont.isClosedEmbedding hinj).isEmbedding (fun z => ?_) hint
  have h1 : mfderiv IS W.model (fun z => P.map (e (z, iccEnd b))) z =
      (mfderiv (𝓡∂ 3) W.model P.map (e (z, iccEnd b))).comp
        (mfderiv IS (𝓡∂ 3) (fun z => e (z, iccEnd b)) z) :=
    mfderiv_comp (f := fun z => e (z, iccEnd b)) z (P.mdifferentiable_map _)
      (hsm.mdifferentiableAt (by simp))
  have h2 : mfderiv IS (𝓡∂ 3) (fun z => e (z, iccEnd b)) z =
      (mfderiv (IS.prod (𝓡∂ 1)) (𝓡∂ 3) e (z, iccEnd b)).comp
        (mfderiv IS (IS.prod (𝓡∂ 1)) (fun z : S => (z, (iccEnd b : Icc (0 : ℝ) 1))) z) :=
    mfderiv_comp (f := fun z : S => (z, (iccEnd b : Icc (0 : ℝ) 1))) z
      (e.contMDiff.mdifferentiableAt (by simp)) (hincl.contMDiff.mdifferentiableAt (by simp))
  rw [h1, h2]
  refine (P.mfderiv_bijective _).injective.comp
    ((e.mfderivToContinuousLinearEquiv (by simp) (z, iccEnd b)).injective.comp ?_)
  exact hincl.isImmersion.mfderiv_injective (by simp) z

/-- **G2, sphere slice.** The end slice of an interval slim model of sphere shape is the image of
a smooth embedding of the two-sphere into `W` when it lies in `W.interior`. -/
theorem exists_endSliceParam_sphere_GSF (P : PieceEmbedding W) (m : SlimModel P) (b : Bool)
    (hm : slimModelIsInterval m) (hshape : slimModelEndShape m = .sphere)
    (hsub : P.map '' slimModelEnd m b ⊆ W.interior) :
    ∃ g : ClosureSphere.{u} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ g ∧
      range g = P.map '' slimModelEnd m b := by
  cases m with
  | sphereInterval e =>
    have hrange : (range fun z => P.map (e (z, iccEnd b))) =
        P.map '' slimModelEnd (SlimModel.sphereInterval e) b := by
      change _ = P.map '' range fun z => e (z, iccEnd b)
      rw [← range_comp]
      rfl
    refine ⟨_, isSmoothEmbedding_endSlice_GSF P e b fun z => hsub ?_, hrange⟩
    rw [← hrange]
    exact ⟨z, rfl⟩
  | torusInterval e => cases hshape
  | overCircle p hp hsub' fib hcl => exact hm.elim

/-- **G2, torus slice.** -/
theorem exists_endSliceParam_torus_GSF (P : PieceEmbedding W) (m : SlimModel P) (b : Bool)
    (hm : slimModelIsInterval m) (hshape : slimModelEndShape m = .torus)
    (hsub : P.map '' slimModelEnd m b ⊆ W.interior) :
    ∃ g : Torus → W.Carrier, IsSmoothEmbedding torusModel W.model ∞ g ∧
      range g = P.map '' slimModelEnd m b := by
  cases m with
  | sphereInterval e => cases hshape
  | torusInterval e =>
    have hrange : (range fun t => P.map (e (t, iccEnd b))) =
        P.map '' slimModelEnd (SlimModel.torusInterval e) b := by
      change _ = P.map '' range fun t => e (t, iccEnd b)
      rw [← range_comp]
      rfl
    refine ⟨_, isSmoothEmbedding_endSlice_GSF P e b fun z => hsub ?_, hrange⟩
    rw [← hrange]
    exact ⟨z, rfl⟩
  | overCircle p hp hsub' fib hcl => cases hshape

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- **G2, sphere.** A sphere-shaped shared face is the image of a smooth embedding of the
two-sphere into `W`. -/
theorem exists_sharedParam_sphere_GSF (σ : Rw.SharedFace) (hσ : Rw.sharedShape σ = .sphere) :
    ∃ g : ClosureSphere.{u} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ g ∧
      range g = Rw.sharedSet σ :=
  exists_endSliceParam_sphere_GSF (Rw.slim.piece σ.1.1.1) (Rw.slim.model σ.1.1.1) σ.1.1.2 σ.1.2
    hσ (Rw.sharedSet_subset_interior_GSF σ)

/-- **G2, torus.** A torus-shaped shared face is the image of a smooth embedding of the torus
into `W`. -/
theorem exists_sharedParam_torus_GSF (σ : Rw.SharedFace) (hσ : Rw.sharedShape σ = .torus) :
    ∃ g : Torus → W.Carrier, IsSmoothEmbedding torusModel W.model ∞ g ∧
      range g = Rw.sharedSet σ :=
  exists_endSliceParam_torus_GSF (Rw.slim.piece σ.1.1.1) (Rw.slim.model σ.1.1.1) σ.1.1.2 σ.1.2
    hσ (Rw.sharedSet_subset_interior_GSF σ)

/-! ## G3: the defining function of the neighbour face -/

/-- **G3.** The neighbour face of a shared face is a regular zero level of a smooth function on an
open set of `W.interior`, whose sublevel there is the neighbour row. -/
theorem exists_neighbourFn_GSF (σ : Rw.SharedFace) :
    ∃ (U : TopologicalSpace.Opens W.Carrier) (f : W.Carrier → ℝ),
      (U : Set W.Carrier) ⊆ W.interior ∧ ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U ∧
      Rw.sharedSet σ ⊆ U ∧ (∀ x ∈ Rw.sharedSet σ, f x = 0) ∧
      (∀ x ∈ Rw.sharedSet σ, mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      ∀ x ∈ (U : Set W.Carrier),
        (x ∈ Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour σ)) ↔ f x ≤ 0) := by
  rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
  rcases Rw.sharedNeighbour σ with ⟨i, A⟩ | ⟨b, A, hA⟩
  · have hlev : ∀ x ∈ neighbourSet (Sum.inl ⟨i, A⟩ : NeighbourFace Rw.zero Rw.cusp),
        Rw.zero.ratio i x = 0 := by
      intro x hx
      have hb : x ∈ pieceBoundary (Rw.zero.piece i) := image_mono A.subset hx
      rw [Rw.zero.boundary_eq i] at hb
      exact hb
    refine ⟨Rw.zero.near i, Rw.zero.ratio i, Rw.zero.near_interior i,
      (Rw.zero.ratio_smooth i).contMDiffOn, fun x hx => Rw.zero.zero_subset_near i (hlev x hx),
      hlev, fun x hx => Rw.zero.ratio_regular i x (hlev x hx), fun x _ => ?_⟩
    change x ∈ range (Rw.zero.piece i).map ↔ _
    rw [Rw.zero.range_eq i]
    rfl
  · have hset : neighbourSet (Sum.inr ⟨b, A, hA⟩ : NeighbourFace Rw.zero Rw.cusp) =
        {x | x ∈ Rw.cusp.near b ∧ Rw.cusp.cuspFn b x = 0} := by
      change (Rw.cusp.piece b).map '' A.1 = _
      rw [hA, Rw.cusp.internalModelFace_eq b, ← Rw.cusp.internal_eq b, ← range_comp]
      rfl
    rw [hset]
    refine ⟨Rw.cusp.near b, Rw.cusp.cuspFn b, Rw.cusp.near_interior b, Rw.cusp.fn_smooth b,
      fun x hx => hx.1, fun x hx => hx.2, fun x hx => Rw.cusp.fn_regular b x hx.1 hx.2,
      fun x hx => ?_⟩
    change x ∈ range (Rw.cusp.piece b).map ↔ _
    have h := Set.ext_iff.mp (Rw.cusp.near_eq b) x
    constructor
    · intro hx'
      exact (h.mp ⟨hx', hx⟩).2
    · intro hx'
      exact (h.mpr ⟨hx, hx'⟩).1

/-! ## G4: the safe open set -/

/-- A shared face misses every row set other than its slim owner and its neighbour. -/
theorem sharedSet_disjoint_rowSet_GSF (σ : Rw.SharedFace) (a : Rw.slim.RowIndex)
    (h1 : a ≠ Rw.slimIndex σ) (h2 : a ≠ Rw.neighbourIndex (Rw.sharedNeighbour σ)) :
    Disjoint (Rw.sharedSet σ) (Rw.slim.rowSet a) := by
  have hslim : Rw.sharedSet σ ⊆ range (Rw.slim.piece σ.1.1.1).map :=
    Rw.slim.endSet_subset_GSAFE σ.1
  have hnb : Rw.sharedSet σ ⊆ Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour σ)) := by
    rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
    exact Rw.neighbourSet_subset_GSAFE _
  rcases a with i' | b' | j'
  · revert hnb h2
    rcases Rw.sharedNeighbour σ with ⟨i, A⟩ | ⟨b, A, hA⟩ <;> intro hnb h2
    · have hii : i ≠ i' := fun h => h2 (by subst h; rfl)
      exact Disjoint.mono_left hnb (Rw.zero.disjoint hii)
    · exact Disjoint.mono_left hnb (Rw.junctions.zero_cusp_disjoint i' b).symm
  · revert hnb h2
    rcases Rw.sharedNeighbour σ with ⟨i, A⟩ | ⟨b, A, hA⟩ <;> intro hnb h2
    · exact Disjoint.mono_left hnb (Rw.junctions.zero_cusp_disjoint i b')
    · have hbb : b ≠ b' := fun h => h2 (by subst h; rfl)
      exact Disjoint.mono_left hnb (Rw.cusp.disjoint hbb)
  · have hjj : σ.1.1.1 ≠ j' := fun h => h1 (by rw [← h]; rfl)
    exact (Rw.slim.disjoint hjj).mono_left hslim

/-- **G4.** An open neighbourhood `V` of a shared face with closure in `N σ` that meets no row set
other than the slim owner and the neighbour. -/
theorem exists_safeOpen_GSF (σ : Rw.SharedFace) (Nσ : TopologicalSpace.Opens W.Carrier)
    (hσN : Rw.sharedSet σ ⊆ Nσ) :
    ∃ V : Set W.Carrier, IsOpen V ∧ Rw.sharedSet σ ⊆ V ∧ closure V ⊆ Nσ ∧
      ∀ a, a ≠ Rw.slimIndex σ → a ≠ Rw.neighbourIndex (Rw.sharedNeighbour σ) →
        Disjoint V (Rw.slim.rowSet a) := by
  classical
  let K : Set W.Carrier := ⋃ (a : Rw.slim.RowIndex)
    (_ : a ≠ Rw.slimIndex σ ∧ a ≠ Rw.neighbourIndex (Rw.sharedNeighbour σ)), Rw.slim.rowSet a
  have hrow : ∀ a, IsClosed (Rw.slim.rowSet a) := by
    rintro (i | b | j)
    · exact (Rw.zero.piece i).isClosed_range
    · exact (Rw.cusp.piece b).isClosed_range
    · exact (Rw.slim.piece j).isClosed_range
  have hK : IsClosed K := isClosed_iUnion_of_finite fun a => isClosed_iUnion_of_finite fun _ => hrow a
  have hσK : Disjoint (Rw.sharedSet σ) K :=
    disjoint_iUnion_right.2 fun a => disjoint_iUnion_right.2 fun ha =>
      Rw.sharedSet_disjoint_rowSet_GSF σ a ha.1 ha.2
  have hO : IsOpen ((Nσ : Set W.Carrier) ∩ Kᶜ) := Nσ.isOpen.inter hK.isOpen_compl
  have hsub : Rw.sharedSet σ ⊆ (Nσ : Set W.Carrier) ∩ Kᶜ :=
    fun x hx => ⟨hσN hx, fun hxK => Set.disjoint_left.1 hσK hx hxK⟩
  obtain ⟨V, hV, hσV, hcl⟩ := normal_exists_closure_subset
    (Rw.isCompact_sharedSet_GSAFE σ).isClosed hO hsub
  refine ⟨V, hV, hσV, hcl.trans inter_subset_left, fun a h1 h2 => Set.disjoint_left.2 ?_⟩
  intro x hxV hxa
  exact (hcl (subset_closure hxV)).2 (mem_iUnion₂.2 ⟨a, ⟨h1, h2⟩, hxa⟩)

/-! ## G5–G6: the seams -/

/-- **G6 sides.** On the safe open set, a point of the neighbour's defining open set with positive
defining function lies in the slim owner's row. -/
theorem mem_slimRow_of_pos_GSF (σ : Rw.SharedFace) {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}
    (hN : SharedSafe Rw N) {V : Set W.Carrier} (hVN : closure V ⊆ N σ)
    (hVrow : ∀ a, a ≠ Rw.slimIndex σ → a ≠ Rw.neighbourIndex (Rw.sharedNeighbour σ) →
      Disjoint V (Rw.slim.rowSet a))
    {x : W.Carrier} (hxV : x ∈ V)
    (hxnb : x ∉ Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour σ))) :
    x ∈ Rw.slim.rowSet (Rw.slimIndex σ) := by
  have hcov : x ∈ ⋃ a, allPieces Rw.slim Rw.edge Rw.circle a := by
    rw [Rw.junctions.cover]
    exact mem_univ x
  obtain ⟨a, ha⟩ := mem_iUnion.1 hcov
  have hxN : x ∈ closure (N σ : Set W.Carrier) := subset_closure (hVN (subset_closure hxV))
  rcases a with r | _ | _
  · by_cases h1 : r = Rw.slimIndex σ
    · rw [← h1]
      exact ha
    · by_cases h2 : r = Rw.neighbourIndex (Rw.sharedNeighbour σ)
      · rw [h2] at ha
        exact (hxnb ha).elim
      · exact (Set.disjoint_left.1 (hVrow r h1 h2) hxV ha).elim
  · exact (Set.disjoint_left.1 (hN.off_region σ) hxN ha).elim
  · exact (Set.disjoint_left.1 (hN.off_edge σ) hxN ha).elim

/-- **G5–G6, sphere.** The seam of a sphere-shaped shared face. -/
theorem exists_sphereSeam_GSF (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier)
    (hN : SharedSafe Rw N) (σ : Rw.SharedFace) (hσ : Rw.sharedShape σ = .sphere) :
    ∃ (Sm : SphereSeam W) (g : ClosureSphere.{u} → W.Carrier),
      IsSmoothEmbedding (𝓡 2) W.model ∞ g ∧ (∀ z, Sm.collar (z, 0) = g z) ∧
      range g = Rw.sharedSet σ ∧
      (∀ z s, s ≤ 0 → -1 < s →
        Sm.collar (z, s) ∈ Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour σ))) ∧
      (∀ z s, 0 ≤ s → s < 1 → Sm.collar (z, s) ∈ Rw.slim.rowSet (Rw.slimIndex σ)) ∧
      closure Sm.collar.target ⊆ (N σ : Set W.Carrier) := by
  obtain ⟨g, hg, hgr⟩ := Rw.exists_sharedParam_sphere_GSF σ hσ
  obtain ⟨U, f, hU, hf, hσU, hlev, hreg, hside⟩ := Rw.exists_neighbourFn_GSF σ
  obtain ⟨V, hV, hσV, hVN, hVrow⟩ := Rw.exists_safeOpen_GSF σ (N σ) (hN.face_subset σ)
  obtain ⟨δ, hδ, Sm, htgt, hzero, hval⟩ := exists_sphereSeam_of_regular_level W U hU f 0 hf g hg
    (hgr ▸ hσU) (fun z => hlev _ (hgr ▸ mem_range_self z))
    (fun z => hreg _ (hgr ▸ mem_range_self z)) V hV (hgr ▸ hσV)
  have hsrc : ∀ z (s : ℝ), -1 < s → s < 1 → (z, s) ∈ Sm.collar.source := by
    intro z s h1 h2
    rw [Sm.source_eq]
    exact ⟨mem_univ _, h1, h2⟩
  refine ⟨Sm, g, hg, hzero, hgr, fun z s hs0 hs1 => ?_, fun z s hs0 hs1 => ?_, ?_⟩
  · have hmem := Sm.collar.map_source (hsrc z s hs1 (by linarith))
    refine (hside _ (htgt hmem).2).2 ?_
    rw [hval _ (Sm.source_eq ▸ hsrc z s hs1 (by linarith))]
    nlinarith
  · rcases hs0.eq_or_lt with rfl | hpos
    · rw [hzero]
      have hgz : g z ∈ Rw.sharedSet σ := hgr ▸ mem_range_self z
      exact Rw.slim.endSet_subset_GSAFE σ.1 hgz
    · have hmem := Sm.collar.map_source (hsrc z s (by linarith) hs1)
      refine mem_slimRow_of_pos_GSF Rw σ hN hVN hVrow (htgt hmem).1 fun hnb => ?_
      have hle := (hside _ (htgt hmem).2).1 hnb
      rw [hval _ (Sm.source_eq ▸ hsrc z s (by linarith) hs1)] at hle
      nlinarith
  · exact (closure_mono fun y hy => (htgt hy).1).trans hVN

/-- **G5–G6, torus.** The seam of a torus-shaped shared face. -/
theorem exists_torusSeam_GSF (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier)
    (hN : SharedSafe Rw N) (σ : Rw.SharedFace) (hσ : Rw.sharedShape σ = .torus) :
    ∃ (Sm : TorusSeam W) (g : Torus → W.Carrier),
      IsSmoothEmbedding torusModel W.model ∞ g ∧ (∀ t, Sm.collar (t, 0) = g t) ∧
      range g = Rw.sharedSet σ ∧
      (∀ t s, -1 < s → s ≤ 0 →
        Sm.collar (t, s) ∈ Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour σ))) ∧
      (∀ t s, 0 ≤ s → s < 1 → Sm.collar (t, s) ∈ Rw.slim.rowSet (Rw.slimIndex σ)) ∧
      closure Sm.collar.target ⊆ (N σ : Set W.Carrier) := by
  obtain ⟨g, hg, hgr⟩ := Rw.exists_sharedParam_torus_GSF σ hσ
  obtain ⟨U, f, hU, hf, hσU, hlev, hreg, hside⟩ := Rw.exists_neighbourFn_GSF σ
  obtain ⟨V, hV, hσV, hVN, hVrow⟩ := Rw.exists_safeOpen_GSF σ (N σ) (hN.face_subset σ)
  have hgU : range g ⊆ U := hgr ▸ hσU
  have hU' : (W.pieceInterior U : Set W.Carrier) = U := Set.inter_eq_left.mpr hU
  obtain ⟨V₀, hV₀, hgV₀, hiso⟩ := exists_isolating_open_of_regular_level (by simp) W U f 0
    (hf.mono fun x hx => hx.1) g hg (fun x hx => ⟨hgU hx, hU (hgU hx)⟩)
    (fun t => hlev _ (hgr ▸ mem_range_self t)) (fun t => hreg _ (hgr ▸ mem_range_self t))
  obtain ⟨δ, hδ, Sm, htgt, hzero, hval⟩ := exists_torusSeam_of_regular_level W U hU f 0 hf g hg
    hgU (fun t => hlev _ (hgr ▸ mem_range_self t)) (fun t => hreg _ (hgr ▸ mem_range_self t))
    ⟨V₀, hV₀, hgV₀, fun x hx hfx => hiso x ⟨hx.1, hU'.symm ▸ hx.2⟩ hfx⟩ V hV (hgr ▸ hσV)
  have hsrc : ∀ t (s : ℝ), -1 < s → s < 1 → (t, s) ∈ Sm.collar.source := by
    intro t s h1 h2
    rw [Sm.source_eq]
    exact ⟨h1, h2⟩
  refine ⟨Sm, g, hg, hzero, hgr, fun t s hs1 hs0 => ?_, fun t s hs0 hs1 => ?_, ?_⟩
  · have hmem := Sm.collar.map_source (hsrc t s hs1 (by linarith))
    refine (hside _ (htgt hmem).2).2 ?_
    rw [hval _ (Sm.source_eq ▸ hsrc t s hs1 (by linarith))]
    nlinarith
  · rcases hs0.eq_or_lt with rfl | hpos
    · rw [hzero]
      have hgt : g t ∈ Rw.sharedSet σ := hgr ▸ mem_range_self t
      exact Rw.slim.endSet_subset_GSAFE σ.1 hgt
    · have hmem := Sm.collar.map_source (hsrc t s (by linarith) hs1)
      refine mem_slimRow_of_pos_GSF Rw σ hN hVN hVrow (htgt hmem).1 fun hnb => ?_
      have hle := (hside _ (htgt hmem).2).1 hnb
      rw [hval _ (Sm.source_eq ▸ hsrc t s (by linarith) hs1)] at hle
      nlinarith
  · exact (closure_mono fun y hy => (htgt hy).1).trans hVN

end FC39RowsV2

end GC.GraphManifold.Assembly.FC39P0
