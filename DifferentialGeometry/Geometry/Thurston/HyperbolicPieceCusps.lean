import DifferentialGeometry.Geometry.Thurston.HyperbolicPieceCover
import DifferentialGeometry.Geometry.Thurston.HyperbolicPieceEnds
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions
import Mathlib.Topology.Homotopy.Product

/-!
# Cusp pieces in the universal cover

Tier T3 of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §1).
Let `p : ℝ³ → N` be a surjective covering, `Γ` its deck group, and `φ : T² × (0, 1) → N` an open
embedding (a collar region `W` of a boundary torus of a compact piece whose interior is `N`).
Fix a lift `ẽ` of `φ (t₀, s₀)` and let `Z̃` be the component of `p⁻¹ W` containing it.

* Deck transformations permute the components of `p⁻¹ W` (`smul_connectedComponentIn`), and lifts
  of paths in `W` stay in one component (`liftPath_mem_connectedComponentIn`).
* The monodromy image `Ψ` of `π₁(T², t₀)` through the torus `t ↦ φ (t, s₀)` is exactly the
  stabiliser of `Z̃` (`range_collarDeckHom`): a loop in `W` lifts into `Z̃`; conversely a path in
  `Z̃` projects to a loop in `W ≅ T² × (0, 1)`, homotopic rel endpoints to a loop in the torus
  because `(0, 1)` is simply connected. If the torus is π₁-injective in `N`, the stabiliser is
  isomorphic to `π₁(T²)`, so freely indecomposable and not cyclic (`collarStabilizerEquiv`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology
open scoped Pointwise unitInterval

namespace GC.Geometry.HyperbolicPiece

open DifferentialGeometry GC.Endpoint

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N] {p : E3 → N}

omit [TopologicalSpace N] in
theorem smul_connectedComponentIn (g : coveringDeckGroup p) (W : Set N) (e : E3) :
    g • connectedComponentIn (p ⁻¹' W) e = connectedComponentIn (p ⁻¹' W) (g • e) := by
  by_cases he : e ∈ p ⁻¹' W
  · have h := (coveringDeckGroupHomeomorph g).image_connectedComponentIn he
    have hpre : (coveringDeckGroupHomeomorph g) '' (p ⁻¹' W) = p ⁻¹' W := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change p (g • z) ∈ W
        rw [coveringDeckGroup_map (p := p)]
        exact hz
      · intro hy
        refine ⟨g⁻¹ • y, ?_, by simp⟩
        change p (g⁻¹ • y) ∈ W
        rw [coveringDeckGroup_map (p := p)]
        exact hy
    rw [hpre] at h
    exact h
  · have he' : g • e ∉ p ⁻¹' W := by
      change p (g • e) ∉ W
      rw [coveringDeckGroup_map (p := p)]
      exact he
    rw [connectedComponentIn_eq_empty he, connectedComponentIn_eq_empty he', smul_set_empty]

omit [TopologicalSpace N] in
theorem smul_connectedComponentIn_eq_self_iff (g : coveringDeckGroup p) (W : Set N) {e : E3}
    (he : e ∈ p ⁻¹' W) :
    g • connectedComponentIn (p ⁻¹' W) e = connectedComponentIn (p ⁻¹' W) e ↔
      g • e ∈ connectedComponentIn (p ⁻¹' W) e := by
  rw [smul_connectedComponentIn]
  constructor
  · intro h
    rw [← h]
    exact mem_connectedComponentIn (by
      change p (g • e) ∈ W
      rw [coveringDeckGroup_map (p := p)]
      exact he)
  · intro h
    exact (connectedComponentIn_eq h).symm

theorem liftPath_mem_connectedComponentIn (hp : IsCoveringMap p) {x y : N} (γ : Path x y)
    {W : Set N} (hγ : ∀ t, γ t ∈ W) (e : E3) (he : γ 0 = p e) (t : I) :
    hp.liftPath γ e he t ∈ connectedComponentIn (p ⁻¹' W) e := by
  have hsub : range (hp.liftPath γ e he) ⊆ p ⁻¹' W := by
    rintro _ ⟨s, rfl⟩
    change (p ∘ hp.liftPath γ e he) s ∈ W
    rw [hp.liftPath_lifts]
    exact hγ s
  have h0 : e ∈ range (hp.liftPath γ e he) := ⟨0, hp.liftPath_zero _ _ _⟩
  exact (isPreconnected_range (hp.liftPath γ e he).continuous).subset_connectedComponentIn h0
    hsub ⟨t, rfl⟩

theorem monodromy_val_of_lift (hp : IsCoveringMap p) {x y : N} (γ : Path x y) (e : p ⁻¹' {x})
    (δ : C(I, E3)) (hδ : p ∘ δ = γ) (hδ0 : δ 0 = e) :
    (hp.monodromy (Path.Homotopic.Quotient.mk γ) e : E3) = δ 1 := by
  have h := (hp.eq_liftPath_iff' (γ := (γ : C(I, N))) (e := (e : E3))
    (γ_0 := γ.source.trans e.2.symm)).mpr ⟨hδ, hδ0⟩
  rw [h]
  rfl

section Collar

variable (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
  {φ : Torus × Ioo (0 : ℝ) 1 → N} (hφ : IsOpenEmbedding φ) (s₀ : Ioo (0 : ℝ) 1) (t₀ : Torus)

def collarTorus : C(Torus, N) :=
  ⟨fun t => φ (t, s₀), hφ.continuous.comp (continuous_id.prodMk continuous_const)⟩

def collarDeckHom (e : p ⁻¹' {φ (t₀, s₀)}) :
    FundamentalGroup Torus t₀ →* coveringDeckGroup p :=
  (fundamentalGroupEquivDeck' hp hsurj e).toMonoidHom.comp
    (FundamentalGroup.map (collarTorus hφ s₀) t₀)

theorem collarDeckHom_inv_smul (e : p ⁻¹' {φ (t₀, s₀)}) (a : FundamentalGroup Torus t₀) :
    (collarDeckHom hp hsurj hφ s₀ t₀ e a)⁻¹ • (e : E3) =
      hp.monodromy (FundamentalGroup.map (collarTorus hφ s₀) t₀ a) e :=
  fundamentalGroupEquivDeck'_smul hp hsurj e _

private theorem connectedSpace_ioo : ContractibleSpace (Ioo (0 : ℝ) 1) :=
  (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by norm_num, by norm_num⟩

theorem collarDeckHom_mem_stabilizer (e : p ⁻¹' {φ (t₀, s₀)}) (a : FundamentalGroup Torus t₀) :
    collarDeckHom hp hsurj hφ s₀ t₀ e a ∈
      MulAction.stabilizer (coveringDeckGroup p) (connectedComponentIn (p ⁻¹' range φ) e) := by
  apply inv_mem_iff.mp
  rw [MulAction.mem_stabilizer_iff,
    smul_connectedComponentIn_eq_self_iff _ _ (show (e : E3) ∈ p ⁻¹' range φ from by
      change p e ∈ range φ
      rw [e.2]
      exact ⟨_, rfl⟩),
    collarDeckHom_inv_smul]
  induction a using Path.Homotopic.Quotient.ind with
  | mk α =>
    change (hp.monodromy (Path.Homotopic.Quotient.mk (α.map (collarTorus hφ s₀).continuous))
      e : E3) ∈ _
    exact liftPath_mem_connectedComponentIn hp _ (W := range φ) (fun t => ⟨(α t, s₀), rfl⟩) _ _ 1

theorem mem_range_collarDeckHom (e : p ⁻¹' {φ (t₀, s₀)}) (g : coveringDeckGroup p)
    (hg : g ∈ MulAction.stabilizer (coveringDeckGroup p)
      (connectedComponentIn (p ⁻¹' range φ) e)) :
    g ∈ (collarDeckHom hp hsurj hφ s₀ t₀ e).range := by
  have := connectedSpace_ioo
  have he : (e : E3) ∈ p ⁻¹' range φ := by
    change p e ∈ range φ
    rw [e.2]
    exact ⟨_, rfl⟩
  have hg' : g⁻¹ • (e : E3) ∈ connectedComponentIn (p ⁻¹' range φ) e := by
    rw [← smul_connectedComponentIn_eq_self_iff _ _ he]
    exact (MulAction.mem_stabilizer_iff.mp (inv_mem hg))
  have hopen : IsOpen (connectedComponentIn (p ⁻¹' range φ) (e : E3)) :=
    (hφ.isOpen_range.preimage hp.continuous).connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn (p ⁻¹' range φ) (e : E3)) :=
    hopen.isConnected_iff_isPathConnected.mp
      (isConnected_connectedComponentIn_iff.mpr he)
  obtain ⟨δ, hδ⟩ := hpc.joinedIn _ (mem_connectedComponentIn he) _ hg'
  have hδW : ∀ t, p (δ t) ∈ range φ := fun t =>
    connectedComponentIn_subset (p ⁻¹' range φ) (e : E3) (hδ t)
  let β : Path (φ (t₀, s₀)) (φ (t₀, s₀)) :=
    { toFun := fun t => p (δ t)
      continuous_toFun := hp.continuous.comp δ.continuous
      source' := by
        simp only [Path.source]
        exact e.2
      target' := by
        simp only [Path.target]
        rw [coveringDeckGroup_map (p := p)]
        exact e.2 }
  let H := hφ.isEmbedding.toHomeomorph
  have hH : ∀ q : Torus × Ioo (0 : ℝ) 1, H.symm ⟨φ q, ⟨q, rfl⟩⟩ = q :=
    hφ.isEmbedding.toHomeomorph_symm_apply
  let γ' : Path (t₀, s₀) (t₀, s₀) :=
    { toFun := fun t => H.symm ⟨β t, hδW t⟩
      continuous_toFun := H.symm.continuous.comp (by fun_prop)
      source' := by
        change H.symm ⟨p (δ 0), _⟩ = _
        simp only [Path.source]
        convert hH (t₀, s₀) using 2
        exact Subtype.ext e.2
      target' := by
        change H.symm ⟨p (δ 1), _⟩ = _
        simp only [Path.target]
        convert hH (t₀, s₀) using 2
        apply Subtype.ext
        change p (g⁻¹ • (e : E3)) = _
        rw [coveringDeckGroup_map (p := p)]
        exact e.2 }
  have hφγ : ∀ t, φ (γ' t) = β t := fun t => by
    change φ (H.symm ⟨β t, hδW t⟩) = β t
    have h := congrArg Subtype.val (H.apply_symm_apply ⟨β t, hδW t⟩)
    exact h
  let a : FundamentalGroup Torus t₀ :=
    Path.Homotopic.Quotient.mk (γ'.map continuous_fst)
  refine ⟨a, ?_⟩
  have hβ : (Path.Homotopic.Quotient.mk β : Path.Homotopic.Quotient _ _) =
      FundamentalGroup.map (collarTorus hφ s₀) t₀ a := by
    have h1 : (Path.Homotopic.Quotient.mk β : Path.Homotopic.Quotient _ _) =
        (Path.Homotopic.Quotient.mk γ').map ⟨φ, hφ.continuous⟩ := by
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact (hφγ t).symm
    rw [h1, ← Path.Homotopic.prod_projLeft_projRight (Path.Homotopic.Quotient.mk γ')]
    have h2 : Path.Homotopic.projRight (Path.Homotopic.Quotient.mk γ') =
        Path.Homotopic.Quotient.mk (Path.refl s₀) := Subsingleton.elim _ _
    rw [h2]
    rfl
  have hmono : (hp.monodromy (FundamentalGroup.map (collarTorus hφ s₀) t₀ a) e : E3) =
      g⁻¹ • (e : E3) := by
    change (hp.monodromy (FundamentalGroup.toPath
      (FundamentalGroup.map (collarTorus hφ s₀) t₀ a)) e : E3) = _
    rw [← hβ]
    exact monodromy_val_of_lift hp β e δ rfl δ.source ▸ δ.target
  rw [← collarDeckHom_inv_smul hp hsurj hφ s₀ t₀ e a] at hmono
  have hfix : (g * (collarDeckHom hp hsurj hφ s₀ t₀ e a)⁻¹) • (e : E3) = e := by
    rw [mul_smul, hmono, smul_inv_smul]
  have h1 := coveringDeckGroup_eq_one_of_apply_eq hp _ _ hfix
  rw [mul_inv_eq_one] at h1
  exact h1.symm

theorem range_collarDeckHom (e : p ⁻¹' {φ (t₀, s₀)}) :
    (collarDeckHom hp hsurj hφ s₀ t₀ e).range =
      MulAction.stabilizer (coveringDeckGroup p) (connectedComponentIn (p ⁻¹' range φ) e) := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact collarDeckHom_mem_stabilizer hp hsurj hφ s₀ t₀ e a
  · exact mem_range_collarDeckHom hp hsurj hφ s₀ t₀ e g

end Collar

section Family

omit [TopologicalSpace N] in
theorem smul_preimage_deck (g : coveringDeckGroup p) (S : Set N) : g • (p ⁻¹' S) = p ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change p (g • z) ∈ S
    rw [coveringDeckGroup_map (p := p)]
    exact hz
  · intro hy
    refine ⟨g⁻¹ • y, ?_, by simp⟩
    change p (g⁻¹ • y) ∈ S
    rw [coveringDeckGroup_map (p := p)]
    exact hy

theorem exists_smul_eq_of_map_eq (hp : IsCoveringMap p) {e₁ e₂ : E3} (h : p e₁ = p e₂) :
    ∃ g : coveringDeckGroup p, g • e₂ = e₁ :=
  (coveringDeckGroup_apply_eq_iff hp).mp h

variable (hp : IsCoveringMap p) (hsurj : Function.Surjective p) {κ : Type*}
  (φ : κ → Torus × Ioo (0 : ℝ) 1 → N) (hφ : ∀ k, IsOpenEmbedding (φ k)) (s₀ : Ioo (0 : ℝ) 1)
  (t₀ : Torus)

def collarHalf : Set (Torus × Ioo (0 : ℝ) 1) := {q | (q.2 : ℝ) ≤ 1 / 2}

def collarOpenHalf : Set (Torus × Ioo (0 : ℝ) 1) := {q | (q.2 : ℝ) < 1 / 2}

include hsurj in
omit [TopologicalSpace N] in
theorem exists_lift (x : N) : Nonempty (p ⁻¹' {x}) :=
  ⟨⟨(hsurj x).choose, (hsurj x).choose_spec⟩⟩

def collarLift (k : κ) : p ⁻¹' {φ k (t₀, s₀)} :=
  Classical.choice (exists_lift hsurj _)

def collarComponent (k : κ) : Set E3 :=
  connectedComponentIn (p ⁻¹' range (φ k)) (collarLift hsurj φ s₀ t₀ k)

def cuspPiece (k : κ) : Set E3 :=
  collarComponent hsurj φ s₀ t₀ k ∩ p ⁻¹' (φ k '' collarHalf)

omit [TopologicalSpace N] in
theorem collarLift_mem (k : κ) : (collarLift hsurj φ s₀ t₀ k : E3) ∈ p ⁻¹' range (φ k) := by
  change p (collarLift hsurj φ s₀ t₀ k) ∈ range (φ k)
  rw [(collarLift hsurj φ s₀ t₀ k).2]
  exact ⟨_, rfl⟩

omit [TopologicalSpace N] in
theorem smul_collarComponent (g : coveringDeckGroup p) (k : κ) :
    g • collarComponent hsurj φ s₀ t₀ k =
      connectedComponentIn (p ⁻¹' range (φ k)) (g • (collarLift hsurj φ s₀ t₀ k : E3)) :=
  smul_connectedComponentIn g _ _

omit [TopologicalSpace N] in
theorem smul_cuspPiece (g : coveringDeckGroup p) (k : κ) :
    g • cuspPiece hsurj φ s₀ t₀ k =
      connectedComponentIn (p ⁻¹' range (φ k)) (g • (collarLift hsurj φ s₀ t₀ k : E3)) ∩
        p ⁻¹' (φ k '' collarHalf) := by
  rw [cuspPiece, Set.smul_set_inter, smul_collarComponent, smul_preimage_deck]

include hp hφ in
theorem exists_smul_collarComponent_eq (k : κ) {y : E3} (hy : y ∈ p ⁻¹' range (φ k)) :
    ∃ g : coveringDeckGroup p, connectedComponentIn (p ⁻¹' range (φ k)) y =
      g • collarComponent hsurj φ s₀ t₀ k := by
  obtain ⟨q, hq⟩ := hy
  have := connectedSpace_ioo
  let ρ : Path (p y) (φ k (t₀, s₀)) :=
    ((PathConnectedSpace.somePath q (t₀, s₀)).map (hφ k).continuous).cast hq.symm rfl
  have hρ : ∀ t, ρ t ∈ range (φ k) := fun t => ⟨PathConnectedSpace.somePath q (t₀, s₀) t, rfl⟩
  let δ := hp.liftPath ρ y ρ.source
  have h1 : δ 1 ∈ connectedComponentIn (p ⁻¹' range (φ k)) y :=
    liftPath_mem_connectedComponentIn hp ρ hρ y ρ.source 1
  have hp1 : p (δ 1) = p (collarLift hsurj φ s₀ t₀ k) := by
    have h := congrFun (hp.liftPath_lifts ρ y ρ.source) 1
    change p (δ 1) = ρ 1 at h
    rw [h, ρ.target, (collarLift hsurj φ s₀ t₀ k).2]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_map_eq hp hp1
  refine ⟨g, ?_⟩
  rw [smul_collarComponent, hg]
  exact connectedComponentIn_eq h1

include hp hφ in
theorem isClosed_cuspPiece (k : κ) (hclosed : IsClosed (φ k '' collarHalf)) :
    IsClosed (cuspPiece hsurj φ s₀ t₀ k) := by
  apply isClosed_of_closure_subset
  intro z hz
  have hzW : z ∈ p ⁻¹' (φ k '' collarHalf) :=
    closure_minimal inter_subset_right (hclosed.preimage hp.continuous) hz
  have hzR : z ∈ p ⁻¹' range (φ k) := by
    obtain ⟨q, -, hq⟩ := hzW
    exact ⟨q, hq⟩
  have hO : IsOpen (connectedComponentIn (p ⁻¹' range (φ k)) z) :=
    ((hφ k).isOpen_range.preimage hp.continuous).connectedComponentIn
  obtain ⟨w, hwO, hwZ⟩ := mem_closure_iff.mp hz _ hO (mem_connectedComponentIn hzR)
  refine ⟨?_, hzW⟩
  have h1 := connectedComponentIn_eq hwO
  have h2 := connectedComponentIn_eq hwZ.1
  change z ∈ collarComponent hsurj φ s₀ t₀ k
  rw [collarComponent, h2, ← h1]
  exact mem_connectedComponentIn hzR

omit [TopologicalSpace N] in
theorem mem_stabilizer_of_smul_eq {k : κ} {g g' : coveringDeckGroup p}
    (h : g • collarComponent hsurj φ s₀ t₀ k = g' • collarComponent hsurj φ s₀ t₀ k) :
    g⁻¹ * g' ∈ MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ t₀ k) := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

omit [TopologicalSpace N] in
theorem smul_collarComponent_eq_of_mem {k : κ} {g : coveringDeckGroup p} {z : E3}
    (hz : z ∈ g • collarComponent hsurj φ s₀ t₀ k) :
    g • collarComponent hsurj φ s₀ t₀ k = connectedComponentIn (p ⁻¹' range (φ k)) z := by
  rw [smul_collarComponent] at hz ⊢
  exact connectedComponentIn_eq hz

omit [TopologicalSpace N] in
theorem smul_cuspPiece_eq (g : coveringDeckGroup p) (k : κ) :
    g • cuspPiece hsurj φ s₀ t₀ k =
      g • collarComponent hsurj φ s₀ t₀ k ∩ p ⁻¹' (φ k '' collarHalf) := by
  rw [cuspPiece, Set.smul_set_inter, smul_preimage_deck]

omit [TopologicalSpace N] in
theorem cuspPiece_disj (hdisjR : Pairwise fun k k' => Disjoint (range (φ k)) (range (φ k')))
    (k k' : κ) (g g' : coveringDeckGroup p)
    (h : (g • cuspPiece hsurj φ s₀ t₀ k ∩ g' • cuspPiece hsurj φ s₀ t₀ k').Nonempty) :
    k = k' ∧ g⁻¹ * g' ∈
      MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ t₀ k) := by
  obtain ⟨y, hy, hy'⟩ := h
  rw [smul_cuspPiece_eq] at hy hy'
  have hk : k = k' := by
    by_contra hne
    have h1 : p y ∈ range (φ k) := by
      have := hy.1
      rw [smul_collarComponent] at this
      exact connectedComponentIn_subset (p ⁻¹' range (φ k)) _ this
    have h2 : p y ∈ range (φ k') := by
      have := hy'.1
      rw [smul_collarComponent] at this
      exact connectedComponentIn_subset (p ⁻¹' range (φ k')) _ this
    exact (hdisjR hne).le_bot ⟨h1, h2⟩
  subst hk
  refine ⟨rfl, mem_stabilizer_of_smul_eq hsurj φ s₀ t₀ ?_⟩
  rw [smul_collarComponent_eq_of_mem hsurj φ s₀ t₀ hy.1,
    smul_collarComponent_eq_of_mem hsurj φ s₀ t₀ hy'.1]

include hp hφ in
theorem cuspPiece_locfin [Finite κ] (hclosed : ∀ k, IsClosed (φ k '' collarHalf)) (y : E3) :
    ∃ V ∈ 𝓝 y, ∀ k (g g' : coveringDeckGroup p), (g • cuspPiece hsurj φ s₀ t₀ k ∩ V).Nonempty →
      (g' • cuspPiece hsurj φ s₀ t₀ k ∩ V).Nonempty → g⁻¹ * g' ∈
        MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ t₀ k) := by
  classical
  let O : κ → Set E3 := fun k => if p y ∈ range (φ k) then
    connectedComponentIn (p ⁻¹' range (φ k)) y else (p ⁻¹' (φ k '' collarHalf))ᶜ
  have hO : ∀ k, O k ∈ 𝓝 y := by
    intro k
    by_cases hk : p y ∈ range (φ k)
    · simp only [O, hk, ite_true]
      exact (((hφ k).isOpen_range.preimage hp.continuous).connectedComponentIn).mem_nhds
        (mem_connectedComponentIn hk)
    · simp only [O, hk, ite_false]
      refine ((hclosed k).preimage hp.continuous).isOpen_compl.mem_nhds ?_
      rintro ⟨q, -, hq⟩
      exact hk ⟨q, hq⟩
  refine ⟨⋂ k, O k, Filter.iInter_mem.mpr hO, ?_⟩
  have key : ∀ k (g : coveringDeckGroup p), (g • cuspPiece hsurj φ s₀ t₀ k ∩ ⋂ k, O k).Nonempty →
      g • collarComponent hsurj φ s₀ t₀ k = connectedComponentIn (p ⁻¹' range (φ k)) y := by
    rintro k g ⟨z, hz, hzO⟩
    rw [smul_cuspPiece_eq] at hz
    have hzk := mem_iInter.mp hzO k
    by_cases hk : p y ∈ range (φ k)
    · simp only [O, hk, ite_true] at hzk
      rw [smul_collarComponent_eq_of_mem hsurj φ s₀ t₀ hz.1]
      exact (connectedComponentIn_eq hzk).symm
    · simp only [O, hk, ite_false] at hzk
      exact absurd hz.2 hzk
  intro k g g' hg hg'
  exact mem_stabilizer_of_smul_eq hsurj φ s₀ t₀ ((key k g hg).trans (key k g' hg').symm)

include hp hφ in
theorem cuspPiece_cover {F : Set E3} (hF : (⋃ k, φ k '' collarOpenHalf)ᶜ ⊆ p '' F) (y : E3) :
    (∃ g : coveringDeckGroup p, y ∈ g • F) ∨
      ∃ k, ∃ g : coveringDeckGroup p, y ∈ g • cuspPiece hsurj φ s₀ t₀ k := by
  by_cases h : p y ∈ ⋃ k, φ k '' collarOpenHalf
  · right
    obtain ⟨k, q, hq, hqy⟩ := mem_iUnion.mp h
    have hyR : y ∈ p ⁻¹' range (φ k) := ⟨q, hqy⟩
    obtain ⟨g, hg⟩ := exists_smul_collarComponent_eq hp hsurj φ hφ s₀ t₀ k hyR
    refine ⟨k, g, ?_⟩
    rw [smul_cuspPiece_eq, ← hg]
    refine ⟨mem_connectedComponentIn hyR, q, ?_, hqy⟩
    change (q.2 : ℝ) ≤ 1 / 2
    exact le_of_lt hq
  · left
    obtain ⟨f, hf, hfy⟩ := hF h
    obtain ⟨g, hg⟩ := exists_smul_eq_of_map_eq hp hfy.symm
    exact ⟨g, hg ▸ Set.smul_mem_smul_set hf⟩

include hp hφ in
theorem exists_compact_cuspPiece (k : κ) (hclosed : IsClosed (φ k '' collarHalf)) {J : Set N}
    (hJ : IsCompact J) (hJW : J ⊆ φ k '' collarHalf) :
    ∃ Q : Set E3, IsCompact Q ∧ Q ⊆ cuspPiece hsurj φ s₀ t₀ k ∧ J ⊆ p '' Q := by
  classical
  have hopen : IsOpen (collarComponent hsurj φ s₀ t₀ k) :=
    ((hφ k).isOpen_range.preimage hp.continuous).connectedComponentIn
  have hloc : ∀ j ∈ J, ∃ K : Set E3, IsCompact K ∧ K ⊆ collarComponent hsurj φ s₀ t₀ k ∧
      p '' interior K ∈ 𝓝 j := by
    intro j hj
    obtain ⟨e, he⟩ := hsurj j
    have heR : e ∈ p ⁻¹' range (φ k) := by
      obtain ⟨q, -, hq⟩ := hJW hj
      exact ⟨q, hq.trans he.symm⟩
    obtain ⟨g, hg⟩ := exists_smul_collarComponent_eq hp hsurj φ hφ s₀ t₀ k heR
    have he' : g⁻¹ • e ∈ collarComponent hsurj φ s₀ t₀ k := by
      have h1 : e ∈ g • collarComponent hsurj φ s₀ t₀ k := hg ▸ mem_connectedComponentIn heR
      obtain ⟨z, hz, rfl⟩ := h1
      rw [inv_smul_smul]
      exact hz
    obtain ⟨K, hK, hKi, hKs⟩ := exists_compact_subset hopen he'
    refine ⟨K, hK, hKs, ?_⟩
    apply (hp.isLocalHomeomorph.isOpenMap _ isOpen_interior).mem_nhds
    refine ⟨g⁻¹ • e, hKi, ?_⟩
    rw [coveringDeckGroup_map (p := p)]
    exact he
  choose K hK hKs hKn using hloc
  let U : N → Set N := fun j => if h : j ∈ J then p '' interior (K j h) else univ
  obtain ⟨t, htJ, hcov⟩ := hJ.elim_nhds_subcover U (fun j hj => by
    simp only [U, hj, dite_true]
    exact hKn j hj)
  let Q : Set E3 := ⋃ j ∈ t, ⋃ (h : j ∈ J), K j h ∩ p ⁻¹' (φ k '' collarHalf)
  refine ⟨Q, ?_, ?_, ?_⟩
  · refine t.finite_toSet.isCompact_biUnion fun j _ => ?_
    by_cases hj : j ∈ J
    · simp only [hj, iUnion_true]
      exact (hK j hj).inter_right (hclosed.preimage hp.continuous)
    · simp only [hj, iUnion_false, isCompact_empty]
  · intro z hz
    obtain ⟨j, -, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨hj, hz⟩ := mem_iUnion.mp hz
    exact ⟨hKs j hj hz.1, hz.2⟩
  · intro j' hj'
    obtain ⟨j, hjt, hj'U⟩ := mem_iUnion₂.mp (hcov hj')
    have hj := htJ j hjt
    simp only [U, hj, dite_true] at hj'U
    obtain ⟨e, he, rfl⟩ := hj'U
    refine ⟨e, mem_iUnion₂.mpr ⟨j, hjt, mem_iUnion.mpr ⟨hj, interior_subset he, hJW hj'⟩⟩, rfl⟩

include hp hφ in
theorem cuspPiece_type [T2Space N] (k : κ) (hclosed : IsClosed (φ k '' collarHalf))
    {F : Set E3} (hF : IsCompact F) :
    ∃ H : Set (coveringDeckGroup p), H.Finite ∧ ∀ g : coveringDeckGroup p,
      (g • F ∩ cuspPiece hsurj φ s₀ t₀ k).Nonempty →
        ∃ π ∈ MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ t₀ k),
          ∃ η ∈ H, g = π * η := by
  have := properlyDiscontinuousSMul_deck hp hsurj
  have hJ : IsCompact (φ k '' collarHalf ∩ p '' F) := (hF.image hp.continuous).inter_left hclosed
  obtain ⟨Q, hQ, hQs, hJQ⟩ := exists_compact_cuspPiece hp hsurj φ hφ s₀ t₀ k hclosed hJ
    inter_subset_left
  refine ⟨{η | (η • F ∩ Q).Nonempty}, finite_setOf_smul_inter_nonempty hF hQ, ?_⟩
  rintro g ⟨z, ⟨f, hf, rfl⟩, hz⟩
  have hzJ : p (g • f) ∈ φ k '' collarHalf ∩ p '' F :=
    ⟨hz.2, f, hf, (coveringDeckGroup_map (p := p) g f).symm⟩
  obtain ⟨q, hq, hpq⟩ := hJQ hzJ
  obtain ⟨π, hπ⟩ := exists_smul_eq_of_map_eq hp hpq.symm
  have hqZ : q ∈ collarComponent hsurj φ s₀ t₀ k := (hQs hq).1
  have h1 : π • q ∈ collarComponent hsurj φ s₀ t₀ k := hπ ▸ hz.1
  have e1 : collarComponent hsurj φ s₀ t₀ k = connectedComponentIn (p ⁻¹' range (φ k)) q :=
    connectedComponentIn_eq (F := p ⁻¹' range (φ k)) hqZ
  have e2 : collarComponent hsurj φ s₀ t₀ k =
      connectedComponentIn (p ⁻¹' range (φ k)) (π • q) :=
    connectedComponentIn_eq (F := p ⁻¹' range (φ k)) h1
  have hπs : π ∈ MulAction.stabilizer (coveringDeckGroup p)
      (collarComponent hsurj φ s₀ t₀ k) := by
    rw [MulAction.mem_stabilizer_iff, e1, smul_connectedComponentIn, ← e2, e1]
  refine ⟨π, hπs, π⁻¹ * g, ⟨q, ⟨f, hf, ?_⟩, hq⟩, by group⟩
  change (π⁻¹ * g) • f = q
  rw [mul_smul, ← hπ, inv_smul_smul]

include hp hsurj in
theorem exists_compact_lift [T2Space N] {K : Set N} (hK : IsCompact K) :
    ∃ F : Set E3, IsCompact F ∧ F.Nonempty ∧ K ⊆ p '' F := by
  choose e he using hsurj
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => p '' Metric.ball (e x) 1)
    (fun x _ => (hp.isLocalHomeomorph.isOpenMap _ Metric.isOpen_ball).mem_nhds
      ⟨e x, Metric.mem_ball_self one_pos, he x⟩)
  refine ⟨insert 0 (⋃ x ∈ t, Metric.closedBall (e x) 1), ?_, insert_nonempty _ _, ?_⟩
  · exact (t.finite_toSet.isCompact_biUnion fun x _ => isCompact_closedBall _ _).insert 0
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcov hy)
    obtain ⟨z, hz, rfl⟩ := hyx
    exact ⟨z, Or.inr (mem_iUnion₂.mpr ⟨x, hxt, Metric.ball_subset_closedBall hz⟩), rfl⟩

def collarStabilizerEquiv (k : κ)
    (hinj : Function.Injective (FundamentalGroup.map (collarTorus (hφ k) s₀) t₀)) :
    FundamentalGroup Torus t₀ ≃*
      MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ t₀ k) :=
  (MonoidHom.ofInjective (f := collarDeckHom hp hsurj (hφ k) s₀ t₀ (collarLift hsurj φ s₀ t₀ k))
    ((fundamentalGroupEquivDeck' hp hsurj _).injective.comp hinj)).trans
    (MulEquiv.subgroupCongr (range_collarDeckHom hp hsurj (hφ k) s₀ t₀ _))

theorem infinite_fundamentalGroup_torus : Infinite (FundamentalGroup Torus (1, 1)) := by
  have : Infinite (Multiplicative ℤ × Multiplicative ℤ) :=
    Infinite.of_injective (fun n : ℤ => (Multiplicative.ofAdd n, (1 : Multiplicative ℤ)))
      fun a b h => Multiplicative.ofAdd.injective (congrArg Prod.fst h)
  exact Infinite.of_injective _ GC.Topology.torusFundamentalGroup.symm.injective

end Family

section Main

theorem one_lt_rank_euclideanSpace_three : 1 < Module.rank ℝ E3 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

theorem freelyIndecomposable_of_cuspCollars [T2Space N] (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) {κ : Type*} [Finite κ] [Nonempty κ]
    (φ : κ → Torus × Ioo (0 : ℝ) 1 → N) (hφ : ∀ k, IsOpenEmbedding (φ k))
    (hdisjR : Pairwise fun k k' => Disjoint (range (φ k)) (range (φ k')))
    (hclosed : ∀ k, IsClosed (φ k '' collarHalf))
    (hcore : IsCompact (⋃ k, φ k '' collarOpenHalf)ᶜ) (s₀ : Ioo (0 : ℝ) 1)
    (hinj : ∀ k, Function.Injective (FundamentalGroup.map (collarTorus (hφ k) s₀) (1, 1)))
    (y : N) : GC.Group.FreelyIndecomposable (FundamentalGroup N y) := by
  have := properlyDiscontinuousSMul_deck hp hsurj
  obtain ⟨F, hF, hFne, hFK⟩ := exists_compact_lift hp hsurj hcore
  obtain ⟨k₀⟩ := (inferInstance : Nonempty κ)
  have : Infinite (coveringDeckGroup p) := by
    have := infinite_fundamentalGroup_torus
    have : Infinite (MulAction.stabilizer (coveringDeckGroup p)
        (collarComponent hsurj φ s₀ (1, 1) k₀)) :=
      Infinite.of_injective _ (collarStabilizerEquiv hp hsurj φ hφ s₀ (1, 1) k₀ (hinj k₀)).injective
    exact Infinite.of_injective (fun x : MulAction.stabilizer (coveringDeckGroup p)
      (collarComponent hsurj φ s₀ (1, 1) k₀) => (x : coveringDeckGroup p)) Subtype.val_injective
  have hΓ : GC.Group.FreelyIndecomposable (coveringDeckGroup p) :=
    freelyIndecomposable_of_cuspedAction one_lt_rank_euclideanSpace_three hF hFne
      (cuspPiece hsurj φ s₀ (1, 1))
      (fun k => isClosed_cuspPiece hp hsurj φ hφ s₀ (1, 1) k (hclosed k))
      (fun k => MulAction.stabilizer (coveringDeckGroup p) (collarComponent hsurj φ s₀ (1, 1) k))
      (fun k π hπ => by
        rw [smul_cuspPiece_eq, MulAction.mem_stabilizer_iff.mp hπ]
        rfl)
      (cuspPiece_cover hp hsurj φ hφ s₀ (1, 1) hFK)
      (cuspPiece_disj hsurj φ s₀ (1, 1) hdisjR)
      (cuspPiece_locfin hp hsurj φ hφ s₀ (1, 1) hclosed)
      (fun k => cuspPiece_type hp hsurj φ hφ s₀ (1, 1) k (hclosed k) hF)
      (fun k => (GC.Seifert.indecomposableNoncyclic_torus (1, 1)).of_mulEquiv
        (collarStabilizerEquiv hp hsurj φ hφ s₀ (1, 1) k (hinj k)))
  obtain ⟨e⟩ := exists_lift hsurj y
  exact hΓ.of_mulEquiv (fundamentalGroupEquivDeck' hp hsurj e).symm

end Main

end GC.Geometry.HyperbolicPiece
