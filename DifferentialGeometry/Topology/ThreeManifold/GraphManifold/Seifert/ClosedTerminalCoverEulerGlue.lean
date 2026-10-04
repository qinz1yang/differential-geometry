import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFibre

/-!
# Homomorphisms out of a closed three-filling block

A homomorphism on an open region `A` extends over `L ∪ A` when `L` is the left region of a seam,
`L ∩ A` is the seam collar and the seam torus goes to the powers of one element by its second
coordinate (`exists_hom_glue_region`, from `exists_hom_glue_solid`); the extension keeps, up to
conjugation, its values on every torus map into `A`.

For a block with three fillings `m₀, m₁, m₂` start from the product homomorphism `ι ∘ (κ × deg)`
on the middle region `M = R₀ ∩ R₁ ∩ R₂` (through the π₁-bijective retraction of
`ClosedTerminalFibre`), and glue the three solid tori along `L₀ ∩ M`, `L₁ ∩ (L₀ ∪ M)` and
`L₂ ∩ (L₁ ∪ L₀ ∪ M)`, each the seam collar. On a seam torus, i.e. a filled port composed with the
matching map, the value is a power of one element once the meridian relation holds
(`forall_conj_seam_of_port`). The result (`exists_closedTriangle_portHom`): for any `ι` killing
the three meridians there is a homomorphism on `π₁` of the carrier whose value on each filled port
torus is `ι (w ^ a, b)` up to conjugation.
-/

set_option autoImplicit false

noncomputable section
open Set Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

section Glue

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

def closedTriangleCod {T : Type*} [TopologicalSpace T] (f : C(T, X)) (S : Set X)
    (hf : ∀ t, f t ∈ S) : C(T, S) :=
  ⟨fun t => ⟨f t, hf t⟩, f.continuous.subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_hom_glue_region (A L : Set X) (hA : IsOpen A) (hL : IsOpen L)
    (hpA : IsPathConnected A) (hpL : IsPathConnected L) (hpLA : IsPathConnected (L ∩ A))
    (sg : C(Torus, X)) (hs : ∀ t, sg t ∈ L ∩ A)
    (hsπ : Function.Surjective
      (FundamentalGroup.map (closedTriangleCod sg (L ∩ A) hs) torusBase))
    (φ : C(L, Circle)) (hφ : ∀ t, φ ⟨sg t, (hs t).1⟩ = t.2)
    {a : A} (FA : FundamentalGroup A a →* G) (y : G)
    (hy : ∀ δ : Path a ⟨sg torusBase, (hs torusBase).2⟩, ∃ k : G, ∀ g,
      FA (GC.Topology.markedMap (closedTriangleCod sg A fun t => (hs t).2) torusBase δ g) =
        k * y ^ toAdd (GC.Topology.torusFundamentalGroup g).2 * k⁻¹) :
    ∃ (s : ↥(L ∪ A)) (FS : FundamentalGroup ↥(L ∪ A) s →* G),
      ∀ (p : C(Torus, X)) (hp : ∀ t, p t ∈ A) (E : FundamentalGroup Torus torusBase → G),
        (∀ δ : Path a ⟨p torusBase, hp torusBase⟩, ∃ k : G, ∀ g,
          FA (GC.Topology.markedMap (closedTriangleCod p A hp) torusBase δ g) =
            k * E g * k⁻¹) →
        ∀ δ : Path s ⟨p torusBase, Or.inr (hp torusBase)⟩, ∃ k : G, ∀ g,
          FS (GC.Topology.markedMap (closedTriangleCod p (L ∪ A) fun t => Or.inr (hp t))
            torusBase δ g) = k * E g * k⁻¹ := by
  let Z := L ∪ A
  let U : Set ↥Z := Subtype.val ⁻¹' L
  let V : Set ↥Z := Subtype.val ⁻¹' A
  have hU : IsOpen U := hL.preimage continuous_subtype_val
  have hV : IsOpen V := hA.preimage continuous_subtype_val
  have hcover : U ∪ V = univ := eq_univ_of_forall fun z => z.2
  have : PathConnectedSpace U := pathConnectedSpace_preimage hpL subset_union_left
  have : PathConnectedSpace V := pathConnectedSpace_preimage hpA subset_union_right
  have : PathConnectedSpace ↑(U ∩ V) :=
    pathConnectedSpace_preimage hpLA (inter_subset_left.trans subset_union_left)
  have : PathConnectedSpace A := isPathConnected_iff_pathConnectedSpace.mp hpA
  let τ : C(Torus, ↑(U ∩ V)) := ⟨fun t => ⟨⟨sg t, Or.inl (hs t).1⟩, (hs t).1, (hs t).2⟩,
    (sg.continuous.subtype_mk _).subtype_mk _⟩
  have hτ : Function.Surjective (FundamentalGroup.map τ torusBase) := by
    let e : ↑(U ∩ V) ≃ₜ ↑(L ∩ A) :=
      { toFun := fun z => ⟨z.1.1, z.2.1, z.2.2⟩
        invFun := fun y => ⟨⟨y.1, Or.inl y.2.1⟩, y.2.1, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
    exact surjective_fundamentalGroup_map_of_comp_eq τ (e : C(↑(U ∩ V), ↑(L ∩ A)))
      (closedTriangleCod sg (L ∩ A) hs) (ContinuousMap.ext fun t => rfl) torusBase
      (bijective_map_homeomorph e _).1 hsπ
  let eU : C(U, L) := ⟨fun z => ⟨z.1.1, z.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hφ' : (φ.comp eU).comp ((interToLeft U V).comp τ) = ContinuousMap.snd :=
    ContinuousMap.ext fun t => hφ t
  let eV : C(V, A) := ⟨fun z => ⟨z.1.1, z.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let v₀ := interToRight U V (τ torusBase)
  let β : Path a (eV v₀) := PathConnectedSpace.somePath _ _
  let fR : FundamentalGroup V v₀ →* G := FA.comp (GC.Topology.markedMap eV v₀ β)
  obtain ⟨k₀, hk₀⟩ := hy β
  have hfR : ∀ g, fR (FundamentalGroup.map ((interToRight U V).comp τ) torusBase g) =
      (k₀ * y * k₀⁻¹) ^ toAdd (GC.Topology.torusFundamentalGroup g).2 := by
    intro g
    have h1 := DFunLike.congr_fun
      (markedMap_comp_map ((interToRight U V).comp τ) eV torusBase β) g
    simp only [MonoidHom.comp_apply] at h1
    change FA (GC.Topology.markedMap eV v₀ β
      (FundamentalGroup.map ((interToRight U V).comp τ) torusBase g)) = _
    refine (congrArg FA h1).trans ?_
    rw [conj_zpow]
    exact hk₀ g
  obtain ⟨FS, hFS⟩ := exists_hom_glue_solid U V hU hV hcover τ hτ (φ.comp eU) hφ' fR _ hfR
  refine ⟨(τ torusBase).1, FS, fun p hp E hE δ => ?_⟩
  let pV : C(Torus, V) := ⟨fun t => ⟨⟨p t, Or.inr (hp t)⟩, hp t⟩,
    (p.continuous.subtype_mk _).subtype_mk _⟩
  refine forall_conj_congr FS (show closedTriangleCod p Z (fun t => Or.inr (hp t)) =
    (subsetToAmbient V).comp pV from ContinuousMap.ext fun t => rfl) torusBase E ?_ δ
  refine forall_conj_push (subsetToAmbient V) v₀ FS fR hFS pV torusBase
    (PathConnectedSpace.somePath _ _) E ?_
  refine forall_conj_comp FA eV v₀ β pV torusBase E ?_
  exact forall_conj_congr FA (show eV.comp pV = closedTriangleCod p A hp from
    ContinuousMap.ext fun t => rfl) torusBase E hE

end Glue

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

theorem exists_hom_glue_seam {G : Type*} [Group G] (m : Fin d.fillingCount) (A : Set W.Carrier)
    (hA : IsOpen A) (hpA : IsPathConnected A)
    (hLA : B.presentation.leftRegion (B.seam m) ∩ A = B.presentation.seamCollar (B.seam m))
    (hsA : ∀ t, B.presentation.seamTorus (B.seam m) t ∈ A)
    {a : A} (FA : FundamentalGroup A a →* G) (y : G)
    (hy : ∀ δ : Path a ⟨B.presentation.seamTorus (B.seam m) torusBase, hsA torusBase⟩,
      ∃ k : G, ∀ g, FA (GC.Topology.markedMap
        (closedTriangleCod (B.presentation.seamTorus (B.seam m)) A hsA) torusBase δ g) =
          k * y ^ toAdd (GC.Topology.torusFundamentalGroup g).2 * k⁻¹) :
    ∃ (s : ↥(B.presentation.leftRegion (B.seam m) ∪ A))
      (FS : FundamentalGroup ↥(B.presentation.leftRegion (B.seam m) ∪ A) s →* G),
      ∀ (p : C(Torus, W.Carrier)) (hp : ∀ t, p t ∈ A) (E : FundamentalGroup Torus torusBase → G),
        (∀ δ : Path a ⟨p torusBase, hp torusBase⟩, ∃ k : G, ∀ g,
          FA (GC.Topology.markedMap (closedTriangleCod p A hp) torusBase δ g) =
            k * E g * k⁻¹) →
        ∀ δ : Path s ⟨p torusBase, Or.inr (hp torusBase)⟩, ∃ k : G, ∀ g,
          FS (GC.Topology.markedMap (closedTriangleCod p
            (B.presentation.leftRegion (B.seam m) ∪ A) fun t => Or.inr (hp t))
              torusBase δ g) = k * E g * k⁻¹ := by
  have hs : ∀ t, B.presentation.seamTorus (B.seam m) t ∈
      B.presentation.leftRegion (B.seam m) ∩ A := fun t => by
    rw [hLA]
    exact B.presentation.seamTorus_mem_seamCollar _ t
  obtain ⟨f₀, hf₀⟩ := B.exists_leafRetraction m
  refine exists_hom_glue_region A _ hA (B.presentation.isOpen_leftRegion _) hpA
    (B.presentation.isPathConnected_leftRegion _)
    (hLA ▸ B.presentation.isPathConnected_seamCollar _) _ hs
    (B.presentation.bijective_seamTorusIn (B.seam m) _ hLA torusBase).2
    ((B.solid m).fibreMap.comp f₀) (fun t => ?_) FA y hy
  change (B.solid m).fibreMap (f₀ (B.presentation.seamTorusToLeft (B.seam m) t)) = t.2
  rw [hf₀]
  exact DFunLike.congr_fun ((B.solid m).fibreMap_comp_portMap 0) t

theorem forall_conj_seam_of_port {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) (w : FreeGroup (Fin 2)) (m : Fin d.fillingCount)
    (hM : ι (w ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 0)) = 1)
    {A : Set W.Carrier}
    (hA : ∀ t, B.productToCarrier.comp (B.product.portMap (B.port (.inr m))) t ∈ A)
    (hsA : ∀ t, B.presentation.seamTorus (B.seam m) t ∈ A) {a : A}
    (FA : FundamentalGroup A a →* H)
    (h : ∀ δ : Path a ⟨_, hA torusBase⟩, ∃ k : H, ∀ g, FA (GC.Topology.markedMap
      (closedTriangleCod (B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))) A hA)
        torusBase δ g) = k * ι (w ^ toAdd (GC.Topology.torusFundamentalGroup g).1,
          (GC.Topology.torusFundamentalGroup g).2) * k⁻¹) :
    ∀ δ : Path a ⟨B.presentation.seamTorus (B.seam m) torusBase, hsA torusBase⟩,
      ∃ k : H, ∀ g, FA (GC.Topology.markedMap
        (closedTriangleCod (B.presentation.seamTorus (B.seam m)) A hsA) torusBase δ g) =
          k * ι (w ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 1,
            ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 1)) ^
              toAdd (GC.Topology.torusFundamentalGroup g).2 * k⁻¹ := by
  have heq : closedTriangleCod (B.presentation.seamTorus (B.seam m)) A hsA =
      (closedTriangleCod (B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))) A
        hA).comp (B.presentation.matchingMap (B.seam m)) := by
    refine ContinuousMap.ext fun t => Subtype.ext ?_
    change B.presentation.seamTorus (B.seam m) t = B.presentation.cutMap
      (B.product.portMap (B.port (.inr m)) (B.presentation.pairing.matching (B.seam m) t))
    rw [B.presentation.seamTorus_eq_cutMap_right, B.portMap_filled_val]
  refine forall_conj_congr FA heq torusBase _ ?_
  intro δ
  obtain ⟨k, hk⟩ := forall_conj_comp_torus FA _ (B.presentation.matchingMap (B.seam m)) _ h δ
  exact ⟨k, fun g => by rw [hk g, port_matching_value ι w _ hM g]⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_closedTriangle_portHom (h3 : d.fillingCount = 3) {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) {b₀ : B.product.base.surface.Carrier}
    (κ : FundamentalGroup B.product.base.surface.Carrier b₀ →* FreeGroup (Fin 2))
    (w : Fin d.fillingCount → FreeGroup (Fin 2))
    (hκ : ∀ m (γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m)) 1)),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m))) 1 γ a) =
          c' * w m ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹)
    (hM : ∀ m, ι (w m ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 0)) = 1) :
    ∃ (z : W.Carrier) (Φ : FundamentalGroup W.Carrier z →* H), ∀ m
      (δ : Path z (B.productToCarrier (B.product.portMap (B.port (.inr m)) torusBase))),
      ∃ k : H, ∀ g, Φ (GC.Topology.markedMap
        (B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))) torusBase δ g) =
          k * ι (w m ^ toAdd (GC.Topology.torusFundamentalGroup g).1,
            (GC.Topology.torusFundamentalGroup g).2) * k⁻¹ := by
  have hW := B.connectedSpace
  have := B.product.pathConnectedSpace_base
  let m₀ : Fin d.fillingCount := ⟨0, by omega⟩
  let m₁ : Fin d.fillingCount := ⟨1, by omega⟩
  let m₂ : Fin d.fillingCount := ⟨2, by omega⟩
  have h01 : m₀ ≠ m₁ := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by norm_num)
  have h02 : m₀ ≠ m₂ := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by norm_num)
  have h12 : m₁ ≠ m₂ := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by norm_num)
  have hcov : ∀ n : Fin d.fillingCount, n = m₀ ∨ n = m₁ ∨ n = m₂ := by
    intro n
    rcases n with ⟨n, hn⟩
    have hn3 : n < 3 := h3 ▸ hn
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  set G := B.presentation with hG
  let π : Fin d.fillingCount → C(Torus, W.Carrier) := fun m =>
    B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))
  let E : Fin d.fillingCount → FundamentalGroup Torus torusBase → H := fun m g =>
    ι (w m ^ toAdd (GC.Topology.torusFundamentalGroup g).1,
      (GC.Topology.torusFundamentalGroup g).2)
  let M := G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)
  have hπM : ∀ m t, π m t ∈ M := fun m t =>
    B.pieceImage_none_subset_middle₃ m₀ m₁ m₂ ⟨_, (B.product.portMap _ t).2, rfl⟩
  obtain ⟨hc₀M, hc₁M, hc₂M⟩ := B.seamCollar_subset_middle₃ h01 h02 h12
  have hsM : ∀ m t, G.seamTorus (B.seam m) t ∈ M := by
    intro m t
    rcases hcov m with rfl | rfl | rfl
    · exact hc₀M (G.seamTorus_mem_seamCollar _ t)
    · exact hc₁M (G.seamTorus_mem_seamCollar _ t)
    · exact hc₂M (G.seamTorus_mem_seamCollar _ t)
  have hpM := B.isPathConnected_middle₃ h01 h02 h12 hcov
  have hoM : IsOpen M :=
    ((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).inter (G.isOpen_rightRegion _)
  obtain ⟨fM, -, hfMx⟩ := B.exists_bijective_middleRetraction₃ h01 h02 h12 hcov
  have hfM : ∀ (u : M) (x : G.components.piece (B.piece none)), u.1 = G.cutMap x → fM u = x := by
    intro u x hu
    obtain ⟨u, hu'⟩ := u
    subst hu
    exact hfMx x hu'
  have : PathConnectedSpace M := isPathConnected_iff_pathConnectedSpace.mp hpM
  let xM : M := ⟨π m₀ torusBase, hπM m₀ torusBase⟩
  let FM : FundamentalGroup M xM →* H :=
    (ι.comp (B.product.productHom κ (fM xM) (PathConnectedSpace.somePath b₀ _))).comp
      (FundamentalGroup.map fM xM)
  have hFM : ∀ m (δ : Path xM ⟨π m torusBase, hπM m torusBase⟩), ∃ k : H, ∀ g,
      FM (GC.Topology.markedMap (closedTriangleCod (π m) M (hπM m)) torusBase δ g) =
        k * E m g * k⁻¹ := by
    intro m δ
    have hp : fM.comp (closedTriangleCod (π m) M (hπM m)) =
        (B.product.portMap (B.port (.inr m))).comp (ContinuousMap.id Torus) :=
      ContinuousMap.ext fun t => hfM _ _ rfl
    obtain ⟨k, hk⟩ := B.forall_conj_product ι κ fM xM _ _ _ _ hp (w m) (hκ m) δ
    exact ⟨k, fun g => by rw [hk g, torusAut_id, MonoidHom.id_apply]⟩
  have hL₀M : G.leftRegion (B.seam m₀) ∩ M = G.seamCollar (B.seam m₀) := by
    ext x
    constructor
    · rintro ⟨hl, ⟨hr, -⟩, -⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₀) (B.isSeparating_seam m₀)]
      exact ⟨hl, hr⟩
    · intro hx
      exact ⟨Or.inr hx, hc₀M hx⟩
  obtain ⟨s₀, F₀, T₀⟩ := B.exists_hom_glue_seam m₀ M hoM hpM hL₀M (hsM m₀) FM _
    (B.forall_conj_seam_of_port ι (w m₀) m₀ (hM m₀) (hπM m₀) (hsM m₀) FM (hFM m₀))
  let S₀ := G.leftRegion (B.seam m₀) ∪ M
  have hπS₀ : ∀ m t, π m t ∈ S₀ := fun m t => Or.inr (hπM m t)
  have hsS₀ : ∀ m t, G.seamTorus (B.seam m) t ∈ S₀ := fun m t => Or.inr (hsM m t)
  have hL₀R₁ : G.leftRegion (B.seam m₀) ⊆ G.rightRegion (B.seam m₁) :=
    B.leftRegion_subset_rightRegion (Ne.symm h01)
  have hL₀R₂ : G.leftRegion (B.seam m₀) ⊆ G.rightRegion (B.seam m₂) :=
    B.leftRegion_subset_rightRegion (Ne.symm h02)
  have hL₁R₂ : G.leftRegion (B.seam m₁) ⊆ G.rightRegion (B.seam m₂) :=
    B.leftRegion_subset_rightRegion (Ne.symm h12)
  have hL₁S₀ : G.leftRegion (B.seam m₁) ∩ S₀ = G.seamCollar (B.seam m₁) := by
    ext x
    constructor
    · rintro ⟨hl, hx⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₁) (B.isSeparating_seam m₁)]
      rcases hx with hx | hx
      · exact ⟨hl, hL₀R₁ hx⟩
      · exact ⟨hl, hx.1.2⟩
    · intro hx
      exact ⟨Or.inr hx, Or.inr (hc₁M hx)⟩
  have hpS₀ : IsPathConnected S₀ := (G.isPathConnected_leftRegion _).union hpM
    ⟨_, Or.inr (G.seamTorus_mem_seamCollar _ torusBase), hc₀M (G.seamTorus_mem_seamCollar _ _)⟩
  have hoS₀ : IsOpen S₀ := (G.isOpen_leftRegion _).union hoM
  obtain ⟨s₁, F₁, T₁⟩ := B.exists_hom_glue_seam m₁ S₀ hoS₀ hpS₀ hL₁S₀ (hsS₀ m₁) F₀ _
    (B.forall_conj_seam_of_port ι (w m₁) m₁ (hM m₁) (hπS₀ m₁) (hsS₀ m₁) F₀
      (T₀ (π m₁) (hπM m₁) (E m₁) (hFM m₁)))
  let S₁ := G.leftRegion (B.seam m₁) ∪ S₀
  have hπS₁ : ∀ m t, π m t ∈ S₁ := fun m t => Or.inr (hπS₀ m t)
  have hsS₁ : ∀ m t, G.seamTorus (B.seam m) t ∈ S₁ := fun m t => Or.inr (hsS₀ m t)
  have hL₂S₁ : G.leftRegion (B.seam m₂) ∩ S₁ = G.seamCollar (B.seam m₂) := by
    ext x
    constructor
    · rintro ⟨hl, hx⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₂) (B.isSeparating_seam m₂)]
      rcases hx with hx | hx | hx
      · exact ⟨hl, hL₁R₂ hx⟩
      · exact ⟨hl, hL₀R₂ hx⟩
      · exact ⟨hl, hx.2⟩
    · intro hx
      exact ⟨Or.inr hx, Or.inr (Or.inr (hc₂M hx))⟩
  have hpS₁ : IsPathConnected S₁ := (G.isPathConnected_leftRegion _).union hpS₀
    ⟨_, Or.inr (G.seamTorus_mem_seamCollar _ torusBase),
      Or.inr (hc₁M (G.seamTorus_mem_seamCollar _ _))⟩
  have hoS₁ : IsOpen S₁ := (G.isOpen_leftRegion _).union hoS₀
  obtain ⟨s₂, F₂, T₂⟩ := B.exists_hom_glue_seam m₂ S₁ hoS₁ hpS₁ hL₂S₁ (hsS₁ m₂) F₁ _
    (B.forall_conj_seam_of_port ι (w m₂) m₂ (hM m₂) (hπS₁ m₂) (hsS₁ m₂) F₁
      (T₁ (π m₂) (hπS₀ m₂) (E m₂) (T₀ (π m₂) (hπM m₂) (E m₂) (hFM m₂))))
  let S₂ := G.leftRegion (B.seam m₂) ∪ S₁
  have huniv : ∀ x, x ∈ S₂ := by
    intro x
    rcases B.mem_pieceImage_cases₃ hcov x with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (B.pieceImage_none_subset_middle₃ m₀ m₁ m₂ h)))
    · exact Or.inr (Or.inr (Or.inl (B.pieceImage_solid_subset_leftRegion m₀ h)))
    · exact Or.inr (Or.inl (B.pieceImage_solid_subset_leftRegion m₁ h))
    · exact Or.inl (B.pieceImage_solid_subset_leftRegion m₂ h)
  let ιS : C(W.Carrier, S₂) := ⟨fun x => ⟨x, huniv x⟩, continuous_id.subtype_mk _⟩
  refine ⟨s₂.1, F₂.comp (FundamentalGroup.map ιS s₂.1), fun m δ => ?_⟩
  refine forall_conj_pull ιS F₂ (π m) torusBase (E m) ?_ δ
  refine forall_conj_congr F₂ (show ιS.comp (π m) = closedTriangleCod (π m) S₂
    (fun t => Or.inr (hπS₁ m t)) from ContinuousMap.ext fun t => rfl) torusBase (E m) ?_
  exact T₂ (π m) (hπS₁ m) (E m) (T₁ (π m) (hπS₀ m) (E m) (T₀ (π m) (hπM m) (E m) (hFM m)))

end SeifertBlock

end GC.Seifert
