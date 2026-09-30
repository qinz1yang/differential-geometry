import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEmptyAnnularBand

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isAnnulusOn_stdSimplex_lateral :
    IsAnnulusOn (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ {0}) (stdSimplexBoundary 2 ×ˢ {1}) := by
  have hβ : ∀ z : stdSimplexBoundary 2, (⟨z.1, z.2.1⟩ : Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∈
      DifferentialGeometry.Simplex.boundary (Fin 3) := fun z => z.2.2
  have hβ' : ∀ z : DifferentialGeometry.Simplex.boundary (Fin 3),
      (z.1.1 : Fin 3 → ℝ) ∈ stdSimplexBoundary 2 := fun z => ⟨z.1.2, z.2⟩
  let β : stdSimplexBoundary 2 ≃ₜ DifferentialGeometry.Simplex.boundary (Fin 3) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, hβ z⟩
      invFun := fun z => ⟨z.1.1, hβ' z⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.1).subtype_mk hβ
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hβ' }
  let θ := β.trans (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  let φ := (θ.symm.prodCongr (Homeomorph.refl (Icc (0 : ℝ) 1))).trans
    (Homeomorph.Set.prod (stdSimplexBoundary 2) (Icc (0 : ℝ) 1)).symm
  have hlevel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) = stdSimplexBoundary 2 ×ˢ {t} := by
    ext x
    constructor
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨(θ.symm p.1).property, hp⟩
    · rintro ⟨hx, hxt⟩
      let p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 :=
        (θ ⟨x.1, hx⟩, ⟨t, ht⟩)
      refine ⟨φ p, ⟨p, rfl, rfl⟩, ?_⟩
      change ((θ.symm (θ ⟨x.1, hx⟩)).val, t) = x
      simp only [Homeomorph.symm_apply_apply]
      exact Prod.ext rfl hxt.symm
  exact ⟨φ, (hlevel 0 ⟨le_rfl, zero_le_one⟩).symm,
    (hlevel 1 ⟨zero_le_one, le_rfl⟩).symm⟩

theorem image_lateral_open_eq_sdiff_ends {M : Type*}
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hinj : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) :
    f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) \
        (f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
          f '' (stdSimplexBoundary 2 ×ˢ {1})) := by
  have hends : (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ)) ∪
      (stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) ⊆
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    union_subset (prod_mono_right (by simp)) (prod_mono_right (by simp))
  rw [← image_union, ← hinj.image_sdiff_subset hends]
  congr 1
  ext x
  simp only [mem_prod, mem_Ioo, mem_sdiff, mem_Icc, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨hx, h₀, h₁⟩
    exact ⟨⟨hx, h₀.le, h₁.le⟩, fun h => h.elim
      (fun hz => h₀.ne' hz.2) (fun ho => h₁.ne ho.2)⟩
  · rintro ⟨⟨hx, h₀, h₁⟩, hn⟩
    exact ⟨hx, lt_of_le_of_ne h₀ (fun h => hn (Or.inl ⟨hx, h.symm⟩)),
      lt_of_le_of_ne h₁ (fun h => hn (Or.inr ⟨hx, h⟩))⟩

theorem closure_image_lateral_open {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) :
    closure (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) =
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hbd : IsClosed (stdSimplexBoundary 2) := by
    have h := (isPLSphere_simplexBoundary_std 1).isPolyhedron.isClosed
    rwa [simplexBoundary_stdVertices_space] at h
  have hcl : closure (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, hbd.closure_eq, closure_Ioo zero_ne_one]
  have hc : IsCompact (closure (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) :=
    hcl.symm ▸ isAnnulusOn_stdSimplex_lateral.isCompact
  simpa only [hcl] using (image_closure_of_isCompact hc (hcl.symm ▸ hf)).symm

theorem IsPLCellOn.connectedComponentIn_eq_lateral_band {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A T : Set M} (hS : IsPLCellOn 3 S B) (hAB : A ⊆ B)
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hinj : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hband : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) T)
    {x : M} (hx : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) :
    connectedComponentIn (A \ T) x =
      f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
      closure (connectedComponentIn (A \ T) x) =
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hsub : f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ A \ T := by
    intro y hy
    exact ⟨hband (image_mono (prod_mono_right Ioo_subset_Icc_self) hy),
      fun hyT => disjoint_left.mp hempty hy hyT⟩
  have hconn := ((isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))).image f
      (hf.mono (prod_mono_right Ioo_subset_Icc_self))
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hf hinj
  have hccband : connectedComponentIn (A \ T) x ⊆
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hann (hband.trans hAB)
      ((connectedComponentIn_subset _ _).trans (sdiff_subset.trans hAB))
      isPreconnected_connectedComponentIn
    · exact ⟨x, mem_connectedComponentIn (hsub hx),
        image_mono (prod_mono_right Ioo_subset_Icc_self) hx⟩
    · exact disjoint_left.mpr fun y hy hyend =>
        (connectedComponentIn_subset _ _ hy).2 (hends hyend)
  have heq : connectedComponentIn (A \ T) x =
      f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) := by
    apply Subset.antisymm
    · intro y hy
      rw [image_lateral_open_eq_sdiff_ends hinj]
      exact ⟨hccband hy, fun hyend =>
        (connectedComponentIn_subset _ _ hy).2 (hends hyend)⟩
    · exact hconn.isPreconnected.subset_connectedComponentIn hx hsub
  exact ⟨heq, heq ▸ closure_image_lateral_open hf⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_piercing_empty_band_components
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hlt : 1 < cnt e)
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ i < cnt e, ∃ j < cnt e, i ≠ j ∧
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
        (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j ∧
      Disjoint ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
        (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e) ∧
      IsAnnulusOn ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
        (Pg e i) (Pg e j) ∧
      ∀ x ∈ (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1),
        connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) x =
          (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
        closure (connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) x) =
          (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨i, hi, j, hj, hij, P, u, φ, hP, hu, hφ, hφP, hφA, hφ₀, hφ₁, hempty⟩ :=
    exists_section34_piercing_empty_annular_band hprep hpack e hlt hess
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hboundary, -, -, -, hGcp, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hmaps : MapsTo φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hφP ⟨x, hx, rfl⟩
  have hcont : ContinuousOn (u ∘ φ) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hmaps
  have hinj : InjOn (u ∘ φ) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hφ.bijOn.injOn hx hy (hu.injOn (hmaps hx) (hmaps hy) hxy)
  have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hPgBd (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun x hx => image_mono (sdiff_subset.trans hAaBd) ((hPg e k hk).2 hx).1
  have hends : (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hφ₀, hφ₁]
    exact union_subset (hPgBd i hi) (hPgBd j hj)
  have hfree : Disjoint ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1) := by
    refine disjoint_left.mpr fun x hxopen hxBd => ?_
    have hxBb := hφA (image_mono (prod_mono_right Ioo_subset_Icc_self) hxopen)
    have hxBd' := image_mono (hBb e).1 hxBb
    have hxAa := image_mono sdiff_subset (hboundary e ⟨hxBd, hxBd'⟩).1.1
    exact disjoint_left.mp hempty hxopen ⟨hxAa, hxBb⟩
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hcont hinj
  rw [hφ₀, hφ₁] at hann
  refine ⟨i, hi, j, hj, hij, P, u, φ, hP, hu, hφ, hφP, hφA, hφ₀, hφ₁, hempty, hann, ?_⟩
  intro x hx
  exact ((hCp (ends e).2).image (hGcp (ends e).2)).connectedComponentIn_eq_lateral_band
    (image_mono (hBb e).1) hcont hinj hφA hends hfree hx

end DifferentialGeometry.Topology.PiecewiseLinear
