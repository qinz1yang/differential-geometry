import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusGenerators

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.isPathConnected {M : Type*} [TopologicalSpace M]
    {A A₀ A₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) : IsPathConnected A := by
  obtain ⟨φ, -, -⟩ := hA
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  let _ : PathConnectedSpace (Icc (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
  let _ : PathConnectedSpace A := φ.surjective.pathConnectedSpace φ.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem IsAnnulusOn.carriesFundamentalGroupOnto_first_of_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ J T : Set M}
    (hA : IsAnnulusOn A A₀ A₁) (hAT : A ⊆ T) (hJA : J ⊆ A) (hne : J.Nonempty)
    (hcarry : CarriesFundamentalGroupOnto J T) : CarriesFundamentalGroupOnto A₀ T := by
  have hcarryA := hcarry.mono_of_isPathConnected hne hJA hAT hA.isPathConnected
  have hcompact := hA.isCompact
  obtain ⟨φ, h₀, -⟩ := hA
  let _ : CompactSpace A := isCompact_iff_compactSpace.mp hcompact
  let f (p : A × ℝ) : M := φ ((φ.symm p.1).1,
    (projIcc 0 1 zero_le_one p.2) * (φ.symm p.1).2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfone (x : A) : f (x, 1) = x := by
    simp [f]
  have hone : (fun x => f (x, (1 : ℝ))) '' univ = A := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      change f (a, 1) ∈ A
      rw [hfone]
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, hfone _⟩
  have hzero : (fun x => f (x, (0 : ℝ))) '' univ = A₀ := by
    rw [h₀]
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      refine ⟨φ ((φ.symm a).1, 0), ⟨((φ.symm a).1, 0), rfl, rfl⟩, ?_⟩
      simp [f]
    · rintro ⟨a, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨φ p, mem_univ _, ?_⟩
      have hp' : p.2 = 0 := Subtype.ext hp
      have heq : (p.1, (0 : Icc (0 : ℝ) 1)) = p := Prod.ext rfl hp'.symm
      simpa [f] using congrArg (fun q => (φ q : M)) heq
  rw [← hzero]
  apply carriesFundamentalGroupOnto_image_zero_of_image_one isCompact_univ hf.continuousOn
    (fun p _ => hAT (φ ((φ.symm p.1).1,
      (projIcc 0 1 zero_le_one p.2) * (φ.symm p.1).2)).2)
  · intro x _ y _ hxy
    exact Subtype.ext (by simpa only [hfone] using hxy)
  · rwa [hone]

theorem IsAnnulusOn.carriesFundamentalGroupOnto_ends_of_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ J T : Set M}
    (hA : IsAnnulusOn A A₀ A₁) (hAT : A ⊆ T) (hJA : J ⊆ A) (hne : J.Nonempty)
    (hcarry : CarriesFundamentalGroupOnto J T) :
    CarriesFundamentalGroupOnto A₀ T ∧ CarriesFundamentalGroupOnto A₁ T :=
  ⟨hA.carriesFundamentalGroupOnto_first_of_subset hAT hJA hne hcarry,
    hA.symm.carriesFundamentalGroupOnto_first_of_subset hAT hJA hne hcarry⟩

theorem IsTopologicalSolidTorus.disjoint_cell_of_carrier_boundary_avoidance {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {T C Cb J : Set M} (hT : IsTopologicalSolidTorus T) (hC : IsPLCellOn 3 C Cb)
    (hCT : C ⊆ T) (hJ : IsPreconnected J) (hne : J.Nonempty)
    (hcarry : CarriesFundamentalGroupOnto J T) (hdis : Disjoint Cb J) : Disjoint C J := by
  have hnot : ¬ J ⊆ C := fun hsub =>
    hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hC hCT hne hsub hcarry
  obtain ⟨x, hxJ, hxC⟩ := not_subset.mp hnot
  have havoid : Disjoint J (frontier Cᶜ) := by
    rw [frontier_compl, ← hC.boundary_eq_frontier]
    exact hdis.symm
  have hsub := IsPreconnected.subset_of_disjoint_frontier hJ ⟨x, hxJ, hxC⟩ havoid
  exact disjoint_left.mpr fun _ hxC hxJ => hsub hxJ hxC

theorem IsAnnulusOn.disjoint_ends_of_cell_in_solid_torus {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A A₀ A₁ J T C Cb : Set M} (hA : IsAnnulusOn A A₀ A₁)
    (hAT : A ⊆ T) (hJA : J ⊆ A) (hne : J.Nonempty)
    (hcarry : CarriesFundamentalGroupOnto J T) (hT : IsTopologicalSolidTorus T)
    (hC : IsPLCellOn 3 C Cb) (hCT : C ⊆ T) (hdis : Disjoint Cb (A₀ ∪ A₁)) :
    Disjoint C (A₀ ∪ A₁) := by
  obtain ⟨h₀, h₁⟩ := hA.carriesFundamentalGroupOnto_ends_of_subset hAT hJA hne hcarry
  apply disjoint_union_right.mpr
  exact ⟨hT.disjoint_cell_of_carrier_boundary_avoidance hC hCT hA.isPreconnected_ends.1
      hA.ends_nonempty.1 h₀ (hdis.mono_right subset_union_left),
    hT.disjoint_cell_of_carrier_boundary_avoidance hC hCT hA.isPreconnected_ends.2
      hA.ends_nonempty.2 h₁ (hdis.mono_right subset_union_right)⟩

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

theorem section34_second_rims_carry_outer_tube
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    CarriesFundamentalGroupOnto (G (ends e).2 '' Bb₀ e) (Sp e) ∧
      CarriesFundamentalGroupOnto (G (ends e).2 '' Bb₁ e) (Sp e) := by
  obtain ⟨k, hk, hcarry, -⟩ := exists_section34_piercing_circle_carrying_generators hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, -, -, -, -, hBbS, -, -, -, -, -, -, -, -, hPg, -⟩ := hpack
  obtain ⟨P, hP⟩ := (hPg e k hk).1
  have hne : (Pg e k).Nonempty := P.piece.bijOn.image_eq ▸ hP.nonempty.image P.piece.map
  have hJB : Pg e k ⊆ G (ends e).2 '' Bb e :=
    fun _ hx => image_mono sdiff_subset ((hPg e k hk).2 hx).2
  exact hann.carriesFundamentalGroupOnto_ends_of_subset
    ((hBbS e).1.trans interior_subset) hJB hne hcarry

end DifferentialGeometry.Topology.PiecewiseLinear
