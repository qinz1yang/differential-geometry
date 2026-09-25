import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusFundamentalGroup

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem int_endomorphism_injective_of_surjective (f : ℤ →+ ℤ)
    (hf : Function.Surjective f) : Function.Injective f := by
  have heq (z : ℤ) : f z = z * f 1 := by
    conv_lhs => rw [show z = z • (1 : ℤ) by simp]
    rw [map_zsmul]
    simp
  obtain ⟨n, hn⟩ := hf 1
  have hne : f 1 ≠ 0 := by
    intro h
    rw [heq, h, mul_zero] at hn
    exact zero_ne_one hn
  intro a b hab
  rw [heq a, heq b] at hab
  exact mul_right_cancel₀ hne hab

theorem IsTopologicalSolidTorus.fundamentalGroup_map_bijective_of_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set X} {T : Set Y}
    (hS : IsTopologicalSolidTorus S) (hT : IsTopologicalSolidTorus T)
    (f : C(S, T)) (x : S) (hf : Function.Surjective (FundamentalGroup.map f x)) :
    Function.Bijective (FundamentalGroup.map f x) := by
  let eS := hS.fundamentalGroupEquivInt x
  let eT := hT.fundamentalGroupEquivInt (f x)
  let g := eT.toMonoidHom.comp ((FundamentalGroup.map f x).comp eS.symm.toMonoidHom)
  have hg : Function.Surjective g := eT.surjective.comp (hf.comp eS.symm.surjective)
  let ga : ℤ →+ ℤ := MonoidHom.toAdditiveRight g
  have hga : Function.Surjective ga := by
    intro z
    obtain ⟨w, hw⟩ := hg (Multiplicative.ofAdd z)
    exact ⟨w.toAdd, congrArg Multiplicative.toAdd hw⟩
  have hgi : Function.Injective g := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    exact int_endomorphism_injective_of_surjective ga hga
      (congrArg Multiplicative.toAdd hab)
  refine ⟨fun a b hab => eS.injective (hgi ?_), hf⟩
  simpa [g] using congrArg eT hab

theorem IsTopologicalSolidTorus.fundamentalGroup_inclusion_bijective
    {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hS : IsTopologicalSolidTorus S) (hT : IsTopologicalSolidTorus T)
    (hcarry : CarriesFundamentalGroupOnto S T) (hST : S ⊆ T) (x : S) :
    Function.Bijective (FundamentalGroup.map
      (⟨inclusion hST, continuous_inclusion hST⟩ : C(S, T)) x) :=
  hS.fundamentalGroup_map_bijective_of_surjective hT _ x (hcarry.2 hST x)

theorem CarriesFundamentalGroupOnto.of_intermediate_solid_torus
    {X : Type*} [TopologicalSpace X] {J S T : Set X}
    (hcarry : CarriesFundamentalGroupOnto J T)
    (hS : IsTopologicalSolidTorus S) (hT : IsTopologicalSolidTorus T)
    (hJS : J ⊆ S) (hST : S ⊆ T) : CarriesFundamentalGroupOnto J S := by
  refine ⟨hJS, fun hJS' x => ?_⟩
  let iJS : C(J, S) := ⟨inclusion hJS', continuous_inclusion hJS'⟩
  let iST : C(S, T) := ⟨inclusion hST, continuous_inclusion hST⟩
  have hcomp : Function.Surjective (FundamentalGroup.map (iST.comp iJS) x) :=
    hcarry.2 (hJS'.trans hST) x
  have hs : Function.Surjective (FundamentalGroup.map iST (iJS x)) := by
    intro z
    obtain ⟨w, hw⟩ := hcomp z
    refine ⟨FundamentalGroup.map iJS x w, ?_⟩
    exact (DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp iJS iST x) w).symm.trans hw
  have hi := (hS.fundamentalGroup_map_bijective_of_surjective hT iST (iJS x) hs).1
  intro z
  obtain ⟨w, hw⟩ := hcomp (FundamentalGroup.map iST (iJS x) z)
  refine ⟨w, hi ?_⟩
  exact (DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp iJS iST x) w).symm.trans hw

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


theorem section34_essential_trace_generates_solid_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    {C : Set M₂} (hC : IsTopologicalSolidTorus C) (hCT : C ⊆ Tp e) (hJC : Pg e i ⊆ C) :
    CarriesFundamentalGroupOnto (Pg e i) C ∧
      (∀ hCT' : C ⊆ Tp e, ∀ x : C, Function.Bijective (FundamentalGroup.map
        (⟨inclusion hCT', continuous_inclusion hCT'⟩ : C(C, Tp e)) x)) ∧
      ∀ hCS : C ⊆ Sp e, ∀ x : C, Function.Bijective (FundamentalGroup.map
        (⟨inclusion hCS, continuous_inclusion hCS⟩ : C(C, Sp e)) x) := by
  have hgen := section34_piercing_generators_of_essential_second hprep hpack e hi hess
  obtain ⟨hS, hT⟩ := section34_tubes_are_topological_solid_tori hprep hpack e
  have hCS := hCT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  have hne : (Pg e i).Nonempty := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPg, -⟩ := hpack
    obtain ⟨P, hP⟩ := (hPg e i hi).1
    obtain ⟨x, hx⟩ := hP.nonempty
    exact ⟨P.piece.map x, P.piece.bijOn.mapsTo hx⟩
  have hcarryT := hgen.2.1.mono_of_isPathConnected hne hJC hCT hC.isPathConnected
  have hcarryS := hgen.1.mono_of_isPathConnected hne hJC hCS hC.isPathConnected
  exact ⟨hgen.2.1.of_intermediate_solid_torus hC hT hJC hCT,
    fun hCT' x => hC.fundamentalGroup_inclusion_bijective hT hcarryT hCT' x,
    fun hCS' x => hC.fundamentalGroup_inclusion_bijective hS hcarryS hCS' x⟩

end DifferentialGeometry.Topology.PiecewiseLinear
