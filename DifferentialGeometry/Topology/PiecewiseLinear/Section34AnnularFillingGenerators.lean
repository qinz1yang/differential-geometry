import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity
import DifferentialGeometry.Topology.VanKampen.CellAttachmentFundamentalGroup

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem CarriesFundamentalGroupOnto.mono_of_isPathConnected
    {X : Type*} [TopologicalSpace X] {J C T : Set X}
    (hJ : CarriesFundamentalGroupOnto J T) (hne : J.Nonempty)
    (hJC : J ⊆ C) (hCT : C ⊆ T) (hC : IsPathConnected C) :
    CarriesFundamentalGroupOnto C T := by
  let _ : PathConnectedSpace C := isPathConnected_iff_pathConnectedSpace.mp hC
  obtain ⟨a, ha⟩ := hne
  refine ⟨hCT, fun hCT' b => ?_⟩
  let iJC : C(J, C) := ⟨inclusion hJC, continuous_inclusion hJC⟩
  let iCT : C(C, T) := ⟨inclusion hCT', continuous_inclusion hCT'⟩
  have hbase : Function.Surjective (FundamentalGroup.map iCT (iJC ⟨a, ha⟩)) := by
    intro z
    obtain ⟨w, hw⟩ := hJ.2 (hJC.trans hCT') ⟨a, ha⟩ z
    refine ⟨FundamentalGroup.map iJC ⟨a, ha⟩ w, ?_⟩
    exact (DFunLike.congr_fun
      (fundamentalGroup_map_continuousMap_comp iJC iCT ⟨a, ha⟩) w).symm.trans hw
  let p := PathConnectedSpace.somePath b (iJC ⟨a, ha⟩)
  let eC := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let eT := FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map iCT.continuous)
  intro z
  obtain ⟨w, hw⟩ := hbase (eT z)
  refine ⟨eC.symm w, eT.injective ?_⟩
  rw [DifferentialGeometry.Topology.fundamentalGroup_map_changeBasepoint]
  simpa only [eC, MulEquiv.apply_symm_apply] using hw

theorem IsTopologicalSolidTorus.not_exterior_compression_of_carrier
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S J : Set M}
    (hS : IsTopologicalSolidTorus S) (hJ : CarriesFundamentalGroupOnto J S)
    (hne : J.Nonempty)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hT : IsPLTorus (frontier R.space))
    {V D : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hV : IsOpen V) (hu : IsPLHomeomorphInto 3 u V) (hRV : R.space ⊆ V)
    (hVS : u '' V ⊆ S) (hJR : J ⊆ u '' R.space)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDV : D ⊆ V)
    (hmeet : D ∩ frontier R.space = r '' stdSimplexBoundary 2)
    (hess : ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨inclusion hboundary, continuous_inclusion hboundary⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic) :
    ¬ D \ r '' stdSimplexBoundary 2 ⊆ R.spaceᶜ := by
  intro hext
  obtain ⟨B, hB, hRB, hBV⟩ := exists_isPLBall_superset_of_exterior_compression
    R hR hT hV hRV hr hDV hmeet hess hext
  have huB : IsPLHomeomorphInto 3 u B :=
    (hu.isPLOn.mono_of_isPolyhedron hB.isPolyhedron hBV).isPLHomeomorphInto_model
      hB.isPolyhedron.isCompact (hu.injOn.mono hBV)
  obtain ⟨rB, hrB⟩ := hB
  have hcell : IsPLCellOn 3 (u '' B) (u '' (rB '' stdSimplexBoundary 3)) :=
    ⟨B, rB, u, hrB, huB, rfl, rfl⟩
  exact hS.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hcell
    ((image_mono hBV).trans hVS) hne (hJR.trans (image_mono (hRB.trans interior_subset))) hJ

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


theorem section34_annular_filling_carries_generators
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i j : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hRP : R.space ⊆ P) (hreg : closure (interior R.space) = R.space)
    (hint : IsConnected (interior R.space)) (hfront : u '' frontier R.space = D ∪ F)
    (hRT : u '' R.space ⊆ Tp e) :
    CarriesFundamentalGroupOnto (u '' R.space) (Tp e) ∧
      CarriesFundamentalGroupOnto (u '' R.space) (Sp e) ∧
      ∀ (d : ℕ) (B Bbd : Set M₂), IsPLCellOn d B Bbd → B ⊆ Sp e → ¬ u '' R.space ⊆ B := by
  have hRclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hFR : F ⊆ u '' R.space := by
    apply Subset.trans subset_union_right
    rw [← hfront]
    exact image_mono hRclosed.frontier_subset
  have hJR := hF.first_subset.trans hFR
  have hconn : IsConnected R.space := hreg ▸ hint.closure
  have hpath := DifferentialGeometry.Topology.SimplicialComplex.isPathConnected_geometricSpace
    R hconn
  have himage : IsPathConnected (u '' R.space) :=
    hpath.image' (hu.continuousOn.mono hRP)
  have hgen := section34_piercing_generators_of_essential_second hprep hpack e hi hess
  have hne := hF.ends_nonempty.1
  have hRS := hRT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  refine ⟨hgen.2.1.mono_of_isPathConnected hne hJR hRT himage,
    hgen.1.mono_of_isPathConnected hne hJR hRS himage, ?_⟩
  intro d B Bbd hB hBS hRB
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).1
  exact htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn
    hB hBS hne (hJR.trans hRB) hgen.1

end DifferentialGeometry.Topology.PiecewiseLinear
