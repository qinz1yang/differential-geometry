import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_small_isPL_homeomorph_generalPosition_off_polyhedron_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace E3 X] [HasGroupoid X (plGroupoid 3)]
    (e : OpenPartialHomeomorph X E3) (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (K L : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) {Q : Set E3} (hQ : IsPolyhedron Q)
    {U : Set X} (hU : IsOpen U) (hKU : K.space ⊆ e '' (e.source ∩ U))
    (hQU : Q ⊆ e '' (e.source ∩ U)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : X ≃ₜ X, IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id (e.symm '' Q) ∧ MapsTo h e.source e.source ∧
      IsPLHomeomorphOn (e ∘ h ∘ e.symm) K.space ((e ∘ h ∘ e.symm) '' K.space) ∧
      IsPolyhedron (((e ∘ h ∘ e.symm) '' K.space) ∩ L.space) ∧
      ∀ z ∈ ((e ∘ h ∘ e.symm) '' K.space) ∩ L.space, z ∉ Q →
        HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z := by
  classical
  let V := e '' (e.source ∩ U)
  have hV : IsOpen V := e.isOpen_image_source_inter hU
  have hVt : V ⊆ e.target := by
    rintro z ⟨x, hx, rfl⟩
    exact e.map_source hx.1
  have hcompact : IsCompact (K.space ∪ Q) := (isPolyhedron_space K).isCompact.union hQ.isCompact
  obtain ⟨r, hr, hrV⟩ := hcompact.exists_cthickening_subset_open hV
    (union_subset hKU hQU)
  let C := cthickening r (K.space ∪ Q)
  let O := thickening r (K.space ∪ Q)
  have hC : IsCompact C := isCompact_of_isClosed_isBounded isClosed_cthickening
    hcompact.isBounded.cthickening
  have hCt : C ⊆ e.target := hrV.trans hVt
  have hOC : O ⊆ C := thickening_subset_cthickening r (K.space ∪ Q)
  obtain ⟨δ, hδ, hδbound⟩ := e.exists_uniform_conjugateMap_radius hC hCt hε
  obtain ⟨k, -, -, -, -, hk, hkclose, hkfix, hkQ, hkcross⟩ :=
    exists_small_homeomorph_generalPosition_off_polyhedron_with_lipschitz_displacement
      K L hK hL (by simp) hQ isOpen_thickening
      (subset_union_left.trans (self_subset_thickening hr _))
      (subset_union_right.trans (self_subset_thickening hr _)) hδ zero_lt_one
  let k₀ : E3 ≃ₜ E3 :=
    { toFun := k
      invFun := Function.invFunOn k univ
      left_inv := fun z => hk.bijOn.invOn_invFunOn.1 (mem_univ z)
      right_inv := fun z => hk.bijOn.invOn_invFunOn.2 (mem_univ z)
      continuous_toFun := continuousOn_univ.mp hk.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hk.isPiecewiseAffineOn_invFunOn.continuousOn }
  have hkC : EqOn k₀ id Cᶜ := fun z hz => hkfix (fun hzO => hz (hOC hzO))
  obtain ⟨hkmap, hclose⟩ := hδbound k₀ (fun z _ => hkclose z) hkC
  let h := e.conjugateHomeomorph k₀ hC hCt hkC
  have hmap : MapsTo h e.source e.source := by
    intro x hx
    rw [show h x = e.conjugateMap k₀ x from rfl, e.conjugateMap_of_mem k₀ hx]
    exact e.map_target (hkmap (e.map_source hx))
  have hcoord : EqOn (e ∘ h ∘ e.symm) k K.space := by
    intro z hz
    have hzt := hVt (hKU hz)
    change e (e.conjugateMap k₀ (e.symm z)) = k z
    rw [e.conjugateMap_of_mem k₀ (e.map_target hzt), e.right_inv hzt,
      e.right_inv (hkmap hzt)]
    rfl
  have himage : (e ∘ h ∘ e.symm) '' K.space = k '' K.space := hcoord.image_eq
  have hkCsymm : EqOn k₀.symm id Cᶜ := by
    intro z hz
    have hfixed := congrArg k₀.symm (hkC hz)
    simpa only [Homeomorph.symm_apply_apply, id_eq] using hfixed.symm
  have hplsymm : IsPL 3 3 h.symm :=
    isPL_conjugateHomeomorph e he k₀.symm hk.isPiecewiseAffineOn_invFunOn hC hCt hkCsymm
  refine ⟨h, isPL_conjugateHomeomorph e he k₀ hk.isPiecewiseAffineOn hC hCt hkC,
    hplsymm, hclose, ?_, ?_, hmap, ?_, ?_, ?_⟩
  · intro x hx
    apply e.conjugateMap_eqOn_compl hkC
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hrV hz
    have heq : e.symm z = w := by rw [← hwz, e.left_inv hw.1]
    exact hx (heq.symm ▸ hw.2)
  · rintro x ⟨z, hz, rfl⟩
    have hzt := hVt (hQU hz)
    change e.conjugateMap k₀ (e.symm z) = e.symm z
    rw [e.conjugateMap_of_mem k₀ (e.map_target hzt), e.right_inv hzt]
    exact congrArg e.symm (hkQ hz)
  · rw [himage]
    exact (hk.restrict (isPolyhedron_space K) (subset_univ _)).congr hcoord
  · rw [himage]
    exact ((isPolyhedron_space K).image_of_isPiecewiseAffineOn
      (hk.isPiecewiseAffineOn.mono_of_isPolyhedron (isPolyhedron_space K) (subset_univ _))
      (hk.bijOn.injOn.mono (subset_univ _))).inter (isPolyhedron_space L)
  · rw [himage]
    exact hkcross

theorem exists_small_isPL_homeomorph_sphere_crossing_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace E3 X] [HasGroupoid X (plGroupoid 3)]
    (e : OpenPartialHomeomorph X E3) (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (K L : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite L.faces]
    (hK : IsPLSphere 2 K.space) {P : Set E3} (hP : IsPLBall 3 P)
    (hLP : L.space = frontier P) {Q : Set E3} (hQ : IsPolyhedron Q)
    (hQL : Disjoint Q L.space) {U : Set X} (hU : IsOpen U)
    (hKU : K.space ⊆ e '' (e.source ∩ U)) (hQU : Q ⊆ e '' (e.source ∩ U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : X ≃ₜ X, IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id (e.symm '' Q) ∧ MapsTo h e.source e.source ∧
      IsPLHomeomorphOn (e ∘ h ∘ e.symm) K.space ((e ∘ h ∘ e.symm) '' K.space) ∧
      IsPolyhedron (((e ∘ h ∘ e.symm) '' K.space) ∩ L.space) ∧
      (∀ z ∈ ((e ∘ h ∘ e.symm) '' K.space) ∩ L.space,
        HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z) ∧
      ∀ z ∈ ((e ∘ h ∘ e.symm) '' K.space) ∩ L.space,
        ∃ (V : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen V ∧ z ∈ V ∧ 0 < ρ ∧
          IsPLHomeomorphOn φ V (Metric.ball 0 ρ) ∧ φ z = 0 ∧
          ∀ y ∈ V, (y ∈ (e ∘ h ∘ e.symm) '' K.space ↔ (φ y).2.2 = 0) ∧
            (y ∈ L.space ↔ (φ y).2.1 = 0) := by
  have hKman : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (n := 1) hK
  have hLsphere : IsPLSphere 2 L.space := by
    rw [hLP]
    exact hP.isPLSphere_frontier
  have hLman : IsCombinatorialManifold 2 L :=
    IsPLSphere.isCombinatorialManifold (n := 1) hLsphere
  obtain ⟨h, hh, hhsymm, hclose, hfix, hfixQ, hmap, hcoord, hpoly, hcross⟩ :=
    exists_small_isPL_homeomorph_generalPosition_off_polyhedron_in_chart e he K L
      hKman.isCombinatorialManifoldWithBoundary hLman.isCombinatorialManifoldWithBoundary
      hQ hU hKU hQU hε
  have hcrossAll : ∀ z ∈ ((e ∘ h ∘ e.symm) '' K.space) ∩ L.space,
      HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z :=
    fun z hz => hcross z hz (fun hzQ => Set.disjoint_left.mp hQL hzQ hz.2)
  refine ⟨h, hh, hhsymm, hclose, hfix, hfixQ, hmap, hcoord, hpoly, hcrossAll, ?_⟩
  intro z hz
  have hS := hK.of_isPLHomeomorphOn hcoord
  have hzP : z ∈ frontier P := hLP ▸ hz.2
  have hzcl : z ∈ closure (interior P) := by
    rw [hP.closure_interior]
    exact hP.isPolyhedron.isClosed.frontier_subset hzP
  have hcrossP := hcrossAll z hz
  rw [hLP] at hcrossP ⊢
  exact hcrossP.exists_lineChart hz.1 (hS.exists_isOpen_inter_homeomorph_of_two hz.1)
    hP.isPolyhedron.isClosed hzcl

end DifferentialGeometry.Topology.PiecewiseLinear
