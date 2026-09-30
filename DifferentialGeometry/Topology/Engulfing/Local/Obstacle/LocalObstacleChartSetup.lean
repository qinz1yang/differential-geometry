import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstaclePreparation
import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstacleComparison
import DifferentialGeometry.Topology.Engulfing.Local.Charts.ChartPreimageStability
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

variable {E M : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] {n d p : ℕ}

structure LocalObstacleChartSetup (K L : SimplicialComplex ℝ E) (g : C(K.space, M))
    {X : Set M} (b : AdaptedPiecewiseLinearChart K L g X n p) (Z : Set E) (d : ℕ) (ε : ℝ) where
  radius : ℝ
  gap : ℝ
  radius_pos : 0 < radius
  gap_pos : 0 < gap
  room : radius + 30 * gap < b.innerRadius
  source : SimplicialComplex ℝ E
  fixed : SimplicialComplex ℝ E
  region : SimplicialComplex ℝ E
  finite_faces : source.faces.Finite
  space : source.space = K.space
  refines : simplicialRefines source K
  dimension : ∀ s ∈ source.faces, s.card ≤ d + 1
  fixed_faces : fixed.faces ⊆ source.faces
  fixed_space : fixed.space = L.space
  fixed_refines : simplicialRefines fixed L
  region_faces : region.faces ⊆ source.faces
  expansions : ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn source A C
  error : ℝ
  error_pos : 0 < error
  error_le : error ≤ gap
  extension : C(source.space, EuclideanSpace ℝ (Fin n))
  extension_exact : ∀ x : source.space, x.val ∈ region.space →
    extension x = b.chart (g ⟨x.val, space ▸ x.property⟩)
  old_source : ∀ x : source.space, x.val ∈ region.space →
    g ⟨x.val, space ▸ x.property⟩ ∈ b.chart.source
  approximation : RelativeGeneralPositionApproximation source (region ⊓ fixed) b.obstacle extension d p error
  map : C(source.space, M)
  map_fixed : ∀ x : source.space, x.val ∈ L.space → map x = g ⟨x.val, space ▸ x.property⟩
  map_near : ∀ x, dist (map x) (g ⟨x.val, space ▸ x.property⟩) < ε
  map_source : ∀ x : source.space, x.val ∈ region.space → map x ∈ b.chart.source
  core : Set source.space
  core_closed : IsClosed core
  core_region : core ⊆ interior (Subtype.val ⁻¹' region.space)
  old_core : ∀ x : source.space,
    g ⟨x.val, space ▸ x.property⟩ ∈ b.chart.symm '' closedBall b.center (radius + 20 * gap) →
      x ∈ interior core
  exact_core : ∀ x ∈ core, b.chart (map x) = approximation.approximation x
  new_core : ∀ x : source.space,
    map x ∈ (correctedAffineChart b.chart approximation.correction).symm ''
      closedBall b.center (radius + 18 * gap) → x ∈ interior core
  active_core : ∀ x : source.space, x.val ∈ Z → x ∈ interior core
  active_raw : ∀ x : source.space, x.val ∈ Z →
    approximation.rawMap x ∈ closedBall b.center (radius + 2 * gap)

theorem exists_local_obstacle_chart_setup
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (hpd : p ≤ d)
    (g : C(K.space, M)) {X : Set M} (b : AdaptedPiecewiseLinearChart K L g X n p)
    (Z : Set E) (hZ : IsCompact Z) (_hZK : Z ⊆ K.space)
    (hZcore : ∀ x : K.space, x.val ∈ Z → g x ∈ b.toBufferedChart.core)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (LocalObstacleChartSetup K L g b Z d ε) := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  let S : Set K.space := Subtype.val ⁻¹' Z
  have hS : IsCompact S := (hZ.isClosed.preimage continuous_subtype_val).isCompact
  have himage : IsCompact (b.chart '' (g '' S)) :=
    (hS.image g.continuous).image_of_continuousOn
      (b.chart.continuousOn.mono (by rintro _ ⟨x, hx, rfl⟩; exact (hZcore x hx).1))
  obtain ⟨r, ⟨hr, hri⟩, hrZ⟩ := exists_pos_lt_subset_ball b.inner_pos himage.isClosed
    (by rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact (hZcore x hx).2)
  let t := (b.innerRadius - r) / 100
  have ht : 0 < t := by dsimp [t]; linarith
  have hroom : r + 30 * t < b.innerRadius := by dsimp [t]; linarith
  have hball (k : ℝ) (hk : k ≤ 30) : closedBall b.center (r + k * t) ⊆ b.chart.target := by
    apply (closedBall_subset_closedBall ?_).trans b.outer_subset
    have := mul_le_mul_of_nonneg_right hk ht.le
    linarith [b.radii_lt]
  obtain ⟨A, U, hA, hAK, hU, hAU, hAmem, hUmem⟩ :=
    exists_chart_source_neighborhood K hK g b.chart b.center
      (show r + 20 * t < r + 21 * t by linarith) (hball 21 (by norm_num))
  obtain ⟨δ, hδ, hcontrol⟩ := exists_chart_preimage_tolerance g b.chart b.center
    (show r + 19 * t < r + 20 * t by linarith) (hball 20 (by norm_num))
    (A := Subtype.val ⁻¹' A) (fun x hx => (hAmem x).mpr hx)
  have hUcore (x : K.space) (hx : x.val ∈ U) : g x ∈ b.toBufferedChart.core :=
    ⟨((hUmem x).mp hx).1,
      ball_subset_ball (by linarith : r + 21 * t ≤ b.innerRadius) ((hUmem x).mp hx).2⟩
  obtain ⟨P, J, D, hP, hspace, href, hdim, hJ, hJP, hJs, hJL,
    hD, hDP, hDU, hAD, hAint, hexp, η, hη, hηR, fext, hfext, a,
    G, B, hB, hAB, hBD, hout, hfix, hnear, hsource, hcore⟩ :=
    exists_local_obstacle_preparation K L hK hLK hd b.obstacle b.obstacle_finite
      b.obstacle_dimension hpd b.chart g b.center
      (show r + 21 * t < r + 22 * t by linarith) (hball 22 (by norm_num))
      (lt_min hε hδ) hA hAK hU hAU
      (fun x hx => ((hUmem x).mp hx).1)
      (fun x hx => ball_subset_closedBall ((hUmem x).mp hx).2)
      (fun s hs => by
        obtain ⟨F, hF⟩ := b.fixed_affine s hs
        exact ⟨F, fun x hx hxU => hF x hx (hUcore x hxU)⟩)
      (fun x hx y hy he => b.fixed_injective ⟨hx.1, hUcore x hx.2⟩
        ⟨hy.1, hUcore y hy.2⟩ he)
  let κ : P.space ≃ₜ K.space := Homeomorph.setCongr hspace
  have hηt : η ≤ t := by linarith
  have hentry (x : P.space)
      (hx : g (κ x) ∈ b.chart.symm '' closedBall b.center (r + 20 * t)) :
      x ∈ interior B := hAB ((hAmem (κ x)).mpr hx)
  have hactive (x : P.space) (hx : x.val ∈ Z) : x ∈ interior B := by
    apply hentry
    refine ⟨b.chart (g (κ x)), ?_, b.chart.left_inv (hZcore (κ x) hx).1⟩
    exact closedBall_subset_closedBall (by linarith : r ≤ r + 20 * t)
      (ball_subset_closedBall (hrZ ⟨g (κ x), ⟨κ x, hx, rfl⟩, rfl⟩))
  have hnew (x : P.space)
      (hx : G x ∈ (correctedAffineChart b.chart a.correction).symm ''
        closedBall b.center (r + 18 * t)) : x ∈ interior B := by
    let Gback : C(K.space, M) := G.comp ⟨κ.symm, κ.symm.continuous⟩
    have hn : ∀ y, dist (Gback y) (g y) < δ := by
      intro y
      have hy := (hnear (κ.symm y)).trans_le (min_le_right ε δ)
      change dist (G (κ.symm y)) (g (κ (κ.symm y))) < δ at hy
      change dist (G (κ.symm y)) (g y) < δ
      simpa only [κ.apply_symm_apply] using hy
    have hxold : Gback (κ x) ∈ b.chart.symm '' closedBall b.center (r + 19 * t) := by
      obtain ⟨y, hy, he⟩ := hx
      refine ⟨a.correction y, ?_, ?_⟩
      · apply mem_closedBall.mpr
        have hc : dist (a.correction y) y < η := by
          simpa only [dist_eq_norm] using a.correction_near y
        have hy' := mem_closedBall.mp hy
        have htri := dist_triangle (a.correction y) y b.center
        linarith
      · change b.chart.symm (a.correction y) = G (κ.symm (κ x))
        rw [κ.symm_apply_apply]
        exact he
    exact hAB (hcontrol Gback hn hxold)
  refine ⟨{
    radius := r, gap := t, radius_pos := hr, gap_pos := ht, room := hroom
    source := P, fixed := J, region := D, finite_faces := hP, space := hspace
    refines := href, dimension := hdim, fixed_faces := hJP, fixed_space := hJs
    fixed_refines := hJL, region_faces := hDP, expansions := hexp
    error := η, error_pos := hη, error_le := hηt, extension := fext
    extension_exact := hfext
    old_source := fun x hx => ((hUmem (κ x)).mp (hDU hx)).1
    approximation := a, map := G, map_fixed := hfix
    map_near := fun x => (hnear x).trans_le (min_le_left ε δ)
    map_source := hsource, core := B, core_closed := hB, core_region := hBD
    old_core := hentry, exact_core := hcore, new_core := hnew, active_core := hactive
    active_raw := ?_
  }⟩
  intro x hx
  have hxD : x.val ∈ D.space :=
    show x ∈ Subtype.val ⁻¹' D.space from interior_subset (hBD (interior_subset (hactive x hx)))
  have hdist := a.original_dist_rawMap_lt x
  rw [hfext x hxD] at hdist
  have hz : dist (b.chart (g (κ x))) b.center < r :=
    hrZ ⟨g (κ x), ⟨κ x, hx, rfl⟩, rfl⟩
  have htri := dist_triangle (a.rawMap x) (b.chart (g (κ x))) b.center
  have hdist' : dist (a.rawMap x) (b.chart (g (κ x))) < 2 * η := by
    rw [dist_comm]
    exact hdist
  apply mem_closedBall.mpr
  linarith

end

end DifferentialGeometry.Topology.Engulfing
