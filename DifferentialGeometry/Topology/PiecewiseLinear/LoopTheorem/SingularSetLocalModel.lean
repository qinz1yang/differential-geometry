/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetChartGerm

open Set Topology
namespace DifferentialGeometry.Topology.PiecewiseLinear
universe u
section Segment
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem mem_convexHull_pair_smul_iff (u : F) {c d : ℝ} (hcd : c ≤ d) {z : F} :
    z ∈ convexHull ℝ ({c • u, d • u} : Set F) ↔ ∃ t : ℝ, c ≤ t ∧ t ≤ d ∧ z = t • u := by
  rw [convexHull_pair]
  constructor
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hlow : α * c + β * d - c = β * (d - c) := by
      have hαβ' : α = 1 - β := by linarith
      rw [hαβ']
      ring
    have hhigh : d - (α * c + β * d) = α * (d - c) := by
      have hαβ' : β = 1 - α := by linarith
      rw [hαβ']
      ring
    refine ⟨α * c + β * d, by linarith [mul_nonneg hβ (sub_nonneg.mpr hcd)],
      by linarith [mul_nonneg hα (sub_nonneg.mpr hcd)], ?_⟩
    rw [smul_smul, smul_smul, ← add_smul]
  · rintro ⟨t, hct, htd, rfl⟩
    rcases eq_or_lt_of_le hcd with rfl | hlt
    · have htc : t = c := le_antisymm htd hct
      subst htc
      exact ⟨1, 0, zero_le_one, le_refl 0, by ring, by rw [zero_smul, add_zero, one_smul]⟩
    · have hdc : (0 : ℝ) < d - c := sub_pos.mpr hlt
      refine ⟨(d - t) / (d - c), (t - c) / (d - c), div_nonneg (by linarith) hdc.le,
        div_nonneg (by linarith) hdc.le, ?_, ?_⟩
      · rw [← add_div, div_eq_one_iff_eq hdc.ne']
        ring
      · have hscal : (d - t) / (d - c) * c + (t - c) / (d - c) * d = t := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdc.ne']
          ring
        rw [smul_smul, smul_smul, ← add_smul, hscal]
end Segment
section Model
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
open Classical in
theorem exists_isPLBall_one_local_model_of_ray_germ
    {A Y : Set E} {x : E} {g : E → F} {u : F} {N : Set E} (hb : Prop)
    (hu0 : u ≠ 0) (hNopen : IsOpen N) (hxN : x ∈ N) (hgx : g x = 0)
    (hPL : IsPLHomeomorphOn g (N ∩ Y) (g '' (N ∩ Y))) (himgopen : IsOpen (g '' (N ∩ Y)))
    (hxA : x ∈ A)
    (hgerm : ∀ z ∈ N, (z ∈ A ↔ z ∈ Y ∧ ∃ t : ℝ, (hb → 0 ≤ t) ∧ g z = t • u)) :
    ∃ (H : Geometry.SimplicialComplex ℝ E) (N' : Set E),
      H.faces.Finite ∧ IsPLBall 1 H.space ∧ ({x} : Finset E) ∈ H.faces ∧
        IsOpen N' ∧ x ∈ N' ∧ N' ⊆ N ∧ (∀ z ∈ N', (z ∈ A ↔ z ∈ H.space)) ∧
          ((boundaryComplex 1 H).space).Finite ∧
            (x ∈ (boundaryComplex 1 H).space ↔ hb) := by
  have hxY : x ∈ Y := ((hgerm x hxN).mp hxA).1
  have hxP : x ∈ N ∩ Y := ⟨hxN, hxY⟩
  have h0img : (0 : F) ∈ g '' (N ∩ Y) := by
    rw [← hgx]
    exact ⟨x, hxP, rfl⟩
  obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp himgopen 0 h0img
  have hcont : ContinuousOn g (N ∩ Y) := hPL.isPiecewiseAffineOn.continuousOn
  have hballmem : g ⁻¹' Metric.ball (0 : F) (δ / 2) ∈ 𝓝[N ∩ Y] x := by
    have hcw := hcont x hxP
    rw [ContinuousWithinAt, hgx] at hcw
    exact hcw (Metric.ball_mem_nhds 0 (by linarith))
  obtain ⟨N₁, hN₁open, hxN₁, hN₁sub⟩ := mem_nhdsWithin.mp hballmem
  have hupos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = δ / (2 * ‖u‖) := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hrdef]
    exact div_pos hδpos (by linarith)
  have hru : r * ‖u‖ = δ / 2 := by
    rw [hrdef]
    field_simp
  obtain ⟨c, hcr, hcle0, hcneg, hczero, hclow⟩ :
      ∃ c : ℝ, c < r ∧ c ≤ 0 ∧ -r ≤ c ∧ (hb ↔ c = 0) ∧
        ∀ t : ℝ, (hb → 0 ≤ t) → -r < t → c ≤ t := by
    by_cases hbc : hb
    · exact ⟨0, hrpos, le_refl 0, by linarith, ⟨fun _ => rfl, fun _ => hbc⟩,
        fun t ht _ => ht hbc⟩
    · exact ⟨-r, by linarith, by linarith, le_refl _, ⟨fun h => absurd h hbc,
        fun h => absurd (neg_eq_zero.mp h) hrpos.ne'⟩, fun t _ ht => ht.le⟩
  have hab : c • u ≠ r • u := by
    intro hcu
    have hz : (c - r) • u = 0 := by rw [sub_smul, hcu, sub_self]
    rcases smul_eq_zero.mp hz with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) (ne_of_lt hcr)
    · exact hu0 h1
  have hT : AffineIndependent ℝ ((↑) : (({c • u, r • u} : Finset F)) → F) :=
    affineIndependent_coe_pair hab
  have hTcard : ({c • u, r • u} : Finset F).card = 1 + 1 := by rw [Finset.card_pair hab]
  have hTne : ({c • u, r • u} : Finset F).Nonempty := ⟨c • u, by simp⟩
  have hcoe : ((({c • u, r • u} : Finset F)) : Set F) = ({c • u, r • u} : Set F) := by simp
  have hJball : IsPLBall 1 (convexHull ℝ ({c • u, r • u} : Set F)) := by
    rw [← hcoe]
    exact isPLBall_convexHull_of_affineIndependent _ hT hTcard
  have hJsub : convexHull ℝ ({c • u, r • u} : Set F) ⊆ Metric.ball (0 : F) δ := by
    intro w hw
    obtain ⟨t, hct, htr, rfl⟩ := (mem_convexHull_pair_smul_iff u hcr.le).mp hw
    have habs : |t| ≤ r := abs_le.mpr ⟨by linarith, htr⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖u‖ ≤ r * ‖u‖ := by nlinarith
      _ = δ / 2 := hru
      _ < δ := by linarith
  have hJimg : convexHull ℝ ({c • u, r • u} : Set F) ⊆ g '' (N ∩ Y) := hJsub.trans hδball
  obtain ⟨φ, hφdef⟩ : ∃ f : F → E, f = Function.invFunOn g (N ∩ Y) := ⟨_, rfl⟩
  have hφmapsTo : ∀ w ∈ g '' (N ∩ Y), φ w ∈ N ∩ Y := by
    intro w hw
    rw [hφdef]
    exact hPL.bijOn.surjOn.mapsTo_invFunOn hw
  have hφright : ∀ w ∈ g '' (N ∩ Y), g (φ w) = w := by
    intro w hw
    rw [hφdef]
    exact hPL.bijOn.invOn_invFunOn.2 hw
  have hφleft : ∀ z ∈ N ∩ Y, φ (g z) = z := by
    intro z hz
    rw [hφdef]
    exact hPL.bijOn.invOn_invFunOn.1 hz
  have hφPL : IsPLHomeomorphOn φ (convexHull ℝ ({c • u, r • u} : Set F))
      (φ '' convexHull ℝ ({c • u, r • u} : Set F)) := by
    rw [hφdef]
    exact hPL.symm.restrict hJball.isPolyhedron hJimg
  have hSball : IsPLBall 1 (φ '' convexHull ℝ ({c • u, r • u} : Set F)) :=
    hJball.of_isPLHomeomorphOn hφPL
  have hφ0 : φ 0 = x := by
    rw [← hgx]
    exact hφleft x hxP
  have h0J : (0 : F) ∈ convexHull ℝ ({c • u, r • u} : Set F) :=
    (mem_convexHull_pair_smul_iff u hcr.le).mpr
      ⟨0, hcle0, hrpos.le, (zero_smul ℝ u).symm⟩
  have hxS : x ∈ φ '' convexHull ℝ ({c • u, r • u} : Set F) := ⟨0, h0J, hφ0⟩
  obtain ⟨H₀, hH₀fin, hH₀space⟩ := hSball.isPolyhedron.exists_simplicialComplex
  let _ : Finite H₀.faces := hH₀fin.to_subtype
  have hH₀ball : IsPLBall 1 H₀.space := by
    rw [hH₀space]
    exact hSball
  have hH₀man : IsCombinatorialManifoldWithBoundary 1 H₀ :=
    IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) hH₀ball
  obtain ⟨H, hsub, hHfin, hxH⟩ := exists_isSubdivision_singleton_mem H₀
    (show x ∈ H₀.space by rw [hH₀space]; exact hxS)
  let _ : Finite H.faces := hHfin.to_subtype
  have hHspace : H.space = φ '' convexHull ℝ ({c • u, r • u} : Set F) := by
    rw [hsub.space_eq, hH₀space]
  have hHball : IsPLBall 1 H.space := by
    rw [hHspace]
    exact hSball
  let _ : Finite (simplexComplex ({c • u, r • u} : Finset F) hT).faces :=
    (simplexComplex_faces_finite _ hT).to_subtype
  have hKsegspace : (simplexComplex ({c • u, r • u} : Finset F) hT).space
      = convexHull ℝ ({c • u, r • u} : Set F) := by
    rw [simplexComplex_space _ hT hTne, hcoe]
  have hKsegball : IsPLBall 1 (simplexComplex ({c • u, r • u} : Finset F) hT).space := by
    rw [hKsegspace]
    exact hJball
  have hφPL' : IsPLHomeomorphOn φ (simplexComplex ({c • u, r • u} : Finset F) hT).space
      H₀.space := by
    rw [hKsegspace, hH₀space]
    exact hφPL
  have hbd₀ : (boundaryComplex 1 H₀).space
      = φ '' (boundaryComplex 1 (simplexComplex ({c • u, r • u} : Finset F) hT)).space :=
    boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall (n := 0) _ H₀ hKsegball hφPL'
  have hbdseg : (boundaryComplex 1 (simplexComplex ({c • u, r • u} : Finset F) hT)).space
      = ({c • u, r • u} : Set F) := by
    have hcomplex : boundaryComplex 1 (simplexComplex ({c • u, r • u} : Finset F) hT)
        = simplexBoundary ({c • u, r • u} : Finset F) hT :=
      boundaryComplex_simplexComplex (n := 0) hT (by rw [Finset.card_pair hab])
    rw [hcomplex, simplexBoundary_pair_space hab]
  have hbdsubdiv : (boundaryComplex 1 H).space = (boundaryComplex 1 H₀).space :=
    boundaryComplex_space_of_isSubdivision (n := 0) H₀ H hH₀man hsub
  have hbdH : (boundaryComplex 1 H).space = φ '' ({c • u, r • u} : Set F) := by
    rw [hbdsubdiv, hbd₀, hbdseg]
  have hinjJ : InjOn φ (convexHull ℝ ({c • u, r • u} : Set F)) := hφPL.bijOn.injOn
  have haJ : c • u ∈ convexHull ℝ ({c • u, r • u} : Set F) :=
    subset_convexHull ℝ _ (by simp)
  have hbJ : r • u ∈ convexHull ℝ ({c • u, r • u} : Set F) :=
    subset_convexHull ℝ _ (by simp)
  refine ⟨H, N ∩ N₁, hHfin, hHball, hxH, hNopen.inter hN₁open, ⟨hxN, hxN₁⟩,
    inter_subset_left, ?_, ?_, ?_⟩
  · intro z hz
    rw [hHspace]
    constructor
    · intro hzA
      obtain ⟨hzY, t, htb, hgz⟩ := (hgerm z hz.1).mp hzA
      have hzP : z ∈ N ∩ Y := ⟨hz.1, hzY⟩
      have hball : g z ∈ Metric.ball (0 : F) (δ / 2) := hN₁sub ⟨hz.2, hzP⟩
      rw [hgz, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs] at hball
      have habs : |t| < r := by
        have h1 : |t| * ‖u‖ < r * ‖u‖ := by
          rw [hru]
          exact hball
        exact lt_of_mul_lt_mul_right h1 hupos.le
      refine ⟨g z, (mem_convexHull_pair_smul_iff u hcr.le).mpr
        ⟨t, hclow t htb (neg_lt_of_abs_lt habs), (lt_of_abs_lt habs).le, hgz⟩, hφleft z hzP⟩
    · rintro ⟨w, hwJ, rfl⟩
      have hwimg : w ∈ g '' (N ∩ Y) := hJimg hwJ
      obtain ⟨t, hct, htr, hwt⟩ := (mem_convexHull_pair_smul_iff u hcr.le).mp hwJ
      refine (hgerm (φ w) hz.1).mpr ⟨(hφmapsTo w hwimg).2, t, fun hbb => ?_, ?_⟩
      · rw [hczero.mp hbb] at hct
        exact hct
      · rw [hφright w hwimg, hwt]
  · rw [hbdH]
    exact (Set.toFinite _).image φ
  · rw [hbdH, hczero]
    constructor
    · rintro ⟨w, hw, hwx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      have hwJ : w ∈ convexHull ℝ ({c • u, r • u} : Set F) := by
        rcases hw with rfl | rfl
        · exact haJ
        · exact hbJ
      have hw0 : w = 0 := by
        refine hinjJ hwJ h0J ?_
        rw [hwx, hφ0]
      rcases hw with rfl | rfl
      · rcases smul_eq_zero.mp hw0 with h1 | h1
        · exact h1
        · exact absurd h1 hu0
      · exfalso
        rcases smul_eq_zero.mp hw0 with h1 | h1
        · exact hrpos.ne' h1
        · exact hu0 h1
    · intro hc0
      refine ⟨c • u, by simp, ?_⟩
      rw [hc0, zero_smul, hφ0]
open Classical in
theorem mem_boundaryComplex_one_space_iff_of_eventually_eq
    (G H : Geometry.SimplicialComplex ℝ E) [Finite G.faces] [Finite H.faces]
    (hGcard : ∀ s ∈ G.faces, s.card ≤ 2) (hHman : IsCombinatorialManifoldWithBoundary 1 H)
    {x : E} (hxG : ({x} : Finset E) ∈ G.faces) (hxH : ({x} : Finset E) ∈ H.faces)
    (heq : ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ H.space) :
    x ∈ (boundaryComplex 1 G).space ↔ x ∈ (boundaryComplex 1 H).space := by
  have hHcard : ∀ s ∈ H.faces, s.card ≤ 2 := fun s hs => hHman.card_le H hs
  obtain ⟨f, hf⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_eventually_eq_of_card_le_two G H hGcard hxG hxH heq
  rw [mem_boundaryComplex_one_space_iff G hGcard, mem_boundaryComplex_one_space_iff H hHcard]
  constructor
  · rintro ⟨-, hsingle⟩
    refine ⟨hxH, ?_⟩
    rw [← isPLBall_zero_iff] at hsingle ⊢
    rw [← geometricLink_space_eq_neighbors_of_card_le H hHcard x]
    rw [← geometricLink_space_eq_neighbors_of_card_le G hGcard x] at hsingle
    exact hsingle.of_isPLHomeomorphOn hf
  · rintro ⟨-, hsingle⟩
    refine ⟨hxG, ?_⟩
    rw [← isPLBall_zero_iff] at hsingle ⊢
    rw [← geometricLink_space_eq_neighbors_of_card_le G hGcard x]
    rw [← geometricLink_space_eq_neighbors_of_card_le H hHcard x] at hsingle
    exact hsingle.of_isPLHomeomorphOn hf.symm
open Classical in
theorem finite_inter_of_local_arc_models {A Bd : Set E} (hA : IsCompact A)
    (hmodel : ∀ x ∈ A, ∃ (H : Geometry.SimplicialComplex ℝ E) (N : Set E),
      H.faces.Finite ∧ IsPLBall 1 H.space ∧ ({x} : Finset E) ∈ H.faces ∧
        IsOpen N ∧ x ∈ N ∧ (∀ z ∈ N, (z ∈ A ↔ z ∈ H.space)) ∧
          ((boundaryComplex 1 H).space).Finite ∧
            (x ∈ (boundaryComplex 1 H).space ↔ x ∈ Bd)) :
    (A ∩ Bd).Finite := by
  choose! H N hHfin hHball hxH hNopen hxN hgerm hbdfin hbdiff using hmodel
  have hloc : ∀ x ∈ A, N x ∩ (A ∩ Bd) ⊆ insert x ((boundaryComplex 1 (H x)).space) := by
    intro x hx z hz
    by_cases hzx : z = x
    · exact Set.mem_insert_iff.mpr (Or.inl hzx)
    refine Set.mem_insert_iff.mpr (Or.inr ?_)
    have hzA : z ∈ A := hz.2.1
    have hzHx : z ∈ (H x).space := (hgerm x hx z hz.1).mp hzA
    let _ : Finite (H x).faces := (hHfin x hx).to_subtype
    let _ : Finite (H z).faces := (hHfin z hzA).to_subtype
    have hHxman : IsCombinatorialManifoldWithBoundary 1 (H x) :=
      IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) (hHball x hx)
    have hHzman : IsCombinatorialManifoldWithBoundary 1 (H z) :=
      IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) (hHball z hzA)
    obtain ⟨H', hsub', hfin', hzH'⟩ := exists_isSubdivision_singleton_mem (H x) hzHx
    let _ : Finite H'.faces := hfin'.to_subtype
    have hH'space : H'.space = (H x).space := hsub'.space_eq
    have hH'man : IsCombinatorialManifoldWithBoundary 1 H' :=
      IsPLBall.isCombinatorialManifoldWithBoundary (n := 0)
        (show IsPLBall 1 H'.space by rw [hH'space]; exact hHball x hx)
    have hH'card : ∀ s ∈ H'.faces, s.card ≤ 2 := fun s hs => hH'man.card_le H' hs
    have hev : ∀ᶠ w in 𝓝 z, (w ∈ H'.space ↔ w ∈ (H z).space) := by
      filter_upwards [((hNopen x hx).inter (hNopen z hzA)).mem_nhds ⟨hz.1, hxN z hzA⟩] with w hw
      rw [hH'space, ← hgerm x hx w hw.1, hgerm z hzA w hw.2]
    have hzbdz : z ∈ (boundaryComplex 1 (H z)).space := (hbdiff z hzA).mpr hz.2.2
    have hzbd' : z ∈ (boundaryComplex 1 H').space :=
      (mem_boundaryComplex_one_space_iff_of_eventually_eq H' (H z) hH'card hHzman hzH'
        (hxH z hzA) hev).mpr hzbdz
    have hbdeq : (boundaryComplex 1 H').space = (boundaryComplex 1 (H x)).space :=
      boundaryComplex_space_of_isSubdivision (n := 0) (H x) H' hHxman hsub'
    rw [hbdeq] at hzbd'
    exact hzbd'
  obtain ⟨t, hts, htcover⟩ :=
    hA.elim_nhds_subcover N fun x hx => (hNopen x hx).mem_nhds (hxN x hx)
  have hsubset : A ∩ Bd ⊆ ⋃ x ∈ t, insert x ((boundaryComplex 1 (H x)).space) := by
    intro z hz
    obtain ⟨x, hxt, hzN⟩ := mem_iUnion₂.mp (htcover hz.1)
    exact mem_iUnion₂.mpr ⟨x, hxt, hloc x (hts x hxt) ⟨hzN, hz⟩⟩
  exact Set.Finite.subset
    (t.finite_toSet.biUnion fun x hx => (hbdfin x (hts x hx)).insert x) hsubset
end Model
section Cell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
open Classical in
theorem SingularTwoCell.exists_local_arc_model_image_doublePointSet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space),
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      ∀ x ∈ Subtype.val '' doublePointSet D D.domain,
        ∃ (H : Geometry.SimplicialComplex ℝ E) (N : Set E),
          H.faces.Finite ∧ IsPLBall 1 H.space ∧ ({x} : Finset E) ∈ H.faces ∧
            IsOpen N ∧ x ∈ N ∧
              (∀ z ∈ N, (z ∈ Subtype.val '' doublePointSet D D.domain ↔ z ∈ H.space)) ∧
                ((boundaryComplex 1 H).space).Finite ∧
                  (x ∈ (boundaryComplex 1 H).space ↔ x ∈ Subtype.val '' BdM) := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM himage hcross x hx
  obtain ⟨g, u, N₀, hu0, hNopen, hxN, hgx, hPLg, hopenimg, hgerm⟩ :=
    SingularTwoCell.exists_ambient_ray_germ_doublePointSet K hK D BdM himage hcross x hx
  obtain ⟨H, N, hHfin, hHball, hxH, hNopen', hxN', -, hgermH, hbdfin, hbdiff⟩ :=
    exists_isPLBall_one_local_model_of_ray_germ (x ∈ Subtype.val '' BdM) hu0 hNopen hxN hgx
      hPLg hopenimg hx hgerm
  exact ⟨H, N, hHfin, hHball, hxH, hNopen', hxN', hgermH, hbdfin, hbdiff⟩
open Classical in
theorem SingularTwoCell.finite_image_doublePointSet_inter_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space),
      (∀ x ∈ D.domain, ∃ V ∈ 𝓝[D.domain] x, Set.InjOn D V) →
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      (Subtype.val '' doublePointSet D D.domain ∩ Subtype.val '' BdM).Finite := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM hloc himage hcross
  have hcompact : IsCompact (Subtype.val '' doublePointSet D D.domain) :=
    (SingularTwoCell.isCompact_doublePointSet D hloc).image continuous_subtype_val
  exact finite_inter_of_local_arc_models hcompact
    (SingularTwoCell.exists_local_arc_model_image_doublePointSet K hK D BdM himage hcross)
end Cell
end DifferentialGeometry.Topology.PiecewiseLinear
