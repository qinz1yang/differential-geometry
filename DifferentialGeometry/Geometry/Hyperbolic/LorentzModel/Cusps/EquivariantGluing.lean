/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.MatchedTruncations
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Extension

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.TranslatedCusps

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful Busemann HorosphereProjection
open BoundaryStabilizer OrbifoldThinRegions CuspCrossSections CuspTruncation MatchedCusps

variable {n : ℕ} {hn : 1 ≤ n} {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {r : ℝ}

abbrev Piece (D : FiniteCuspTruncation hn Γ r) := D.centers × Γ

def pieceCenter (D : FiniteCuspTruncation hn Γ r) (a : Piece D) : BoundaryH n :=
  (poBoundaryMulAction hn).smul (a.2 : PO n 1) a.1.val

def pieceSet (D : FiniteCuspTruncation hn Γ r) (a : Piece D) : Set (HUpper n) :=
  (fun x : HUpper n => (poMulAction hn).smul (a.2 : PO n 1) x) ''
    horoball a.1.val (D.level a.1)

def cuspSet (D : FiniteCuspTruncation hn Γ r) : Set (HUpper n) :=
  ⋃ a : Piece D, pieceSet D a

theorem mem_pieceSet_iff (D : FiniteCuspTruncation hn Γ r) (a : Piece D) (x : HUpper n) :
    x ∈ pieceSet D a ↔
      (poMulAction hn).smul (a.2 : PO n 1)⁻¹ x ∈ horoball a.1.val (D.level a.1) := by
  let := poMulAction hn
  change (∃ y ∈ horoball a.1.val (D.level a.1), (a.2 : PO n 1) • y = x) ↔
    (a.2 : PO n 1)⁻¹ • x ∈ horoball a.1.val (D.level a.1)
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul] using hy
  · intro hx
    exact ⟨(a.2 : PO n 1)⁻¹ • x, hx, smul_inv_smul _ _⟩

theorem isClosed_pieceSet (D : FiniteCuspTruncation hn Γ r) (a : Piece D) :
    IsClosed (pieceSet D a) :=
  (interiorHomeomorph hn a.2).isClosedMap _ (isClosed_le (continuous_busemann a.1.val) continuous_const)

theorem pieceSet_subset_thinRegion (D : FiniteCuspTruncation hn Γ r) (a : Piece D) :
    pieceSet D a ⊆ thinRegion hn Γ r {pieceCenter D a} := by
  rintro x ⟨y, hy, rfl⟩
  have he := smul_mem_thinRegion hn Γ r (interior_subset (D.horoball_inside a.1 hy)) a.2
  simpa only [image_singleton, pieceCenter] using he

theorem pieceSet_eq_of_center_eq (D : FiniteCuspTruncation hn Γ r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (a b : Piece D)
    (hc : pieceCenter D a = pieceCenter D b) : pieceSet D a = pieceSet D b := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  rcases a with ⟨i, γ⟩
  rcases b with ⟨j, δ⟩
  have hcenter : ((δ⁻¹ * γ : Γ) : PO n 1) • i.val = j.val := by
    have he := congrArg (fun ξ : BoundaryH n => (δ : PO n 1)⁻¹ • ξ) hc
    change (δ : PO n 1)⁻¹ • ((γ : PO n 1) • i.val) =
      (δ : PO n 1)⁻¹ • ((δ : PO n 1) • j.val) at he
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul] using he
  have hij : i = j := D.distinct_orbits i j (δ⁻¹ * γ) hcenter
  subst j
  have hpres := (D.precisely_invariant hΓ i (δ⁻¹ * γ)).1 hcenter
  have hpres' : (fun x : HUpper n => ((δ : PO n 1)⁻¹ * (γ : PO n 1)) • x) ''
      horoball i.val (D.level i) = horoball i.val (D.level i) := hpres
  change (fun x : HUpper n => (γ : PO n 1) • x) '' horoball i.val (D.level i) =
    (fun x : HUpper n => (δ : PO n 1) • x) '' horoball i.val (D.level i)
  calc
    _ = (fun x : HUpper n => (δ : PO n 1) • x) ''
        ((fun x : HUpper n => ((δ : PO n 1)⁻¹ * (γ : PO n 1)) • x) ''
          horoball i.val (D.level i)) := by
      rw [image_image]
      simp only [mul_smul, smul_inv_smul]
    _ = _ := by rw [hpres']

theorem center_eq_of_close (D : FiniteCuspTruncation hn Γ r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {a b : Piece D} {x y : HUpper n} (hx : x ∈ pieceSet D a) (hy : y ∈ pieceSet D b)
    (hd : dist x y < (ε - r) / 2) : pieceCenter D a = pieceCenter D b :=
  singleton_injective (label_eq_of_dist_lt hn Γ hΓ hre hgeom
    (pieceSet_subset_thinRegion D a hx) (pieceSet_subset_thinRegion D b hy) hd)

theorem isClosed_cuspSet (D : FiniteCuspTruncation hn Γ r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    IsClosed (cuspSet D) := by
  apply isClosed_of_closure_subset
  intro x hx
  have hρ : 0 < (ε - r) / 8 := by linarith
  obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.mp hx ((ε - r) / 8) hρ
  obtain ⟨a, hya⟩ := mem_iUnion.mp hy
  have hxa : x ∈ closure (pieceSet D a) := by
    apply Metric.mem_closure_iff.mpr
    intro t ht
    obtain ⟨z, hz, hdz⟩ := Metric.mem_closure_iff.mp hx (min t ((ε - r) / 8))
      (lt_min ht hρ)
    obtain ⟨b, hzb⟩ := mem_iUnion.mp hz
    have hclose : dist y z < (ε - r) / 2 := by
      have hzρ := lt_of_lt_of_le hdz (min_le_right _ _)
      have htri := dist_triangle y x z
      rw [dist_comm y x] at htri
      linarith
    have he := pieceSet_eq_of_center_eq D hΓ a b (center_eq_of_close D hΓ hre hgeom hya hzb hclose)
    exact ⟨z, he.symm ▸ hzb, lt_of_lt_of_le hdz (min_le_left _ _)⟩
  exact mem_iUnion.mpr ⟨a, (isClosed_pieceSet D a).closure_subset hxa⟩

theorem smul_mem_cuspSet (D : FiniteCuspTruncation hn Γ r)
    (δ : Γ) {x : HUpper n} (hx : x ∈ cuspSet D) :
    (poMulAction hn).smul (δ : PO n 1) x ∈ cuspSet D := by
  obtain ⟨⟨i, γ⟩, y, hy, rfl⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨(i, δ * γ), y, hy,
    (poMulAction hn).mul_smul (δ : PO n 1) (γ : PO n 1) y⟩

theorem openCuspSet_subset_interior (D : FiniteCuspTruncation hn Γ r) :
    openCuspSet hn Γ D.centers D.level ⊆ interior (cuspSet D) := by
  have hs : openCuspSet hn Γ D.centers D.level ⊆ cuspSet D := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨γ, y, hy, rfl⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨(i, γ), y,
      show busemann i.val y ≤ D.level i from le_of_lt hy, rfl⟩
  intro x hx
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset
    ((isOpen_openCuspSet hn Γ D.centers D.level).mem_nhds hx) hs)

def pieceMap (T : MatchedTruncation hn Γ Λ f r) (a : Piece T.source)
    (x : HUpper n) : HUpper n :=
  (poMulAction hn).smul (f a.2 : PO n 1)
    ((T.cuspMap a.1).toEquiv ((poMulAction hn).smul (a.2 : PO n 1)⁻¹ x))

theorem continuous_pieceMap (T : MatchedTruncation hn Γ Λ f r) (a : Piece T.source) :
    Continuous (pieceMap T a) :=
  (interiorHomeomorph hn (f a.2 : PO n 1)).continuous.comp
    ((T.cuspMap a.1).uniform_toFun.continuous.comp
      (interiorHomeomorph hn (a.2 : PO n 1)⁻¹).continuous)

def cuspidalMap (T : MatchedTruncation hn Γ Λ f r) (x : HUpper n) : HUpper n := by
  classical
  exact if hx : x ∈ cuspSet T.source then
    pieceMap T (Classical.choose (mem_iUnion.mp hx)) x else basepointH

theorem cuspidalMap_eq_pieceMap (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (a : Piece T.source)
    {x : HUpper n} (hx : x ∈ pieceSet T.source a) : cuspidalMap T x = pieceMap T a x := by
  classical
  let := poMulAction hn
  have hxc : x ∈ cuspSet T.source := mem_iUnion.mpr ⟨a, hx⟩
  let b : Piece T.source := Classical.choose (mem_iUnion.mp hxc)
  have hb : x ∈ pieceSet T.source b := Classical.choose_spec (mem_iUnion.mp hxc)
  change (if hx : x ∈ cuspSet T.source then
    pieceMap T (Classical.choose (mem_iUnion.mp hx)) x else basepointH) = _
  rw [dite_eq_left hxc]
  exact T.compatible_on_overlap hΓ b.1 a.1 b.2 a.2
    ((b.2 : PO n 1)⁻¹ • x) ((a.2 : PO n 1)⁻¹ • x)
    ((mem_pieceSet_iff T.source b x).mp hb) ((mem_pieceSet_iff T.source a x).mp hx)
    (by change (b.2 : PO n 1) • ((b.2 : PO n 1)⁻¹ • x) =
        (a.2 : PO n 1) • ((a.2 : PO n 1)⁻¹ • x)
        simp only [smul_inv_smul])

theorem cuspidalMap_smul (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (δ : Γ) {x : HUpper n} (hx : x ∈ cuspSet T.source) :
    cuspidalMap T ((poMulAction hn).smul (δ : PO n 1) x) =
      (poMulAction hn).smul (f δ : PO n 1) (cuspidalMap T x) := by
  let := poMulAction hn
  obtain ⟨⟨i, γ⟩, y, hy, rfl⟩ := mem_iUnion.mp hx
  have h1 : (γ : PO n 1) • y ∈ pieceSet T.source (i, γ) := ⟨y, hy, rfl⟩
  have h2 : (δ : PO n 1) • ((γ : PO n 1) • y) ∈ pieceSet T.source (i, δ * γ) :=
    ⟨y, hy, (poMulAction hn).mul_smul (δ : PO n 1) (γ : PO n 1) y⟩
  change cuspidalMap T ((δ : PO n 1) • ((γ : PO n 1) • y)) =
    (f δ : PO n 1) • cuspidalMap T ((γ : PO n 1) • y)
  rw [cuspidalMap_eq_pieceMap T hΓ _ h2, cuspidalMap_eq_pieceMap T hΓ _ h1]
  change (f (δ * γ) : PO n 1) •
      (T.cuspMap i).toEquiv (((δ * γ : Γ) : PO n 1)⁻¹ • ((δ : PO n 1) • ((γ : PO n 1) • y))) =
    (f δ : PO n 1) • ((f γ : PO n 1) • (T.cuspMap i).toEquiv ((γ : PO n 1)⁻¹ • ((γ : PO n 1) • y)))
  simp only [map_mul, Subgroup.coe_mul, mul_inv_rev, mul_smul, inv_smul_smul]

theorem continuousOn_cuspidalMap (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ContinuousOn (cuspidalMap T) (cuspSet T.source) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨a, ha⟩ := mem_iUnion.mp x.property
  have hρ : 0 < (ε - r) / 2 := by linarith
  have he : (fun y : cuspSet T.source => cuspidalMap T y.val) =ᶠ[𝓝 x]
      (fun y : cuspSet T.source => pieceMap T a y.val) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (Metric.ball_mem_nhds x.val hρ)] with y hy
    obtain ⟨b, hb⟩ := mem_iUnion.mp y.property
    have hd : dist x.val y.val < (ε - r) / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hy
    have hab := pieceSet_eq_of_center_eq T.source hΓ a b
      (center_eq_of_close T.source hΓ hre hgeom ha hb hd)
    exact cuspidalMap_eq_pieceMap T hΓ a (hab.symm ▸ hb)
  exact ((continuous_pieceMap T a).comp continuous_subtype_val).continuousAt.congr he.symm

theorem exists_continuous_global_map (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ∃ Φ : HUpper n → HUpper n, Continuous Φ ∧
      PseudoIsometry.IsFEquivariant f hn Φ ∧
      ∀ (a : Piece T.source) (x : HUpper n), x ∈ pieceSet T.source a → Φ x = pieceMap T a x := by
  have hcover (x : HUpper n) (hx : x ∉ interior (cuspSet T.source)) :
      ∃ γ : Γ, (poMulAction hn).smul (γ : PO n 1) x ∈ T.source.core := by
    apply T.source.covers_truncated x
    intro h
    exact hx (openCuspSet_subset_interior T.source h)
  obtain ⟨Φ, hc, he, hΦ⟩ :=
    EquivariantExtension.exists_continuous_equivariant_extension hn Γ Λ hΓ f
      (isClosed_cuspSet T.source hΓ hre hgeom) T.source.compact_core
      (fun γ _ hx => smul_mem_cuspSet T.source γ hx) hcover
      (cuspidalMap T) (continuousOn_cuspidalMap T hΓ hre hgeom)
      (fun γ _ hx => cuspidalMap_smul T hΓ γ hx)
  exact ⟨Φ, hc, he, fun a x hx =>
    (hΦ (mem_iUnion.mpr ⟨a, hx⟩)).trans (cuspidalMap_eq_pieceMap T hΓ a hx)⟩

end DifferentialGeometry.TranslatedCusps
