import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrants

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34CornerBase (a b : Bool) : Set (ℝ × ℝ) :=
  ((if a then Icc (0 : ℝ) (1 / 2) else Icc (-1 / 2 : ℝ) 0) ×ˢ {0}) ∪
    ({0} ×ˢ (if b then Icc (0 : ℝ) (1 / 2) else Icc (-1 / 2 : ℝ) 0))

noncomputable def section34CornerPush (a b : Bool) (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (z.1.1 + (if a then z.2 / 2 else -z.2 / 2),
    z.1.2 + (if b then z.2 / 2 else -z.2 / 2))

theorem section34_corner_base_isPolyhedron (a b : Bool) :
    IsPolyhedron (section34CornerBase a b) := by
  cases a <;> cases b <;>
    exact (isHPolytope_Icc.isPolyhedron.prod (isHPolytope_singleton _).isPolyhedron).union
      ((isHPolytope_singleton _).isPolyhedron.prod isHPolytope_Icc.isPolyhedron)

theorem section34_corner_base_subset (a b : Bool) :
    section34CornerBase a b ⊆ section34CrossingQuadrant a b := by
  cases a <;> cases b <;> rintro ⟨x, y⟩ (⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc, mem_singleton_iff] at * <;>
    rcases (by assumption : _ ∧ _) with ⟨h₀, h₁⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem section34_corner_push_zero (a b : Bool) (p : ℝ × ℝ) :
    section34CornerPush a b (p, 0) = p := by simp [section34CornerPush]

theorem section34_corner_push_injOn (a b : Bool) :
    InjOn (section34CornerPush a b) (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1) := by
  intro z hz w hw hzw
  have hx := congrArg Prod.fst hzw
  have hy := congrArg Prod.snd hzw
  cases a <;> cases b <;>
    rcases hz with ⟨⟨hzx, hzy⟩ | ⟨hzx, hzy⟩, hzt⟩ <;>
    rcases hw with ⟨⟨hwx, hwy⟩ | ⟨hwx, hwy⟩, hwt⟩ <;>
    simp only [section34CornerPush, Bool.false_eq_true, ↓reduceIte] at hx hy <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc, mem_singleton_iff] at * <;>
    apply Prod.ext <;> first
    | apply Prod.ext <;> linarith
    | linarith

theorem section34_corner_push_mapsTo (a b : Bool) :
    MapsTo (section34CornerPush a b) (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1)
      (section34CrossingQuadrant a b) := by
  cases a <;> cases b <;>
    rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩ | ⟨hx, hy⟩, ht⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc, mem_singleton_iff] at * <;>
    exact ⟨⟨by dsimp [section34CornerPush]; linarith,
      by dsimp [section34CornerPush]; linarith⟩,
      by dsimp [section34CornerPush]; linarith,
      by dsimp [section34CornerPush]; linarith⟩

theorem section34_corner_push_sheet_contacts (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((section34CornerPush a b (p, t)).1 = 0 ↔ p.1 = 0 ∧ t = 0) ∧
      ((section34CornerPush a b (p, t)).2 = 0 ↔ p.2 = 0 ∧ t = 0) := by
  cases a <;> cases b <;> rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc, mem_singleton_iff] at * <;>
    constructor <;> constructor
  all_goals first
    | intro h; constructor <;> dsimp [section34CornerPush] at h <;> linarith
    | rintro ⟨h, rfl⟩; simpa only [section34_corner_push_zero] using h

theorem section34_corner_push_isPLHomeomorphOn (a b : Bool) :
    IsPLHomeomorphOn (section34CornerPush a b)
      (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1)
      (section34CornerPush a b '' (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1)) := by
  let L : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := section34CornerPush a b
      map_add' := by
        intro z w
        cases a <;> cases b <;> ext <;> simp [section34CornerPush] <;> ring
      map_smul' := by
        intro c z
        cases a <;> cases b <;> ext <;> simp [section34CornerPush] <;> ring }
  have hP : IsPolyhedron (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1) :=
    (section34_corner_base_isPolyhedron a b).prod isHPolytope_Icc.isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine L.toAffineMap isOpen_univ).mono_of_isPolyhedron hP
      (subset_univ _)) (section34_corner_push_injOn a b).bijOn_image

end DifferentialGeometry.Topology.PiecewiseLinear
