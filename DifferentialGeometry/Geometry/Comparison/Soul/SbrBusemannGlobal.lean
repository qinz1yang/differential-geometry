import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannLevelMap
import DifferentialGeometry.Geometry.Comparison.Soul.SbrRetractionLaws
import DifferentialGeometry.Geometry.Comparison.Soul.SbrRetractionShift

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

private theorem isCompact_busemann_complement_nonnegative
    {X : Type*} [MetricSpace X] (c : ℝ≥0 → X)
    (hproper : IsProperMap (busemann c)) (hbelow : BddBelow (range (busemann c))) (d : ℝ) :
    IsCompact {z : X | 0 ≤ d - busemann c z} := by
  simpa only [sub_nonneg] using isCompact_busemann_sublevel_of_proper c hproper hbelow d

private theorem busemann_complement_maximum_of_proper
    {X : Type*} [MetricSpace X] (c : ℝ≥0 → X)
    (hproper : IsProperMap (busemann c)) (hbelow : BddBelow (range (busemann c))) (d : ℝ) :
    ∃ q : X, d - busemann c q = d - (⨅ z : X, busemann c z) ∧
      ∀ z : X, d - busemann c z ≤ d - (⨅ w : X, busemann c w) := by
  obtain ⟨q, hq, _hmin⟩ := exists_busemann_minimum_of_proper c hproper hbelow
  exact ⟨q, congrArg (fun a : ℝ => d - a) hq,
    fun z => sub_le_sub_left (ciInf_le hbelow z) d⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
    tensor04SectionalNonnegativeCone (I := I) (M := M))
  {c : ℝ≥0 → M} (hc : Isometry c)
  (hproper : IsProperMap (busemann c)) (hbelow : BddBelow (range (busemann c)))

def busemannSharafutdinovMap (d a : ℝ) : M → M :=
  sharafutdinovLevelMap g hEnorm (fun z => d - busemann c z) 1
    (lipschitzWith_busemann_complement hc d)
    (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
    (isCompact_busemann_complement_nonnegative c hproper hbelow d)
    (busemann_complement_maximum_of_proper c hproper hbelow d) (d - a)

local notation "B" => busemannSharafutdinovMap g hEnorm hsec hc hproper hbelow
local notation "bmin" => (⨅ z : M, busemann c z)


theorem busemannSharafutdinovMap_of_le (d a : ℝ) (x : M) (hx : busemann c x ≤ a) :
    B d a x = x := by
  exact sharafutdinovLevelMap_of_le g hEnorm (fun z => d - busemann c z) 1
    (lipschitzWith_busemann_complement hc d)
    (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
    (isCompact_busemann_complement_nonnegative c hproper hbelow d)
    (busemann_complement_maximum_of_proper c hproper hbelow d)
    (d - a) x (sub_le_sub_left hx d)

theorem busemannSharafutdinovMap_level {d a : ℝ} (ha : bmin ≤ a) (had : a ≤ d)
    {x : M} (hx : busemann c x ≤ d) :
    busemann c (B d a x) = min (busemann c x) a := by
  by_cases hxa : busemann c x ≤ a
  · rw [busemannSharafutdinovMap_of_le g hEnorm hsec hc hproper hbelow d a x hxa,
      min_eq_left hxa]
  have hax : a < busemann c x := lt_of_not_ge hxa
  have hlev := sharafutdinovLevelMap_level g hEnorm (fun z => d - busemann c z) 1
    (lipschitzWith_busemann_complement hc d)
    (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
    (isCompact_busemann_complement_nonnegative c hproper hbelow d)
    (busemann_complement_maximum_of_proper c hproper hbelow d)
    ⟨sub_nonneg.mpr had, sub_le_sub_left ha d⟩ (sub_nonneg.mpr hx)
  rw [max_eq_right (sub_le_sub_left hax.le d)] at hlev
  change d - busemann c (B d a x) = d - a at hlev
  rw [min_eq_right hax.le]
  linarith


theorem busemannSharafutdinovMap_lipschitzOnWith
    {d a : ℝ} (ha : bmin ≤ a) (had : a ≤ d) :
    LipschitzOnWith 1 (B d a) {x : M | busemann c x ≤ d} := by
  simpa only [busemannSharafutdinovMap, sub_nonneg] using
    sharafutdinovLevelMap_lipschitzOnWith g hEnorm (fun z => d - busemann c z) 1
      (lipschitzWith_busemann_complement hc d)
      (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
      (isCompact_busemann_complement_nonnegative c hproper hbelow d)
      (busemann_complement_maximum_of_proper c hproper hbelow d)
      ⟨sub_nonneg.mpr had, sub_le_sub_left ha d⟩

theorem busemannSharafutdinovMap_image_level {d a : ℝ} (ha : bmin ≤ a) (had : a ≤ d) :
    B d a '' {x : M | busemann c x = d} = {x : M | busemann c x = a} := by
  rcases eq_or_lt_of_le had with heq | hlt
  · subst a
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [busemannSharafutdinovMap_of_le g hEnorm hsec hc hproper hbelow d d x hx.le]
      exact hx
    · intro hy
      exact ⟨y, hy,
        busemannSharafutdinovMap_of_le g hEnorm hsec hc hproper hbelow d d y hy.le⟩
  · exact sharafutdinovLevelMap_image_busemann_level g hEnorm c hc hlt
      (lipschitzWith_busemann_complement hc d)
      (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
      (isCompact_busemann_complement_nonnegative c hproper hbelow d)
      (sub_le_sub_left ha d) (busemann_complement_maximum_of_proper c hproper hbelow d)

theorem busemannSharafutdinovMap_outer_independent {a d e : ℝ}
    (ha : bmin ≤ a) (had : a ≤ d) (hde : d ≤ e)
    {x : M} (hx : busemann c x ≤ d) : B e a x = B d a x := by
  let F := fun z : M => d - busemann c z
  let k := e - d
  have hfun : (fun z => F z + k) = (fun z : M => e - busemann c z) := by
    funext z
    dsimp only [F, k]
    ring
  have hmaximum : d - bmin + k = e - bmin := by dsimp only [k]; ring
  have hlevel : d - a + k = e - a := by dsimp only [k]; ring
  have hval (z : M) : F z + k = e - busemann c z := congrFun hfun z
  have hCk : IsCompact {z : M | 0 ≤ F z + k} := by
    simpa only [hval] using isCompact_busemann_complement_nonnegative c hproper hbelow e
  have hmaxk : ∃ q : M, F q + k = d - bmin + k ∧
      ∀ z : M, F z + k ≤ d - bmin + k := by
    obtain ⟨q, hq, hbound⟩ := busemann_complement_maximum_of_proper c hproper hbelow d
    exact ⟨q, congrArg (fun t : ℝ => t + k) hq, fun z => add_le_add (hbound z) le_rfl⟩
  have hshift := sharafutdinovLevelMap_add_const g hEnorm F 1
    (lipschitzWith_busemann_complement hc d)
    (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
    (isCompact_busemann_complement_nonnegative c hproper hbelow d)
    (busemann_complement_maximum_of_proper c hproper hbelow d)
    k (sub_nonneg.mpr hde) hCk hmaxk
    ⟨sub_nonneg.mpr had, sub_le_sub_left ha d⟩ (sub_nonneg.mpr hx)
  simpa only [hfun, hmaximum, hlevel, F, busemannSharafutdinovMap] using hshift

theorem busemannSharafutdinovMap_comp {a b d : ℝ}
    (ha : bmin ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    {x : M} (hx : busemann c x ≤ d) : B b a (B d b x) = B d a x := by
  have hy : busemann c (B d b x) ≤ b := by
    rw [busemannSharafutdinovMap_level g hEnorm hsec hc hproper hbelow (ha.trans hab) hbd hx]
    exact min_le_right _ _
  rw [← busemannSharafutdinovMap_outer_independent
    g hEnorm hsec hc hproper hbelow ha hab hbd hy]
  have hcomp := (sharafutdinovLevelMap_comp g hEnorm (fun z => d - busemann c z) 1
    (lipschitzWith_busemann_complement hc d)
    (concaveOn_busemann_complement_intrinsicGeodesic g hEnorm hsec hc d)
    (isCompact_busemann_complement_nonnegative c hproper hbelow d)
    (busemann_complement_maximum_of_proper c hproper hbelow d)
    ⟨sub_nonneg.mpr (hab.trans hbd), sub_le_sub_left ha d⟩
    ⟨sub_nonneg.mpr hbd, sub_le_sub_left (ha.trans hab) d⟩ (sub_nonneg.mpr hx)).1
  simpa only [max_eq_left (sub_le_sub_left hab d), busemannSharafutdinovMap] using hcomp

def busemannLevelMap {a d : ℝ} (ha : bmin ≤ a) (had : a ≤ d) :
    {x : M // busemann c x = d} → {x : M // busemann c x = a} :=
  fun x => ⟨B d a x.1, by
    have hlev := busemannSharafutdinovMap_level g hEnorm hsec hc hproper hbelow ha had x.2.le
    simpa only [x.2, min_eq_right had] using hlev⟩


@[simp] theorem busemannLevelMap_coe {a d : ℝ} (ha : bmin ≤ a) (had : a ≤ d)
    (x : {x : M // busemann c x = d}) :
    (busemannLevelMap g hEnorm hsec hc hproper hbelow ha had x).1 = B d a x.1 := rfl


theorem lipschitzWith_busemannLevelMap {a d : ℝ} (ha : bmin ≤ a) (had : a ≤ d) :
    LipschitzWith 1 (busemannLevelMap g hEnorm hsec hc hproper hbelow ha had) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (busemannSharafutdinovMap_lipschitzOnWith
    g hEnorm hsec hc hproper hbelow ha had).dist_le_mul x.1 x.2.le y.1 y.2.le


theorem surjective_busemannLevelMap {a d : ℝ} (ha : bmin ≤ a) (had : a ≤ d) :
    Function.Surjective (busemannLevelMap g hEnorm hsec hc hproper hbelow ha had) := by
  intro y
  have hy : y.1 ∈ B d a '' {x : M | busemann c x = d} := by
    rw [busemannSharafutdinovMap_image_level g hEnorm hsec hc hproper hbelow ha had]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩


@[simp] theorem busemannLevelMap_self {a : ℝ} (ha : bmin ≤ a) :
    busemannLevelMap g hEnorm hsec hc hproper hbelow ha le_rfl = id := by
  funext x
  apply Subtype.ext
  exact busemannSharafutdinovMap_of_le g hEnorm hsec hc hproper hbelow a a x.1 x.2.le


theorem busemannLevelMap_comp {a b d : ℝ}
    (ha : bmin ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    busemannLevelMap g hEnorm hsec hc hproper hbelow ha hab ∘
        busemannLevelMap g hEnorm hsec hc hproper hbelow (ha.trans hab) hbd =
      busemannLevelMap g hEnorm hsec hc hproper hbelow ha (hab.trans hbd) := by
  funext x
  apply Subtype.ext
  exact busemannSharafutdinovMap_comp g hEnorm hsec hc hproper hbelow ha hab hbd x.2.le

end DifferentialGeometry.Geometry.Topology

end
