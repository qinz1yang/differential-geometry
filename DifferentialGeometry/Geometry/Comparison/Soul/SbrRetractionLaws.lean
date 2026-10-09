import DifferentialGeometry.Geometry.Comparison.Soul.SbrRetraction
import DifferentialGeometry.Topology.Homotopy.DeformationRetract

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
  (hconc : ∀ (p : M) (v : TangentSpace I p),
    ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
  (hC : IsCompact {z : M | 0 ≤ F z}) {m : ℝ}
  (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)

local notation "R" => sharafutdinovLevelMap g hEnorm F L hF hconc hC hmax

theorem continuousOn_sharafutdinovLevelMap :
    ContinuousOn (fun z : M × ℝ => R z.2 z.1)
      ({z : M | 0 ≤ F z} ×ˢ Icc 0 m) := by
  intro p hp
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have horbit := sharafutdinovLevelMap_continuousOn_orbit
    g hEnorm F L hF hconc hC hmax hp.1 p.2 hp.2
  obtain ⟨δ, hδ, hδcontrol⟩ :=
    Metric.continuousWithinAt_iff.mp horbit (ε / 2) hhalf
  refine ⟨min δ (ε / 2), lt_min hδ hhalf, ?_⟩
  intro z hz hzp
  have hpdist := (show max (dist z.1 p.1) (dist z.2 p.2) < min δ (ε / 2) by
    simpa only [Prod.dist_eq] using hzp)
  have hpoint : dist z.1 p.1 < ε / 2 :=
    (le_max_left _ _).trans_lt (hpdist.trans_le (min_le_right _ _))
  have htime : dist z.2 p.2 < δ :=
    (le_max_right _ _).trans_lt (hpdist.trans_le (min_le_left _ _))
  have hlip := (sharafutdinovLevelMap_lipschitzOnWith
    g hEnorm F L hF hconc hC hmax hz.2).dist_le_mul z.1 hz.1 p.1 hp.1
  have hspace : dist (R z.2 z.1) (R z.2 p.1) ≤ dist z.1 p.1 := by
    simpa only [NNReal.coe_one, one_mul] using hlip
  have htime' := hδcontrol hz.2 htime
  calc
    dist (R z.2 z.1) (R p.2 p.1) ≤
        dist (R z.2 z.1) (R z.2 p.1) + dist (R z.2 p.1) (R p.2 p.1) :=
      dist_triangle _ _ _
    _ ≤ dist z.1 p.1 + dist (R z.2 p.1) (R p.2 p.1) :=
      add_le_add hspace le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hpoint htime'
    _ = ε := add_halves ε

private theorem sharafutdinovLevelMap_ordered_comp
    {s t : ℝ} (hs : s ∈ Icc 0 m) (ht : t ∈ Icc 0 m) (hst : s ≤ t)
    {x : M} (hx : 0 ≤ F x) :
    R s (R t x) = R t x ∧ R t (R s x) = R t x := by
  constructor
  · apply sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax
    rw [sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax ht hx]
    exact hst.trans (le_max_right _ _)
  · by_cases hxs : s ≤ F x
    · rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x hxs]
    have hxs' : F x < s := lt_of_not_ge hxs
    let y := R s x
    have hy : F y = s := by
      rw [show F y = F (R s x) from rfl,
        sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hs hx,
        max_eq_right hxs'.le]
    have hy0 : 0 ≤ F y := by simpa only [hy] using hs.1
    have hsub : Icc s m ⊆ Icc 0 m := fun _ hu => ⟨hs.1.trans hu.1, hu.2⟩
    have heq := eqOn_normalized_intrinsicGeneralizedGradient_curves
      g hEnorm hF hconc (fun u => R u y) (fun u => R u x)
      ((sharafutdinovLevelMap_continuousOn_orbit
        g hEnorm F L hF hconc hC hmax hy0).mono hsub)
      ((sharafutdinovLevelMap_continuousOn_orbit
        g hEnorm F L hF hconc hC hmax hx).mono hsub)
      (fun u hu => (sharafutdinovLevelMap_hasMFDerivWithinAt_orbit
        g hEnorm F L hF hconc hC hmax hy0 (by simpa only [hy] using hu.1) hu.2).2)
      (fun u hu => (sharafutdinovLevelMap_hasMFDerivWithinAt_orbit
        g hEnorm F L hF hconc hC hmax hx (hxs'.le.trans hu.1) hu.2).2)
      (by
        intro u hu
        have hu' : u ∈ Icc 0 m := ⟨hs.1.trans hu.1, hu.2.le⟩
        rw [sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hu' hy0,
          sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hu' hx,
          hy, max_eq_right hu.1, max_eq_right (hxs'.le.trans hu.1)])
      (by
        change R s y = y
        exact sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s y hy.ge)
    exact heq ⟨hst, ht.2⟩

theorem sharafutdinovLevelMap_comp
    {s t : ℝ} (hs : s ∈ Icc 0 m) (ht : t ∈ Icc 0 m)
    {x : M} (hx : 0 ≤ F x) :
    R s (R t x) = R (max s t) x ∧ R t (R s x) = R (max s t) x := by
  rcases le_total s t with hst | hts
  · simpa only [max_eq_right hst] using
      sharafutdinovLevelMap_ordered_comp g hEnorm F L hF hconc hC hmax hs ht hst hx
  · simpa only [max_eq_left hts] using
      (sharafutdinovLevelMap_ordered_comp g hEnorm F L hF hconc hC hmax ht hs hts hx).symm

def sharafutdinovStrongDeformationRetract {s : ℝ} (hs : s ∈ Icc 0 m) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      {x : {z : M // 0 ≤ F z} | s ≤ F x.1} := by
  let X := {z : M // 0 ≤ F z}
  let A : Set X := {x | s ≤ F x.1}
  have hlevel : ∀ x : X, s ≤ F (R s x.1) := by
    intro x
    rw [sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hs x.2]
    exact le_max_right _ _
  have hmaps := sharafutdinovLevelMap_mapsTo g hEnorm F L hF hconc hC hmax hs
  let r : C(X, A) := ⟨fun x => ⟨⟨R s x.1, hmaps x.2⟩, hlevel x⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (sharafutdinovLevelMap_lipschitzOnWith
      g hEnorm F L hF hconc hC hmax hs).continuousOn.domRestrict⟩
  have htlevel : ∀ t : unitInterval, (t : ℝ) * s ∈ Icc 0 m := by
    intro t
    refine ⟨mul_nonneg t.2.1 hs.1, ?_⟩
    exact (show (t : ℝ) * s ≤ s by nlinarith [t.2.2, hs.1]).trans hs.2
  let Hmap : C(unitInterval × X, X) := ⟨fun p =>
    ⟨R ((p.1 : ℝ) * s) p.2.1,
      sharafutdinovLevelMap_mapsTo g hEnorm F L hF hconc hC hmax
        (htlevel p.1) p.2.2⟩, by
    apply Continuous.subtype_mk
    have hpair : Continuous (fun p : unitInterval × X => (p.2.1, (p.1 : ℝ) * s)) := by
      dsimp only [X]
      fun_prop
    exact (continuousOn_sharafutdinovLevelMap g hEnorm F L hF hconc hC hmax).comp_continuous
      hpair (fun p => ⟨p.2.2, htlevel p.1⟩)⟩
  refine ⟨r, ⟨⟨Hmap, ?_, ?_⟩, ?_⟩⟩
  · intro x
    apply Subtype.ext
    change R ((0 : ℝ) * s) x.1 = x.1
    rw [zero_mul]
    exact sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax 0 x.1 x.2
  · intro x
    apply Subtype.ext
    change R ((1 : ℝ) * s) x.1 = R s x.1
    rw [one_mul]
  · intro t x hx
    apply Subtype.ext
    change R ((t : ℝ) * s) x.1 = x.1
    apply sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax
    exact (show (t : ℝ) * s ≤ s by nlinarith [t.2.2, hs.1]).trans hx


theorem sharafutdinovStrongDeformationRetract_retraction_apply
    {s : ℝ} (hs : s ∈ Icc 0 m) (x : {z : M // 0 ≤ F z}) :
    (((sharafutdinovStrongDeformationRetract
      g hEnorm F L hF hconc hC hmax hs).retraction x).1).1 = R s x.1 := rfl


theorem sharafutdinovStrongDeformationRetract_homotopy_apply
    {s : ℝ} (hs : s ∈ Icc 0 m) (t : unitInterval) (x : {z : M // 0 ≤ F z}) :
    ((sharafutdinovStrongDeformationRetract
      g hEnorm F L hF hconc hC hmax hs).homotopy (t, x)).1 = R ((t : ℝ) * s) x.1 := rfl

end DifferentialGeometry.Geometry.Topology

end
