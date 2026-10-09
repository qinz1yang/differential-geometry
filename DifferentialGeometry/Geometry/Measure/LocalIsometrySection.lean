import DifferentialGeometry.Geometry.Measure.LocalIsometryOn
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Group.FundamentalDomain

noncomputable section

open Set Function MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Measure

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [SigmaCompactSpace X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y]
  [T2Space Y] [SigmaCompactSpace Y]

private local instance : MeasurableSpace X := borel X
private local instance : BorelSpace X := ⟨rfl⟩
private local instance : MeasurableSpace Y := borel Y
private local instance : BorelSpace Y := ⟨rfl⟩

theorem exists_measurable_subset_bijOn_volume_eq_of_local_isometry
    (gX : SmoothRiemannianMetric I X) (gY : SmoothRiemannianMetric J Y)
    (p : X → Y) (hp : IsLocalDiffeomorph I J ∞ p) (V : TopologicalSpace.Opens X)
    (hmetric : ∀ (x : X) (v w : TangentSpace I x),
      gX.inner x v w = gY.inner (p x) (mfderiv I J p x v) (mfderiv I J p x w)) :
    ∃ D : Set X, MeasurableSet D ∧ D ⊆ V ∧ BijOn p D (p '' (V : Set X)) ∧
      riemannianVolumeMeasure I X gX D = riemannianVolumeMeasure J Y gY (p '' (V : Set X)) := by
  classical
  by_cases hX : Nonempty X
  · let _ : Nonempty X := hX
    let Φ (x : X) : PartialDiffeomorph I J X Y ∞ := (hp x).choose
    have hΦ (x : X) : x ∈ (Φ x).source ∧ EqOn p (Φ x) (Φ x).source :=
      (hp x).choose_spec
    let T (x : X) : Set Y := p '' ((Φ x).source ∩ (V : Set X))
    have hTopen (x : X) : IsOpen (T x) := hp.isOpenMap _ ((Φ x).open_source.inter V.isOpen)
    have hcover : p '' (V : Set X) ⊆ ⋃ x, T x := by
      rintro y ⟨x, hx, rfl⟩
      exact mem_iUnion.mpr ⟨x, x, ⟨(hΦ x).1, hx⟩, rfl⟩
    obtain ⟨q, hq⟩ := (isSigmaCompact_of_isOpen J (hp.isOpenMap _ V.isOpen)).isLindelof.indexed_countable_subcover
      T hTopen hcover
    let U (n : ℕ) : Set Y := T (q n)
    let B : ℕ → Set Y := disjointed U
    let S (n : ℕ) : Set X := ((Φ (q n)).source ∩ (V : Set X)) ∩ p ⁻¹' B n
    let D : Set X := ⋃ n, S n
    have hUcover : ⋃ n, U n = p '' (V : Set X) := by
      apply Subset.antisymm
      · intro y hy
        obtain ⟨n, hn⟩ := mem_iUnion.mp hy
        obtain ⟨x, hx, rfl⟩ := hn
        exact ⟨x, hx.2, rfl⟩
      · exact hq
    have hBcover : ⋃ n, B n = p '' (V : Set X) := by
      rw [show B = disjointed U from rfl, iUnion_disjointed, hUcover]
    have hBsub (n : ℕ) : B n ⊆ U n := disjointed_subset U n
    have hBmeas (n : ℕ) : MeasurableSet (B n) :=
      MeasurableSet.disjointed (fun n => (hTopen (q n)).measurableSet) n
    have hBdisj : Pairwise (Disjoint on B) := disjoint_disjointed U
    have hpmeas : Measurable p := hp.contMDiff.continuous.measurable
    have hSmeas (n : ℕ) : MeasurableSet (S n) :=
      ((Φ (q n)).open_source.measurableSet.inter V.isOpen.measurableSet).inter (hpmeas (hBmeas n))
    have hSinj (n : ℕ) : InjOn p (Φ (q n)).source := by
      intro x hx y hy hxy
      apply (Φ (q n)).toPartialEquiv.injOn hx hy
      rw [← (hΦ (q n)).2 hx, ← (hΦ (q n)).2 hy]
      exact hxy
    have hSimage (n : ℕ) : p '' S n = B n := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨x, hx, hxy⟩ := hBsub n hy
        exact ⟨x, ⟨hx, by change p x ∈ B n; rwa [hxy]⟩, hxy⟩
    have hSdisj : Pairwise (Disjoint on S) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp (hBdisj hnm) hx.2 hy.2
    have hSvolume (n : ℕ) : riemannianVolumeMeasure I X gX (S n) =
        riemannianVolumeMeasure J Y gY (B n) := by
      let V : TopologicalSpace.Opens X := ⟨(Φ (q n)).source, (Φ (q n)).open_source⟩
      rw [← hSimage n]
      exact riemannianVolumeMeasure_image_eq_of_injOn_local_isometry gX gY p V
        (hp.isLocalDiffeomorphOn V) (hSinj n) (fun x _ => hmetric x)
        (hSmeas n) (fun _ hx => hx.1.1)
    refine ⟨D, MeasurableSet.iUnion hSmeas, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1.2
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact ⟨x, hn.1.2, rfl⟩
      · intro x hx y hy hxy
        obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
        obtain ⟨m, hym⟩ := mem_iUnion.mp hy
        have hnm : n = m := by
          by_contra hne
          exact Set.disjoint_left.mp (hBdisj hne) hxn.2 (hxy.symm ▸ hym.2)
        subst m
        exact hSinj n hxn.1.1 hym.1.1 hxy
      · intro y hyp
        have hy : y ∈ ⋃ n, B n := by rwa [hBcover]
        obtain ⟨n, hn⟩ := mem_iUnion.mp hy
        obtain ⟨x, hx, hpx⟩ := (hSimage n).symm ▸ hn
        exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, hpx⟩
    · calc
        riemannianVolumeMeasure I X gX D =
            ∑' n, riemannianVolumeMeasure I X gX (S n) := measure_iUnion hSdisj hSmeas
        _ = ∑' n, riemannianVolumeMeasure J Y gY (B n) := tsum_congr hSvolume
        _ = riemannianVolumeMeasure J Y gY (⋃ n, B n) :=
          (measure_iUnion hBdisj hBmeas).symm
        _ = riemannianVolumeMeasure J Y gY (p '' (V : Set X)) := by rw [hBcover]
  · let _ : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
    have hV : (V : Set X) = ∅ := Set.eq_empty_of_isEmpty _
    refine ⟨∅, MeasurableSet.empty, empty_subset _, ?_, ?_⟩
    · rw [hV, image_empty]
      exact Set.bijOn_empty p
    · rw [hV, image_empty, measure_empty, measure_empty]

theorem exists_measurable_bijOn_volume_eq_of_surjective_local_isometry
    (gX : SmoothRiemannianMetric I X) (gY : SmoothRiemannianMetric J Y)
    (p : X → Y) (hp : IsLocalDiffeomorph I J ∞ p) (honto : Surjective p)
    (hmetric : ∀ (x : X) (v w : TangentSpace I x),
      gX.inner x v w = gY.inner (p x) (mfderiv I J p x v) (mfderiv I J p x w)) :
    ∃ D : Set X, MeasurableSet D ∧ BijOn p D univ ∧
      riemannianVolumeMeasure I X gX D = riemannianVolumeMeasure J Y gY univ := by
  obtain ⟨D, hD, _, hbij, hvol⟩ :=
    exists_measurable_subset_bijOn_volume_eq_of_local_isometry gX gY p hp ⊤ hmetric
  have himage : p '' (⊤ : TopologicalSpace.Opens X).carrier = Set.univ := by
    simpa only [TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.coe_top,
      image_univ] using honto.range_eq
  exact ⟨D, hD, himage ▸ hbij, himage ▸ hvol⟩

theorem exists_fundamental_domain_volume_eq_of_surjective_local_isometry
    {G : Type*} [Group G] [MulAction G X]
    (gX : SmoothRiemannianMetric I X) (gY : SmoothRiemannianMetric J Y)
    (p : X → Y) (hp : IsLocalDiffeomorph I J ∞ p) (honto : Surjective p)
    (hmetric : ∀ (x : X) (v w : TangentSpace I x),
      gX.inner x v w = gY.inner (p x) (mfderiv I J p x v) (mfderiv I J p x w))
    (hfiber : ∀ x y : X, p x = p y ↔ ∃ a : G, a • x = y)
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : X, a • x ≠ x) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x : X, ∃! a : G, a • x ∈ D) ∧
      IsFundamentalDomain G D (riemannianVolumeMeasure I X gX) ∧
      riemannianVolumeMeasure I X gX D = riemannianVolumeMeasure J Y gY univ := by
  obtain ⟨D, hD, hbij, hvol⟩ :=
    exists_measurable_bijOn_volume_eq_of_surjective_local_isometry gX gY p hp honto hmetric
  have hproj (a : G) (x : X) : p (a • x) = p x :=
    ((hfiber x (a • x)).mpr ⟨a, rfl⟩).symm
  have hrep (x : X) : ∃! a : G, a • x ∈ D := by
    obtain ⟨y, hy, hpy⟩ := hbij.surjOn (mem_univ (p x))
    obtain ⟨a, ha⟩ := (hfiber x y).mp hpy.symm
    have haD : a • x ∈ D := ha.symm ▸ hy
    refine ⟨a, haD, ?_⟩
    intro b hb
    have hpoint : b • x = a • x :=
      hbij.injOn hb haD ((hproj b x).trans (hproj a x).symm)
    have hab : a⁻¹ * b = 1 := by
      by_contra hne
      apply hfree (a⁻¹ * b) hne x
      rw [mul_smul, hpoint, inv_smul_smul]
    exact (inv_mul_eq_one.mp hab).symm
  exact ⟨D, hD, hrep, IsFundamentalDomain.mk' hD.nullMeasurableSet hrep, hvol⟩

end DifferentialGeometry.Geometry.Measure
