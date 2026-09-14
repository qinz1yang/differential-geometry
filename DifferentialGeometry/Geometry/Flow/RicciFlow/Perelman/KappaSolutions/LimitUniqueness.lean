import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Cross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem isometry_of_tendsto_edist {P Q : Type*} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    {f : Nat -> P -> Q} {g : P -> Q}
    (hconv : forall x : P, Filter.Tendsto (fun k : Nat => f k x) Filter.atTop (nhds (g x)))
    (hdist : forall x y : P,
      Filter.Tendsto (fun k : Nat => edist (f k x) (f k y)) Filter.atTop (nhds (edist x y))) :
    Isometry g := by
  intro x y
  exact tendsto_nhds_unique ((hconv x).edist (hconv y)) (hdist x y)

namespace CheegerGromovCompactness

noncomputable def sourceRiemannianEDist (X : PointedFlowSeq (I := I)) (k : Nat) (t : Real) :
    (X.term k).M -> (X.term k).M -> ℝ≥0∞ := by
  letI : TopologicalSpace (X.term k).M := (X.term k).topology
  letI : ChartedSpace H (X.term k).M := (X.term k).charted
  letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  exact fun x y => riemannianEDistOf (I := I) ((X.term k).S.family.metric t) x y

theorem sourceRiemannianEDist_self (X : PointedFlowSeq (I := I)) (k : Nat) (t : Real)
    (x : (X.term k).M) : sourceRiemannianEDist (I := I) X k t x x = 0 :=
  letI : TopologicalSpace (X.term k).M := (X.term k).topology
  letI : ChartedSpace H (X.term k).M := (X.term k).charted
  letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  riemannianEDistOf_self (I := I) ((X.term k).S.family.metric t) x

theorem sourceRiemannianEDist_comm (X : PointedFlowSeq (I := I)) (k : Nat) (t : Real)
    (x y : (X.term k).M) :
    sourceRiemannianEDist (I := I) X k t x y = sourceRiemannianEDist (I := I) X k t y x :=
  letI : TopologicalSpace (X.term k).M := (X.term k).topology
  letI : ChartedSpace H (X.term k).M := (X.term k).charted
  letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  riemannianEDistOf_comm (I := I) ((X.term k).S.family.metric t) x y

theorem sourceRiemannianEDist_triangle (X : PointedFlowSeq (I := I)) (k : Nat) (t : Real)
    (x y z : (X.term k).M) :
    sourceRiemannianEDist (I := I) X k t x z ≤
      sourceRiemannianEDist (I := I) X k t x y +
        sourceRiemannianEDist (I := I) X k t y z :=
  letI : TopologicalSpace (X.term k).M := (X.term k).topology
  letI : ChartedSpace H (X.term k).M := (X.term k).charted
  letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  riemannianEDistOf_triangle (I := I) ((X.term k).S.family.metric t) x y z

noncomputable def pointedRiemannianEDist (P : PointedRiemannianManifold (I := I)) :
    P.M -> P.M -> ℝ≥0∞ := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  exact fun x y => riemannianEDistOf (I := I) P.metric x y

omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem pointedRiemannianEDist_comm (P : PointedRiemannianManifold (I := I)) (x y : P.M) :
    pointedRiemannianEDist (I := I) P x y = pointedRiemannianEDist (I := I) P y x :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  riemannianEDistOf_comm (I := I) P.metric x y

omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem pointedRiemannianEDist_triangle (P : PointedRiemannianManifold (I := I))
    (x y z : P.M) :
    pointedRiemannianEDist (I := I) P x z ≤
      pointedRiemannianEDist (I := I) P x y +
        pointedRiemannianEDist (I := I) P y z :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  riemannianEDistOf_triangle (I := I) P.metric x y z

theorem pointedRiemannianEDist_eq_of_tendsto_source
    {X : PointedFlowSeq (I := I)} {P₁ P₂ : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat} (Φ₁ : PointedCGHMaps (I := I) X P₁ subseq)
    (Φ₂ : PointedCGHMaps (I := I) X P₂ subseq) (F : P₁.M -> P₂.M)
    (hΦ₁ : forall x y : P₁.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₁.map k y))
      Filter.atTop (nhds (pointedRiemannianEDist (I := I) P₁ x y)))
    (hΦ₂ : forall x y : P₂.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₂.map k x) (Φ₂.map k y))
      Filter.atTop (nhds (pointedRiemannianEDist (I := I) P₂ x y)))
    (hpair : forall x : P₁.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)))
      Filter.atTop (nhds 0)) :
    forall x y : P₁.M,
      pointedRiemannianEDist (I := I) P₂ (F x) (F y) =
        pointedRiemannianEDist (I := I) P₁ x y := by
  intro x y
  have keyA : forall k : Nat,
      sourceRiemannianEDist (I := I) X (subseq k) 0
          (Φ₂.map k (F x)) (Φ₂.map k (F y)) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₁.map k y) +
          (sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)) +
            sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k y)
              (Φ₂.map k (F y))) := by
    intro k
    have h1 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₂.map k (F x)) (Φ₂.map k (F y)) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₂.map k (F x)) (Φ₁.map k x) +
          sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F y)) :=
      sourceRiemannianEDist_triangle (I := I) X (subseq k) 0
        (Φ₂.map k (F x)) (Φ₁.map k x) (Φ₂.map k (F y))
    have h2 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₁.map k x) (Φ₂.map k (F y)) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₁.map k y) +
          sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k y) (Φ₂.map k (F y)) :=
      sourceRiemannianEDist_triangle (I := I) X (subseq k) 0
        (Φ₁.map k x) (Φ₁.map k y) (Φ₂.map k (F y))
    have h3 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₂.map k (F x)) (Φ₁.map k x) =
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)) :=
      sourceRiemannianEDist_comm (I := I) X (subseq k) 0 (Φ₂.map k (F x)) (Φ₁.map k x)
    exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by rw [h3]; ac_rfl)
  have keyB : forall k : Nat,
      sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₁.map k y) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0
            (Φ₂.map k (F x)) (Φ₂.map k (F y)) +
          (sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)) +
            sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k y)
              (Φ₂.map k (F y))) := by
    intro k
    have h1 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₁.map k x) (Φ₁.map k y) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)) +
          sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₂.map k (F x)) (Φ₁.map k y) :=
      sourceRiemannianEDist_triangle (I := I) X (subseq k) 0
        (Φ₁.map k x) (Φ₂.map k (F x)) (Φ₁.map k y)
    have h2 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₂.map k (F x)) (Φ₁.map k y) ≤
        sourceRiemannianEDist (I := I) X (subseq k) 0
            (Φ₂.map k (F x)) (Φ₂.map k (F y)) +
          sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₂.map k (F y)) (Φ₁.map k y) :=
      sourceRiemannianEDist_triangle (I := I) X (subseq k) 0
        (Φ₂.map k (F x)) (Φ₂.map k (F y)) (Φ₁.map k y)
    have h3 : sourceRiemannianEDist (I := I) X (subseq k) 0
        (Φ₂.map k (F y)) (Φ₁.map k y) =
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k y) (Φ₂.map k (F y)) :=
      sourceRiemannianEDist_comm (I := I) X (subseq k) 0 (Φ₂.map k (F y)) (Φ₁.map k y)
    exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by rw [h3]; ac_rfl)
  have hba : pointedRiemannianEDist (I := I) P₂ (F x) (F y) ≤
      pointedRiemannianEDist (I := I) P₁ x y := by
    have hlim := le_of_tendsto_of_tendsto (hΦ₂ (F x) (F y))
      ((hΦ₁ x y).add ((hpair x).add (hpair y))) (Filter.Eventually.of_forall keyA)
    simpa using hlim
  have hab : pointedRiemannianEDist (I := I) P₁ x y ≤
      pointedRiemannianEDist (I := I) P₂ (F x) (F y) := by
    have hlim := le_of_tendsto_of_tendsto (hΦ₁ x y)
      ((hΦ₂ (F x) (F y)).add ((hpair x).add (hpair y))) (Filter.Eventually.of_forall keyB)
    simpa using hlim
  exact le_antisymm hba hab

namespace PointedRiemannianManifold

def PointedlyIsometric (P₁ P₂ : PointedRiemannianManifold (I := I)) : Prop :=
  letI : TopologicalSpace P₁.M := P₁.topology
  letI : ChartedSpace H P₁.M := P₁.charted
  letI : IsManifold I ∞ P₁.M := P₁.smooth
  letI : T2Space P₁.M := P₁.t2
  letI : TopologicalSpace P₂.M := P₂.topology
  letI : ChartedSpace H P₂.M := P₂.charted
  letI : IsManifold I ∞ P₂.M := P₂.smooth
  exists F : P₁.M ≃ₘ⟮I, I⟯ P₂.M,
    F P₁.basepoint = P₂.basepoint ∧
      Diffeomorph.pullbackMetricCross P₂.metric F = P₁.metric

omit [CompleteSpace E] in
theorem pointedlyIsometric_refl (P : PointedRiemannianManifold (I := I)) :
    PointedlyIsometric (I := I) P P :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space P.M := P.t2
  ⟨_root_.Diffeomorph.refl I P.M ∞, rfl,
    Diffeomorph.pullbackMetricCross_refl (I := I) P.metric⟩

end PointedRiemannianManifold

def RiemannianIsometrySmoothInput (P₁ P₂ : PointedRiemannianManifold (I := I)) : Prop :=
  letI : TopologicalSpace P₁.M := P₁.topology
  letI : ChartedSpace H P₁.M := P₁.charted
  letI : IsManifold I ∞ P₁.M := P₁.smooth
  letI : T2Space P₁.M := P₁.t2
  letI : TopologicalSpace P₂.M := P₂.topology
  letI : ChartedSpace H P₂.M := P₂.charted
  letI : IsManifold I ∞ P₂.M := P₂.smooth
  forall (F : P₁.M -> P₂.M), Function.Bijective F -> F P₁.basepoint = P₂.basepoint ->
    (forall x y : P₁.M,
      pointedRiemannianEDist (I := I) P₂ (F x) (F y) =
        pointedRiemannianEDist (I := I) P₁ x y) ->
    PointedRiemannianManifold.PointedlyIsometric (I := I) P₁ P₂

theorem PointedRiemannianManifold.pointedlyIsometric_of_tendsto_source
    {X : PointedFlowSeq (I := I)} {P₁ P₂ : PointedRiemannianManifold (I := I)}
    (hinput : RiemannianIsometrySmoothInput (I := I) P₁ P₂)
    {subseq : Nat -> Nat} (Φ₁ : PointedCGHMaps (I := I) X P₁ subseq)
    (Φ₂ : PointedCGHMaps (I := I) X P₂ subseq) (F : P₁.M -> P₂.M)
    (hobj : Function.Bijective F) (hbase : F P₁.basepoint = P₂.basepoint)
    (hΦ₁ : forall x y : P₁.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₁.map k y))
      Filter.atTop (nhds (pointedRiemannianEDist (I := I) P₁ x y)))
    (hΦ₂ : forall x y : P₂.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₂.map k x) (Φ₂.map k y))
      Filter.atTop (nhds (pointedRiemannianEDist (I := I) P₂ x y)))
    (hpair : forall x : P₁.M, Filter.Tendsto
      (fun k : Nat =>
        sourceRiemannianEDist (I := I) X (subseq k) 0 (Φ₁.map k x) (Φ₂.map k (F x)))
      Filter.atTop (nhds 0)) :
    PointedRiemannianManifold.PointedlyIsometric (I := I) P₁ P₂ :=
  letI : TopologicalSpace P₁.M := P₁.topology
  letI : ChartedSpace H P₁.M := P₁.charted
  letI : IsManifold I ∞ P₁.M := P₁.smooth
  letI : T2Space P₁.M := P₁.t2
  letI : TopologicalSpace P₂.M := P₂.topology
  letI : ChartedSpace H P₂.M := P₂.charted
  letI : IsManifold I ∞ P₂.M := P₂.smooth
  hinput F hobj hbase
    (pointedRiemannianEDist_eq_of_tendsto_source (I := I) Φ₁ Φ₂ F hΦ₁ hΦ₂ hpair)

def PointedCGHMaps.PointedlyIdentified
    {X : PointedFlowSeq (I := I)} {P₁ P₂ : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat} (Φ₁ : PointedCGHMaps (I := I) X P₁ subseq)
    (Φ₂ : PointedCGHMaps (I := I) X P₂ subseq) : Prop :=
  letI : TopologicalSpace P₁.M := P₁.topology
  letI : ChartedSpace H P₁.M := P₁.charted
  letI : IsManifold I ∞ P₁.M := P₁.smooth
  letI : T2Space P₁.M := P₁.t2
  letI : TopologicalSpace P₂.M := P₂.topology
  letI : ChartedSpace H P₂.M := P₂.charted
  letI : IsManifold I ∞ P₂.M := P₂.smooth
  exists F : P₁.M ≃ₘ⟮I, I⟯ P₂.M,
    F P₁.basepoint = P₂.basepoint ∧
      Diffeomorph.pullbackMetricCross P₂.metric F = P₁.metric ∧
      (forall x : P₁.M,
        Filter.Tendsto (fun k : Nat =>
          sourceRiemannianEDist (I := I) X (subseq k) 0
            (Φ₁.map k x) (Φ₂.map k (F x)))
          Filter.atTop (nhds 0))

theorem PointedCGHMaps.pointedlyIdentified_refl
    {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat} (Φ : PointedCGHMaps (I := I) X P subseq) :
    PointedlyIdentified (I := I) Φ Φ :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space P.M := P.t2
  ⟨_root_.Diffeomorph.refl I P.M ∞, rfl,
    Diffeomorph.pullbackMetricCross_refl (I := I) P.metric,
    fun x => by
      have hzero : (fun k : Nat =>
          sourceRiemannianEDist (I := I) X (subseq k) 0
            (Φ.map k x) (Φ.map k ((_root_.Diffeomorph.refl I P.M ∞) x))) = fun _ => 0 := by
        funext k
        exact sourceRiemannianEDist_self (I := I) X (subseq k) 0 (Φ.map k x)
      rw [hzero]
      exact tendsto_const_nhds⟩

noncomputable def SmoothCGHConverges.PointedlyIdentified
    {X : PointedFlowSeq (I := I)} {L₁ L₂ : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat} (h₁ : SmoothCGHConverges (I := I) X L₁ subseq)
    (h₂ : SmoothCGHConverges (I := I) X L₂ subseq) : Prop :=
  PointedCGHMaps.PointedlyIdentified (I := I) h₁.spatial.maps h₂.spatial.maps

theorem SmoothCGHConverges.pointedlyIdentified_refl
    {X : PointedFlowSeq (I := I)} {L : PointedFlowData (I := I) X.D} {subseq : Nat -> Nat}
    (h : SmoothCGHConverges (I := I) X L subseq) : h.PointedlyIdentified h :=
  PointedCGHMaps.pointedlyIdentified_refl (I := I) h.spatial.maps

end CheegerGromovCompactness

end DifferentialGeometry
