import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DefectJetsAllOrders_S67
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity

set_option autoImplicit false

/-!
# CH12-S82 / G1: the defect-jet tower is the `∇_h`-tower (K4)

`defectJet_S57 S h N r = ∇_h^N g_r + 2 r (∇_{g_r}-Ricci-tower slot-permuted)` (S57).  For the Landau step
(`landau_step_S75`) one needs `A_{j+1} = ∇_h A_j` as `Tensor0SField`s, new derivative slot first.
Pieces: `metricCovDeriv g h (j+1) = metricCovDerivStep h j (metricCovDeriv g h j)` (definitional),
`ricCovTower g h (j+1) = covStep h (2+j) (ricCovTower g h j)` (`iterCov` is `Nat.rec`), the slot permutation
`acEquiv (j+1) = frontExtendEquiv (acEquiv j)` + `totalNabla0SFun_domDomCongr`, and linearity of `∇`.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- the slot-permuted Ricci tower `∇_h^p Ric g` as a field of arity `p + 2` (= `nablaRicReal` pointwise). -/
def nablaRicField_S82 (g h : SmoothRiemannianMetric I M) (p : ℕ) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (p + 2) :=
  Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (acEquiv p) (ricCovTower (I := I) g h p)

/-- the Ricci-defect jet at time `r` as a smooth field: `∇_h^j g_r + 2 r ∇_h^j Ric g_r`. -/
def defectJetField_S82 (g h : SmoothRiemannianMetric I M) (j : ℕ) (r : ℝ) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (j + 2) :=
  metricCovDeriv (I := I) g h j + (2 * r) • nablaRicField_S82 g h j

omit [CompleteSpace E] in
theorem nablaRicField_apply_S82 (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I M) (p i : ℕ) (s : ℝ) (x : M) :
    nablaRicReal (I := I) gSeq h p i s x = nablaRicField_S82 (gSeq i s) h p x := by
  rw [nablaRicField_S82, Tensor0SField.domDomCongr_apply]
  rfl

/-- `defectJet_S57` is the pointwise value of the smooth field `defectJetField_S82`. -/
theorem defectJet_eq_field_S82 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) (j : ℕ) (r : ℝ) (x : M) :
    defectJet_S57 S h j r x = defectJetField_S82 (S.base.metric r) h j r x := by
  have := nablaRicField_apply_S82 (I := I) (fun _ s => S.base.metric s) h j 0 r x
  simp only [defectJet_S57, defectJetField_S82, this]
  rfl

theorem metricCovDeriv_succ_apply_S82 [IsManifold I 2 M]
    (g h : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    metricCovDeriv (I := I) g h (j + 1) x =
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (j + 2)
        (LeviCivita (I := I) h) (metricCovDeriv (I := I) g h j) x := by
  have : metricCovDeriv (I := I) g h (j + 1) x =
      metricCovDerivStep (I := I) h j (metricCovDeriv (I := I) g h j) x := rfl
  rw [this, metricCovDerivStep_apply]
  rfl

theorem nablaRicField_succ_apply_S82 [IsManifold I 1 M] [IsManifold I 2 M]
    (g h : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    nablaRicField_S82 g h (p + 1) x =
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + 2)
        (LeviCivita (I := I) h) (nablaRicField_S82 g h p) x := by
  unfold nablaRicField_S82
  rw [Tensor0SField.domDomCongr_apply, totalNabla0SFun_domDomCongr]
  have h1 : ricCovTower (I := I) g h (p + 1) x =
      covStep (I := I) h (2 + p) (ricCovTower (I := I) g h p) x := rfl
  rw [h1, covStep_apply]
  rfl

/-- **K4, field form.**  `A_{j+1} = ∇_h A_j` for the smooth defect-jet fields (new slot first). -/
theorem defectJetField_succ_apply_S82 [IsManifold I 1 M] [IsManifold I 2 M]
    (g h : SmoothRiemannianMetric I M) (j : ℕ) (r : ℝ) (x : M) :
    defectJetField_S82 g h (j + 1) r x =
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (j + 2)
        (LeviCivita (I := I) h) (defectJetField_S82 g h j r) x := by
  have e1 : defectJetField_S82 g h (j + 1) r x =
      metricCovDeriv (I := I) g h (j + 1) x + (2 * r) • nablaRicField_S82 g h (j + 1) x := rfl
  rw [e1, metricCovDeriv_succ_apply_S82, nablaRicField_succ_apply_S82]
  unfold defectJetField_S82
  rw [totalNabla0SFun_add, totalNabla0SFun_smul]

/-- **K4.**  The `S57` defect jet of order `j + 1` is `∇_h` of the order-`j` defect-jet field. -/
theorem defectJet_succ_eq_totalNabla_S82 [IsManifold I 1 M] [IsManifold I 2 M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) (j : ℕ) (r : ℝ) (x : M) :
    defectJet_S57 S h (j + 1) r x =
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (j + 2)
        (LeviCivita (I := I) h) (defectJetField_S82 (S.base.metric r) h j r) x := by
  rw [defectJet_eq_field_S82, defectJetField_succ_apply_S82]

end GC.LongTime.Ch12
