import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_basis_eq_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, basis i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    let : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro s c hsum k hk
    have hzero :
        g.inner x (smoothOrthoFrame (I := I) g x k x)
          (∑ j ∈ s, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]
      simp
    rw [map_sum] at hzero
    have hpull : ∀ j ∈ s,
        g.inner x (smoothOrthoFrame (I := I) g x k x)
            (c j • smoothOrthoFrame (I := I) g x j x) =
          c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul,
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl hpull] at hzero
    rw [Finset.sum_eq_single_of_mem k hk] at hzero
    · simpa using hzero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli hcard
  refine ⟨basis, fun i => ?_⟩
  change (basisOfLinearIndependentOfCardEqFinrank' _ hli hcard :
      Fin (Module.finrank ℝ E) → TangentSpace I x) i =
    smoothOrthoFrame (I := I) g x i x
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

def smoothOrthoFrameBasis (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (exists_basis_eq_smoothOrthoFrame g x).choose

@[simp] theorem smoothOrthoFrameBasis_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    smoothOrthoFrameBasis g x i = smoothOrthoFrame g x i x :=
  (exists_basis_eq_smoothOrthoFrame g x).choose_spec i

end DifferentialGeometry.Geometry.Connection
