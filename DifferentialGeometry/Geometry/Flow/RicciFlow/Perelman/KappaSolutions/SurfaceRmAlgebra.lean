import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRicciAlgebra

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

private def surfaceRmSlotsEquiv :
    (Fin 4 → Fin 2) ≃ (((Fin 2 × Fin 2) × Fin 2) × Fin 2) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private theorem surfaceRm_sum_slots (F : (Fin 4 → Fin 2) → ℝ) :
    (∑ a : Fin 4 → Fin 2, F a) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv surfaceRmSlotsEquiv F
    (fun p : (((Fin 2 × Fin 2) × Fin 2) × Fin 2) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro a
    have hslots :
        slots4 (surfaceRmSlotsEquiv a).1.1.1 (surfaceRmSlotsEquiv a).1.1.2
          (surfaceRmSlotsEquiv a).1.2 (surfaceRmSlotsEquiv a).2 = a :=
      surfaceRmSlotsEquiv.left_inv a
    rw [hslots]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M]

local instance surfaceRmAlgebraManifoldTwo : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance surfaceRmAlgebraManifoldThree : IsManifold I 3 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem metricRm_normSq_eq_scalar_sq_of_finrank_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2) (x : M) :
    normSq0S (I := I) g x 4 (metricRm04At (I := I) g x) =
      metricScalarAt (I := I) g x ^ 2 := by
  classical
  have hdimT : Module.finrank ℝ (TangentSpace I x) = 2 := hdim
  have hb := exists_orthonormal_basis (I := I) g x
  rw [hdimT] at hb
  obtain ⟨basis, hON⟩ := hb
  let curvature := metricCurvatureSections (I := I) g
  let Rm : Tensor04At (I := I) (M := M) x := metricRm04 (I := I) g x
  let K : ℝ := Rm (vec4 (basis 1) (basis 0) (basis 0) (basis 1))
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) g x) (metricRm04 (I := I) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) g)
      (metricRm13 (I := I) g) (metricRm04 (I := I) g)
      curvature.rm13Realizes curvature.rm04Realizes x
  have hTrace := ricci_diag_eq_sum_rm04_diag_of_orthonormal
    (I := I) g basis (metricRicci (I := I) g) (metricRm13 (I := I) g)
      (metricRm04 (I := I) g) curvature.ricciRealizes hLower hON
  have hInput : ∀ X Y Z W : TangentSpace I x,
      Rm (vec4 Y X Z W) = -Rm (vec4 X Y Z W) :=
    rm04InputSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm04 (I := I) g) curvature.rm04Realizes
  have hOutput : ∀ X Y Z W : TangentSpace I x,
      Rm (vec4 X Y Z W) = -Rm (vec4 X Y W Z) :=
    rm04OutputSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm04 (I := I) g) curvature.rm04Realizes
  have hfirstZero : ∀ X Z W : TangentSpace I x, Rm (vec4 X X Z W) = 0 := by
    intro X Z W
    linarith [hInput X X Z W]
  have hlastZero : ∀ X Y Z : TangentSpace I x, Rm (vec4 X Y Z Z) = 0 := by
    intro X Y Z
    linarith [hOutput X Y Z Z]
  have h1010 : Rm (vec4 (basis 1) (basis 0) (basis 1) (basis 0)) = -K :=
    hOutput (basis 1) (basis 0) (basis 1) (basis 0)
  have h0101 : Rm (vec4 (basis 0) (basis 1) (basis 0) (basis 1)) = -K :=
    hInput (basis 1) (basis 0) (basis 0) (basis 1)
  have h0110 : Rm (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) = K := by
    have h := hInput (basis 1) (basis 0) (basis 1) (basis 0)
    rw [h1010, neg_neg] at h
    exact h
  have hK : K = metricScalarAt (I := I) g x / 2 := by
    have h := hTrace (0 : Fin 2) 0
    change metricRicciAt (I := I) g x (vec2 (basis 0) (basis 0)) =
      ∑ a : Fin 2, Rm (vec4 (basis a) (basis 0) (basis 0) (basis a)) at h
    rw [Fin.sum_univ_two, hfirstZero, zero_add] at h
    calc
      K = metricRicciAt (I := I) g x (vec2 (basis 0) (basis 0)) := h.symm
      _ = (metricScalarAt (I := I) g x / 2) * g.inner x (basis 0) (basis 0) :=
        metricRicciAt_apply_of_finrank_two g hdim x (basis 0) (basis 0)
      _ = metricScalarAt (I := I) g x / 2 := by rw [hON]; simp
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin 2)) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hcomponent (i j k l : Fin 2) :
      component0S (I := I) basis Rm (slots4 i j k l) =
        Rm (vec4 (basis i) (basis j) (basis k) (basis l)) := by
    rw [component0S_apply]
    congr 1
    funext a
    fin_cases a <;> simp [slots4, vec4]
  have hnorm : normSq0S (I := I) g x 4 Rm = 4 * K ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 4 basis hinv Rm,
      surfaceRm_sum_slots]
    simp_rw [hcomponent]
    simp only [Fin.sum_univ_two, hfirstZero, hlastZero, h1010, h0101, h0110]
    dsimp only [K]
    ring
  calc
    normSq0S (I := I) g x 4 (metricRm04At (I := I) g x) =
        normSq0S (I := I) g x 4 Rm := by simp only [Rm, metricRm04_apply]
    _ = 4 * K ^ 2 := hnorm
    _ = metricScalarAt (I := I) g x ^ 2 := by rw [hK]; ring


theorem sqrt_metricRm_normSq_eq_abs_scalar_of_finrank_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2) (x : M) :
    Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) =
      |metricScalarAt (I := I) g x| := by
  rw [metricRm_normSq_eq_scalar_sq_of_finrank_two g hdim x, Real.sqrt_sq_eq_abs]

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
