import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.NonnegativeCurvatureOperator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem raw_reaction_of_realization
    (N : Tensor02ReactionAt (I := I) (M := M))
    (t : ℝ) (g : SmoothRiemannianMetric I M)
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hsymm : TwoTensorSymmetricAt (I := I) (M := M) A x)
    (B : Tensor02At (I := I) (M := M) x)
    (hB : Tensor02RealizesRawAt (I := I) (M := M) A x B)
    (v w : TangentSpace I x) :
    Tensor02ReactionAt.toRawSymm N t g A x v w =
      N t g x B (vec2 (I := I) v w) := by
  have hBsym :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) A) x B := by
    intro u z
    rw [rawSym2_eq_of_symm hsymm]
    exact hB u z
  have hreal :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) A) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hident := tensor02_realizes_ext hreal hBsym
  rw [Tensor02ReactionAt.toRawSymm_eval_of_bilin
    N t g A x hbilin v w, hident]

private theorem upper_bound_reaction_diagonal
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (r1 r2 r3 : ℝ)
    (hdiag : ∀ i j : Fin 3,
      Ric (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j) :
    ricciUpperBoundReactAt g
        (((1 / 2 : ℝ) * metricTracePair0SAt g Ric) •
          metricTensorField g x - Ric)
        (vec2 (I := I) (basis 0) (basis 0)) =
      2 * (r1 - r2) * (r1 - r3) := by
  classical
  let A : Tensor02At (I := I) (M := M) x :=
    ((1 / 2 : ℝ) * metricTracePair0SAt g Ric) •
      metricTensorField g x - Ric
  have htraceA :
      metricTracePair0SAt g A =
        (1 / 2 : ℝ) * metricTracePair0SAt g Ric := by
    dsimp only [A]
    rw [metricTracePair0SAt_sub, metricTracePair0SAt_smul,
      metricTrace_metric3 basis horth]
    ring
  have hrecover :
      metricTracePair0SAt g A • metricTensorField g x - A = Ric := by
    rw [htraceA]
    dsimp only [A]
    abel
  have hcomponents :
      (fun i j : Fin 3 =>
        Ric (vec2 (I := I) (basis i) (basis j))) =
          ricciDiag3 r1 r2 r3 := by
    funext i j
    exact hdiag i j
  have hRm :
      (fun a b c d : Fin 3 =>
        rm04OfRic3At g Ric
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) =
        standardRmOfRic3 (ricciDiag3 r1 r2 r3) := by
    funext a b c d
    rw [rm04OfRic3At_comp_orthonormal basis horth Ric a b c d,
      hcomponents]
  have hnorm := ricciNorm3_comp_orthonormal basis horth Ric
  rw [hcomponents] at hnorm
  have htrace := metricTrace_comp_orthonormal basis horth Ric
  rw [hcomponents] at htrace
  have hreaction :=
    ricciReaction3At_comp_orthonormal basis horth Ric 0 0
  rw [hRm, hcomponents] at hreaction
  have hmetric :
      metricTensorField g x
        (vec2 (I := I) (basis 0) (basis 0)) = 1 := by
    simpa [metricTensorField_apply, vec2,
      DifferentialGeometry.Geometry.Curvature.vec2, delta3]
      using horth 0 0
  change ricciUpperBoundReactAt g A
    (vec2 (I := I) (basis 0) (basis 0)) = _
  dsimp only [ricciUpperBoundReactAt]
  rw [hrecover]
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply]
  rw [hnorm, htrace, hreaction, hmetric, hdiag 0 0]
  norm_num [ricciNorm3, ricciScal3, ricciPresReact, ricciSq3,
    standardRmOfRic3, ricciDiag3, delta3, Fin.sum_univ_three,
    show (2 : Fin 3) ≠ 0 by decide,
    show (0 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 1 by decide]
  ring

theorem ricci_upper_bound_reaction_in_eigenframe
    {D : RealTimeInterval} [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (r1 r2 r3 : ℝ)
    (hdiag : ∀ i j : Fin 3,
      S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j) :
    ricciUpperBoundReact (I := I) (M := M)
        t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (ricciUpperBoundSec S) t)
        x (basis 0) (basis 0) =
      2 * (r1 - r2) * (r1 - r3) := by
  have hraw :
      ricciUpperBoundReact (I := I) (M := M)
          t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (ricciUpperBoundSec S) t)
          x (basis 0) (basis 0) =
        ricciUpperBoundReactAt (S.base.metric t)
          (ricciUpperBoundSec S t x)
          (vec2 (I := I) (basis 0) (basis 0)) := by
    apply raw_reaction_of_realization
      (fun _t g _x A => ricciUpperBoundReactAt g A)
      t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (ricciUpperBoundSec S) t)
      x
      (twoTensorSecToFamily_bilin
        (I := I) (M := M) (ricciUpperBoundSec S) t x)
      ((ricci_upper_bound_sec_symm S Set.univ)
        t (Set.mem_univ t) x)
      (ricciUpperBoundSec S t x)
    intro v w
    rfl
  have hA :
      ricciUpperBoundSec S t x =
        (((1 / 2 : ℝ) *
          metricTracePair0SAt (S.base.metric t) (S.ricciAt t x)) •
            metricTensorField (S.base.metric t) x - S.ricciAt t x) := by
    rw [ricci_upper_bound_sec_at_point, SolutionOn.scalar_eq_metricTrace]
    simp only [SolutionOn.family_metric, SolutionOn.ricci,
      SolutionFamily.ricci_apply, SolutionOn.ricciAt]
  rw [hraw, hA]
  exact upper_bound_reaction_diagonal
    (S.base.metric t) x (S.ricciAt t x) basis horth r1 r2 r3 hdiag

theorem exists_ordered_ricci_frame_upper_bound_reaction
    {D : RealTimeInterval} [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    ∃ basis : Module.Basis (Fin 3) ℝ (TangentSpace I x),
      ∃ r1 r2 r3 : ℝ,
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis ∧
        r2 ≤ r1 ∧ r3 ≤ r2 ∧
        (∀ i j : Fin 3,
          S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) =
            ricciDiag3 r1 r2 r3 i j) ∧
        ricciUpperBoundReact (I := I) (M := M)
            t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M)
              (ricciUpperBoundSec S) t)
            x (basis 0) (basis 0) =
          2 * (r1 - r2) * (r1 - r3) ∧
        0 ≤ ricciUpperBoundReact (I := I) (M := M)
          t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (ricciUpperBoundSec S) t)
          x (basis 0) (basis 0) := by
  have hsymm : RicciSymAt (I := I) (S.ricciAt t x) := by
    intro v w
    exact ricciAt_symm S t x v w
  obtain ⟨basis, r1, r2, r3, horth, h21, h32, hdiag⟩ :=
    ricciEigen3_ordered (S.base.metric t) (S.ricciAt t x) hdim hsymm
  have hcomponents : ∀ i j : Fin 3,
      S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j := by
    intro i j
    simpa only [ricciCompAt_apply] using hdiag.2 i j
  have heq := ricci_upper_bound_reaction_in_eigenframe
    S t x basis horth r1 r2 r3 hcomponents
  refine ⟨basis, r1, r2, r3, horth, h21, h32, hcomponents, heq, ?_⟩
  rw [heq]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sub_nonneg.mpr h21))
    (sub_nonneg.mpr (h32.trans h21))

end DifferentialGeometry.PDE.RicciFlow
