import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabCovariantChangeBound
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  {Idx : Type*} [Fintype Idx]

private theorem koszul_combination_bound
    {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → ℝ)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin 2 → Idx) → ℝ)
    (hg : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (c₁ c₂ c₃ : ℝ) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (m : ℕ) {x : M} (hx : x ∈ u) :
    compL2 (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) =>
        c₁ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₁ j)) +
        (c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j)))) m x) ≤
      (|c₁| + |c₂| + |c₃|) * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) := by
  classical
  have hsm : ∀ (c : ℝ) (P : Fin 3 ≃ Fin 3) (k : Fin 3 → Idx),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun z => c * iterCovComp (I := I) frame chr g 1 z (fun j => k (P j))) u :=
    fun c P k => contMDiffOn_const.mul
      (iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1 (fun j => k (P j)))
  have hterm (c : ℝ) (P : Fin 3 ≃ Fin 3) :
      compL2 (iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) => c * iterCovComp (I := I) frame chr g 1 z
          (fun j => k (P j))) m x) =
        |c| * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) := by
    rw [show iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c * iterCovComp (I := I) frame chr g 1 z
            (fun j => k (P j))) m x =
        fun n => c * iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => iterCovComp (I := I) frame chr g 1 z
            (fun j => k (P j))) m x n from
      funext (iterCovComp_smul hu frame chr c _ hframe hchr
        (fun k => iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1
          (fun j => k (P j))) m x hx),
      compL2_smul,
      compL2_iterCovComp_compReindex P frame chr (iterCovComp (I := I) frame chr g 1) m x,
      ← compL2_iterCovComp_shift frame chr g m x]
  rw [show iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) =>
          c₁ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₁ j)) +
          (c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j)))) m x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₁ * iterCovComp (I := I) frame chr g 1 z
            (fun j => k (P₁ j))) m x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) =>
            c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
              c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hsm c₁ P₁)
        (fun k => (hsm c₂ P₂ k).add (hsm c₃ P₃ k)) m x hx)]
  refine (compL2_add_le _ _).trans ?_
  rw [hterm c₁ P₁,
    show iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) =>
          c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z
            (fun j => k (P₂ j))) m x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z
            (fun j => k (P₃ j))) m x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hsm c₂ P₂) (hsm c₃ P₃) m x hx)]
  have h23 := compL2_add_le
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z
        (fun j => k (P₂ j))) m x)
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z
        (fun j => k (P₃ j))) m x)
  rw [hterm c₂ P₂, hterm c₃ P₃] at h23
  linarith

variable [CompleteSpace E] [IsManifold I 2 M]

theorem exists_uniform_lowered_connection_difference_bound
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀] (basisE : Module.Basis Idx ℝ E)
    {u : Set M} (hu : IsOpen u) (hub : u ⊆ e₀.baseSet)
    (CA : ℕ → ℝ) (hCA0 : ∀ c, 0 ≤ CA c) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (chr : M → Idx → Idx → Idx → ℝ),
      (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => chr y d i j) u) →
      ∀ (gK gRef : SmoothRiemannianMetric I M),
      (∀ c, c < a → ∀ y ∈ u,
        compL2 (iterCovCompU (I := I) (fun d z => e₀.localFrame basisE d z) chr
          (fun z (n : Fin 3 → Idx) =>
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
              (fun d w => e₀.localFrame basisE d w)
              (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) z (n 0) (n 1) (n 2) -
                chr z (n 0) (n 1) (n 2)) c y) ≤ CA c) →
      ∀ (eps : ℝ), 0 < eps →
      (∀ j, j ≤ a → ∀ y ∈ u,
        compL2 (iterCovComp (I := I) (fun d z => e₀.localFrame basisE d z)
          (fun z => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun d w => e₀.localFrame basisE d w)
            (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) z)
          (frameComp0S (I := I) (metricTensorField (I := I) gK)
            (fun d z => e₀.localFrame basisE d z)) (j + 1) y) ≤ eps) →
      ∀ y ∈ u,
        compL2 (iterCovComp (I := I) (fun d z => e₀.localFrame basisE d z) chr
          (fun z => contrTail (akCompField (I := I) e₀ gK gRef basisE z)
            (frameComp0S (I := I) (metricTensorField (I := I) gK)
              (fun d w => e₀.localFrame basisE d w) z)) a y) ≤ C * eps := by
  classical
  let frame : Idx → (x : M) → TangentSpace I x := fun d z => e₀.localFrame basisE d z
  have hf := fun d => (frame_e_mdiffOn (I := I) e₀ basisE d).mono hub
  obtain ⟨C, hC0, hC⟩ := exists_linear_covariant_connection_change_bound
    hu frame hf CA hCA0 a 2
  refine ⟨C * (3 / 2), mul_nonneg hC0 (by norm_num), ?_⟩
  intro chr hchr gK gRef hCA eps heps hbound y hy
  let chrRef := fun z => christoffelSymbolInFrame
    (leviCivitaConnectionOfMetric (I := I) gRef) frame
    (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) z
  let G := frameComp0S (I := I) (metricTensorField (I := I) gK) frame
  let F := fun z => contrTail (akCompField (I := I) e₀ gK gRef basisE z) (G z)
  have hchrRef := fun d i j => (lcChrist_e_mdiffOn (I := I) e₀ gRef basisE d i j).mono hub
  have hG := fun k => (gCompField_mdiffOn (I := I) e₀ gK basisE k).mono hub
  have hkos : ∀ z ∈ u, F z = fun k : Fin 3 → Idx =>
      (1 / 2 : ℝ) * iterCovComp (I := I) frame chrRef G 1 z k +
      ((1 / 2 : ℝ) * iterCovComp (I := I) frame chrRef G 1 z
        (fun j => k (Equiv.swap (0 : Fin 3) 1 j)) +
      (-(1 / 2) : ℝ) * iterCovComp (I := I) frame chrRef G 1 z
        (fun j => k ((finRotate 3).symm j))) := by
    intro z hz
    exact koszulComp_at frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)
      e₀.open_baseSet gK gRef (hub hz)
  have hF : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun z => F z k) u := by
    intro k z hz
    have hs := iterCovComp_contMDiffOn hu frame chrRef G hf hchrRef hG 1
    have hsum := ((contMDiffOn_const (c := (1 / 2 : ℝ))).mul (hs k)).add
      (((contMDiffOn_const (c := (1 / 2 : ℝ))).mul
        (hs (fun j => k (Equiv.swap (0 : Fin 3) 1 j)))).add
        ((contMDiffOn_const (c := (-(1 / 2) : ℝ))).mul
          (hs (fun j => k ((finRotate 3).symm j)))))
    refine ((hsum.contMDiffAt (hu.mem_nhds hz)).congr_of_eventuallyEq
      ?_).contMDiffWithinAt
    filter_upwards [hu.mem_nhds hz] with w hw
    exact congrFun (hkos w hw) k
  have hFbound : ∀ j, j ≤ a → ∀ z ∈ u,
      compL2 (iterCovComp (I := I) frame chrRef F j z) ≤ (3 / 2) * eps := by
    intro j hj z hz
    rw [iterCovComp_congr_on hu frame chrRef hkos j z hz]
    have hb := koszul_combination_bound hu frame chrRef hf hchrRef G hG
      (1 / 2) (1 / 2) (-(1 / 2)) (Equiv.refl (Fin 3))
      (Equiv.swap (0 : Fin 3) 1) ((finRotate 3).symm) j hz
    norm_num only [abs_one, abs_div, abs_neg, Equiv.refl_apply] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hbound j hj z hz) (by norm_num))
  have hfinal := hC chr chrRef hchr hchrRef hCA ((3 / 2) * eps)
    (mul_pos (by norm_num) heps) F hF hFbound y hy
  simpa only [mul_assoc] using hfinal

theorem metric_component_succ_le_metric_error
    (gK gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hcomp : ∀ (s : ℕ) (A : Tensor0SSpace s I y),
      (∑ k : Fin s → Idx, component0S (I := I) (hframe.toBasisAt hy) A k ^ 2) ≤
        2 ^ s * normSq0S (I := I) gRef y s A)
    (a : ℕ) :
    compL2 (iterCovComp (I := I) frame
      (fun z => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe z)
      (frameComp0S (I := I) (metricTensorField (I := I) gK) frame) (a + 1) y) ≤
      2 ^ (2 + (a + 1)) * DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm
        (I := I) (a + 1) gK gRef gRef y := by
  classical
  have hnorm : DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm
      (I := I) (a + 1) gK gRef gRef y =
      DifferentialGeometry.CheegerGromovCompactness.metricCovDerivNorm
        (I := I) (a + 1) gK gRef y := by
    unfold DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm
      DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt
    rw [DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_succ (I := I) gRef a]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sub_zero]
    rfl
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) gRef y
  have hinv : MetricInverseInBasis (I := I) gRef y basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I y)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  rw [hnorm, DifferentialGeometry.CheegerGromovCompactness.metricCovDerivNorm_eq_iterCov
    (I := I) gK gRef (a + 1) basis hinv]
  exact compL2_tower_le gRef gRef (metricTensorField (I := I) gK)
    frame hframe hu hy hcomp (a + 1)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
