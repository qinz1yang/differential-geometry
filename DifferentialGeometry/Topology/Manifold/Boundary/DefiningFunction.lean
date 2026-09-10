import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UnitSpeedField

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Manifold.Boundary
variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [SigmaCompactSpace M]


theorem exists_global_boundary_definingFunction (hK : IsCompact ((𝓡∂ n).boundary M)) :
    ∃ (r : M → ℝ) (W : TopologicalSpace.Opens M), ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x, r x = 0 ↔ (𝓡∂ n).IsBoundaryPoint x) ∧
      (∀ x, (𝓡∂ n).IsInteriorPoint x → 0 < r x) ∧ (𝓡∂ n).boundary M ⊆ W ∧
      ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
        ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞ (fun y => (⟨y,V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
        IsCompact (tsupport V) ∧
        (∀ y ∈ W, (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) ∧
        ∀ y : BoundaryManifold (𝓡∂ n) M,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) := by
  classical
  obtain ⟨O,hBO,f,hf,hfn,hfzero,V,hV,hVc,hunit,hpos⟩ :=
    DifferentialGeometry.Manifold.BoundaryCollar.exists_smooth_unitSpeed_boundaryField hK
  let _ : LocallyCompactSpace (EuclideanHalfSpace n) := (𝓡∂ n).locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace n) M
  obtain ⟨W,hW,hBW,hclW,_⟩ := exists_open_between_and_isCompact_closure hK O.isOpen hBO
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ n)
    (show IsClosed (closure W) from isClosed_closure) (fun _ : Unit => (O : Set M))
    (fun _ => O.isOpen) (fun x hx => mem_iUnion.mpr ⟨(),hclW hx⟩)
  have hone : ∀ x ∈ W, ρ () x = 1 := by
    intro x hx
    simpa only [finsum_eq_sum_of_fintype,Fintype.sum_unique] using ρ.sum_eq_one (subset_closure hx)
  let r : M → ℝ := fun x => ρ () x * f x + (1 - ρ () x)
  have hr : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ r :=
    ((ρ ()).contMDiff.mul hf).add (contMDiff_const.sub (ρ ()).contMDiff)
  have hrn : ∀ x, 0 ≤ r x := fun x =>
    add_nonneg (mul_nonneg (ρ.nonneg () x) (hfn x)) (sub_nonneg.mpr (ρ.le_one () x))
  have hreq : EqOn r f W := by
    intro x hx
    simp only [r,hone x hx,one_mul,sub_self,add_zero]
  have hrzero : ∀ x, r x = 0 ↔ (𝓡∂ n).IsBoundaryPoint x := by
    intro x
    constructor
    · intro hx
      have hm : ρ () x * f x = 0 := (add_eq_zero_iff_of_nonneg
        (mul_nonneg (ρ.nonneg () x) (hfn x)) (sub_nonneg.mpr (ρ.le_one () x))).mp hx |>.1
      have h1 : 1 - ρ () x = 0 := (add_eq_zero_iff_of_nonneg
        (mul_nonneg (ρ.nonneg () x) (hfn x)) (sub_nonneg.mpr (ρ.le_one () x))).mp hx |>.2
      have hρ1 : ρ () x = 1 := (sub_eq_zero.mp h1).symm
      have hxO : x ∈ O := hρ () (subset_tsupport _ (by change ρ () x ≠ 0; rw [hρ1]; exact one_ne_zero))
      apply (hfzero x hxO).mp
      simpa only [hρ1,one_mul] using hm
    · intro hx
      exact (hreq (hBW hx)).trans ((hfzero x (hBO hx)).mpr hx)
  have hrpositive : ∀ x, (𝓡∂ n).IsInteriorPoint x → 0 < r x := by
    intro x hx
    exact lt_of_le_of_ne (hrn x) (fun he =>
      ((𝓡∂ n).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx ((hrzero x).mp he.symm))
  refine ⟨r,⟨W,hW⟩,hr,hrn,hrzero,hrpositive,hBW,V,hV,hVc,?_,hpos⟩
  intro y hy
  have heq : r =ᶠ[𝓝 y] f := by
    filter_upwards [hW.mem_nhds hy] with z hz
    exact hreq hz
  have he : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) r y = mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y := heq.mfderiv_eq
  exact (congrArg (fun L : TangentSpace (𝓡∂ n) y →L[ℝ] ℝ => L (V y)) he).trans
    (hunit y (hclW (subset_closure hy)))

end DifferentialGeometry.Manifold.Boundary
