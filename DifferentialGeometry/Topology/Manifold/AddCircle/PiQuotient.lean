import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Pi
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.QuotientEquivalence

open scoped ContDiff Manifold

namespace AddCircle

theorem isLocalDiffeomorph_pi_coe {ι : Type*} [Fintype ι] :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ)
      (ModelWithCorners.pi (fun _ : ι => 𝓘(ℝ, ℝ))) ∞
      (fun x : ι → ℝ => fun i => (x i : AddCircle (1 : ℝ))) := by
  classical
  intro x
  choose d hd he using fun i : ι => isLocalDiffeomorph_coe (x i)
  let D : PartialDiffeomorph 𝓘(ℝ, ι → ℝ)
      (ModelWithCorners.pi (fun _ : ι => 𝓘(ℝ, ℝ)))
      (ι → ℝ) (ι → AddCircle (1 : ℝ)) ∞ :=
    { toPartialEquiv := PartialEquiv.pi (fun i => (d i).toPartialEquiv)
      open_source := isOpen_set_pi Set.finite_univ (fun i _ => (d i).open_source)
      open_target := isOpen_set_pi Set.finite_univ (fun i _ => (d i).open_target)
      contMDiffOn_toFun := by
        intro z hz
        apply contMDiffWithinAt_pi.mpr
        intro i
        exact ((d i).contMDiffOn_toFun.comp
          (s := Set.pi Set.univ (fun j => (d j).source))
          (contDiff_apply ℝ ℝ i).contMDiff.contMDiffOn
          (fun _ hy => hy i trivial)) z hz
      contMDiffOn_invFun := by
        intro z hz
        apply contMDiffWithinAt_pi_space.mpr
        intro i
        exact ((d i).contMDiffOn_invFun.comp
          (s := Set.pi Set.univ (fun j => (d j).target))
          (contMDiff_pi_apply (J := fun _ : ι => 𝓘(ℝ, ℝ)) i).contMDiffOn
          (fun _ hy => hy i trivial)) z hz }
  refine ⟨D, (fun i _ => hd i), ?_⟩
  intro y hy
  exact funext (fun i => he i (hy i trivial))

theorem exists_pi_diffeomorph_of_fibers
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    (q : (ι → ℝ) → S)
    (hq : IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) J ∞ q)
    (hs : Function.Surjective q)
    (hf : ∀ x y, q x = q y ↔
      (fun i => (x i : AddCircle (1 : ℝ))) =
        (fun i => (y i : AddCircle (1 : ℝ)))) :
    ∃ D : Diffeomorph (ModelWithCorners.pi (fun _ : ι => 𝓘(ℝ, ℝ))) J
        (ι → AddCircle (1 : ℝ)) S ∞,
      (∀ x, D (fun i => (x i : AddCircle (1 : ℝ))) = q x) ∧
      ∀ x, D.symm (q x) = fun i => (x i : AddCircle (1 : ℝ)) := by
  exact isLocalDiffeomorph_pi_coe.exists_diffeomorph_of_fibers
    (Function.Surjective.piMap (fun _ : ι => QuotientAddGroup.mk_surjective))
    hq hs (fun x y => (hf x y).symm)

theorem exists_pi_diffeomorph_of_integer_fibers
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    (q : (ι → ℝ) → S)
    (hq : IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) J ∞ q)
    (hs : Function.Surjective q)
    (hf : ∀ x y, q x = q y ↔ ∀ i, ∃ z : ℤ, x i - y i = (z : ℝ)) :
    ∃ D : Diffeomorph (ModelWithCorners.pi (fun _ : ι => 𝓘(ℝ, ℝ))) J
        (ι → AddCircle (1 : ℝ)) S ∞,
      (∀ x, D (fun i => (x i : AddCircle (1 : ℝ))) = q x) ∧
      ∀ x, D.symm (q x) = fun i => (x i : AddCircle (1 : ℝ)) := by
  apply exists_pi_diffeomorph_of_fibers q hq hs
  intro x y
  rw [hf, funext_iff]
  apply forall_congr'
  intro i
  rw [← sub_eq_zero, ← coe_sub, coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, eq_comm]

end AddCircle
