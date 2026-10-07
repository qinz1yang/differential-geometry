import DifferentialGeometry.Topology.Manifold.Quotient

open scoped ContDiff Manifold

theorem IsLocalDiffeomorph.exists_diffeomorph_of_fibers
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {H'' : Type*} [TopologicalSpace H'']
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
    {K : ModelWithCorners 𝕜 G H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {n : WithTop ℕ∞} {p : M → N} {q : M → P}
    (hp : IsLocalDiffeomorph I J n p) (hs : Function.Surjective p)
    (hq : IsLocalDiffeomorph I K n q) (ht : Function.Surjective q)
    (hfib : ∀ x y, p x = p y ↔ q x = q y) :
    ∃ D : Diffeomorph J K N P n,
      (∀ x, D (p x) = q x) ∧ ∀ x, D.symm (q x) = p x := by
  classical
  let r : N → M := Function.surjInv hs
  let f : N → P := q ∘ r
  have hcomm (x : M) : f (p x) = q x :=
    (hfib (r (p x)) x).mp (Function.surjInv_eq hs (p x))
  have hf : Function.Bijective f := by
    constructor
    · intro y z hyz
      have heq := (hfib (r y) (r z)).mpr hyz
      simpa only [r, Function.surjInv_eq] using heq
    · intro z
      obtain ⟨x, rfl⟩ := ht z
      exact ⟨p x, hcomm x⟩
  let e : N ≃ P := Equiv.ofBijective f hf
  have he (x : M) : e (p x) = q x := hcomm x
  have hei (x : M) : e.symm (q x) = p x := by
    rw [← he x]
    exact e.symm_apply_apply (p x)
  let D : Diffeomorph J K N P n :=
    { toEquiv := e
      contMDiff_toFun := hp.contMDiff_of_comp_of_surjective hs
        (hq.contMDiff.congr he)
      contMDiff_invFun := hq.contMDiff_of_comp_of_surjective ht
        (hp.contMDiff.congr hei) }
  exact ⟨D, he, hei⟩
