import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {m n : WithTop ℕ∞}

theorem ContMDiffAt.tangentMap_const_apply
    {f : N → M → M'} {x : N} (y : M) (v : TangentSpace I y)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (x, y))
    (hmn : m + 1 ≤ n) :
    ContMDiffAt J I'.tangent m
      (fun z => (⟨f z y, mfderiv I I' (f z) y v⟩ : TangentBundle I' M')) x := by
  have hbase : ContMDiffAt J I' m (fun z => f z y) x := by
    have h := (hf.of_le (le_trans (le_add_of_nonneg_right zero_le_one) hmn)).comp
      x (contMDiffAt_id.prodMk contMDiffAt_const)
    simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using h
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hbase, ?_⟩
  have hs := ContMDiffAt.mfderiv_apply (I := I) (I' := I') (J := J) (J' := J)
    (f := f) (g := fun _ : N => y) (g₁ := id) (g₂ := fun _ : N => v)
    (x₀ := x) hf contMDiffAt_const contMDiffAt_id contMDiffAt_const hmn
  apply hs.congr_of_eventuallyEq
  have hsrc := hbase.continuousAt.preimage_mem_nhds
    ((chartAt H' (f x y)).open_source.mem_nhds (mem_chart_source H' (f x y)))
  filter_upwards [hsrc] with z hz
  simp only [id_eq]
  rw [inTangentCoordinates_eq (I := I) (I' := I')
    (fun _ : N => y) (fun z => f z y)
    (fun z => mfderiv I I' (f z) y) (mem_chart_source H y) hz]
  change (trivializationAt E' (TangentSpace I') (f x y)
      (⟨f z y, mfderiv I I' (f z) y v⟩ : TangentBundle I' M')).2 =
    (tangentBundleCore I' M').coordChange (achart H' (f z y)) (achart H' (f x y))
      (f z y) (mfderiv I I' (f z) y
        ((tangentBundleCore I M).coordChange (achart H y) (achart H y) y v))
  rw [(tangentBundleCore I M).coordChange_self (achart H y) y (mem_chart_source H y) v]
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I')
    (b₀ := f x y) (b := f z y) hz]
  have hval : (trivializationAt E' (TangentSpace I') (f x y)).continuousLinearMapAt 𝕜
      (f z y) (mfderiv I I' (f z) y v) =
      (trivializationAt E' (TangentSpace I') (f x y)
        (⟨f z y, mfderiv I I' (f z) y v⟩ : TangentBundle I' M')).2 := by
    rw [(trivializationAt E' (TangentSpace I') (f x y)).continuousLinearMapAt_apply (R := 𝕜),
      (trivializationAt E' (TangentSpace I') (f x y)).coe_linearMapAt_of_mem hz]
  exact hval.symm

theorem ContMDiff.tangentMap_const_apply
    {f : N → M → M'} (hf : ContMDiff (J.prod I) I' n (Function.uncurry f))
    (y : M) (v : TangentSpace I y) (hmn : m + 1 ≤ n) :
    ContMDiff J I'.tangent m
      (fun z => (⟨f z y, mfderiv I I' (f z) y v⟩ : TangentBundle I' M')) := by
  intro x
  exact hf.contMDiffAt.tangentMap_const_apply y v hmn
