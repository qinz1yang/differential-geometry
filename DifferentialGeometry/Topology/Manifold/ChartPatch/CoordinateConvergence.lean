import DifferentialGeometry.Topology.Manifold.ChartPatch.ProtectedGerms
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Bilinear
import DifferentialGeometry.Analysis.Calculus.MapConvergence.SupportedProduct

import DifferentialGeometry.Analysis.Calculus.MapConvergence.ChartTransition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteLocality

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.CheegerGromovCompactness

theorem exists_fixed_cutoff_chart_patch_with_coordinate_convergence
    {E F H G X α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace X] [ChartedSpace H X] [T2Space X]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {p : ℕ} [IsManifold I p X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace G (Y i)]
    {A W T P : Set X}
    (hA : IsOpen A) (hW : IsOpen W) (hT : IsOpen T)
    (hcompact : IsCompact (closure W)) (hcover : closure W ⊆ A ∪ T)
    (hP : IsCompact P) (hPA : P ⊆ A) (hPW : P ⊆ W)
    (f : ∀ i, X → Y i) (b : ∀ i, Y i) (q : X → F)
    (hf : ∀ᶠ i in atTop, ContMDiffOn I J p (f i) A)
    (hq : ContMDiffOn I 𝓘(ℝ, F) p q (W ∩ T))
    (e : ∀ i, OpenPartialHomeomorph F (Y i))
    (he : ∀ i, ContMDiffOn 𝓘(ℝ, F) J p (e i) (e i).source)
    (heinv : ∀ i, ContMDiffOn J 𝓘(ℝ, F) p (e i).symm (e i).target)
    {D : Set F} (hD : Convex ℝ D) (hDe : ∀ i, D ⊆ (e i).source)
    (hqD : MapsTo q (W ∩ T) D)
    (hfD : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
      f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ D)
    (σ : α → E → X) (U : α → Set E) (hU : ∀ a, IsOpen (U a))
    (hσ : ∀ a, ContMDiffOn 𝓘(ℝ, E) I p (σ a) (U a))
    (hconv : ∀ a (L : Set E), IsCompact L → L ⊆ U a ∩ (σ a) ⁻¹' (W ∩ T ∩ A) →
      MapCPConvergenceOn L p (fun i x ↦ (e i).symm (f i (σ a x))) (q ∘ σ a)) :
    ∃ χ : X → ℝ, ∃ g : ∀ i, X → Y i,
      ContMDiff I 𝓘(ℝ, ℝ) p χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ A ∧
      W ∩ tsupport (fun x ↦ 1 - χ x) ⊆ T ∧
      χ =ᶠ[𝓝ˢ P] 1 ∧ (∀ i, ContMDiffOn I J p (g i) W) ∧
      (∀ᶠ i in atTop,
        EqOn (g i) (f i) (W \ T) ∧
        (∀ x ∈ P, g i =ᶠ[𝓝 x] f i) ∧
        EqOn (g i) (f i) (W ∩ {x | χ x = 1}) ∧
        EqOn (g i) (e i ∘ q) (W ∩ {x | χ x = 0}) ∧
        MapsTo (g i) (W ∩ T) (e i).target ∧
        (∀ x ∈ W ∩ T,
          g i x = e i (q x + χ x • ((e i).symm (f i x) - q x))) ∧
        (∀ x ∈ W ∩ T,
          (e i).symm (g i x) = q x + χ x • ((e i).symm (f i x) - q x))) ∧
      ∀ a (L : Set E), IsCompact L → L ⊆ U a ∩ (σ a) ⁻¹' (W ∩ T) →
        MapCPConvergenceOn L p (fun i x ↦ (e i).symm (g i (σ a x))) (q ∘ σ a) := by
  obtain ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, htail⟩ :=
    exists_fixed_cutoff_eventually_chart_patch_preserving_germs
      (p := (p : ℕ∞)) hA hW hT hcompact hcover hP hPA hPW
      f b q hf hq e he heinv hD hDe hqD hfD
  refine ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, htail, ?_⟩
  intro a L hL hLU
  have hsupp (x : E) (hx : x ∈ L ∩ tsupport (χ ∘ σ a)) : σ a x ∈ tsupport χ := by
    by_contra hn
    have hzero : (χ ∘ σ a) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        ((hσ a).contMDiffAt ((hU a).mem_nhds (hLU hx.1).1)).continuousAt
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx.2
  have hcoord : MapCPConvergenceOn (L ∩ tsupport (χ ∘ σ a)) p
      (fun i x ↦ (e i).symm (f i (σ a x))) (q ∘ σ a) :=
    hconv a _ (hL.inter_right (isClosed_tsupport _))
      (fun x hx ↦ ⟨(hLU hx.1).1, (hLU hx.1).2, hχA (hsupp x hx)⟩)
  have hδconv : MapCPConvergenceOn (L ∩ tsupport (χ ∘ σ a)) p
      (fun i x ↦ (e i).symm (f i (σ a x)) - q (σ a x)) (fun _ ↦ 0) := by
    simpa only [MapCPConvergenceOn, mapDerivNorm, Function.comp_apply, sub_zero] using hcoord
  have hχσ : ∀ x ∈ L ∩ tsupport (χ ∘ σ a), ContDiffAt ℝ p (χ ∘ σ a) x := by
    intro x hx
    have hσx := (hσ a).contMDiffAt ((hU a).mem_nhds (hLU hx.1).1)
    simpa only [WithTop.coe_natCast] using (hχ.contMDiffAt.comp x hσx).contDiffAt
  have hδ : ∀ᶠ i in atTop, ∀ x ∈ L ∩ tsupport (χ ∘ σ a),
      ContDiffAt ℝ p (fun x ↦ (e i).symm (f i (σ a x)) - q (σ a x)) x := by
    filter_upwards [hf, hfD] with i hi hiD x hx
    have hxA := hχA (hsupp x hx)
    have hxWT := (hLU hx.1).2
    have hσx := (hσ a).contMDiffAt ((hU a).mem_nhds (hLU hx.1).1)
    have hfi := hi.contMDiffAt (hA.mem_nhds hxA)
    have hei := (heinv i).contMDiffAt ((e i).open_target.mem_nhds
      (hiD (σ a x) ⟨hxWT, hxA⟩).1)
    have hqi := hq.contMDiffAt ((hW.inter hT).mem_nhds hxWT)
    simpa only [WithTop.coe_natCast, Function.comp_apply] using
      (((hei.comp (σ a x) hfi).comp x hσx).contDiffAt.sub
        (hqi.comp x hσx).contDiffAt)
  have hproduct := hδconv.supported_smul_of_eventually_contDiffAt
    (hL.inter_right (isClosed_tsupport _)) hχσ hδ
  have hformula : MapCPConvergenceOn L p
      (fun i x ↦ q (σ a x) + χ (σ a x) • ((e i).symm (f i (σ a x)) - q (σ a x)))
      (q ∘ σ a) := by
    simpa only [MapCPConvergenceOn, mapDerivNorm, Function.comp_apply,
      add_sub_cancel_left, sub_zero] using hproduct
  apply hformula.congr_eventually
    ((hσ a).continuousOn.isOpen_inter_preimage (hU a) (hW.inter hT)) hLU
  · filter_upwards [htail] with i hi x hx
    exact hi.2.2.2.2.2.2 (σ a x) hx.2
  · exact Set.eqOn_refl _ _

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

private theorem eventually_mapsTo_and_mapCPConvergenceOn_of_open_cover
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : ℕ → Type*} {U V K : Set E} {p : ℕ}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKUV : K ⊆ U ∪ V)
    (f : ∀ i, E → Y i) (d : ∀ i, Y i → F) (T : ∀ i, Set (Y i)) (fInf : E → F)
    (hleft : ∀ L : Set E, IsCompact L → L ⊆ U →
      (∀ᶠ i in atTop, MapsTo (f i) L (T i)) ∧
      MapCPConvergenceOn L p (fun i x ↦ d i (f i x)) fInf)
    (hright : ∀ L : Set E, IsCompact L → L ⊆ V →
      (∀ᶠ i in atTop, MapsTo (f i) L (T i)) ∧
      MapCPConvergenceOn L p (fun i x ↦ d i (f i x)) fInf) :
    (∀ᶠ i in atTop, MapsTo (f i) K (T i)) ∧
      MapCPConvergenceOn K p (fun i x ↦ d i (f i x)) fInf := by
  have hlocal : ∀ x ∈ K, ∃ N ∈ 𝓝 x,
      (∀ᶠ i in atTop, MapsTo (f i) (K ∩ N) (T i)) ∧
      MapCPConvergenceOn (K ∩ N) p (fun i x ↦ d i (f i x)) fInf := by
    intro x hx
    rcases hKUV hx with hxU | hxV
    · obtain ⟨N, hN, hclosed, hNU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
      exact ⟨N, hN, hleft (K ∩ N) (hK.inter_right hclosed)
        (inter_subset_right.trans hNU)⟩
    · obtain ⟨N, hN, hclosed, hNV⟩ := exists_mem_nhds_isClosed_subset (hV.mem_nhds hxV)
      exact ⟨N, hN, hright (K ∩ N) (hK.inter_right hclosed)
        (inter_subset_right.trans hNV)⟩
  refine ⟨?_, MapCPConvergenceOn.of_nhds hK ?_⟩
  · apply hK.induction_on (p := fun L ↦ ∀ᶠ i in atTop, MapsTo (f i) L (T i))
    · exact Eventually.of_forall fun _ _ hx ↦ hx.elim
    · intro s t hst ht
      exact ht.mono fun _ hi _ hx ↦ hi (hst hx)
    · intro s t hs ht
      filter_upwards [hs, ht] with i hiS hiT x hx
      exact hx.elim (fun hs ↦ hiS hs) (fun ht ↦ hiT ht)
    · intro x hx
      obtain ⟨N, hN, hmem, _⟩ := hlocal x hx
      exact ⟨K ∩ N, inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hN), hmem⟩
  · intro x hx
    obtain ⟨N, hN, _, hconv⟩ := hlocal x hx
    exact ⟨N, hN, hconv⟩

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.CheegerGromovCompactness

theorem exists_fixed_cutoff_chart_patch_preserving_chart_convergence
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [ChartedSpace E X] [T2Space X]
    {p : ℕ} [IsManifold 𝓘(ℝ, E) p X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    {A W T P : Set X}
    (hA : IsOpen A) (hW : IsOpen W) (hT : IsOpen T)
    (hcompact : IsCompact (closure W)) (hcover : closure W ⊆ A ∪ T)
    (hP : IsCompact P) (hPA : P ⊆ A) (hPW : P ⊆ W)
    (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X p)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) p)
    (a₀ : α) (hTσ : T ⊆ (σ a₀).target)
    (f : ∀ i, X → Y i)
    (hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (f i) A)
    {D : Set E} (hD : Convex ℝ D) (hDe : ∀ i, D ⊆ (d a₀ i).source)
    (hqD : MapsTo (σ a₀).symm (W ∩ T) D)
    (hfD : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
      f i x ∈ (d a₀ i).target ∧ (d a₀ i).symm (f i x) ∈ D)
    (hold : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' A →
      (∀ᶠ i in atTop, MapsTo (f i ∘ σ a) L (d a i).target) ∧
      MapCPConvergenceOn L p (fun i x ↦ (d a i).symm (f i (σ a x))) id)
    (htrans : ∀ a (L : Set E), IsCompact L → L ⊆ ((σ a).trans (σ a₀).symm).target →
      MapCPConvergenceOn L p (fun i x ↦ (d a i).symm (d a₀ i x))
        ((σ a).trans (σ a₀).symm).symm ∧
      ∀ᶠ i in atTop, L ⊆ ((d a₀ i).trans (d a i).symm).source) :
    ∃ χ : X → ℝ, ∃ g : ∀ i, X → Y i,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) p χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ A ∧
      W ∩ tsupport (fun x ↦ 1 - χ x) ⊆ T ∧
      χ =ᶠ[𝓝ˢ P] 1 ∧ (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (g i) W) ∧
      (∀ᶠ i in atTop,
        EqOn (g i) (f i) (W \ T) ∧
        (∀ x ∈ P, g i =ᶠ[𝓝 x] f i) ∧
        EqOn (g i) (f i) (W ∩ {x | χ x = 1}) ∧
        EqOn (g i) (d a₀ i ∘ (σ a₀).symm) (W ∩ {x | χ x = 0}) ∧
        MapsTo (g i) (W ∩ T) (d a₀ i).target ∧
        (∀ x ∈ W ∩ T, g i x = d a₀ i
          ((σ a₀).symm x + χ x • ((d a₀ i).symm (f i x) - (σ a₀).symm x))) ∧
        (∀ x ∈ W ∩ T, (d a₀ i).symm (g i x) =
          (σ a₀).symm x + χ x • ((d a₀ i).symm (f i x) - (σ a₀).symm x))) ∧
      ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
        (∀ᶠ i in atTop, MapsTo (g i ∘ σ a) L (d a i).target) ∧
        MapCPConvergenceOn L p (fun i x ↦ (d a i).symm (g i (σ a x))) id := by
  have hpre : ∀ a (L : Set E), IsCompact L →
      L ⊆ (σ a).source ∩ σ a ⁻¹' (W ∩ T ∩ A) →
      MapCPConvergenceOn L p (fun i x ↦ (d a₀ i).symm (f i (σ a x)))
        ((σ a₀).symm ∘ σ a) := by
    intro a L hL hLU
    exact (mapCPConvergenceOn_chart_inverse_comp_of_source_chart_convergence
      hA hL (σ a) (σ a₀)
      (fun x hx ↦ ⟨(hLU hx).1, (hLU hx).2.2, hTσ (hLU hx).2.1.2⟩)
      (d a₀) f hf (fun L hL hLA ↦ (hold a₀ L hL hLA).1)
      (fun L hL hLA ↦ (hold a₀ L hL hLA).2)).2
  obtain ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, htail, hnew⟩ :=
    exists_fixed_cutoff_chart_patch_with_coordinate_convergence
      hA hW hT hcompact hcover hP hPA hPW f (fun i ↦ d a₀ i 0) (σ a₀).symm hf
      ((σ a₀).contMDiffOn_invFun.mono (fun _ hx ↦ hTσ hx.2))
      (fun i ↦ (d a₀ i).toOpenPartialHomeomorph)
      (fun i ↦ (d a₀ i).contMDiffOn_toFun)
      (fun i ↦ (d a₀ i).contMDiffOn_invFun) hD hDe hqD hfD
      (fun a ↦ (σ a : E → X)) (fun a ↦ (σ a).source)
      (fun a ↦ (σ a).open_source) (fun a ↦ (σ a).contMDiffOn_toFun) hpre
  refine ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, htail, ?_⟩
  let O : Set X := W ∩ (tsupport (fun x ↦ 1 - χ x))ᶜ
  have hO : IsOpen O := hW.inter (isClosed_tsupport _).isOpen_compl
  have hχone (x : X) (hx : x ∈ O) : χ x = 1 := by
    have hzero : 1 - χ x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x ↦ 1 - χ x) hx.2
    exact (sub_eq_zero.mp hzero).symm
  have hOA : O ⊆ A := by
    intro x hx
    apply hχA
    apply subset_tsupport χ
    change χ x ≠ 0
    rw [hχone x hx]
    exact one_ne_zero
  have hagree : ∀ᶠ i in atTop, EqOn (g i) (f i) O := by
    filter_upwards [htail] with i hi x hx
    exact hi.2.2.1 ⟨hx.1, hχone x hx⟩
  intro a K hK hKW
  let U : Set E := (σ a).source ∩ σ a ⁻¹' (W ∩ T)
  let V : Set E := (σ a).source ∩ σ a ⁻¹' O
  have hU : IsOpen U :=
    (σ a).toOpenPartialHomeomorph.isOpen_inter_preimage (hW.inter hT)
  have hV : IsOpen V := (σ a).toOpenPartialHomeomorph.isOpen_inter_preimage hO
  have hKUV : K ⊆ U ∪ V := by
    intro x hx
    by_cases hxT : σ a x ∈ T
    · exact Or.inl ⟨(hKW hx).1, (hKW hx).2, hxT⟩
    · exact Or.inr ⟨(hKW hx).1, (hKW hx).2, fun hs ↦ hxT (hχT ⟨(hKW hx).2, hs⟩)⟩
  apply eventually_mapsTo_and_mapCPConvergenceOn_of_open_cover hU hV hK hKUV
    (fun i ↦ g i ∘ σ a) (fun i ↦ (d a i).symm) (fun i ↦ (d a i).target) id
  · intro L hL hLU
    apply mapCPConvergenceOn_chart_inverse_comp_of_partialDiffeomorph_transitions
      (hW.inter hT) hL (σ a) (σ a₀)
      (fun x hx ↦ ⟨(hLU hx).1, (hLU hx).2, hTσ (hLU hx).2.2⟩)
      (d a₀) (d a) g (fun i ↦ (hg i).mono inter_subset_left)
    · intro S hS hSD
      filter_upwards [htail] with i hi x hx
      exact hi.2.2.2.2.1 (hSD hx).2.1
    · intro S hS hSD
      exact hnew a S hS (fun x hx ↦ ⟨(hSD hx).1, (hSD hx).2.1⟩)
    · intro S hS hSD
      exact (htrans a S hS hSD).1
    · intro S hS hSD
      exact (htrans a S hS hSD).2
  · intro L hL hLV
    have hLA : L ⊆ (σ a).source ∩ σ a ⁻¹' A :=
      fun x hx ↦ ⟨(hLV hx).1, hOA (hLV hx).2⟩
    have hconv := hold a L hL hLA
    refine ⟨?_, hconv.2.congr_eventually hV hLV ?_ (Set.eqOn_refl _ _)⟩
    · filter_upwards [hconv.1, hagree] with i hi heq x hx
      change g i (σ a x) ∈ (d a i).target
      rw [heq (hLV hx).2]
      exact hi hx
    · filter_upwards [hagree] with i hi x hx
      exact congrArg (d a i).symm (hi hx.2)

end DifferentialGeometry.Topology.Manifold
