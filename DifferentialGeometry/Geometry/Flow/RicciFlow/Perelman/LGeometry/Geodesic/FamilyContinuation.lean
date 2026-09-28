import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.PhaseFamily
import DifferentialGeometry.Geometry.Curve.VelocityFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology
variable {A E H M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
 {D : RealTimeInterval}

theorem exists_lRegularizedGeodesicFamily_extension_to_time
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {α : A × ℝ → M} {V : Set A} {J₀ : Set ℝ} {a0 : A} {s0 b : ℝ}
    (hV : IsOpen V) (ha0 : a0 ∈ V) (hJ₀ : IsOpen J₀) (hconn₀ : IsPreconnected J₀) (hs0J₀ : s0 ∈ J₀)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ J₀))
    (hcurves : ∀ a ∈ V, IsLRegularizedGeodesicOn S T (fun s => α (a, s)) J₀)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hconn : IsPreconnected J) (hs0J : s0 ∈ J) (hbJ : b ∈ J)
    (hγ : IsLRegularizedGeodesicOn S T γ J)
    (hcenter : (fun r => α (a0, r)) =ᶠ[𝓝 s0] γ) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ J₀ ⊆ K ∧ b ∈ K ∧
        ∃ β : A × ℝ → M,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ K) ∧
          EqOn β α (U ×ˢ J₀) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) K) ∧
          EqOn (fun r => β (a0, r)) γ (K ∩ J) := by
  classical
  let ζ : A → TangentBundle I M := fun a => ⟨α (a, s0), lVelocity (I := I) (fun r => α (a, r)) s0⟩
  have hζ : ContMDiffOn 𝓘(ℝ, A) I.tangent ∞ ζ V :=
    (DifferentialGeometry.Geometry.contMDiffOn_curve_velocity_family hV hJ₀ hα).comp
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun a ha => ⟨ha, hs0J₀⟩)
  have hpos : γ s0 = (ζ a0).proj := hcenter.self_of_nhds.symm
  have hvel : lVelocity (I := I) γ s0 = (ζ a0).2 := by
    unfold lVelocity
    exact (congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ))
      (hcenter.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))).symm
  obtain ⟨U, hU, haU, hUV, K, hK, hKconn, hsK, hbK, η, hη, hηdata, hηcenter⟩ :=
    exists_lRegularizedGeodesicFamily_to_time_of_smooth_phase S hS T hV ha0 ζ hζ hJ hconn hs0J hbJ hpos hvel hγ
  have hmatch (a : A) (ha : a ∈ U) : EqOn (fun s => α (a, s)) (fun s => η (a, s)) (J₀ ∩ K) :=
    lRegularizedSolution_eqOn S hS T hJ₀ hconn₀ hs0J₀ hK hKconn hsK
      (hcurves a (hUV ha)) (hηdata a ha).2.2 (hηdata a ha).1.symm (hηdata a ha).2.1.symm
  let β : A × ℝ → M := fun p => if p.2 ∈ J₀ then α p else η p
  have hβα (p : A × ℝ) (hp : p.2 ∈ J₀) : β =ᶠ[𝓝 p] α := by
    filter_upwards [(hJ₀.preimage continuous_snd).mem_nhds hp] with q hq
    exact ite_eq_left hq
  have hβη (p : A × ℝ) (hp : p ∈ U ×ˢ K) : β =ᶠ[𝓝 p] η := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp.1,
      (hK.preimage continuous_snd).mem_nhds hp.2] with q hqU hqK
    dsimp only [β]
    split_ifs with hqJ
    · exact hmatch q.1 hqU ⟨hqJ, hqK⟩
    · rfl
  have hβ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ (J₀ ∪ K)) := by
    intro p hp
    rcases hp.2 with hpJ | hpK
    · exact (((hα p ⟨hUV hp.1, hpJ⟩).contMDiffAt
        ((hV.prod hJ₀).mem_nhds ⟨hUV hp.1, hpJ⟩)).congr_of_eventuallyEq (hβα p hpJ)).contMDiffWithinAt
    · exact (((hη p ⟨hp.1, hpK⟩).contMDiffAt
        ((hU.prod hK).mem_nhds ⟨hp.1, hpK⟩)).congr_of_eventuallyEq (hβη p ⟨hp.1, hpK⟩)).contMDiffWithinAt
  have hβgeo (a : A) (ha : a ∈ U) : IsLRegularizedGeodesicOn S T (fun r => β (a, r)) (J₀ ∪ K) := by
    intro s hs
    rcases hs with hsJ | hsK
    · have heq : (fun r => β (a, r)) =ᶠ[𝓝 s] (fun r => α (a, r)) := by
        filter_upwards [hJ₀.mem_nhds hsJ] with r hr
        exact ite_eq_left hr
      exact lRegularizedData_congr S T s heq (hcurves a (hUV ha) s hsJ)
    · have heq : (fun r => β (a, r)) =ᶠ[𝓝 s] (fun r => η (a, r)) := by
        filter_upwards [hK.mem_nhds hsK] with r hr
        dsimp only [β]
        split_ifs with hrJ
        · exact hmatch a ha ⟨hrJ, hr⟩
        · rfl
      exact lRegularizedData_congr S T s heq ((hηdata a ha).2.2 s hsK)
  refine ⟨U, hU, haU, hUV, J₀ ∪ K, hJ₀.union hK,
    hconn₀.union s0 hs0J₀ hsK hKconn, subset_union_left, Or.inr hbK, β, hβ,
    (fun p hp => ite_eq_left hp.2), hβgeo, ?_⟩
  apply lRegularizedSolution_eqOn S hS T (hJ₀.union hK)
    (hconn₀.union s0 hs0J₀ hsK hKconn) (Or.inl hs0J₀) hJ hconn hs0J (hβgeo a0 haU) hγ
  · exact (show β (a0, s0) = α (a0, s0) from ite_eq_left hs0J₀).trans hcenter.self_of_nhds
  · have heq : (fun r => β (a0, r)) =ᶠ[𝓝 s0] γ := by
      filter_upwards [hJ₀.mem_nhds hs0J₀, hcenter] with r hr hrc
      exact (ite_eq_left hr).trans hrc
    exact congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ))
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))

theorem exists_lRegularizedGeodesicFamily_extension_from_boundary
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {α : A × ℝ → M} {V : Set A} {J₀ : Set ℝ} {a0 : A} {w s0 b e : ℝ}
    (hV : IsOpen V) (ha0 : a0 ∈ V) (hJ₀ : IsOpen J₀) (hconn₀ : IsPreconnected J₀)
    (hwJ₀ : w ∈ J₀) (hs0J₀ : s0 ∈ J₀) (hs0 : s0 ∈ Ioo w e) (hb : b ∈ Ioo w e)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ J₀))
    (hcurves : ∀ a ∈ V, IsLRegularizedGeodesicOn S T (fun s => α (a, s)) (J₀ ∩ Ioo w e))
    {γ : ℝ → M} (hγ : IsLRegularizedGeodesicOn S T γ (Ioo w e))
    (hcenter : EqOn (fun r => α (a0, r)) γ (J₀ ∩ Icc w e)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ w ∈ K ∧ b ∈ K ∧
        ∃ β : A × ℝ → M,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ K) ∧
          EqOn β α (U ×ˢ (J₀ ∩ Iio e)) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) (K ∩ Ioo w e)) ∧
          EqOn (fun r => β (a0, r)) γ (K ∩ Icc w e) := by
  classical
  let J₁ := J₀ ∩ Ioo w e
  have hJ₁ : IsOpen J₁ := hJ₀.inter isOpen_Ioo
  have hconn₁ : IsPreconnected J₁ := (hconn₀.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hsJ₁ : s0 ∈ J₁ := ⟨hs0J₀, hs0⟩
  have hcenterGerm : (fun r => α (a0, r)) =ᶠ[𝓝 s0] γ :=
    (hcenter.mono (by intro r hr; exact ⟨hr.1, hr.2.1.le, hr.2.2.le⟩)).eventuallyEq_of_mem
      (hJ₁.mem_nhds hsJ₁)
  obtain ⟨U, hU, haU, hUV, C, hC, hconnC, hJ₁C, hbC, η, hη, hηeq, hηgeo, hηcenter⟩ :=
    exists_lRegularizedGeodesicFamily_extension_to_time S hS T hV ha0 hJ₁ hconn₁ hsJ₁
      (hα.mono (prod_mono subset_rfl inter_subset_left)) hcurves
      isOpen_Ioo isPreconnected_Ioo hs0 hb hγ hcenterGerm
  let O := J₀ ∩ Iio e
  let C₁ := C ∩ Ioo w e
  have hO : IsOpen O := hJ₀.inter isOpen_Iio
  have hC₁ : IsOpen C₁ := hC.inter isOpen_Ioo
  have hconnO : IsPreconnected O := (hconn₀.ordConnected.inter ordConnected_Iio).isPreconnected
  have hconnC₁ : IsPreconnected C₁ := (hconnC.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hsO : s0 ∈ O := ⟨hs0J₀, hs0.2⟩
  have hsC₁ : s0 ∈ C₁ := ⟨hJ₁C hsJ₁, hs0⟩
  have hmatch (a : A) (ha : a ∈ U) (r : ℝ) (hr : r ∈ O ∩ C₁) : α (a, r) = η (a, r) :=
    (hηeq ⟨ha, hr.1.1, hr.2.2⟩).symm
  let β : A × ℝ → M := fun p => if p.2 ∈ O then α p else η p
  have hβα (p : A × ℝ) (hp : p.2 ∈ O) : β =ᶠ[𝓝 p] α := by
    filter_upwards [(hO.preimage continuous_snd).mem_nhds hp] with q hq
    exact ite_eq_left hq
  have hβη (p : A × ℝ) (hp : p ∈ U ×ˢ C₁) : β =ᶠ[𝓝 p] η := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp.1,
      (hC₁.preimage continuous_snd).mem_nhds hp.2] with q hqU hqC
    dsimp only [β]
    split_ifs with hqO
    · exact hmatch q.1 hqU q.2 ⟨hqO, hqC⟩
    · rfl
  have hβ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ (O ∪ C₁)) := by
    intro p hp
    rcases hp.2 with hpO | hpC
    · exact (((hα p ⟨hUV hp.1, hpO.1⟩).contMDiffAt
        ((hV.prod hJ₀).mem_nhds ⟨hUV hp.1, hpO.1⟩)).congr_of_eventuallyEq (hβα p hpO)).contMDiffWithinAt
    · exact (((hη p ⟨hp.1, hpC.1⟩).contMDiffAt
        ((hU.prod hC).mem_nhds ⟨hp.1, hpC.1⟩)).congr_of_eventuallyEq (hβη p ⟨hp.1, hpC⟩)).contMDiffWithinAt
  refine ⟨U, hU, haU, hUV, O ∪ C₁, hO.union hC₁,
    hconnO.union s0 hsO hsC₁ hconnC₁, Or.inl ⟨hwJ₀, hs0.1.trans hs0.2⟩,
    Or.inr ⟨hbC, hb⟩, β, hβ, (fun p hp => ite_eq_left hp.2), ?_, ?_⟩
  · intro a ha r hr
    rcases hr.1 with hrO | hrC
    · have heq : (fun s => β (a, s)) =ᶠ[𝓝 r] (fun s => α (a, s)) := by
        filter_upwards [hO.mem_nhds hrO] with q hq
        exact ite_eq_left hq
      exact lRegularizedData_congr S T r heq (hcurves a (hUV ha) r ⟨hrO.1, hr.2⟩)
    · have heq : (fun s => β (a, s)) =ᶠ[𝓝 r] (fun s => η (a, s)) := by
        filter_upwards [hC₁.mem_nhds hrC] with q hq
        dsimp only [β]
        split_ifs with hqO
        · exact hmatch a ha q ⟨hqO, hq⟩
        · rfl
      exact lRegularizedData_congr S T r heq (hηgeo a ha r hrC.1)
  · intro r hr
    by_cases hrO : r ∈ O
    · exact (show β (a0, r) = α (a0, r) from ite_eq_left hrO).trans (hcenter ⟨hrO.1, hr.2⟩)
    · have hrC : r ∈ C₁ := hr.1.resolve_left hrO
      exact (show β (a0, r) = η (a0, r) from ite_eq_right hrO).trans (hηcenter ⟨hrC.1, hrC.2⟩)

theorem exists_lRegularizedGeodesicFamily_extension_to_boundary
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {α : A × ℝ → M} {V : Set A} {J₀ : Set ℝ} {a0 : A} {w c s0 e : ℝ}
    (hV : IsOpen V) (ha0 : a0 ∈ V) (hJ₀ : IsOpen J₀) (hconn₀ : IsPreconnected J₀)
    (hwJ₀ : w ∈ J₀) (hs0J₀ : s0 ∈ J₀) (hwc : w ≤ c) (hcs0 : c < s0) (hs0e : s0 < e)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ J₀))
    (hcurves : ∀ a ∈ V, IsLRegularizedGeodesicOn S T (fun s => α (a, s)) (J₀ ∩ Ioo w e))
    {γ τ : ℝ → M} {W : Set ℝ} (hW : IsOpen W) (htail : Icc c e ⊆ W)
    (hτ : IsLRegularizedGeodesicOn S T τ W)
    (hτγ : EqOn τ γ (Icc c e))
    (hcenter : EqOn (fun r => α (a0, r)) γ (J₀ ∩ Icc w e)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ w ∈ K ∧ e ∈ K ∧
        ∃ β : A × ℝ → M,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ K) ∧
          EqOn β α (U ×ˢ (J₀ ∩ Iio e)) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) (K ∩ Ioi w)) ∧
          EqOn (fun r => β (a0, r)) γ (K ∩ Icc w e) := by
  classical
  have hs0 : s0 ∈ Ioo w e := ⟨hwc.trans_lt hcs0, hs0e⟩
  have hce : c < e := hcs0.trans hs0e
  obtain ⟨l, d, heI, hId⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hW.mem_nhds (htail ⟨hce.le, le_rfl⟩))
  have hJtail : Ioo c d ⊆ W := by
    intro r hr
    by_cases hre : r ≤ e
    · exact htail ⟨hr.1.le, hre⟩
    · exact hId ⟨heI.1.trans (lt_of_not_ge hre), hr.2⟩
  let J₁ := J₀ ∩ Ioo w e
  have hJ₁ : IsOpen J₁ := hJ₀.inter isOpen_Ioo
  have hconn₁ : IsPreconnected J₁ := (hconn₀.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hsJ₁ : s0 ∈ J₁ := ⟨hs0J₀, hs0⟩
  have hcenterGerm : (fun r => α (a0, r)) =ᶠ[𝓝 s0] τ := by
    filter_upwards [hJ₀.mem_nhds hs0J₀, Icc_mem_nhds hcs0 hs0e] with r hrJ hr
    exact (hcenter ⟨hrJ, hwc.trans hr.1, hr.2⟩).trans (hτγ hr).symm
  obtain ⟨U, hU, haU, hUV, C, hC, hconnC, hJ₁C, heC, η, hη, hηeq, hηgeo, hηcenter⟩ :=
    exists_lRegularizedGeodesicFamily_extension_to_time S hS T hV ha0 hJ₁ hconn₁ hsJ₁
      (hα.mono (prod_mono subset_rfl inter_subset_left)) hcurves
      isOpen_Ioo isPreconnected_Ioo ⟨hcs0, hs0e.trans heI.2⟩ ⟨hce, heI.2⟩
      (fun r hr => hτ r (hJtail hr)) hcenterGerm
  let O := J₀ ∩ Iio e
  let C₁ := C ∩ Ioo c d
  have hO : IsOpen O := hJ₀.inter isOpen_Iio
  have hC₁ : IsOpen C₁ := hC.inter isOpen_Ioo
  have hconnO : IsPreconnected O := (hconn₀.ordConnected.inter ordConnected_Iio).isPreconnected
  have hconnC₁ : IsPreconnected C₁ := (hconnC.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hsO : s0 ∈ O := ⟨hs0J₀, hs0.2⟩
  have hsC₁ : s0 ∈ C₁ := ⟨hJ₁C hsJ₁, hcs0, hs0e.trans heI.2⟩
  have hmatch (a : A) (ha : a ∈ U) (r : ℝ) (hr : r ∈ O ∩ C₁) : α (a, r) = η (a, r) :=
    (hηeq (x := (a, r)) ⟨ha, hr.1.1, hwc.trans_lt hr.2.2.1, hr.1.2⟩).symm
  let β : A × ℝ → M := fun p => if p.2 ∈ O then α p else η p
  have hβα (p : A × ℝ) (hp : p.2 ∈ O) : β =ᶠ[𝓝 p] α := by
    filter_upwards [(hO.preimage continuous_snd).mem_nhds hp] with q hq
    exact ite_eq_left hq
  have hβη (p : A × ℝ) (hp : p ∈ U ×ˢ C₁) : β =ᶠ[𝓝 p] η := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp.1,
      (hC₁.preimage continuous_snd).mem_nhds hp.2] with q hqU hqC
    dsimp only [β]
    split_ifs with hqO
    · exact hmatch q.1 hqU q.2 ⟨hqO, hqC⟩
    · rfl
  have hβ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ (O ∪ C₁)) := by
    intro p hp
    rcases hp.2 with hpO | hpC
    · exact (((hα p ⟨hUV hp.1, hpO.1⟩).contMDiffAt
        ((hV.prod hJ₀).mem_nhds ⟨hUV hp.1, hpO.1⟩)).congr_of_eventuallyEq (hβα p hpO)).contMDiffWithinAt
    · exact (((hη p ⟨hp.1, hpC.1⟩).contMDiffAt
        ((hU.prod hC).mem_nhds ⟨hp.1, hpC.1⟩)).congr_of_eventuallyEq (hβη p ⟨hp.1, hpC⟩)).contMDiffWithinAt
  refine ⟨U, hU, haU, hUV, O ∪ C₁, hO.union hC₁,
    hconnO.union s0 hsO hsC₁ hconnC₁, Or.inl ⟨hwJ₀, hs0.1.trans hs0.2⟩,
    Or.inr ⟨heC, hce, heI.2⟩, β, hβ, (fun p hp => ite_eq_left hp.2), ?_, ?_⟩
  · intro a ha r hr
    rcases hr.1 with hrO | hrC
    · have heq : (fun s => β (a, s)) =ᶠ[𝓝 r] (fun s => α (a, s)) := by
        filter_upwards [hO.mem_nhds hrO] with q hq
        exact ite_eq_left hq
      exact lRegularizedData_congr S T r heq (hcurves a (hUV ha) r ⟨hrO.1, hr.2, hrO.2⟩)
    · have heq : (fun s => β (a, s)) =ᶠ[𝓝 r] (fun s => η (a, s)) := by
        filter_upwards [hC₁.mem_nhds hrC] with q hq
        dsimp only [β]
        split_ifs with hqO
        · exact hmatch a ha q ⟨hqO, hq⟩
        · rfl
      exact lRegularizedData_congr S T r heq (hηgeo a ha r hrC.1)
  · intro r hr
    by_cases hrO : r ∈ O
    · exact (show β (a0, r) = α (a0, r) from ite_eq_left hrO).trans (hcenter ⟨hrO.1, hr.2⟩)
    · have hrC : r ∈ C₁ := hr.1.resolve_left hrO
      exact (show β (a0, r) = η (a0, r) from ite_eq_right hrO).trans
        ((hηcenter ⟨hrC.1, hrC.2⟩).trans (hτγ ⟨hrC.2.1.le, hr.2.2⟩))

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
