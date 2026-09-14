import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SmoothRegularLoopFamily
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem rfs_csf_immersed_area_of_embedded_area_of_generic_curves
    (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hEmbedded : ∀ {a b : ℝ} (B' : RicciBackground (I := I) (M := M) D a b)
        (_ : Module.finrank ℝ E = 3) (γ' : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ').SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ').ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ' t)) →
      (∀ t ∈ Icc a b, Topology.IsEmbedding (γ' t)) →
      ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B'.family.metric γ' (t + h) -
            loopFamilyLeastArea B'.family.metric γ' t) / h ≤
          -2 * Real.pi - scalarMinimum B'.family t *
              loopFamilyLeastArea B'.family.metric γ' t / 2 +
            (curveOfLoopFamily γ').areaError B'.family.metric (Icc a b) t + ε)
    (hGeneric : ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError B.family.metric (Icc a b) t -
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t| < ε) ∧
      ((∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
          |loopFamilyLeastArea B.family.metric (approximants j) t -
            loopFamilyLeastArea B.family.metric γ t| < ε)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  let restrict : ∀ {a' b' : ℝ}, a ≤ a' → a' < b' → b' ≤ b →
      RicciBackground (I := I) (M := M) D a' b' := fun {a' b'} ha' hlt hb' =>
    { family := B.family, smooth := B.smooth, lt := hlt,
      regular := fun t ht => B.regular ⟨le_trans ha' ht.1, le_trans ht.2 hb'⟩,
      equation := B.equation, B₀ := B.B₀, B₁ := B.B₁, B₂ := B.B₂,
      B₀_nonneg := B.B₀_nonneg, B₁_nonneg := B.B₁_nonneg, B₂_nonneg := B.B₂_nonneg,
      ricci_bound := fun t ht p => B.ricci_bound t ⟨le_trans ha' ht.1, le_trans ht.2 hb'⟩ p,
      riemann_bound := fun t ht p =>
        B.riemann_bound t ⟨le_trans ha' ht.1, le_trans ht.2 hb'⟩ p,
      nablaRicci_bound := fun t ht p =>
        B.nablaRicci_bound t ⟨le_trans ha' ht.1, le_trans ht.2 hb'⟩ p }
  obtain ⟨app, happ, hconv, herr, hcl⟩ :=
    hGeneric
  obtain ⟨hctrApp, hAconv⟩ := hcl hctr
  choose exc hexc using fun j => (happ j).2.2
  have hAj : ∀ j : ℕ,
      ContinuousOn (loopFamilyLeastArea B.family.metric (app j)) (Icc a b) := fun j =>
    continuousOn_loopFamilyLeastArea_of_smoothOn (I := I) (M := M) B (app j) (happ j).1
      (fun t ht => hctrApp j t ht)
  have hdini : ∀ j : ℕ, ∀ v ∈ Ioo a b, v ∉ exc j → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ b →
      (loopFamilyLeastArea B.family.metric (app j) (v + h) -
          loopFamilyLeastArea B.family.metric (app j) v) / h ≤
        -2 * Real.pi - scalarMinimum B.family v *
            loopFamilyLeastArea B.family.metric (app j) v / 2 +
          (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v + ε := by
    intro j v hv hvexc ε hε
    have hclosed : IsClosed ((exc j : Set ℝ)) := (exc j).finite_toSet.isClosed
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
      Metric.mem_nhds_iff.mp ((hclosed.isOpen_compl).mem_nhds (by simpa using hvexc))
    set a' : ℝ := max a (v - δ₀ / 2) with ha'def
    set b' : ℝ := min b (v + δ₀ / 2) with hb'def
    have ha_le : a ≤ a' := le_max_left _ _
    have hb'_le : b' ≤ b := min_le_left _ _
    have hva' : a' < v := by
      rw [ha'def, max_lt_iff]
      exact ⟨hv.1, by linarith [hδ₀pos]⟩
    have hvb' : v < b' := by
      rw [hb'def, lt_min_iff]
      exact ⟨hv.2, by linarith [hδ₀pos]⟩
    have ha'b' : a' < b' := lt_trans hva' hvb'
    have hmem_ball : ∀ t ∈ Icc a' b', t ∈ Metric.ball v δ₀ := by
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      refine ⟨?_, ?_⟩
      · have h1 : v - δ₀ < a' := by
          rw [ha'def, lt_max_iff]
          exact Or.inr (by linarith)
        linarith [ht.1]
      · have h1 : b' < v + δ₀ := by
          rw [hb'def, min_lt_iff]
          exact Or.inr (by linarith)
        linarith [ht.2]
    have hemb' : ∀ t ∈ Icc a' b', Topology.IsEmbedding (app j t) := by
      intro t ht
      refine hexc j t ⟨le_trans ha_le ht.1, le_trans ht.2 hb'_le⟩ ?_
      exact fun hc => hδ₀ (hmem_ball t ht) hc
    have hnhd' : Icc a' b' ∈ 𝓝 v := Icc_mem_nhds hva' hvb'
    have hnhd : Icc a b ∈ 𝓝 v := Icc_mem_nhds hv.1 hv.2
    let hB' : RicciBackground (I := I) (M := M) D a' b' := restrict ha_le ha'b' hb'_le
    have hfam : hB'.family = B.family := rfl
    have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha_le hb'_le
    have hγ' : (curveOfLoopFamily (app j)).SmoothOn (I := I) (Icc a' b') :=
      (happ j).1.mono (Set.prod_mono (subset_univ _) hsub)
    have hi' : (curveOfLoopFamily (app j)).ImmersedOn (I := I) (Icc a' b') :=
      fun x t ht => (happ j).2.1 x t (hsub ht)
    have hctr' : ∀ t ∈ Icc a' b', IsContractibleLoop (app j t) :=
      fun t ht => hctrApp j t (hsub ht)
    have hvel : ∀ x : ℝ, (curveOfLoopFamily (app j)).velocity (I := I) (Icc a' b') x v =
        (curveOfLoopFamily (app j)).velocity (I := I) (Icc a b) x v := by
      intro x
      simp only [CurveMap.velocity]
      rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I) hnhd',
        mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I) hnhd]
    have hErr : (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a' b') v =
        (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v := by
      simp only [CurveMap.areaError, CurveMap.integral]
      refine intervalIntegral.integral_congr fun x _ => ?_
      have hnv : (curveOfLoopFamily (app j)).normalVelocityError B.family.metric
            (Icc a' b') x v =
          (curveOfLoopFamily (app j)).normalVelocityError B.family.metric (Icc a b) x v := by
        simp only [CurveMap.normalVelocityError, hvel x]
      simp only [CurveMap.normSq, hnv]
    have hres := hEmbedded hB' hdim (app j) hγ' hi' hctr' hemb'
    have hv' : v ∈ Ico a' b' := ⟨hva'.le, hvb'⟩
    obtain ⟨δ, hδpos, hδ⟩ := hres v hv' ε hε
    refine ⟨min δ (b' - v), lt_min hδpos (sub_pos.mpr hvb'), fun h hh hb => ?_⟩
    have hhδ : h < δ := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have hhb' : h < b' - v := lt_of_lt_of_le hh.2 (min_le_right _ _)
    have hbbb : v + h ≤ b' := by linarith
    have h1 := hδ h ⟨hh.1, hhδ⟩ hbbb
    rw [hfam, hErr] at h1
    exact h1
  have hode : ∀ j : ℕ, ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      areaIntegratingFactor B.family s u * loopFamilyLeastArea B.family.metric (app j) u ≤
        loopFamilyLeastArea B.family.metric (app j) s +
          ∫ v in s..u, areaIntegratingFactor B.family s v *
            (-2 * Real.pi + (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) := by
    intro j s hs u hu
    have hst : s ≤ u := hu.1
    have hsub : Icc s u ⊆ Icc a b := Icc_subset_Icc hs.1 hu.2
    have hrho : ContinuousOn (fun w => scalarMinimum B.family w / 2) (Icc s u) :=
      ((RicciBackground.continuousOn_scalarMinimum B).div_const 2).mono hsub
    have hF : ContinuousOn (fun v => -2 * Real.pi +
        (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) (Icc s u) :=
      (continuousOn_const.add
        (continuousOn_loopFamily_areaError B (app j) (happ j).1 (happ j).2.1)).mono hsub
    have hDini : ∀ v ∈ Ico s u, v ∉ (insert a (exc j) : Finset ℝ) → ∀ ε > 0, ∃ δ > 0,
        ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ u →
          (loopFamilyLeastArea B.family.metric (app j) (v + h) -
              loopFamilyLeastArea B.family.metric (app j) v) / h ≤
            -(scalarMinimum B.family v / 2) * loopFamilyLeastArea B.family.metric (app j) v +
              (-2 * Real.pi +
                (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) + ε := by
      intro v hv hvexc ε hε
      have hva : a < v := by
        rcases lt_or_eq_of_le (le_trans hs.1 hv.1) with h | h
        · exact h
        · exact absurd (h ▸ Finset.mem_insert_self a (exc j)) hvexc
      have hvexc' : v ∉ exc j := fun hc => hvexc (Finset.mem_insert_of_mem hc)
      obtain ⟨δ, hδpos, hδ⟩ := hdini j v ⟨hva, lt_of_lt_of_le hv.2 hu.2⟩ hvexc' ε hε
      refine ⟨δ, hδpos, fun h hh hb => ?_⟩
      have h2 : -2 * Real.pi - scalarMinimum B.family v *
            loopFamilyLeastArea B.family.metric (app j) v / 2 +
            (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v + ε =
          -(scalarMinimum B.family v / 2) * loopFamilyLeastArea B.family.metric (app j) v +
            (-2 * Real.pi +
              (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) + ε := by
        ring
      exact (hδ h hh (le_trans hb hu.2)).trans_eq h2
    have hmain := rfs_csf_area_comparison_ode
      (A := loopFamilyLeastArea B.family.metric (app j))
      (rho := fun v => scalarMinimum B.family v / 2)
      (F := fun v => -2 * Real.pi +
        (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v)
      s u hst ((hAj j).mono hsub) hrho hF (insert a (exc j)) hDini
    have hrho' : (fun w => scalarMinimum B.family w / 2) =
        fun w => (1 / 2 : ℝ) * scalarMinimum B.family w := by
      funext w; ring
    rw [hrho'] at hmain
    simpa only [areaIntegratingFactor, intervalIntegral.integral_const_mul] using hmain
  have hwindow : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      Real.exp (∫ w in s..u, scalarMinimum B.family w / 2) *
          loopFamilyLeastArea B.family.metric γ u ≤
        loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..u, Real.exp (∫ w in s..v, scalarMinimum B.family w / 2) *
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) := by
    intro s hs u hu
    have hst : s ≤ u := hu.1
    have hexp : ∀ v : ℝ, Real.exp (∫ w in s..v, scalarMinimum B.family w / 2) =
        areaIntegratingFactor B.family s v := by
      intro v
      rw [areaIntegratingFactor, intervalIntegral.integral_div]
      congr 1
      ring
    have hIntab : IntervalIntegrable (scalarMinimum B.family) volume a b := by
      have hc : ContinuousOn (scalarMinimum B.family) (uIcc a b) := by
        rw [uIcc_of_le B.lt.le]
        exact RicciBackground.continuousOn_scalarMinimum B
      exact hc.intervalIntegrable
    have hpr : ContinuousOn (fun v : ℝ => ∫ w in s..v, scalarMinimum B.family w)
        (Icc a b) := by
      have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
        (f := scalarMinimum B.family) (a := s) hIntab (by rw [uIcc_of_le B.lt.le]; exact hs)
      simpa [uIcc_of_le B.lt.le] using h
    have hφcont : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v) (Icc a b) := by
      have h1 : ContinuousOn (fun v : ℝ => (1 / 2 : ℝ) *
          (∫ w in s..v, scalarMinimum B.family w)) (Icc a b) :=
        continuousOn_const.mul hpr
      have h2 : ContinuousOn (Real.exp ∘ fun v : ℝ => (1 / 2 : ℝ) *
          (∫ w in s..v, scalarMinimum B.family w)) (Icc a b) :=
        Real.continuous_exp.comp_continuousOn h1
      exact h2.congr (fun v _ => rfl)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (RicciBackground.continuousOn_scalarMinimum B)
    set C' : ℝ := max C 0 with hC'def
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hC'bound : ∀ w ∈ Icc a b, ‖scalarMinimum B.family w‖ ≤ C' :=
      fun w hw => le_trans (hC w hw) (le_max_left _ _)
    set Mb : ℝ := Real.exp ((1 / 2) * (C' * (b - a))) with hMbdef
    have hMb0 : 0 ≤ Mb := le_of_lt (Real.exp_pos _)
    have hφle : ∀ v ∈ Icc a b, areaIntegratingFactor B.family s v ≤ Mb := by
      intro v hv
      have hint : (∫ w in s..v, scalarMinimum B.family w) ≤ C' * (b - a) := by
        have h1 : ‖∫ w in s..v, scalarMinimum B.family w‖ ≤ C' * |v - s| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun w hw => by
            simp only [uIoc] at hw
            exact hC'bound w ⟨le_trans (le_min hs.1 hv.1) hw.1.le,
              le_trans hw.2 (max_le hs.2 hv.2)⟩
        have h2 : |v - s| ≤ b - a := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hv.2, hs.1], by linarith [hv.1, hs.2]⟩
        calc (∫ w in s..v, scalarMinimum B.family w)
            ≤ ‖∫ w in s..v, scalarMinimum B.family w‖ := le_abs_self _
          _ ≤ C' * |v - s| := h1
          _ ≤ C' * (b - a) := mul_le_mul_of_nonneg_left h2 hC'0
      have h3 : (1 / 2 : ℝ) * (∫ w in s..v, scalarMinimum B.family w) ≤
          (1 / 2 : ℝ) * (C' * (b - a)) :=
        mul_le_mul_of_nonneg_left hint (by norm_num)
      calc areaIntegratingFactor B.family s v
          = Real.exp ((1 / 2 : ℝ) * (∫ w in s..v, scalarMinimum B.family w)) := rfl
        _ ≤ Real.exp ((1 / 2 : ℝ) * (C' * (b - a))) := Real.exp_le_exp.mpr h3
        _ = Mb := rfl
    have hgoal : areaIntegratingFactor B.family s u * loopFamilyLeastArea B.family.metric γ u ≤
        loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..u, areaIntegratingFactor B.family s v *
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      set K : ℝ := 1 + Mb + Mb * (u - s) with hKdef
      have hK0 : 0 ≤ K := by
        have h1 : 0 ≤ Mb * (u - s) := mul_nonneg hMb0 (by linarith)
        rw [hKdef]; linarith
      have hε' : 0 < ε / (K + 1) := by positivity
      have hKε : K * (ε / (K + 1)) ≤ ε := by
        have h1 : K * (ε / (K + 1)) = ε * (K / (K + 1)) := by ring
        rw [h1]
        have h2 : K / (K + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        calc ε * (K / (K + 1)) ≤ ε * 1 := mul_le_mul_of_nonneg_left h2 hε.le
          _ = ε := mul_one ε
      obtain ⟨jA, hjA⟩ := hAconv (ε / (K + 1)) hε'
      obtain ⟨jF, hjF⟩ := herr (ε / (K + 1)) hε'
      set j : ℕ := max jA jF with hjdef
      have hjAg := hjA j (le_max_left _ _)
      have hjFg := hjF j (le_max_right _ _)
      have hAu : loopFamilyLeastArea B.family.metric γ u ≤
          loopFamilyLeastArea B.family.metric (app j) u + ε / (K + 1) := by
        have h := hjAg u ⟨le_trans hs.1 hu.1, hu.2⟩
        rw [abs_lt] at h
        linarith [h.1]
      have hAs : loopFamilyLeastArea B.family.metric (app j) s ≤
          loopFamilyLeastArea B.family.metric γ s + ε / (K + 1) := by
        have h := hjAg s hs
        rw [abs_lt] at h
        linarith [h.2]
      have hIntj : (∫ v in s..u, areaIntegratingFactor B.family s v *
            (-2 * Real.pi +
              (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v)) ≤
          (∫ v in s..u, areaIntegratingFactor B.family s v *
            (-2 * Real.pi +
              (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) +
            (ε / (K + 1)) * (Mb * (u - s)) := by
        have hφsu : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v) (uIcc s u) := by
          rw [uIcc_of_le hst]
          exact hφcont.mono (fun v hv => ⟨le_trans hs.1 hv.1, le_trans hv.2 hu.2⟩)
        have hFsu : ContinuousOn (fun v : ℝ => -2 * Real.pi +
            (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) (uIcc s u) := by
          rw [uIcc_of_le hst]
          exact (continuousOn_const.add
              (continuousOn_loopFamily_areaError B (app j) (happ j).1 (happ j).2.1)).mono
              (fun v hv => ⟨le_trans hs.1 hv.1, le_trans hv.2 hu.2⟩)
        have hFsuγ : ContinuousOn (fun v : ℝ => -2 * Real.pi +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) (uIcc s u) := by
          rw [uIcc_of_le hst]
          exact (continuousOn_const.add
              (continuousOn_loopFamily_areaError B γ hγ hi)).mono
              (fun v hv => ⟨le_trans hs.1 hv.1, le_trans hv.2 hu.2⟩)
        have hcontj : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v *
            (-2 * Real.pi +
              (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v))
            (uIcc s u) := hφsu.mul hFsu
        have hcont : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v *
            (-2 * Real.pi +
              (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v))
            (uIcc s u) := hφsu.mul hFsuγ
        have hsplit : (∫ v in s..u, areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v)) =
            (∫ v in s..u, areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) +
            ∫ v in s..u, (areaIntegratingFactor B.family s v *
                (-2 * Real.pi +
                  (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) -
              areaIntegratingFactor B.family s v *
                (-2 * Real.pi +
                  (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) := by
          rw [intervalIntegral.integral_sub hcontj.intervalIntegrable hcont.intervalIntegrable]
          ring
        rw [hsplit]
        have hmono : (∫ v in s..u, (areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) -
            areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)))
            ≤ ∫ _v in s..u, Mb * (ε / (K + 1)) := by
          refine intervalIntegral.integral_mono_on hst ?_ intervalIntegrable_const ?_
          · exact (hcontj.sub hcont).intervalIntegrable
          · intro v hv
            have hvab : v ∈ Icc a b := ⟨le_trans hs.1 hv.1, le_trans hv.2 hu.2⟩
            have h1 : areaIntegratingFactor B.family s v *
                ((curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v -
                  (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) ≤
                areaIntegratingFactor B.family s v * (ε / (K + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
              have h := hjFg v hvab
              rw [abs_lt] at h
              linarith [h.2]
            have h2 : areaIntegratingFactor B.family s v * (ε / (K + 1)) ≤
                Mb * (ε / (K + 1)) :=
              mul_le_mul_of_nonneg_right (hφle v hvab) hε'.le
            have h3 : areaIntegratingFactor B.family s v *
                  (-2 * Real.pi +
                    (curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v) -
                areaIntegratingFactor B.family s v *
                  (-2 * Real.pi +
                    (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) =
                areaIntegratingFactor B.family s v *
                  ((curveOfLoopFamily (app j)).areaError B.family.metric (Icc a b) v -
                    (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) := by
              ring
            linarith [h1, h2, h3.le, h3.ge]
        have hMbc : (∫ _v in s..u, Mb * (ε / (K + 1))) =
            (ε / (K + 1)) * (Mb * (u - s)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        rw [hMbc] at hmono
        linarith [hmono]
      have hodej := hode j s hs u hu
      have hstep1 : areaIntegratingFactor B.family s u *
            loopFamilyLeastArea B.family.metric γ u ≤
          areaIntegratingFactor B.family s u *
              loopFamilyLeastArea B.family.metric (app j) u + Mb * (ε / (K + 1)) := by
        have h1 : areaIntegratingFactor B.family s u *
              loopFamilyLeastArea B.family.metric γ u ≤
            areaIntegratingFactor B.family s u *
              (loopFamilyLeastArea B.family.metric (app j) u + ε / (K + 1)) :=
          mul_le_mul_of_nonneg_left hAu (le_of_lt (Real.exp_pos _))
        have h2 : areaIntegratingFactor B.family s u *
              (loopFamilyLeastArea B.family.metric (app j) u + ε / (K + 1)) =
            areaIntegratingFactor B.family s u *
                loopFamilyLeastArea B.family.metric (app j) u +
              areaIntegratingFactor B.family s u * (ε / (K + 1)) := by ring
        have h3 : areaIntegratingFactor B.family s u * (ε / (K + 1)) ≤
            Mb * (ε / (K + 1)) :=
          mul_le_mul_of_nonneg_right (hφle u ⟨le_trans hs.1 hu.1, hu.2⟩) hε'.le
        linarith [h1, h2.le, h2.ge, h3]
      have hstep2 : areaIntegratingFactor B.family s u *
            loopFamilyLeastArea B.family.metric (app j) u ≤
          loopFamilyLeastArea B.family.metric γ s +
            (∫ v in s..u, areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) +
            (ε / (K + 1)) * (Mb * (u - s)) + ε / (K + 1) := by
        linarith [hodej, hIntj, hAs]
      have hsum : Mb * (ε / (K + 1)) + (ε / (K + 1)) * (Mb * (u - s)) + ε / (K + 1) =
          (ε / (K + 1)) * K := by rw [hKdef]; ring
      have hcombine : areaIntegratingFactor B.family s u *
            loopFamilyLeastArea B.family.metric γ u ≤
          loopFamilyLeastArea B.family.metric γ s +
            (∫ v in s..u, areaIntegratingFactor B.family s v *
              (-2 * Real.pi +
                (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) +
            (Mb * (ε / (K + 1)) + (ε / (K + 1)) * (Mb * (u - s)) + ε / (K + 1)) := by
        linarith [hstep1, hstep2]
      rw [hsum] at hcombine
      have hKε' : (ε / (K + 1)) * K ≤ ε := by rw [mul_comm]; exact hKε
      exact hcombine.trans (add_le_add le_rfl hKε')
    simpa only [hexp u, hexp] using hgoal
  have hA : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
    intro τ
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hAconv (ε / 3) (by linarith)
    have hcontj : ContinuousAt
        (fun t : Icc a b => loopFamilyLeastArea B.family.metric (app j₀) t) τ :=
      (continuousOn_iff_continuous_domRestrict.mp (hAj j₀)).continuousAt
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcontj (ε / 3) (by linarith)
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    have h1 := hδ ht
    have h2 := hj₀ j₀ le_rfl t t.2
    have h3 := hj₀ j₀ le_rfl τ τ.2
    rw [Real.dist_eq] at h1 ⊢
    simp only [Set.domRestrict_apply] at ⊢
    rw [abs_lt] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  exact rfs_csf_immersed_area_of_continuousOn_leastArea_of_window (I := I) (M := M) B γ
    hγ hi hA hwindow

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
