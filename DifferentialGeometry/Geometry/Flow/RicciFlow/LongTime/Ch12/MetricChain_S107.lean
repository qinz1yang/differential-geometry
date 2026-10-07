import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SurvivorFlowIdent_S107

set_option autoImplicit false

/-!
# CH12-S107 / G1b: the Grönwall chain `g_t / t` vs `g_s / s` along the tracked survivor, across events

`metric_chain_S107` : with the dyadic-defect hypothesis `DefectAllAt_S85 … η r` on `[t, s]`, at every point
`y` of the survivor domain `D = backwardSurvivorDomain j0 last` (`last = actS s`, `ψ_{j0} y = J p`, `p ∈ B`)
and every vector `V`,
`g^{j0}_t(ψ_{j0} y)(dψ V, dψ V) / t ≤ (s/t)^η · (g^{last}_s(y)(V,V) / s)` and the reverse.
Proof: on `[t, time last]` the glued smooth flow `G` of `exists_backwardSurvivor_isSolutionOn`
(`survivorFlow_inner_S107` = `G ρ = ψ_j^* stageMetric j ρ`) + `gronwall_variation_open_S104`; on
`[time last, s]` the stage flow of `last` itself (`stage_inner_hasDerivAt_S104`); glued by
`(b/t)^η (s/b)^η = (s/t)^η`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

/-- `g^j_r (ψ_j y) (dψ_j V, dψ_j V)` : the stage-`j` metric at time `r`, evaluated on the push-forward of
`V ∈ T_y D` through the survivor map `ψ_j`. -/
def pushInner_S107 (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1))
    (hle : first ≤ last) (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) (r : ℝ)
    (y : K.backwardSurvivorDomain first last hle) (V : TangentSpace ThreeModel y) : ℝ :=
  (K.stageMetric j r).inner (K.backwardSurvivorMap first last hle j hj hl y)
    (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V)
    (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V)

theorem pushInner_self_S107 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1)) (hle : j ≤ j)
    (r : ℝ) (y : K.backwardSurvivorDomain j j hle) (V : TangentSpace ThreeModel y) :
    pushInner_S107 K j j hle j hle hle r y V = (K.stageMetric j r).inner y.val V V := by
  unfold pushInner_S107
  have he : K.backwardSurvivorMap j j hle j hle hle = Subtype.val := by
    funext x
    exact K.backwardSurvivorMap_last j j hle x
  rw [he, mfderiv_subtype_val_apply]

theorem chain_combine_S107 {x1 x2 x3 t b s η : ℝ} (ht : 0 < t) (htb : t ≤ b) (hbs : b ≤ s)
    (h1 : x1 / t ≤ (b / t) ^ η * (x2 / b) ∧ x2 / b ≤ (b / t) ^ η * (x1 / t))
    (h2 : x2 / b ≤ (s / b) ^ η * (x3 / s) ∧ x3 / s ≤ (s / b) ^ η * (x2 / b)) :
    x1 / t ≤ (s / t) ^ η * (x3 / s) ∧ x3 / s ≤ (s / t) ^ η * (x1 / t) := by
  have hb : 0 < b := ht.trans_le htb
  have hs : 0 < s := hb.trans_le hbs
  have hA : 0 ≤ (b / t) ^ η := (Real.rpow_pos_of_pos (div_pos hb ht) _).le
  have hB : 0 ≤ (s / b) ^ η := (Real.rpow_pos_of_pos (div_pos hs hb) _).le
  have hAB : (b / t) ^ η * (s / b) ^ η = (s / t) ^ η := by
    rw [← Real.mul_rpow (div_pos hb ht).le (div_pos hs hb).le]
    congr 1
    field_simp
  constructor
  · calc x1 / t ≤ (b / t) ^ η * (x2 / b) := h1.1
      _ ≤ (b / t) ^ η * ((s / b) ^ η * (x3 / s)) := mul_le_mul_of_nonneg_left h2.1 hA
      _ = (s / t) ^ η * (x3 / s) := by rw [← hAB]; ring
  · calc x3 / s ≤ (s / b) ^ η * (x2 / b) := h2.2
      _ ≤ (s / b) ^ η * ((b / t) ^ η * (x1 / t)) := mul_le_mul_of_nonneg_left h1.2 hB
      _ = (s / t) ^ η * (x1 / t) := by rw [← hAB]; ring

theorem Icc_subset_stageDomain_S107 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1)) {s : ℝ}
    (hs : s ∈ K.stageDomain j) : Icc (K.time j) s ⊆ K.stageDomain j := by
  intro ρ hρ
  cases j using Fin.lastCases with
  | last =>
    exact (ObservedHistory.mem_stageDomain_last K ρ).2
      ⟨hρ.1, hρ.2.trans ((ObservedHistory.mem_stageDomain_last K s).1 hs).2⟩
  | cast i =>
    rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hs ⊢
    exact ⟨hρ.1, lt_of_le_of_lt hρ.2 hs.2⟩

theorem metric_chain_S107 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η t s : ℝ} (ht0 : 0 < t) (hts : t ≤ s)
    (hs : s ≤ K.horizon) (hj0 : actS_S70 K t = j0)
    (hW : ∀ r ∈ Icc t s, DefectAllAt_S85 K j0 J B η r)
    {last : Fin (K.eventCount + 1)} (hlast : actS_S70 K s = last) (hle : j0 ≤ last)
    (p : X) (hp : p ∈ B) (y : K.backwardSurvivorDomain j0 last hle)
    (hy : K.backwardSurvivorMap j0 last hle j0 le_rfl hle y = J p) (V : TangentSpace ThreeModel y) :
    pushInner_S107 K j0 last hle j0 le_rfl hle t y V / t ≤
        (s / t) ^ η * ((K.stageMetric last s).inner y.val V V / s) ∧
      (K.stageMetric last s).inner y.val V V / s ≤
        (s / t) ^ η * (pushInner_S107 K j0 last hle j0 le_rfl hle t y V / t) := by
  have hrange : ∀ r ∈ Icc t s, r ∈ Icc (0 : ℝ) K.horizon := fun r hr =>
    ⟨ht0.le.trans hr.1, hr.2.trans hs⟩
  have hs' : s ∈ Icc (0 : ℝ) K.horizon := hrange s ⟨hts, le_rfl⟩
  have ht' : t ∈ Icc (0 : ℝ) K.horizon := hrange t ⟨le_rfl, hts⟩
  have hTs : K.time last ≤ s := hlast ▸ actS_time_le_S70 K hs'
  have hj0t : K.time j0 ≤ t := hj0 ▸ actS_time_le_S70 K ht'
  have hsdom : s ∈ K.stageDomain last := hlast ▸ actS_mem_stageDomain_S85 K hs'
  -- the last-stage piece on `[a, s]`
  have piece2 : ∀ a : ℝ, 0 < a → K.time last ≤ a → a ≤ s → t ≤ a →
      (K.stageMetric last a).inner y.val V V / a ≤
          (s / a) ^ η * ((K.stageMetric last s).inner y.val V V / s) ∧
        (K.stageMetric last s).inner y.val V V / s ≤
          (s / a) ^ η * ((K.stageMetric last a).inner y.val V V / a) := by
    intro a ha hTa has hta
    have hsub : Icc (K.time last) s ⊆ K.stageDomain last := Icc_subset_stageDomain_S107 K last hsdom
    refine gronwall_variation_open_S104 (rv := fun ρ => ricciTensor (K.stageMetric last ρ) y.val V V)
      ha has ((stage_inner_ricci_continuousOn_S85 K last y.val V).2.mono
        (fun ρ hρ => hsub ⟨hTa.trans hρ.1, hρ.2⟩)) (fun ρ hρ => ?_) (fun ρ hρ => ?_)
    · exact stage_inner_hasDerivAt_S104 K last y.val V
        ((interior_maximal (t := Ioo (K.time last) s) (s := K.stageDomain last)
          (fun τ hτ => hsub ⟨hτ.1.le, hτ.2.le⟩) isOpen_Ioo) ⟨lt_of_le_of_lt hTa hρ.1, hρ.2⟩)
    · have hr : ρ ∈ Icc t s := ⟨hta.trans hρ.1.le, hρ.2.le⟩
      have hact : actS_S70 K ρ = last :=
        le_antisymm (hlast ▸ actS_mono_S70 K (hrange ρ hr) hs' hr.2)
          (le_actS_S70 K (hrange ρ hr) (hTa.trans hρ.1.le))
      exact defectAllAt_transport_S85 K j0 J B hact (hW ρ hr) hle p hp y.val ⟨y, rfl, hy⟩ V
  by_cases hjl : j0 = last
  · subst hjl
    have hTt : K.time j0 ≤ t := hj0t
    have h2 := piece2 t ht0 hTt hts le_rfl
    rw [pushInner_self_S107]
    simpa using h2
  · have hlt : j0 < last := lt_of_le_of_ne hle hjl
    have hTt : t ≤ K.time last := by
      by_contra hcon
      have h1 := le_actS_S70 K ht' (j := last) (not_le.mp hcon).le
      rw [hj0] at h1
      exact absurd hlt (not_lt.mpr h1)
    obtain ⟨G, hslab, hinit, -, hsol⟩ := K.exists_backwardSurvivor_isSolutionOn j0 last hlt
    have hdom0 : t ∈ K.stageDomain j0 := by
      have := actS_mem_stageDomain_S85 K ht'
      rwa [hj0] at this
    have hx1 : (G t).inner y V V = pushInner_S107 K j0 last hle j0 le_rfl hle t y V :=
      (survivorFlow_inner_S107 K j0 last hlt.le G hslab hinit j0 le_rfl hlt.le hdom0 hTt y V).1
    have hx2 : (G (K.time last)).inner y V V = (K.stageMetric last (K.time last)).inner y.val V V := by
      rw [hinit last hlt.le le_rfl, K.backwardSurvivorInitialMetric_last j0 last hlt.le,
        SmoothRiemannianMetric.restrictOpen_inner, K.stageMetric_initial]
    have p1 : (G t).inner y V V / t ≤ (K.time last / t) ^ η * ((G (K.time last)).inner y V V / K.time last) ∧
        (G (K.time last)).inner y V V / K.time last ≤ (K.time last / t) ^ η * ((G t).inner y V V / t) := by
      refine gronwall_variation_open_S104 (gv := fun ρ => (G ρ).inner y V V)
        (rv := fun ρ => ricciTensor (G ρ) y V V) ht0 hTt
        ((hsol.smoothMetric.coeff_cont y V V).mono (fun ρ hρ => ⟨hj0t.trans hρ.1, hρ.2⟩))
        (fun ρ hρ => ?_) (fun ρ hρ => ?_)
      · have hreg : ρ ∈ Ioo (K.time j0) (K.time last) := ⟨hj0t.trans_lt hρ.1, hρ.2⟩
        refine (DifferentialGeometry.PDE.RicciFlow.metricDerivAt _ hsol ⟨ρ, hreg⟩ y V V).congr_deriv ?_
        congr 1
        exact metricRicciAt_apply_eq_ricciTensor (G ρ) y V V
      · have hr : ρ ∈ Icc t s := ⟨hρ.1.le, hρ.2.le.trans hTs⟩
        have hρ0 := hrange ρ hr
        have hjl' : j0 ≤ actS_S70 K ρ := hj0 ▸ actS_mono_S70 K ht' hρ0 hr.1
        have hjl'' : actS_S70 K ρ ≤ last := hlast ▸ actS_mono_S70 K hρ0 hs' hr.2
        have hL := survivorFlow_inner_S107 K j0 last hlt.le G hslab hinit (actS_S70 K ρ) hjl' hjl''
          (actS_mem_stageDomain_S85 K hρ0) hρ.2.le y V
        have hD := hW ρ hr hjl' p hp _ (tracked_restrict_S70 K hle hjl' hjl'' J p y hy)
          (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap j0 last hle (actS_S70 K ρ) hjl' hjl'') y V)
        unfold DefectAt_S85 at hD
        rw [hL.1, hL.2]
        exact hD
    rw [hx1, hx2] at p1
    have hTpos : 0 < K.time last := ht0.trans_le hTt
    exact chain_combine_S107 ht0 hTt hTs p1 (piece2 (K.time last) hTpos le_rfl hTs hTt)

end GC.LongTime.Ch12
