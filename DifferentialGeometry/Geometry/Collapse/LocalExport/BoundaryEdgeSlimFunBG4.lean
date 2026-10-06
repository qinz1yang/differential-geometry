import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSlimPointBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSignedFunctionBG4

/-!
# BCF02 G4, group G4b: the face function of an interval of an arc of `K₃` (lane S-BCF02-G4)

For an arc `γ = Kc.arc j` and parameters `0 ≤ t_a < t_b ≤ 1`, the function of the edge base
whose sign records where `π₃ y` lies with respect to the open sub-arc `γ((t_a, t_b))`:

* `slim_interval_data_BG4`: a function `a₀` smooth on an open neighbourhood `Ω₀` of the two end
  points `γ t_a`, `γ t_b` (inside the good neighbourhood of `B₃`) with `a₀ < 0` exactly on the
  open sub-arc and `a₀ = 0` exactly at the two ends, whose pull back `a₀ ∘ f₃` is smooth with
  non-zero differential at every point of `X₃` over an end (one product chart at each end:
  `slim_point_datum_BG4`);
* `isOpen_slimArc_preimage_BG4`: `{q | f₃ q ∈ γ((t_a, t_b))}` is open (interior arc points are
  interior points of the arc in `B₃`);
* `exists_slimIntervalFun_BG4`: the face function (via `exists_signed_function_BG4`) with
  `h y < 0 ⟺ π₃ y ∈ γ((t_a, t_b))`, `h y = 0 ⟺ π₃ y ∈ {γ t_a, γ t_b}`,
  `0 < h y ⟺ π₃ y ∉ γ([t_a, t_b])`, smooth on an open set of `H` around every zero, and
  smooth / regular / transverse after `f₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Interior arc points are interior in the slim base**: the preimage under `f₃` of an open
sub-arc `γ((t_a, t_b))` is open in `W`. -/
theorem isOpen_slimArc_preimage_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) {ta tb : ℝ} (hta : 0 ≤ ta) (htb : tb ≤ 1) :
    IsOpen {q : W.Carrier | C.toChain.stageMap 2 q ∈ Kc.arc j '' Ioo ta tb} := by
  classical
  have hdat : ∀ t : ↥(Ioo ta tb), ∃ V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), IsOpen V ∧ Kc.arc j t ∈ V ∧
      ∀ z ∈ Bs.base 2 ∩ V, z ∈ Kc.arc j '' Ioo ta tb := by
    rintro ⟨t, ht⟩
    obtain ⟨ℓ, V, δ, hV, hy, hδ, hδ₀, hiso, hcls, hend, -⟩ := C.slim_point_datum_BG4 WF Kc j
      (t₀ := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      (δ₀ := min (t - ta) (tb - t)) (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
    refine ⟨V, hV, hy, fun z hz => ?_⟩
    rcases hcls z hz with h | ⟨t', -, -, hlt, hzt, -⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact ⟨t, ht, h.symm⟩
    · have h1 : |t' - t| < min (t - ta) (tb - t) := lt_of_lt_of_le hlt hδ₀
      have h2 := (abs_lt.mp h1)
      refine ⟨t', ⟨?_, ?_⟩, hzt.symm⟩
      · linarith [h2.1, min_le_left (t - ta) (tb - t)]
      · linarith [h2.2, min_le_right (t - ta) (tb - t)]
    · exfalso
      linarith [ht.1]
    · exfalso
      linarith [ht.2]
  choose V hVo hyV hVsub using hdat
  have hN : IsOpen (⋃ t, V t) := isOpen_iUnion hVo
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hset : {q : W.Carrier | C.toChain.stageMap 2 q ∈ Kc.arc j '' Ioo ta tb} =
      C.toChain.stageMap 2 ⁻¹' (⋃ t, V t) ∩ Bs.source 2 := by
    ext q
    constructor
    · rintro ⟨t, ht, hqt⟩
      have hB : C.toChain.stageMap 2 q ∈ Bs.base 2 :=
        hqt ▸ Kc.arc_subset_base j ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_preimage, ← hqt]
        exact mem_iUnion.mpr ⟨⟨t, ht⟩, hyV ⟨t, ht⟩⟩
      · rw [Bs.slim_source_eq]
        exact hB
    · rintro ⟨hqN, hqX⟩
      obtain ⟨t, htq⟩ := mem_iUnion.mp hqN
      have hB : C.toChain.stageMap 2 q ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hqX
      exact hVsub t _ ⟨hB, htq⟩
  rw [hset]
  exact (hN.preimage hf₃).inter (Bs.isOpen_source 2 (by decide))

/-- **The defining function of an open sub-arc near its two end points** (see the module
docstring). -/
theorem slim_interval_data_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) {ta tb : ℝ} (hta : 0 ≤ ta) (hab : ta < tb) (htb : tb ≤ 1) :
    ∃ (a₀ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ)
      (Ω₀ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))),
      IsOpen Ω₀ ∧ Kc.arc j ta ∈ Ω₀ ∧ Kc.arc j tb ∈ Ω₀ ∧
      (∀ q : W.Carrier, C.toChain.stageMap 2 q ∈ Ω₀ → C.toChain.stageMap 2 q ∈ Bs.base 2) ∧
      ContDiffOn ℝ ∞ a₀ Ω₀ ∧
      (∀ z ∈ Bs.base 2 ∩ Ω₀, (a₀ z < 0 ↔ z ∈ Kc.arc j '' Ioo ta tb) ∧
        (a₀ z = 0 ↔ z = Kc.arc j ta ∨ z = Kc.arc j tb)) ∧
      (∀ p ∈ Bs.source 2, (C.toChain.stageMap 2 p = Kc.arc j ta ∨
          C.toChain.stageMap 2 p = Kc.arc j tb) →
        ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => a₀ (C.toChain.stageMap 2 q)) p ∧
        mfderiv W.model 𝓘(ℝ, ℝ) (fun q => a₀ (C.toChain.stageMap 2 q)) p ≠ 0) := by
  classical
  obtain ⟨G, hG, hBG, hGgood⟩ := C.exists_slim_good_nbhd_BG4 (Bs := Bs)
  have hta1 : ta ∈ Icc (0 : ℝ) 1 := ⟨hta, by linarith⟩
  have htb1 : tb ∈ Icc (0 : ℝ) 1 := ⟨by linarith, htb⟩
  obtain ⟨ℓa, Va, δa, hVa, hya, hδa, hδa₀, hisoa, hclsa, -, hrega⟩ :=
    C.slim_point_datum_BG4 WF Kc j hta1 (δ₀ := tb - ta) (sub_pos.mpr hab)
  obtain ⟨ℓb, Vb, δb, hVb, hyb, hδb, hδb₀, hisob, hclsb, -, hregb⟩ :=
    C.slim_point_datum_BG4 WF Kc j htb1 (δ₀ := tb - ta) (sub_pos.mpr hab)
  have hne : Kc.arc j ta ≠ Kc.arc j tb := fun h =>
    hab.ne (Kc.arc_injOn j hta1 htb1 h)
  have hr : 0 < dist (Kc.arc j ta) (Kc.arc j tb) / 2 := by
    have := dist_pos.mpr hne
    linarith
  set r : ℝ := dist (Kc.arc j ta) (Kc.arc j tb) / 2 with hrdef
  set Va' := Va ∩ G ∩ Metric.ball (Kc.arc j ta) r with hVa'
  set Vb' := Vb ∩ G ∩ Metric.ball (Kc.arc j tb) r with hVb'
  have hVa'o : IsOpen Va' := (hVa.inter hG).inter Metric.isOpen_ball
  have hVb'o : IsOpen Vb' := (hVb.inter hG).inter Metric.isOpen_ball
  have hya' : Kc.arc j ta ∈ Va' :=
    ⟨⟨hya, hBG (Kc.arc_subset_base j ⟨ta, hta1, rfl⟩)⟩, Metric.mem_ball_self hr⟩
  have hyb' : Kc.arc j tb ∈ Vb' :=
    ⟨⟨hyb, hBG (Kc.arc_subset_base j ⟨tb, htb1, rfl⟩)⟩, Metric.mem_ball_self hr⟩
  have hdisj : Disjoint Va' Vb' := by
    refine Set.disjoint_left.mpr fun z hza hzb => ?_
    have h1 : dist z (Kc.arc j ta) < r := hza.2
    have h2 : dist z (Kc.arc j tb) < r := hzb.2
    have := dist_triangle_left (Kc.arc j ta) (Kc.arc j tb) z
    linarith
  -- the function `a₀`
  let a₀ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ := fun z =>
    if z ∈ Va' then -(ℓa (z - Kc.arc j ta)) else if z ∈ Vb' then ℓb (z - Kc.arc j tb) else 0
  have ha₀a : ∀ z ∈ Va', a₀ z = -(ℓa (z - Kc.arc j ta)) := fun z hz => by
    simp [a₀, hz]
  have ha₀b : ∀ z ∈ Vb', a₀ z = ℓb (z - Kc.arc j tb) := fun z hz => by
    have hnz : z ∉ Va' := fun h => Set.disjoint_left.mp hdisj h hz
    simp [a₀, hnz, hz]
  have hcda : ContDiffOn ℝ ∞ a₀ Va' :=
    ((ℓa.contDiff.comp (contDiff_id.sub contDiff_const)).neg.contDiffOn).congr ha₀a
  have hcdb : ContDiffOn ℝ ∞ a₀ Vb' :=
    ((ℓb.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn).congr ha₀b
  have hcd : ContDiffOn ℝ ∞ a₀ (Va' ∪ Vb') := hcda.union_of_isOpen hcdb hVa'o hVb'o
  have hIcc : ∀ t ∈ Ioo ta tb, t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  refine ⟨a₀, Va' ∪ Vb', hVa'o.union hVb'o, Or.inl hya', Or.inr hyb', ?_, hcd, ?_, ?_⟩
  · intro q hq
    exact hGgood q (by rcases hq with h | h <;> exact h.1.2)
  · -- the sign of `a₀` on the points of `B₃` near the two ends
    have hnegc : ∀ z, a₀ z < 0 → z ∈ Kc.arc j '' Ioo ta tb → z ≠ Kc.arc j ta →
        z ≠ Kc.arc j tb → (a₀ z < 0 ↔ z ∈ Kc.arc j '' Ioo ta tb) ∧
          (a₀ z = 0 ↔ z = Kc.arc j ta ∨ z = Kc.arc j tb) := by
      intro z h1 h2 h3 h4
      refine ⟨⟨fun _ => h2, fun _ => h1⟩, ⟨fun h => absurd h h1.ne, ?_⟩⟩
      rintro (h | h)
      · exact absurd h h3
      · exact absurd h h4
    have hposc : ∀ z, 0 < a₀ z → z ∉ Kc.arc j '' Ioo ta tb → z ≠ Kc.arc j ta →
        z ≠ Kc.arc j tb → (a₀ z < 0 ↔ z ∈ Kc.arc j '' Ioo ta tb) ∧
          (a₀ z = 0 ↔ z = Kc.arc j ta ∨ z = Kc.arc j tb) := by
      intro z h1 h2 h3 h4
      refine ⟨⟨fun h => absurd h h1.not_gt, fun h => absurd h h2⟩, ⟨fun h => absurd h h1.ne', ?_⟩⟩
      rintro (h | h)
      · exact absurd h h3
      · exact absurd h h4
    have hzeroc : ∀ z, a₀ z = 0 → z ∉ Kc.arc j '' Ioo ta tb →
        (z = Kc.arc j ta ∨ z = Kc.arc j tb) → (a₀ z < 0 ↔ z ∈ Kc.arc j '' Ioo ta tb) ∧
          (a₀ z = 0 ↔ z = Kc.arc j ta ∨ z = Kc.arc j tb) := by
      intro z h1 h2 h3
      exact ⟨⟨fun h => absurd h (by rw [h1]; exact lt_irrefl 0), fun h => absurd h h2⟩,
        ⟨fun _ => h3, fun _ => h1⟩⟩
    rintro z ⟨hzB, hzΩ⟩
    rcases hzΩ with hza | hzb
    · have hzVa : z ∈ Va := hza.1.1
      have hza0 : a₀ z = -(ℓa (z - Kc.arc j ta)) := ha₀a z hza
      rcases hclsa z ⟨hzB, hzVa⟩ with h1 | ⟨t, ht, hpos, hlt, hzt, hside⟩ | ⟨hoff, hend⟩
      · refine hzeroc z (by rw [hza0, h1]; simp) ?_ (Or.inl h1)
        rintro ⟨t', ht', htt⟩
        have : t' = ta := Kc.arc_injOn j (hIcc t' ht') hta1 (htt.trans h1)
        linarith [ht'.1]
      · have hδ1 : |t - ta| < tb - ta := lt_of_lt_of_le hlt hδa₀
        have hne_t : t ≠ ta := fun h => by
          rw [h, sub_self, abs_zero] at hpos
          exact lt_irrefl 0 hpos
        have hz_ne_a : z ≠ Kc.arc j ta := fun h => hne_t (Kc.arc_injOn j ht hta1 (hzt ▸ h))
        rcases hside with ⟨htl, hℓ⟩ | ⟨htg, hℓ⟩
        · refine hposc z (by rw [hza0]; linarith) ?_ hz_ne_a ?_
          · rintro ⟨t', ht', htt⟩
            have : t' = t := Kc.arc_injOn j (hIcc t' ht') ht (htt.trans hzt)
            linarith [ht'.1]
          · intro h
            have : t = tb := Kc.arc_injOn j ht htb1 (hzt ▸ h)
            linarith
        · have htt : t < tb := by linarith [(abs_lt.mp hδ1).2]
          refine hnegc z (by rw [hza0]; linarith) ⟨t, ⟨htg, htt⟩, hzt.symm⟩ hz_ne_a ?_
          intro h
          have : t = tb := Kc.arc_injOn j ht htb1 (hzt ▸ h)
          linarith
      · rcases hend with ⟨h0, hℓ⟩ | ⟨h1, -⟩
        · refine hposc z (by rw [hza0]; linarith) ?_ ?_ ?_
          · rintro ⟨t', ht', htt⟩
            exact hoff ⟨t', hIcc t' ht', htt⟩
          · intro h
            exact hoff ⟨ta, hta1, h.symm⟩
          · intro h
            exact hoff ⟨tb, htb1, h.symm⟩
        · exfalso
          linarith
    · have hzVb : z ∈ Vb := hzb.1.1
      have hzb0 : a₀ z = ℓb (z - Kc.arc j tb) := ha₀b z hzb
      rcases hclsb z ⟨hzB, hzVb⟩ with h1 | ⟨t, ht, hpos, hlt, hzt, hside⟩ | ⟨hoff, hend⟩
      · refine hzeroc z (by rw [hzb0, h1]; simp) ?_ (Or.inr h1)
        rintro ⟨t', ht', htt⟩
        have : t' = tb := Kc.arc_injOn j (hIcc t' ht') htb1 (htt.trans h1)
        linarith [ht'.2]
      · have hδ1 : |t - tb| < tb - ta := lt_of_lt_of_le hlt hδb₀
        have hne_t : t ≠ tb := fun h => by
          rw [h, sub_self, abs_zero] at hpos
          exact lt_irrefl 0 hpos
        have hz_ne_b : z ≠ Kc.arc j tb := fun h => hne_t (Kc.arc_injOn j ht htb1 (hzt ▸ h))
        rcases hside with ⟨htl, hℓ⟩ | ⟨htg, hℓ⟩
        · have hta' : ta < t := by linarith [(abs_lt.mp hδ1).1]
          refine hnegc z (by rw [hzb0]; exact hℓ) ⟨t, ⟨hta', htl⟩, hzt.symm⟩ ?_ hz_ne_b
          intro h
          have : t = ta := Kc.arc_injOn j ht hta1 (hzt ▸ h)
          linarith
        · refine hposc z (by rw [hzb0]; exact hℓ) ?_ ?_ hz_ne_b
          · rintro ⟨t', ht', htt⟩
            have : t' = t := Kc.arc_injOn j (hIcc t' ht') ht (htt.trans hzt)
            linarith [ht'.2]
          · intro h
            have : t = ta := Kc.arc_injOn j ht hta1 (hzt ▸ h)
            linarith
      · rcases hend with ⟨h0, -⟩ | ⟨h1, hℓ⟩
        · exfalso
          linarith
        · refine hposc z (by rw [hzb0]; exact hℓ) ?_ ?_ ?_
          · rintro ⟨t', ht', htt⟩
            exact hoff ⟨t', hIcc t' ht', htt⟩
          · intro h
            exact hoff ⟨ta, hta1, h.symm⟩
          · intro h
            exact hoff ⟨tb, htb1, h.symm⟩
  · intro p hpX hpe
    rcases hpe with hpa | hpb
    · have hmem : p ∈ C.toChain.stageMap 2 ⁻¹' Va' := by
        rw [mem_preimage, hpa]
        exact hya'
      have heq : (fun q => a₀ (C.toChain.stageMap 2 q)) =ᶠ[𝓝 p]
          fun q => (-1 : ℝ) * ℓa (C.toChain.stageMap 2 q - Kc.arc j ta) := by
        filter_upwards [(hVa'o.preimage hf₃).mem_nhds hmem] with q hq
        rw [ha₀a _ hq, neg_one_mul]
      have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
          fun q => (-1 : ℝ) * ℓa (C.toChain.stageMap 2 q - Kc.arc j ta) :=
        (contDiff_const.mul (ℓa.contDiff.comp (contDiff_id.sub contDiff_const))).comp_contMDiff
          (C.stageMap_contMDiff_BAUGD 2)
      refine ⟨(hsm p).congr_of_eventuallyEq heq, ?_⟩
      rw [heq.mfderiv_eq]
      exact hrega p hpX hpa (-1) (by norm_num)
    · have hmem : p ∈ C.toChain.stageMap 2 ⁻¹' Vb' := by
        rw [mem_preimage, hpb]
        exact hyb'
      have heq : (fun q => a₀ (C.toChain.stageMap 2 q)) =ᶠ[𝓝 p]
          fun q => (1 : ℝ) * ℓb (C.toChain.stageMap 2 q - Kc.arc j tb) := by
        filter_upwards [(hVb'o.preimage hf₃).mem_nhds hmem] with q hq
        rw [ha₀b _ hq, one_mul]
      have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
          fun q => (1 : ℝ) * ℓb (C.toChain.stageMap 2 q - Kc.arc j tb) :=
        (contDiff_const.mul (ℓb.contDiff.comp (contDiff_id.sub contDiff_const))).comp_contMDiff
          (C.stageMap_contMDiff_BAUGD 2)
      refine ⟨(hsm p).congr_of_eventuallyEq heq, ?_⟩
      rw [heq.mfderiv_eq]
      exact hregb p hpX hpb 1 one_ne_zero


/-- **The face function of an interval of an arc of `K₃`** (see the module docstring), stated at
the edge base through `π₃ = (actualSlotsV2_BAUGD S).stageProj 2`. -/
theorem exists_slimIntervalFun_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) {ta tb : ℝ} (hta : 0 ≤ ta) (hab : ta < tb) (htb : tb ≤ 1) :
    ∃ h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContinuousOn h (Bs.base 1) ∧
      (∀ y ∈ Bs.base 1,
        (h y < 0 ↔ (actualSlotsV2_BAUGD S).stageProj 2 y ∈ Kc.arc j '' Ioo ta tb) ∧
        (h y = 0 ↔ (actualSlotsV2_BAUGD S).stageProj 2 y = Kc.arc j ta ∨
          (actualSlotsV2_BAUGD S).stageProj 2 y = Kc.arc j tb) ∧
        (0 < h y ↔ (actualSlotsV2_BAUGD S).stageProj 2 y ∉ Kc.arc j '' Icc ta tb)) ∧
      (∀ y ∈ Bs.base 1, h y = 0 → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ ∞ h O) ∧
      (∀ p ∈ Bs.source 1, h (C.toChain.stageMap 1 p) = 0 →
        ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => h (C.toChain.stageMap 1 q)) p ∧
        mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 ∧
        (C.toChain.heightRatio p = 4 * Δ →
          Surjective fun v : TangentSpace W.model p =>
            (mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p v,
              mvfderiv W.model C.toChain.heightRatio p v))) := by
  classical
  obtain ⟨a₀, Ω₀, hΩo, hya, hyb, hgood, hcd, hsign, hreg⟩ :=
    C.slim_interval_data_BG4 WF Kc j hta hab htb
  have hta1 : ta ∈ Icc (0 : ℝ) 1 := ⟨hta, by linarith⟩
  have htb1 : tb ∈ Icc (0 : ℝ) 1 := ⟨by linarith, htb⟩
  have hf₂ : Continuous (C.toChain.stageMap 1) := (C.stageMap_contMDiff_BAUGD 1).continuous
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hπ : ∀ p, C.toChain.stageMap 2 p =
      (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 1 p) := fun p =>
    ((stageProj_one_two_V2_BAUGD S (C.toChain.E p)).1).symm
  have hIcc : ∀ t ∈ Ioo ta tb, t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the sets `R`, `P`
  let R : Set W.Carrier := {q | C.toChain.stageMap 2 q ∈ Kc.arc j '' Ioo ta tb}
  let P : Set W.Carrier := {q | C.toChain.stageMap 2 q = Kc.arc j ta ∨
    C.toChain.stageMap 2 q = Kc.arc j tb}
  have hR : IsOpen R := C.isOpen_slimArc_preimage_BG4 WF Kc j hta htb
  have hRPeq : R ∪ P = C.toChain.stageMap 2 ⁻¹' (Kc.arc j '' Icc ta tb) := by
    ext q
    constructor
    · rintro (⟨t, ht, hqt⟩ | (h | h))
      · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hqt⟩
      · exact ⟨ta, ⟨le_rfl, hab.le⟩, h.symm⟩
      · exact ⟨tb, ⟨hab.le, le_rfl⟩, h.symm⟩
    · rintro ⟨t, ht, hqt⟩
      rcases ht.1.eq_or_lt with h1 | h1
      · exact Or.inr (Or.inl (by rw [← hqt, ← h1]))
      · rcases ht.2.eq_or_lt with h2 | h2
        · exact Or.inr (Or.inr (by rw [← hqt, h2]))
        · exact Or.inl ⟨t, ⟨h1, h2⟩, hqt⟩
  have hRP : IsClosed (R ∪ P) := by
    rw [hRPeq]
    have hK : IsCompact (Kc.arc j '' Icc ta tb) :=
      isCompact_Icc.image_of_continuousOn
        ((Kc.arc_smooth j).continuousOn.mono (Icc_subset_Icc hta htb))
    exact hK.isClosed.preimage hf₃
  have hdisj : Disjoint R P := by
    refine Set.disjoint_left.mpr fun q hqR hqP => ?_
    obtain ⟨t, ht, hqt⟩ := hqR
    rcases hqP with h | h
    · have : t = ta := Kc.arc_injOn j (hIcc t ht) hta1 (hqt.trans h)
      linarith [ht.1]
    · have : t = tb := Kc.arc_injOn j (hIcc t ht) htb1 (hqt.trans h)
      linarith [ht.2]
  -- the whole edge fibres lie in `f₃`-fibres
  have hfib : ∀ y ∈ Bs.base 1, ∀ q ∈ Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y},
      C.toChain.stageMap 2 q = (actualSlotsV2_BAUGD S).stageProj 2 y := by
    intro y hy q hq
    rw [hπ q, show C.toChain.stageMap 1 q = y from hq.2]
  have hne : ∀ y ∈ Bs.base 1, (Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y}).Nonempty := by
    intro y hy
    rw [← Bs.image_eq 1] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨p, hp, rfl⟩
  have hFT : ∀ y ∈ Bs.base 1, ∀ T : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆
        C.toChain.stageMap 2 ⁻¹' T ↔ (actualSlotsV2_BAUGD S).stageProj 2 y ∈ T := by
    intro y hy T
    constructor
    · intro h
      obtain ⟨p, hp⟩ := hne y hy
      have := h hp
      rwa [mem_preimage, hfib y hy p hp] at this
    · intro h q hq
      rw [mem_preimage, hfib y hy q hq]
      exact h
  have hdich : ∀ y ∈ Bs.base 1,
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ R ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ P ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ (R ∪ P)ᶜ := by
    intro y hy
    by_cases h1 : (actualSlotsV2_BAUGD S).stageProj 2 y ∈ Kc.arc j '' Ioo ta tb
    · exact Or.inl ((hFT y hy (Kc.arc j '' Ioo ta tb)).mpr h1)
    · by_cases h2 : (actualSlotsV2_BAUGD S).stageProj 2 y = Kc.arc j ta ∨
          (actualSlotsV2_BAUGD S).stageProj 2 y = Kc.arc j tb
      · exact Or.inr (Or.inl ((hFT y hy {z | z = Kc.arc j ta ∨ z = Kc.arc j tb}).mpr h2))
      · refine Or.inr (Or.inr fun q hq hq' => ?_)
        have hq3 := hfib y hy q hq
        rcases hq' with hqR | hqP
        · exact h1 (hq3 ▸ hqR)
        · exact h2 (hq3 ▸ hqP)
  obtain ⟨h, hcont, hsgn, hsm⟩ := exists_signed_function_BG4 (X := Bs.source 1)
    (f := C.toChain.stageMap 1) (B := Bs.base 1) hf₂.continuousOn (Bs.image_eq 1) (Bs.proper 1)
    (R := R) (P := P) hR hRP hdisj hdich (O := C.toChain.stageMap 2 ⁻¹' Ω₀)
    (hΩo.preimage hf₃)
    (fun p hp => by
      rcases hp.1 with h | h
      · exact show C.toChain.stageMap 2 p ∈ Ω₀ by rw [h]; exact hya
      · exact show C.toChain.stageMap 2 p ∈ Ω₀ by rw [h]; exact hyb)
    (a := fun z => a₀ ((actualSlotsV2_BAUGD S).stageProj 2 z))
    (d := fun q => a₀ (C.toChain.stageMap 2 q))
    (Ω := (actualSlotsV2_BAUGD S).stageProj 2 ⁻¹' Ω₀)
    (hΩo.preimage ((actualSlotsV2_BAUGD S).stageProj 2).continuous)
    (hcd.continuousOn.comp ((actualSlotsV2_BAUGD S).stageProj 2).continuous.continuousOn
      (fun z hz => hz))
    (fun p hp => show (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 1 p) ∈ Ω₀ by
      rw [← hπ p]; exact hp.1)
    (fun p _ => by rw [← hπ p])
    (fun p hp => (hsign _ ⟨hgood p hp.1, hp.1⟩).1.symm)
    (fun p hp => (hsign _ ⟨hgood p hp.1, hp.1⟩).2.symm)
  have hRP' : (R ∪ P)ᶜ = C.toChain.stageMap 2 ⁻¹' (Kc.arc j '' Icc ta tb)ᶜ := by
    rw [hRPeq]
    rfl
  have hpt : ∀ y ∈ Bs.base 1, Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ P →
      (actualSlotsV2_BAUGD S).stageProj 2 y ∈ Ω₀ := by
    intro y hy hP
    rcases (hFT y hy {z | z = Kc.arc j ta ∨ z = Kc.arc j tb}).mp hP with h | h
    · rw [h]
      exact hya
    · rw [h]
      exact hyb
  refine ⟨h, hcont, fun y hy => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hsgn y hy
    refine ⟨h1.trans (hFT y hy (Kc.arc j '' Ioo ta tb)),
      h2.trans (hFT y hy {z | z = Kc.arc j ta ∨ z = Kc.arc j tb}), ?_⟩
    rw [h3, hRP']
    exact (hFT y hy (Kc.arc j '' Icc ta tb)ᶜ)
  · intro y hy h0
    have hP := (hsgn y hy).2.1.mp h0
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm y hy hP
    refine ⟨V ∩ (actualSlotsV2_BAUGD S).stageProj 2 ⁻¹' Ω₀,
      hVo.inter (hΩo.preimage ((actualSlotsV2_BAUGD S).stageProj 2).continuous),
      ⟨hyV, hpt y hy hP⟩, ?_⟩
    exact ((hcd.comp ((actualSlotsV2_BAUGD S).stageProj 2).contDiff.contDiffOn
      (fun z hz => hz)).mono inter_subset_right).congr fun z hz => hVeq z hz.1
  · intro p hp h0
    have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
    have hP := (hsgn _ hy).2.1.mp h0
    have hpP : p ∈ P := hP ⟨hp, rfl⟩
    have hpX3 : p ∈ Bs.source 2 := by
      rw [Bs.slim_source_eq]
      rcases hpP with h | h
      · exact show C.toChain.stageMap 2 p ∈ Bs.base 2 by
          rw [h]
          exact Kc.arc_subset_base j ⟨ta, hta1, rfl⟩
      · exact show C.toChain.stageMap 2 p ∈ Bs.base 2 by
          rw [h]
          exact Kc.arc_subset_base j ⟨tb, htb1, rfl⟩
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm _ hy hP
    have hheq : (fun q => h (C.toChain.stageMap 1 q)) =ᶠ[𝓝 p]
        fun q => a₀ (C.toChain.stageMap 2 q) := by
      filter_upwards [(hVo.preimage hf₂).mem_nhds hyV] with q hq
      rw [hVeq _ hq, hπ q]
    obtain ⟨hsm2, hreg2⟩ := hreg p hpX3 hpP
    have hreg3 : mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 := by
      rw [mvfderiv_congr_nhds_BG4 hheq]
      exact mvfderiv_ne_zero_iff_BCG6K.mpr hreg2
    refine ⟨hsm2.congr_of_eventuallyEq hheq, hreg3, fun hT => ?_⟩
    have hΩy : (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 1 p) ∈ Ω₀ :=
      hpt _ hy hP
    have hca : ContDiffAt ℝ ∞ (fun z => a₀ ((actualSlotsV2_BAUGD S).stageProj 2 z))
        (C.toChain.stageMap 1 p) :=
      (hcd.contDiffAt (hΩo.mem_nhds hΩy)).comp (C.toChain.stageMap 1 p)
        ((actualSlotsV2_BAUGD S).stageProj 2).contDiff.contDiffAt
    have hhd : DifferentiableAt ℝ h (C.toChain.stageMap 1 p) :=
      (hca.differentiableAt (by simp)).congr_of_eventuallyEq
        (Filter.mem_of_superset (hVo.mem_nhds hyV) fun z hz => hVeq z hz)
    exact C.surjective_comp_height_BG4 (Bs.source_one_subset_edgeParent_BIFc hp) hT hhd hreg3

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
