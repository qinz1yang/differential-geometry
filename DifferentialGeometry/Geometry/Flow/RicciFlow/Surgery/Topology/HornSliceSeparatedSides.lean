import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationFrontierScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

open private horn_sides_of_complementPair from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornCentralSphereSeparation

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s} :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem exists_eventually_separated_sides_of_frontier_scalar_lt :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e →
          (∀ w ∈ frontier (P.core c), 2 * metricScalarAt D.terminal.metric w < N.scale) →
          ∃ S V W : Set D.stage.Carrier, IsOpen V ∧ IsOpen W ∧ Disjoint V W ∧
            (∀ᶠ τ in 𝓝[<] D.endTime, ∀ z ∈ S,
              riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val z ≤
                ENNReal.ofReal (7 / Real.sqrt (D.slab.flow.scalar τ N.center.val))) ∧
            ∀ {A : ℝ}, 0 < A →
              IsCompact (riemannianClosedBallOf D.terminal.metric N.center
                (4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center))) →
              (∀ w ∈ frontier (P.core c), ENNReal.ofReal
                  (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
                riemannianEDistOf D.terminal.metric N.center w) →
              ∀ᶠ τ in 𝓝[<] D.endTime,
                riemannianClosedBallOf (D.slab.flow.base.metric τ) N.center.val
                    (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) \ S ⊆ V ∪ W ∧
                ∃ p ∈ V, ∃ q ∈ W,
                  ENNReal.ofReal (A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ≤
                    riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val p ∧
                  riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val p <
                    ENNReal.ofReal (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ∧
                  ENNReal.ofReal (A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ≤
                    riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val q ∧
                  riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val q <
                    ENNReal.ofReal (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) := by
  obtain ⟨eta, heta, hsep⟩ := exists_horn_neck_end_separation_tolerance.{u}
  have hα : (0 : ℝ) < 1 / 504 := by norm_num
  have hm := neckModelTolerance_pos hα
  refine ⟨min (min eta (1 / 8646)) (neckModelTolerance (1 / 504) / 2),
    lt_min (lt_min heta (by norm_num)) (by positivity), ?_⟩
  intro D ε Λ P hε c hc e δ k N hδ hk hcenter hfs
  have hε1 : ε ≤ min eta (1 / 8646) := hε.trans (min_le_left _ _)
  have hεsmall : ε ≤ 1 / 8646 := hε1.trans (min_le_right _ _)
  have hεpos : 0 < ε := N.delta_pos.trans_le hδ
  have hlarge : (1 : ℝ) ≤ ε⁻¹ := (le_inv_comm₀ (by norm_num) hεpos).mpr (by linarith)
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hlarge)
  have hk2 : 2 ≤ k := by omega
  have hδs : δ ≤ 1 / 8646 := hδ.trans hεsmall
  have hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale := by
    intro w hw
    have h := hfs w hw
    have hhalf : (1 / 2 : ℝ) * N.scale ≤ (1 - 4323 * δ) * N.scale :=
      mul_le_mul_of_nonneg_right (by linarith) N.scale_pos.le
    linarith
  obtain ⟨Θ, hΘ, hmap⟩ := P.exists_neck_coordinates_in_horn_of_frontier_scalar_lt c hc e N hk2
    (hδs.trans (by norm_num)) hcenter hfront
  obtain ⟨p, R, -, hfl, hfr, -, hclr, -, -, hlo, hhi, -⟩ := hsep P (hε1.trans (min_le_left _ _))
    c e N hδ ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk) Θ hΘ hmap
  obtain ⟨hVo, hsub, hleft, -, -⟩ := horn_sides_of_complementPair P c e p hclr hlo
  let c0 : neckCentralOpen δ := ⟨(N.sphereMark, 0), mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos), inv_pos.mpr N.delta_pos⟩
  have hx : P.horn c e ((Θ c0).val.1, (Θ c0).val.2) = N.center := by
    change P.horn c e (Θ c0).val = N.center
    rw [hmap c0]
    exact N.marked
  have hs0 : 0 < (Θ c0).val.2 := (Θ c0).property.2
  have hbase0 : P.horn c e ((Θ c0).val.1, 0) ∈ frontier (P.core c) := by
    rw [P.horn_base_covers_boundary c hc]
    exact mem_iUnion.mpr ⟨e, (Θ c0).val.1, rfl⟩
  set V := P.positiveHornMap c e '' p.right with hVdef
  have hcovL : (N.chart '' {z | z.val.2 = 0})ᶜ ⊆ (closure V)ᶜ ∪ V := by
    intro w hwS
    by_cases hcl : w ∈ closure V
    · rcases hsub hcl with h | ⟨_, ⟨q, rfl⟩, rfl⟩
      · exact Or.inr h
      · refine absurd ⟨TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ)
          ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
            inv_pos.mpr N.delta_pos⟩, rfl, ?_⟩ hwS
        exact (hmap _).symm
    · exact Or.inl hcl
  have hΩ := D.slab.terminalRegularOpen.isOpen
  have hεm : ε ≤ neckModelTolerance (1 / 504) / 2 := hε.trans (min_le_right _ _)
  have hkm : ⌈(neckModelTolerance (1 / 504) / 2)⁻¹⌉₊ ≤ k :=
    (Nat.ceil_mono (inv_anti₀ hεpos hεm)).trans ((Nat.ceil_le_floor_add_one _).trans hk)
  have hneck := D.terminal.eventually_exists_spatialNeck_of_normalizedNeck N hα (by norm_num)
    (hδ.trans hεm) hkm
  refine ⟨Subtype.val '' (N.chart '' {z | z.val.2 = 0}), Subtype.val '' (closure V)ᶜ,
    Subtype.val '' V, hΩ.isOpenMap_subtype_val _ isClosed_closure.isOpen_compl,
    hΩ.isOpenMap_subtype_val _ hVo,
    (disjoint_image_iff Subtype.val_injective).mpr
      (disjoint_compl_left_iff_subset.mpr subset_closure), ?_, ?_⟩
  · filter_upwards [hneck] with τ hτ
    obtain ⟨nk, hnkmap⟩ := hτ
    rintro _ ⟨_, ⟨z0, hz0, rfl⟩, rfl⟩
    have hmem : (N.chart z0 : D.stage.Carrier) ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) :=
      ⟨z0.val, ⟨mem_univ _, hz0⟩, hnkmap z0⟩
    exact nk.central_sphere_subset_closedBall hmem
  intro A hA hK hbase
  have hq : 0 < metricScalarAt D.terminal.metric N.center := N.scale_scalar ▸ N.scale_pos
  set q := metricScalarAt D.terminal.metric N.center with hqdef
  set sq := Real.sqrt q with hsqdef
  have hsq : 0 < sq := Real.sqrt_pos.mpr hq
  have hsq2 : sq ^ 2 = q := Real.sq_sqrt hq.le
  have hcpt : ∀ m : ℝ, 0 < m → m ≤ 4 →
      IsCompact (riemannianClosedBallOf D.terminal.metric N.center (m * A / sq)) := by
    intro m hm0 hm4
    refine hK.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist D.terminal.metric N.center) continuous_const)
      (riemannianClosedBallOf_mono _ _ ?_)
    exact div_le_div_of_nonneg_right (by nlinarith) hsq.le
  obtain ⟨a, b, ha, hb, hda, hdb⟩ := P.exists_horn_side_points_at_distance c e p
    (fun w hw => frontier_subset_closure (hfl.symm ▸ hw))
    (fun w hw => frontier_subset_closure (hfr.symm ▸ hw))
    (Θ c0).val.1 hs0 ⟨N.sphereMark, rfl⟩ (A := 2 * A / sq) (by positivity) (Real.exp_pos (-R))
    (by rw [hx]; exact hcpt 2 (by norm_num) (by norm_num)) (by rw [hx]; exact hbase _ hbase0)
    hlo hhi
  rw [hx] at hda hdb
  have hball := D.terminal.eventually_riemannianBallOf_subset_image_closedBall N.center
    (by positivity) (hcpt 4 (by norm_num) le_rfl)
  have hlow := D.terminal.eventually_riemannianBallOf_subset_image_closedBall N.center
    (by positivity) (hcpt (7 / 4) (by norm_num) (by norm_num))
  have hlt : ENNReal.ofReal (2 * A / sq) < ENNReal.ofReal (9 * A / (4 * sq)) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by
      rw [div_lt_div_iff₀ hsq (by positivity)]
      nlinarith)
  have hupa := D.terminal.eventually_riemannianEDistOf_lt N.center (P.positiveHornMap c e a)
    (hda ▸ hlt)
  have hupb := D.terminal.eventually_riemannianEDistOf_lt N.center (P.positiveHornMap c e b)
    (hdb ▸ hlt)
  have hscal : ∀ᶠ τ in 𝓝[<] D.endTime,
      |metricScalarAt (D.slab.flow.base.metric τ) N.center.val - q| < q / 10 := by
    have h := Metric.tendsto_nhds.mp (D.terminal.tendsto_metricScalarAt N.center) (q / 10)
      (by positivity)
    filter_upwards [h] with τ hτ
    rwa [Real.dist_eq] at hτ
  filter_upwards [hball, hlow, hupa, hupb, hscal] with τ hb4 hb7 hya hyb hs
  set gτ := D.slab.flow.base.metric τ with hgτ
  set Rτ := D.slab.flow.scalar τ N.center.val with hRτ
  have hRτq : Rτ = metricScalarAt gτ N.center.val := rfl
  rw [← hRτq] at hs
  have hs1 := abs_lt.mp hs
  have hRpos : 0 < Rτ := by linarith [hs1.1]
  set sR := Real.sqrt Rτ with hsRdef
  have hsR : 0 < sR := Real.sqrt_pos.mpr hRpos
  have hsRlo : 9 / 10 * sq ≤ sR :=
    (Real.le_sqrt (by positivity) hRpos.le).mpr (by nlinarith [hs1.1])
  have hsRhi : sR ≤ 4 / 3 * sq :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [hs1.2]⟩
  have hr4 : 3 * A / sR < 16 * (4 * A / sq) / 17 := by
    rw [show 16 * (4 * A / sq) / 17 = 64 * A / (17 * sq) by field_simp; ring,
      div_lt_div_iff₀ hsR (by positivity)]
    nlinarith
  have hr7 : A / sR < 16 * (7 / 4 * A / sq) / 17 := by
    rw [show 16 * (7 / 4 * A / sq) / 17 = 28 * A / (17 * sq) by field_simp; ring,
      div_lt_div_iff₀ hsR (by positivity)]
    nlinarith
  have hr9 : 9 * A / (4 * sq) ≤ 3 * A / sR := by
    rw [div_le_div_iff₀ (by positivity) hsR]
    nlinarith
  have hfar : ∀ w : D.slab.terminalRegularOpen,
      riemannianEDistOf D.terminal.metric N.center w = ENNReal.ofReal (2 * A / sq) →
      ENNReal.ofReal (A / sR) ≤ riemannianEDistOf gτ N.center.val w.val := by
    intro w hw
    by_contra hcon
    have hmem : riemannianEDistOf gτ N.center.val w.val <
        ENNReal.ofReal (16 * (7 / 4 * A / sq) / 17) :=
      lt_of_lt_of_le (not_le.mp hcon) (ENNReal.ofReal_le_ofReal hr7.le)
    obtain ⟨w', hw', hww⟩ := hb7 hmem
    rw [Subtype.val_injective hww] at hw'
    change riemannianEDistOf D.terminal.metric N.center w ≤ _ at hw'
    rw [hw, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hw'
    exact absurd hw' (not_le.mpr (div_lt_div_of_pos_right (by linarith) hsq))
  refine ⟨?_, _, ⟨P.positiveHornMap c e a, fun hcl => disjoint_left.mp hleft ⟨a, ha, rfl⟩ hcl,
    rfl⟩, _, ⟨P.positiveHornMap c e b, ⟨b, hb, rfl⟩, rfl⟩, hfar _ hda,
    hya.trans_le (ENNReal.ofReal_le_ofReal hr9), hfar _ hdb,
    hyb.trans_le (ENNReal.ofReal_le_ofReal hr9)⟩
  rintro w ⟨hwB, hwS⟩
  have hwB' : riemannianEDistOf gτ N.center.val w < ENNReal.ofReal (16 * (4 * A / sq) / 17) :=
    lt_of_le_of_lt hwB ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hr4)
  obtain ⟨w', -, rfl⟩ := hb4 hwB'
  have hw' : w' ∈ (N.chart '' {z | z.val.2 = 0})ᶜ := fun h => hwS ⟨w', h, rfl⟩
  rcases hcovL hw' with h | h
  · exact Or.inl ⟨w', h, rfl⟩
  · exact Or.inr ⟨w', h, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end
