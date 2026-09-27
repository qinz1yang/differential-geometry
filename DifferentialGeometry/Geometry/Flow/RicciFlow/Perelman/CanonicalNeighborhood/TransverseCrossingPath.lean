import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry
import Mathlib.Analysis.Normed.Module.Connected


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


theorem MinimizingArm.edistOf_eq {g : SmoothRiemannianMetric I3 M} {x : M}
    (a : MinimizingArm g x) {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) a.length)
    (hz : z ∈ Icc (0 : ℝ) a.length) :
    riemannianEDistOf g (a.point y) (a.point z) = ENNReal.ofReal |y - z| := by
  have hd : (riemannianEDistOf g (a.point y) (a.point z)).toReal = |y - z| :=
    a.minimizing y hy z hz
  rcases eq_or_ne (riemannianEDistOf g (a.point y) (a.point z)) ⊤ with htop | hne
  · exfalso
    rw [htop, ENNReal.toReal_top] at hd
    have hyz : y = z := by
      have h := abs_eq_zero.mp hd.symm
      linarith
    rw [hyz, riemannianEDistOf_self] at htop
    exact (by simp : (0 : ℝ≥0∞) ≠ ⊤) htop
  · exact (ENNReal.ofReal_toReal hne).symm.trans (congrArg ENNReal.ofReal hd)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem MinimizingArm.continuousOn_point [T2Space M] {g : SmoothRiemannianMetric I3 M} {x : M}
    (a : MinimizingArm g x) : ContinuousOn a.point (Icc 0 a.length) := by
  let : RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I3
  let : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I3 M
  have hlip : LipschitzOnWith 1 a.point (Icc 0 a.length) := by
    intro y hy z hz
    rw [IsRiemannianManifold.out (I := I3) (a.point y) (a.point z), ENNReal.coe_one,
      one_mul, edist_dist, Real.dist_eq]
    exact le_of_eq (a.edistOf_eq hy hz)
  exact hlip.continuousOn


theorem exists_spherePath (p q : Sphere 2) :
    ∃ γ : ℝ → Sphere 2, Continuous γ ∧ γ (1 / 3) = p ∧ γ (2 / 3) = q := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2 + 1)
  have hpc : IsPathConnected (Sphere 2) := isPathConnected_sphere hrank 0 zero_le_one
  let : PathConnectedSpace (Sphere 2) := isPathConnected_iff_pathConnectedSpace.mp hpc
  obtain ⟨P⟩ := PathConnectedSpace.joined p q
  have hzero : P.extend (3 * (1 / 3 : ℝ) - 1) = p := by
    rw [(by norm_num : 3 * (1 / 3 : ℝ) - 1 = (0 : ℝ))]
    exact P.extend_zero
  have hone : P.extend (3 * (2 / 3 : ℝ) - 1) = q := by
    rw [(by norm_num : 3 * (2 / 3 : ℝ) - 1 = (1 : ℝ))]
    exact P.extend_one
  exact ⟨fun τ => P.extend (3 * τ - 1), P.continuous_extend.comp (by fun_prop), hzero, hone⟩


theorem exists_transversePath_of_opposite_arms [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ Icc (0 : ℝ) a.length) (hv : v ∈ Icc (0 : ℝ) b.length)
    {p q : Sphere 2} {k l : ℝ}
    (ha : a.point s = neck.map (p, k)) (hb : b.point v = neck.map (q, l))
    (hkl : k * l < 0) (hk : |k| < eps⁻¹) (hl : |l| < eps⁻¹)
    (hano : ∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ)))
    (hbno : ∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (univ ×ˢ ({0} : Set ℝ))),
      (0 < l → path.intersection = 1) ∧ (l < 0 → path.intersection = -1) := by
  have hepspos : (0 : ℝ) < eps := neck.eps_pos
  have hepsinv : (11 : ℝ) < eps⁻¹ := by
    have hcancel : eps * eps⁻¹ = 1 := mul_inv_cancel₀ hepspos.ne'
    have hlt : eps * 11 < eps * eps⁻¹ := by
      rw [hcancel]
      nlinarith [neck.eps_small]
    exact lt_of_mul_lt_mul_left hlt hepspos.le
  obtain ⟨hk1, hk2⟩ := abs_lt.mp hk
  obtain ⟨hl1, hl2⟩ := abs_lt.mp hl
  obtain ⟨γ, hγc, hγp, hγq⟩ := exists_spherePath p q
  have hLb : ∀ τ ∈ Icc (1 / 3 : ℝ) (2 / 3),
      k + (l - k) * (3 * τ - 1) ∈ Ioo (-eps⁻¹) eps⁻¹ := by
    intro τ hτ
    have h1 : (0 : ℝ) ≤ 3 * τ - 1 := by linarith [hτ.1]
    have h2 : (0 : ℝ) ≤ 1 - (3 * τ - 1) := by linarith [hτ.2]
    rcases le_total k l with hle | hle
    · have p1 := mul_nonneg (sub_nonneg.mpr hle) h1
      have p2 := mul_nonneg (sub_nonneg.mpr hle) h2
      exact ⟨by nlinarith, by nlinarith⟩
    · have p1 := mul_nonneg (sub_nonneg.mpr hle) h1
      have p2 := mul_nonneg (sub_nonneg.mpr hle) h2
      exact ⟨by nlinarith, by nlinarith⟩
  have hLmem : ∀ τ ∈ Icc (1 / 3 : ℝ) (2 / 3),
      ((γ τ, k + (l - k) * (3 * τ - 1)) : Cylinder) ∈ neck.map.source := fun τ hτ =>
    neck.domain ⟨mem_univ _, hLb τ hτ⟩
  have hmapsA : ∀ τ ∈ Icc (0 : ℝ) (1 / 3),
      a.length - 3 * τ * (a.length - s) ∈ Icc s a.length := by
    intro τ hτ
    have h0 : (0 : ℝ) ≤ a.length - s := by linarith [hs.2]
    have h1 : (0 : ℝ) ≤ 3 * τ := by linarith [hτ.1]
    have h2 : (0 : ℝ) ≤ 1 - 3 * τ := by linarith [hτ.2]
    have p1 := mul_nonneg h1 h0
    have p2 := mul_nonneg h2 h0
    exact ⟨by nlinarith, by nlinarith⟩
  have hmapsB : ∀ τ ∈ Icc (2 / 3 : ℝ) 1,
      v + (3 * τ - 2) * (b.length - v) ∈ Icc v b.length := by
    intro τ hτ
    have h0 : (0 : ℝ) ≤ b.length - v := by linarith [hv.2]
    have h1 : (0 : ℝ) ≤ 3 * τ - 2 := by linarith [hτ.1]
    have h2 : (0 : ℝ) ≤ 1 - (3 * τ - 2) := by linarith [hτ.2]
    have p1 := mul_nonneg h1 h0
    have p2 := mul_nonneg h2 h0
    exact ⟨by nlinarith, by nlinarith⟩
  obtain ⟨c, hcA, hcM, hcB⟩ :
      ∃ c : ℝ → M,
        (∀ τ : ℝ, τ ≤ 1 / 3 → c τ = a.point (a.length - 3 * τ * (a.length - s))) ∧
        (∀ τ : ℝ, 1 / 3 < τ → τ ≤ 2 / 3 →
          c τ = neck.map (γ τ, k + (l - k) * (3 * τ - 1))) ∧
        (∀ τ : ℝ, 2 / 3 < τ → c τ = b.point (v + (3 * τ - 2) * (b.length - v))) := by
    refine ⟨fun τ => if τ ≤ 1 / 3 then a.point (a.length - 3 * τ * (a.length - s))
      else if τ ≤ 2 / 3 then neck.map (γ τ, k + (l - k) * (3 * τ - 1))
      else b.point (v + (3 * τ - 2) * (b.length - v)),
      fun τ hτ => if_pos hτ, fun τ h1 h2 => ?_, fun τ h => ?_⟩
    · exact (if_neg (not_le.mpr h1)).trans (if_pos h2)
    · exact (if_neg (not_le.mpr (by linarith : (1 : ℝ) / 3 < τ))).trans (if_neg (not_le.mpr h))
  have hcleft : ∀ τ ∈ Icc (0 : ℝ) (1 / 3),
      c τ = a.point (a.length - 3 * τ * (a.length - s)) := fun τ hτ => hcA τ hτ.2
  have hcmid : ∀ τ ∈ Icc (1 / 3 : ℝ) (2 / 3),
      c τ = neck.map (γ τ, k + (l - k) * (3 * τ - 1)) := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h | h
    · subst h
      rw [hcA (1 / 3) le_rfl]
      have e1 : a.length - 3 * (1 / 3 : ℝ) * (a.length - s) = s := by ring
      have e2 : k + (l - k) * (3 * (1 / 3 : ℝ) - 1) = k := by ring
      rw [e1, e2, hγp, ha]
    · exact hcM τ h hτ.2
  have hcright : ∀ τ ∈ Icc (2 / 3 : ℝ) 1,
      c τ = b.point (v + (3 * τ - 2) * (b.length - v)) := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h | h
    · subst h
      rw [hcM (2 / 3) (by norm_num) le_rfl]
      have e1 : k + (l - k) * (3 * (2 / 3 : ℝ) - 1) = l := by ring
      have e2 : v + (3 * (2 / 3 : ℝ) - 2) * (b.length - v) = v := by ring
      rw [e1, hγq, e2, hb]
    · exact hcB τ h
  have hstart : c 0 = a.point a.length := by
    rw [hcA 0 (by norm_num)]
    congr 1
    ring
  have hfinish : c 1 = b.point b.length := by
    rw [hcB 1 (by norm_num)]
    congr 1
    ring
  have hcontA : ContinuousOn
      (fun τ : ℝ => a.point (a.length - 3 * τ * (a.length - s))) (Icc 0 (1 / 3)) := by
    refine a.continuousOn_point.comp (by fun_prop) ?_
    intro τ hτ
    exact ⟨le_trans hs.1 (hmapsA τ hτ).1, (hmapsA τ hτ).2⟩
  have hcontB : ContinuousOn
      (fun τ : ℝ => b.point (v + (3 * τ - 2) * (b.length - v))) (Icc (2 / 3) 1) := by
    refine b.continuousOn_point.comp (by fun_prop) ?_
    intro τ hτ
    exact ⟨le_trans hv.1 (hmapsB τ hτ).1, (hmapsB τ hτ).2⟩
  have hcontM : ContinuousOn
      (fun τ : ℝ => neck.map (γ τ, k + (l - k) * (3 * τ - 1))) (Icc (1 / 3) (2 / 3)) := by
    refine neck.map.contMDiffOn_toFun.continuousOn.comp ?_ hLmem
    exact (hγc.prodMk (by fun_prop)).continuousOn
  have hcont : ContinuousOn c (Icc 0 1) := by
    have h1 : ContinuousOn c (Icc 0 (1 / 3)) := hcontA.congr hcleft
    have h2 : ContinuousOn c (Icc (1 / 3) (2 / 3)) := hcontM.congr hcmid
    have h3 : ContinuousOn c (Icc (2 / 3) 1) := hcontB.congr hcright
    have e1 : Icc (1 / 3 : ℝ) (2 / 3) ∪ Icc (2 / 3 : ℝ) 1 = Icc (1 / 3 : ℝ) 1 :=
      Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
    have e2 : Icc (0 : ℝ) (1 / 3) ∪ Icc (1 / 3 : ℝ) 1 = Icc (0 : ℝ) 1 :=
      Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
    have hsplit : Icc (0 : ℝ) 1 = Icc 0 (1 / 3) ∪ (Icc (1 / 3) (2 / 3) ∪ Icc (2 / 3) 1) := by
      rw [e1, e2]
    rw [hsplit]
    exact h1.union_of_isClosed (h2.union_of_isClosed h3 isClosed_Icc isClosed_Icc)
      isClosed_Icc (isClosed_Icc.union isClosed_Icc)
  have hcollar : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ neck.map.source := by
    rintro ⟨y, w⟩ ⟨-, hw⟩
    refine neck.domain ⟨mem_univ _, ?_⟩
    have h1 : (-1 : ℝ) ≤ w := hw.1
    have h2 : w ≤ 1 := hw.2
    constructor <;> linarith
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkl
    exact absurd hkl (lt_irrefl 0)
  have hl0 : l ≠ 0 := by
    intro h
    rw [h, mul_zero] at hkl
    exact absurd hkl (lt_irrefl 0)
  have hlk : l - k ≠ 0 := by
    intro h
    have hlek : l = k := by linarith
    rw [hlek] at hkl
    nlinarith [mul_self_nonneg k]
  have hkl' : k - l ≠ 0 := by
    intro h
    exact hlk (by linarith)
  obtain ⟨τ₀, hτ₀mem, hτ₀zero⟩ :
      ∃ τ₀ : ℝ, τ₀ ∈ Ioo (1 / 3 : ℝ) (2 / 3) ∧ k + (l - k) * (3 * τ₀ - 1) = 0 := by
    have key : ∀ u : ℝ, 0 < u → u < 1 → k + (l - k) * u = 0 →
        ∃ τ₀ : ℝ, τ₀ ∈ Ioo (1 / 3 : ℝ) (2 / 3) ∧ k + (l - k) * (3 * τ₀ - 1) = 0 := by
      intro u hu0 hu1 hueq
      refine ⟨(1 + u) / 3, ⟨by linarith, by linarith⟩, ?_⟩
      have h3 : 3 * ((1 + u) / 3) - 1 = u := by ring
      rw [h3]
      exact hueq
    rcases lt_trichotomy k 0 with hkneg | hkzero | hkpos
    · have hlpos : 0 < l := by
        by_contra hcon
        have hcon' : l ≤ 0 := not_lt.mp hcon
        nlinarith [mul_nonneg (neg_nonneg.mpr hkneg.le) (neg_nonneg.mpr hcon')]
      have hd : (0 : ℝ) < l - k := by linarith
      have hcancel : (l - k) * (-k / (l - k)) = -k := by
        field_simp
      refine key (-k / (l - k)) (div_pos (by linarith) hd)
        ((div_lt_one hd).mpr (by linarith)) ?_
      rw [hcancel]
      ring
    · exact absurd hkzero hk0
    · have hlneg : l < 0 := by
        by_contra hcon
        have hcon' : 0 ≤ l := not_lt.mp hcon
        nlinarith [mul_nonneg hkpos.le hcon']
      have hd : (0 : ℝ) < k - l := by linarith
      have hcancel : (l - k) * (k / (k - l)) = -k := by
        field_simp
        ring
      refine key (k / (k - l)) (div_pos hkpos hd) ((div_lt_one hd).mpr (by linarith)) ?_
      rw [hcancel]
      ring
  have hzero_unique : ∀ τ : ℝ, k + (l - k) * (3 * τ - 1) = 0 → τ = τ₀ := by
    intro τ hτ
    have h : (l - k) * (3 * τ - 1) = (l - k) * (3 * τ₀ - 1) := by linarith
    have h2 : 3 * τ - 1 = 3 * τ₀ - 1 := mul_left_cancel₀ hlk h
    linarith
  have hsymm : ∀ z ∈ neck.map.source, neck.map.symm (neck.map z) = z := by
    intro z hz
    exact neck.map.left_inv' hz
  have hsphere_mid : ∀ τ ∈ Icc (1 / 3 : ℝ) (2 / 3),
      (neck.map (γ τ, k + (l - k) * (3 * τ - 1)) ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ)) ↔
        τ = τ₀) := by
    intro τ hτ
    constructor
    · rintro ⟨z, hz, hzeq⟩
      have hz2 : z.2 = 0 := hz.2
      have hzsrc : z ∈ neck.map.source := by
        refine neck.domain ⟨mem_univ _, ?_⟩
        rw [hz2]
        constructor <;> linarith
      have h1 := hsymm z hzsrc
      rw [hzeq, hsymm _ (hLmem τ hτ)] at h1
      rw [← h1] at hz2
      exact hzero_unique τ hz2
    · intro hτeq
      rw [hτeq, hτ₀zero]
      exact ⟨(γ τ₀, (0 : ℝ)), ⟨mem_univ _, rfl⟩, rfl⟩
  have hleft_no : ∀ τ ∈ Icc (0 : ℝ) (1 / 3),
      c τ ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ)) := by
    intro τ hτ
    rw [hcleft τ hτ]
    exact hano _ (hmapsA τ hτ)
  have hright_no : ∀ τ ∈ Icc (2 / 3 : ℝ) 1,
      c τ ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ)) := by
    intro τ hτ
    rw [hcright τ hτ]
    exact hbno _ (hmapsB τ hτ)
  have hint : ∀ σ ∈ ({τ₀} : Finset ℝ), σ ∈ Ioo (0 : ℝ) 1 := by
    intro σ hσ
    rw [Finset.mem_singleton] at hσ
    subst hσ
    exact ⟨by linarith [hτ₀mem.1], by linarith [hτ₀mem.2]⟩
  have hcross : ∀ σ ∈ Icc (0 : ℝ) 1,
      (c σ ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ)) ↔ σ ∈ ({τ₀} : Finset ℝ)) := by
    intro σ hσ
    rw [Finset.mem_singleton]
    rcases le_or_gt σ (1 / 3 : ℝ) with h | h
    · constructor
      · intro hmem
        exact absurd hmem (hleft_no σ ⟨hσ.1, h⟩)
      · intro he
        exfalso
        rw [he] at h
        linarith [hτ₀mem.1]
    · rcases le_or_gt σ (2 / 3 : ℝ) with h2 | h2
      · rw [hcmid σ ⟨h.le, h2⟩]
        exact hsphere_mid σ ⟨h.le, h2⟩
      · constructor
        · intro hmem
          exact absurd hmem (hright_no σ ⟨h2.le, hσ.2⟩)
        · intro he
          exfalso
          rw [he] at h2
          linarith [hτ₀mem.2]
  have hevent : (fun w : ℝ => (neck.map.symm (c w)).2) =ᶠ[𝓝 τ₀]
      (fun w : ℝ => k + (l - k) * (3 * w - 1)) := by
    have hopen : Ioo (1 / 3 : ℝ) (2 / 3) ∈ 𝓝 τ₀ := isOpen_Ioo.mem_nhds hτ₀mem
    filter_upwards [hopen] with w hw
    have hw' : w ∈ Icc (1 / 3 : ℝ) (2 / 3) := ⟨hw.1.le, hw.2.le⟩
    rw [hcmid w hw', hsymm _ (hLmem w hw')]
  have hderiv : deriv (fun w : ℝ => (neck.map.symm (c w)).2) τ₀ = (l - k) * 3 := by
    rw [hevent.deriv_eq]
    have h0 : HasDerivAt (fun w : ℝ => w) 1 τ₀ := hasDerivAt_id τ₀
    have h1 : HasDerivAt (fun w : ℝ => 3 * w - 1) 3 τ₀ := by
      simpa using (h0.const_mul (3 : ℝ)).sub_const 1
    exact ((h1.const_mul (l - k)).const_add k).deriv
  have htrans : ∀ σ ∈ ({τ₀} : Finset ℝ),
      deriv (fun w : ℝ => (neck.map.symm (c w)).2) σ ≠ 0 := by
    intro σ hσ
    rw [Finset.mem_singleton] at hσ
    subst hσ
    rw [hderiv]
    intro h
    exact hlk (by linarith)
  refine ⟨⟨c, hcont, hstart, hfinish, neck.map, hcollar, rfl, {τ₀}, hint, hcross, htrans⟩,
    ?_, ?_⟩
  · intro hlpos
    have hkneg : k < 0 := by
      by_contra hcon
      have hcon' : 0 ≤ k := not_lt.mp hcon
      nlinarith [mul_nonneg hcon' hlpos.le]
    have hpos : (0 : ℝ) < (l - k) * 3 := by linarith
    simp only [TransversePath.intersection, Finset.sum_singleton, hderiv, if_pos hpos]
  · intro hlneg
    have hkpos : (0 : ℝ) < k := by
      by_contra hcon
      have hcon' : k ≤ 0 := not_lt.mp hcon
      nlinarith [mul_nonneg (neg_nonneg.mpr hcon') (neg_nonneg.mpr hlneg.le)]
    have hneg : ¬ (0 : ℝ) < (l - k) * 3 := not_lt.mpr (by linarith)
    simp only [TransversePath.intersection, Finset.sum_singleton, hderiv, if_neg hneg]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
