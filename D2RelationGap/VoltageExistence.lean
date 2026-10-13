import D2RelationGap.IntegerHeights

/-!
Nonexact integer voltages for actual finite ordered simplicial chains.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the tower.
Character/presentation/geometric adequacy, the fixed source and tower remain open.
-/
noncomputable section
namespace D2RelationGap.VoltageExistence
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops PathChains IntegerHeights SimplicialImages
variable {V K : Type*} [LinearOrder V] [Field K]

theorem ordinary_range_le_kernel (A : PreAbstractSimplicialComplex V) :
    (ordinaryTwo A).range ≤ (ordinaryOne A).ker := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have h := unit_boundary_chain (trivialTransport (K := ℚ) A)
  rw [ordinary_coeff] at h
  exact DFunLike.congr_fun h y

/-- The cardinal inequality leaves an ordinary rational cycle outside the boundaries. -/
theorem exists_nonboundary_cycle (A : PreAbstractSimplicialComplex V)
    [Fintype (Vertex A)] [Fintype (Edge A)] [Fintype (Triangle A)] (r : Vertex A)
    (hcount : Fintype.card (Vertex A) + Fintype.card (Triangle A) ≤ Fintype.card (Edge A)) :
    ∃ z : Edge A →₀ ℚ, z ∈ (ordinaryOne A).ker ∧ z ∉ (ordinaryTwo A).range := by
  have hns := trivial_boundary_not_surjective (K := ℚ) A r
  rw [ordinary_coeff] at hns
  have hne : (ordinaryOne A).range ≠ ⊤ := fun he => hns (LinearMap.range_eq_top.mp he)
  have hdim1 := Submodule.finrank_lt hne
  rw [Module.finrank_finsupp_self] at hdim1
  have hdim2 := (ordinaryTwo A).finrank_range_le
  rw [Module.finrank_finsupp_self] at hdim2
  have hn := (ordinaryOne A).finrank_range_add_finrank_ker
  rw [Module.finrank_finsupp_self] at hn
  have hlt : Module.finrank ℚ (ordinaryTwo A).range < Module.finrank ℚ (ordinaryOne A).ker := by omega
  have hproper : (ordinaryTwo A).range < (ordinaryOne A).ker := by
    apply lt_of_le_of_ne (ordinary_range_le_kernel A)
    intro he
    rw [he] at hlt
    exact (lt_irrefl _ hlt)
  exact IsConcreteLE.exists_of_lt hproper

/-- Separation is performed on the actual quotient vector space, not assumed. -/
theorem exists_closed_functional (A : PreAbstractSimplicialComplex V)
    [Fintype (Vertex A)] [Fintype (Edge A)] [Fintype (Triangle A)] (r : Vertex A)
    (hcount : Fintype.card (Vertex A) + Fintype.card (Triangle A) ≤ Fintype.card (Edge A)) :
    ∃ (z : Edge A →₀ ℚ) (phi : (Edge A →₀ ℚ) →ₗ[ℚ] ℚ),
      z ∈ (ordinaryOne A).ker ∧ phi z ≠ 0 ∧ phi.comp (ordinaryTwo A) = 0 := by
  obtain ⟨z, hz, hnot⟩ := exists_nonboundary_cycle A r hcount
  obtain ⟨phi, hp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨z, phi, hz, hp, ?_⟩
  apply LinearMap.ext
  intro t
  have hm : phi (ordinaryTwo A t) ∈ (ordinaryTwo A).range.map phi :=
    ⟨ordinaryTwo A t, ⟨t, rfl⟩, rfl⟩
  rw [hmap] at hm
  exact hm

/-- A product of positive denominators suffices; minimality/primitive normalization is unnecessary. -/
theorem integer_multiple {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ b : ι → ℤ, ∀ i, (b i : ℚ) = (D : ℚ) * q i := by
  classical
  let d : ℕ := ∏ i : ι, (q i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ => (q i).den_pos)
  refine ⟨(d : ℤ), by exact_mod_cast (Nat.ne_of_gt hd), ?_⟩
  refine ⟨fun i => (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ), ?_⟩
  intro i
  have hp : ((∏ j ∈ Finset.univ.erase i, (q j).den : ℕ) : ℚ) * (q i).den = (d : ℚ) := by
    exact_mod_cast (Finset.prod_erase_mul Finset.univ (fun j => (q j).den) (Finset.mem_univ i))
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [← hp, ← Rat.mul_den_eq_num (q i)]
  ring

def pairVoltage (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ) (u v : V) : ℤ := by
  classical
  exact if hf : ({u, v} : Finset V) ∈ A then
    if huv : u < v then b ⟨u, v, huv, hf⟩ else
    if hvu : v < u then -b ⟨v, u, hvu, by simpa [Finset.pair_comm] using hf⟩ else 0
  else 0

theorem pairVoltage_diagonal (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ) (u : V) :
    pairVoltage A b u u = 0 := by simp [pairVoltage]

theorem pairVoltage_reverse (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) : pairVoltage A b v u = -pairVoltage A b u v := by
  have hr : ({v, u} : Finset V) ∈ A := by simpa [Finset.pair_comm] using h
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [pairVoltage, h, hr, huv, not_lt_of_gt huv]
  · simp [pairVoltage]
  · simp [pairVoltage, h, hr, hvu, not_lt_of_gt hvu]

theorem pairVoltage_ordered (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ) (e : Edge A) :
    pairVoltage A b e.src e.dst = b e := by simp [pairVoltage, e.face, e.ordered]

theorem ordered_flat (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ)
    (hb : ∀ t : Triangle A, b (face01 t) + b (face12 t) = b (face02 t))
    (u v w : V) (huv : u < v) (hvw : v < w) (h : ({u, v, w} : Finset V) ∈ A) :
    pairVoltage A b u v + pairVoltage A b v w = pairVoltage A b u w := by
  let t : Triangle A := ⟨u, v, w, huv, hvw, h⟩
  have he01 := pairVoltage_ordered A b (face01 t)
  have he12 := pairVoltage_ordered A b (face12 t)
  have he02 := pairVoltage_ordered A b (face02 t)
  change pairVoltage A b u v = b (face01 t) at he01
  change pairVoltage A b v w = b (face12 t) at he12
  change pairVoltage A b u w = b (face02 t) at he02
  rw [he01, he12, he02]
  exact hb t

theorem pairVoltage_flat (A : PreAbstractSimplicialComplex V) (b : Edge A → ℤ)
    (hb : ∀ t : Triangle A, b (face01 t) + b (face12 t) = b (face02 t)) :
    FlatVoltage A (pairVoltage A b) := by
  intro u v w h
  have hr01 := pairVoltage_reverse A b u v (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  have hr02 := pairVoltage_reverse A b u w (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  have hr12 := pairVoltage_reverse A b v w (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  rcases lt_trichotomy u v with huv | rfl | hvu
  · rcases lt_trichotomy v w with hvw | rfl | hwv
    · exact ordered_flat A b hb u v w huv hvw h
    · simp [pairVoltage_diagonal]
    · rcases lt_trichotomy u w with huw | rfl | hwu
      · have ht := ordered_flat A b hb u w v huw hwv (by convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        omega
      · simp [pairVoltage_diagonal] at hr01 ⊢; omega
      · have ht := ordered_flat A b hb w u v hwu huv (by convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        omega
  · simp [pairVoltage_diagonal]
  · rcases lt_trichotomy u w with huw | rfl | hwu
    · have ht := ordered_flat A b hb v u w hvu huw (by convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      omega
    · simp [pairVoltage_diagonal] at hr01 ⊢; omega
    · rcases lt_trichotomy v w with hvw | rfl | hwv
      · have ht := ordered_flat A b hb v w u hvw hwu (by convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        omega
      · simp [pairVoltage_diagonal]
      · have ht := ordered_flat A b hb w v u hwv hvu (by convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        omega

theorem scaled_coefficients_closed (A : PreAbstractSimplicialComplex V)
    (phi : (Edge A →₀ ℚ) →ₗ[ℚ] ℚ) (hc : phi.comp (ordinaryTwo A) = 0)
    (D : ℤ) (b : Edge A → ℤ)
    (hb : ∀ e, (b e : ℚ) = (D : ℚ) * phi (Finsupp.single e 1)) :
    ∀ t : Triangle A, b (face01 t) + b (face12 t) = b (face02 t) := by
  intro t
  have hp : phi (Finsupp.single (face12 t) 1) - phi (Finsupp.single (face02 t) 1) +
      phi (Finsupp.single (face01 t) 1) = 0 := by
    have h := DFunLike.congr_fun hc (Finsupp.single t 1)
    simpa [ordinaryTwo, boundaryTwo_single] using h
  have hq : (b (face01 t) : ℚ) + (b (face12 t) : ℚ) = (b (face02 t) : ℚ) := by
    rw [hb, hb, hb]
    calc
      _ = (D : ℚ) * (phi (Finsupp.single (face12 t) 1) -
          phi (Finsupp.single (face02 t) 1) + phi (Finsupp.single (face01 t) 1)) +
          (D : ℚ) * phi (Finsupp.single (face02 t) 1) := by ring
      _ = _ := by rw [hp]; ring
  exact_mod_cast hq

theorem evaluate_scaled (A : PreAbstractSimplicialComplex V)
    (phi : (Edge A →₀ ℚ) →ₗ[ℚ] ℚ) (D : ℤ) (b : Edge A → ℤ)
    (hb : ∀ e, (b e : ℚ) = (D : ℚ) * phi (Finsupp.single e 1)) :
    evaluate A (pairVoltage A b) = (D : ℚ) • phi := by
  apply Finsupp.lhom_ext
  intro e c
  have hs : Finsupp.single e c = c • Finsupp.single e (1 : ℚ) := by simp
  simp only [evaluate, Finsupp.linearCombination_single, pairVoltage_ordered,
    hb, LinearMap.smul_apply, smul_eq_mul]
  rw [hs, map_smul, smul_eq_mul]
  ring

theorem exact_evaluate_factor (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : ExactVoltage A a) :
    ∃ psi : (Vertex A →₀ ℚ) →ₗ[ℚ] ℚ, evaluate A a = psi.comp (ordinaryOne A) := by
  obtain ⟨p, hp⟩ := ha
  refine ⟨Finsupp.linearCombination ℚ (fun v : Vertex A => (p v.val : ℚ)), ?_⟩
  apply Finsupp.lhom_ext
  intro e c
  simp [evaluate, ordinaryOne, boundaryOne, VoltageChains.baseOne, incidence,
    hp e.src e.dst e.face, Int.cast_sub, mul_sub]

/-- The integer voltage has a detected period, so cannot be a vertex coboundary. -/
theorem exists_nonexact_integer_voltage (A : PreAbstractSimplicialComplex V)
    [Fintype (Vertex A)] [Fintype (Edge A)] [Fintype (Triangle A)] (r : Vertex A)
    (hcount : Fintype.card (Vertex A) + Fintype.card (Triangle A) ≤ Fintype.card (Edge A)) :
    ∃ a : V → V → ℤ, FlatVoltage A a ∧ ¬ ExactVoltage A a := by
  obtain ⟨z, phi, hz, hphi, hclosed⟩ := exists_closed_functional A r hcount
  obtain ⟨D, hD, b, hb⟩ := integer_multiple (fun e => phi (Finsupp.single e 1))
  refine ⟨pairVoltage A b, pairVoltage_flat A b (scaled_coefficients_closed A phi hclosed D b hb), ?_⟩
  intro he
  obtain ⟨psi, hpsi⟩ := exact_evaluate_factor A (pairVoltage A b) he
  have hev : evaluate A (pairVoltage A b) z = 0 := by
    rw [hpsi]
    change psi (ordinaryOne A z) = 0
    rw [show ordinaryOne A z = 0 from hz, map_zero]
  rw [evaluate_scaled A phi D b hb] at hev
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  exact (mul_ne_zero hDq hphi) hev

/-- Uses precisely supplied holonomy and actual finite weighted chains. -/
theorem exists_voltage_from_holonomy
    (A : PreAbstractSimplicialComplex V) [Fintype (Vertex A)] [Fintype (Edge A)]
    [Fintype (Triangle A)] (tau : Transport (K := K) A) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (c : Loop A r)
    (hc : holonomy tau r c ≠ 1) (h2 : Function.Injective (boundaryTwo A (coeff tau))) :
    ∃ a : V → V → ℤ, FlatVoltage A a ∧ ¬ ExactVoltage A a :=
  exists_nonexact_integer_voltage A r (finite_cell_bound tau r paths c hc h2)

theorem zero_scale_is_exact (A : PreAbstractSimplicialComplex V) :
    ExactVoltage A (pairVoltage A (fun _ => 0)) := by
  refine ⟨fun _ => 0, ?_⟩
  intro u v h
  simp [pairVoltage, h]

theorem rounding_without_scaling_rejected :
    ¬ ∃ b : Fin 1 → ℤ, ∀ i, (b i : ℚ) = (1 / 2 : ℚ) := by
  rintro ⟨b, hb⟩
  have hq : ((2 * b 0 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hb]
    norm_num
  have hi : 2 * b 0 = 1 := by exact_mod_cast hq
  omega

theorem gradient_exact (A : PreAbstractSimplicialComplex V) (p : V → ℤ) :
    ExactVoltage A (pairVoltage A (fun e => p e.dst - p e.src)) := by
  refine ⟨p, ?_⟩
  intro u v h
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [pairVoltage, h, huv]
  · simp [pairVoltage]
  · simp [pairVoltage, h, hvu, not_lt_of_gt hvu]

theorem nonzero_exact_voltage_rejected :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let a := pairVoltage A (fun e => (e.dst.val : ℤ) - (e.src.val : ℤ))
    a 0 1 ≠ 0 ∧ ExactVoltage A a := by
  dsimp only
  refine ⟨?_, gradient_exact _ (fun v : Fin 2 => (v.val : ℤ))⟩
  have h : ({0, 1} : Finset (Fin 2)) ∈ (⊤ : PreAbstractSimplicialComplex (Fin 2)) :=
    Finset.insert_nonempty _ _
  norm_num [pairVoltage, h]

end D2RelationGap.VoltageExistence
