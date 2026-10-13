import D2RelationGap.PathChains

/-!
Integer heights from exactness of actual ordinary rational ordered chains.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the tower.
Actual Moore-source chain exactness and presentation/geometric adequacy remain open.
No rational potential or integral H1=0 is assumed in the height construction.
-/
noncomputable section
namespace D2RelationGap.IntegerHeights
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops PathChains SimplicialImages
variable {U V : Type*} [LinearOrder U] [LinearOrder V]

abbrev ordinaryOne (A : PreAbstractSimplicialComplex V) := boundaryOne A (fun _ _ => (1 : ℚ))
abbrev ordinaryTwo (A : PreAbstractSimplicialComplex V) := boundaryTwo A (fun _ _ => (1 : ℚ))

theorem trivial_unit (A : PreAbstractSimplicialComplex V) (u v : V) :
    (trivialTransport (K := ℚ) A).unit u v = 1 := by
  change (1 : ℚˣ)⁻¹ * 1 = 1
  simp

theorem ordinary_coeff (A : PreAbstractSimplicialComplex V) :
    coeff (trivialTransport (K := ℚ) A) = (fun _ _ => (1 : ℚ)) := by
  funext u v
  change ((1 : ℚˣ)⁻¹ * 1 : ℚˣ).val = 1
  simp

def integral (a : V → V → ℤ) {A : PreAbstractSimplicialComplex V} {u v : V} : Path A u v → ℤ
  | .refl _ _ => 0
  | @Path.cons _ _ _ u w _ _ p => a u w + integral a p

def evaluate (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ) :
    (Edge A →₀ ℚ) →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun e => (a e.src e.dst : ℚ))

theorem voltage_diagonal {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) (u : V) (hu : ({u} : Finset V) ∈ A) : a u u = 0 := by
  have h := ha u u u (by simpa using hu)
  omega

theorem voltage_reverse {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) (u v : V) (h : ({u, v} : Finset V) ∈ A) : a v u = -a u v := by
  have ht := ha u v u (by simpa [Finset.insert_comm, Finset.pair_comm] using h)
  rw [voltage_diagonal a ha u (vertex_mem_of_face A _ h u (by simp))] at ht
  omega

theorem evaluate_edge {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) (u v : V) (h : ({u, v} : Finset V) ∈ A) :
    evaluate A a (edge (trivialTransport (K := ℚ) A) u v h) = (a u v : ℚ) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [edge, huv, evaluate]
  · simp [edge, voltage_diagonal a ha u (vertex_mem_of_face A _ h u (by simp))]
  · simp [edge, hvu, not_lt_of_gt hvu, coeff, trivialTransport, gaugeTransport,
      evaluate, voltage_reverse a ha u v h]

theorem evaluate_boundary_zero {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) : (evaluate A a).comp (ordinaryTwo A) = 0 := by
  apply Finsupp.lhom_ext
  intro t c
  have ht := ha t.v0 t.v1 t.v2 t.face
  have hq : (a t.v0 t.v1 : ℚ) + (a t.v1 t.v2 : ℚ) = (a t.v0 t.v2 : ℚ) := by exact_mod_cast ht
  simp [ordinaryTwo, boundaryTwo_single, evaluate, face01, face02, face12]
  rw [← hq]
  ring

theorem trivial_value {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    value (trivialTransport (K := ℚ) A) p = 1 := by
  induction p with
  | refl => rfl
  | cons h p ih => simp only [value, trivial_unit, ih, mul_one]

theorem evaluate_chain {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) {u v : V} (p : Path A u v) :
    evaluate A a (chain (trivialTransport (K := ℚ) A) p) = (integral a p : ℚ) := by
  induction p with
  | refl => simp [chain, integral]
  | cons h p ih =>
      rw [chain, map_add, map_smul, evaluate_edge a ha, ih, ordinary_coeff]
      simp [integral]

theorem ordinary_chain_boundary {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    ordinaryOne A (chain (trivialTransport (K := ℚ) A) p) =
      point v (endActive p) - point u (startActive p) := by
  have h := chain_boundary (trivialTransport (K := ℚ) A) p
  rw [ordinary_coeff, trivial_value, Units.val_one, one_smul] at h
  exact h

theorem integral_path_independent {A : PreAbstractSimplicialComplex V}
    (a : V → V → ℤ) (ha : FlatVoltage A a)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    {u v : V} (p q : Path A u v) : integral a p = integral a q := by
  let tau := trivialTransport (K := ℚ) A
  let z := chain tau p - chain tau q
  have hz : z ∈ (ordinaryOne A).ker := by
    change ordinaryOne A z = 0
    rw [map_sub, ordinary_chain_boundary, ordinary_chain_boundary]
    abel
  obtain ⟨t, ht⟩ := (show z ∈ (ordinaryTwo A).range from hex.symm ▸ hz)
  have he : evaluate A a z = 0 := by
    rw [← ht]
    exact DFunLike.congr_fun (evaluate_boundary_zero a ha) t
  have hq : (integral a p : ℚ) = (integral a q : ℚ) := by
    apply sub_eq_zero.mp
    simpa only [z, tau, map_sub, evaluate_chain a ha] using he
  exact_mod_cast hq

def height {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val) (v : V) : ℤ := by
  classical
  exact if hv : ({v} : Finset V) ∈ A then integral a (paths ⟨v, hv⟩) else 0

theorem height_root_zero {A : PreAbstractSimplicialComplex V}
    (a : V → V → ℤ) (ha : FlatVoltage A a) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) : height a r paths r.val = 0 := by
  have h := integral_path_independent a ha hex (paths r) (.refl r.val r.property)
  simpa [height, r.property, integral] using h

theorem height_edge {A : PreAbstractSimplicialComplex V} (a : V → V → ℤ)
    (ha : FlatVoltage A a) (r : Vertex A) (paths : ∀ v : Vertex A, Path A r.val v.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) :
    height a r paths v - height a r paths u = a u v := by
  let pu := paths ⟨u, vertex_mem_of_face A _ h u (by simp)⟩
  let pv := paths ⟨v, vertex_mem_of_face A _ h v (by simp)⟩
  let tau := trivialTransport (K := ℚ) A
  let z := chain tau pu + edge tau u v h - chain tau pv
  have hz : z ∈ (ordinaryOne A).ker := by
    change ordinaryOne A z = 0
    simp only [z, map_sub, map_add]
    rw [ordinary_chain_boundary, ordinary_chain_boundary]
    have hb := edge_boundary tau u v h
    change boundaryOne A (coeff (trivialTransport (K := ℚ) A)) (edge tau u v h) = _ at hb
    rw [ordinary_coeff, one_smul] at hb
    rw [hb]
    abel
  have hr : z ∈ (ordinaryTwo A).range := hex.symm ▸ hz
  obtain ⟨t, ht⟩ := hr
  have he : evaluate A a z = 0 := by
    rw [← ht]
    exact DFunLike.congr_fun (evaluate_boundary_zero a ha) t
  have hc : (integral a pu : ℚ) + (a u v : ℚ) - (integral a pv : ℚ) = 0 := by
    simpa only [z, tau, map_sub, map_add, evaluate_chain a ha, evaluate_edge a ha] using he
  have hq : (integral a pv : ℚ) - (integral a pu : ℚ) = (a u v : ℚ) := by
    rw [← sub_eq_zero.mp hc]
    ring
  have hi : integral a pv - integral a pu = a u v := by exact_mod_cast hq
  simpa [height, pu, pv, vertex_mem_of_face A _ h u (by simp),
    vertex_mem_of_face A _ h v (by simp)] using hi

theorem exists_height_of_chain_exactness {A : PreAbstractSimplicialComplex V}
    (a : V → V → ℤ) (ha : FlatVoltage A a) (r : Vertex A)
    (paths : ∀ v : Vertex A, Path A r.val v.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) :
    ∃ h : V → ℤ, ∀ u v, ({u, v} : Finset V) ∈ A → h v - h u = a u v :=
  ⟨height a r paths, height_edge a ha r paths hex⟩

theorem flat_pullback {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (a : V → V → ℤ) (ha : FlatVoltage B a) :
    FlatVoltage A (fun u v => a (f u) (f v)) := by
  intro r u v h
  apply ha
  simpa using image_mem f hf _ h

/-- Supplies exactly the existing height-image input, even for collapsed/reordered maps. -/
theorem pullback_height {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (a : V → V → ℤ) (ha : FlatVoltage B a)
    (r : Vertex A) (paths : ∀ u : Vertex A, Path A r.val u.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) :
    ∃ h : U → ℤ, ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v) :=
  exists_height_of_chain_exactness _ (flat_pullback f hf a ha) r paths hex

theorem lift_exists_from_chain_exactness
    {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (a : V → V → ℤ) (ha : FlatVoltage B a)
    (r : Vertex A) (paths : ∀ u : Vertex A, Path A r.val u.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) :
    ∃ h : U → ℤ, (∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v)) ∧
      A.map (heightLift f h) ≤ voltageComplex (A.map f) a := by
  obtain ⟨h, hh⟩ := pullback_height f hf a ha r paths hex
  exact ⟨h, hh, height_image_le_voltage A f h a hh⟩

def circleVoltage (u v : Fin 3) : ℤ :=
  if u = 1 ∧ v = 2 then 1 else if u = 2 ∧ v = 1 then -1 else 0

theorem circle_voltage_flat : FlatVoltage cycleComplex circleVoltage := by
  intro u v w h
  change ({u, v, w} : Finset (Fin 3)).Nonempty ∧ ({u, v, w} : Finset (Fin 3)).card ≤ 2 at h
  fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all [circleVoltage]

theorem circle_voltage_nonexact : ¬ ExactVoltage cycleComplex circleVoltage := by
  rintro ⟨h, hh⟩
  have h01 := hh 0 1 (by change ({0, 1} : Finset (Fin 3)).Nonempty ∧ _; decide)
  have h02 := hh 0 2 (by change ({0, 2} : Finset (Fin 3)).Nonempty ∧ _; decide)
  have h12 := hh 1 2 (by change ({1, 2} : Finset (Fin 3)).Nonempty ∧ _; decide)
  norm_num [circleVoltage] at h01 h02 h12
  omega

def circlePaths (v : Vertex cycleComplex) : Path cycleComplex 0 v.val :=
  single (by change ({0, v.val} : Finset (Fin 3)).Nonempty ∧ _
             exact ⟨Finset.insert_nonempty _ _, Finset.card_le_two⟩)

/-- Flatness and path connectedness do not supply ordinary rational chain exactness. -/
theorem omitted_chain_exactness_rejected :
    (ordinaryTwo cycleComplex).range ≠ (ordinaryOne cycleComplex).ker := by
  intro hex
  obtain ⟨h, hh⟩ := exists_height_of_chain_exactness circleVoltage circle_voltage_flat
    cycleBase circlePaths hex
  exact circle_voltage_nonexact ⟨h, fun u v huv => (hh u v huv).symm⟩

theorem corrupted_triangle_voltage_rejected :
    ¬ FlatVoltage (⊤ : PreAbstractSimplicialComplex (Fin 3)) circleVoltage := by
  intro ha
  have h := ha 0 1 2 (Finset.insert_nonempty _ _)
  norm_num [circleVoltage] at h

theorem corrupted_height_sign_rejected :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let r : Vertex A := ⟨0, Finset.singleton_nonempty _⟩
    let paths : ∀ v : Vertex A, Path A r.val v.val :=
      fun _v => single (Finset.insert_nonempty _ _)
    let a : Fin 2 → Fin 2 → ℤ := fun u v => (v.val : ℤ) - (u.val : ℤ)
    height a r paths 1 - height a r paths 0 ≠ -1 := by
  dsimp only
  have h1 : ({1} : Finset (Fin 2)) ∈ (⊤ : PreAbstractSimplicialComplex (Fin 2)) :=
    Finset.singleton_nonempty _
  norm_num [height, integral, single, h1]

end D2RelationGap.IntegerHeights
