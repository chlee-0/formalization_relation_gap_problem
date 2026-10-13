import D2RelationGap.OrientedSimplices
import Mathlib.Tactic.Abel

/-!
Unit transports and coefficient-correct orientation on actual abstract simplicial chains.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying groups, character/Fox data and tower obstruction. This module constructs
combinatorial transport/chain rules, not geometric local-system homology or a gap theorem.
-/

noncomputable section
namespace D2RelationGap.SimplicialTransport
open OrientedSimplices
variable {V K : Type*} [LinearOrder V] [Field K]

/-- Flatness includes repeated vertices of faces. No holonomy or homology
conclusion, or existence from a group character, is assumed here. -/
structure Transport (A : PreAbstractSimplicialComplex V) where
  unit : V → V → Kˣ
  flat : ∀ u v w, ({u, v, w} : Finset V) ∈ A → unit u v * unit v w = unit u w

def coeff {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) : K := tau.unit u v

theorem diagonal_unit {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u : V) (hu : ({u} : Finset V) ∈ A) : tau.unit u u = 1 := by
  have h := tau.flat u u u (by simpa using hu)
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem coeff_diagonal {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u : V) (hu : ({u} : Finset V) ∈ A) : coeff tau u u = 1 := by
  simp [coeff, diagonal_unit tau u hu]

theorem coeff_flat {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) :
    coeff tau u v * coeff tau v w = coeff tau u w := by
  exact congrArg (fun x : Kˣ => (x : K)) (tau.flat u v w h)

theorem coeff_inverse_mul {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) : coeff tau u v * coeff tau v u = 1 := by
  have hp : ({u, v, u} : Finset V) ∈ A := by simpa [Finset.insert_comm, Finset.pair_comm] using h
  rw [coeff_flat tau u v u hp, coeff_diagonal tau u (vertex_mem_of_face A _ h u (by simp))]

theorem coeff_ne_zero {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) : coeff tau u v ≠ 0 := (tau.unit u v).ne_zero

theorem unit_reverse {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) : tau.unit v u = (tau.unit u v)⁻¹ := by
  have hp : ({u, v, u} : Finset V) ∈ A := by simpa [Finset.insert_comm, Finset.pair_comm] using h
  apply mul_left_cancel (a := tau.unit u v)
  rw [tau.flat u v u hp, diagonal_unit tau u (vertex_mem_of_face A _ h u (by simp)),
    mul_inv_cancel]

theorem unit_boundary_chain {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A) :
    (boundaryOne A (coeff tau)).comp (boundaryTwo A (coeff tau)) = 0 := by
  apply boundary_chain
  intro t
  exact coeff_flat tau t.v0 t.v1 t.v2 t.face

def point {A : PreAbstractSimplicialComplex V} (u : V) (hu : ({u} : Finset V) ∈ A) :
    Vertex A →₀ K := Finsupp.single ⟨u, hu⟩ 1

/-- A coefficient based at u is moved to the first vertex of the sorted edge.
A collapsed edge contributes zero. -/
def edge {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) : Edge A →₀ K :=
  if huv : u < v then Finsupp.single ⟨u, v, huv, h⟩ 1
  else if hvu : v < u then
    -(coeff tau u v • Finsupp.single ⟨v, u, hvu, by simpa [Finset.pair_comm] using h⟩ 1)
  else 0

theorem edge_collapsed {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u : V) (h : ({u, u} : Finset V) ∈ A) : edge tau u u h = 0 := by simp [edge]

theorem edge_reverse {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) :
    edge tau v u (by simpa [Finset.pair_comm] using h) = -(coeff tau v u • edge tau u v h) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [edge, huv, not_lt_of_gt huv]
  · simp [edge]
  · have hi := coeff_inverse_mul tau v u (by simpa [Finset.pair_comm] using h)
    simp [edge, hvu, not_lt_of_gt hvu, hi]

theorem edge_boundary {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v} : Finset V) ∈ A) :
    boundaryOne A (coeff tau) (edge tau u v h) =
      coeff tau u v • point v (vertex_mem_of_face A _ h v (by simp)) -
        point u (vertex_mem_of_face A _ h u (by simp)) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [edge, huv, boundaryOne, VoltageChains.baseOne, incidence, point]
  · simp [edge, point, coeff_diagonal tau u (vertex_mem_of_face A _ h u (by simp))]
  · have hi := coeff_inverse_mul tau u v h
    simp [edge, hvu, not_lt_of_gt hvu, boundaryOne, VoltageChains.baseOne,
      incidence, point, smul_sub, hi]



/-- Six sorted orientations, with transport from the old first vertex to the new.
Repeated vertices contribute zero, including collapsed triangles. -/
def triangle {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) : Triangle A →₀ K :=
  if h012 : u < v ∧ v < w then Finsupp.single ⟨u, v, w, h012.1, h012.2, h⟩ 1
  else if h021 : u < w ∧ w < v then
    -Finsupp.single ⟨u, w, v, h021.1, h021.2, by
      convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ 1
  else if h102 : v < u ∧ u < w then
    -(coeff tau u v • Finsupp.single ⟨v, u, w, h102.1, h102.2, by
      convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ 1)
  else if h120 : v < w ∧ w < u then
    coeff tau u v • Finsupp.single ⟨v, w, u, h120.1, h120.2, by
      convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ 1
  else if h201 : w < u ∧ u < v then
    coeff tau u w • Finsupp.single ⟨w, u, v, h201.1, h201.2, by
      convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ 1
  else if h210 : w < v ∧ v < u then
    -(coeff tau u w • Finsupp.single ⟨w, v, u, h210.1, h210.2, by
      convert h using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ 1)
  else 0



theorem triangle_collapsed01 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u w : V) (h : ({u, u, w} : Finset V) ∈ A) : triangle tau u u w h = 0 := by
  have hn : ¬ (u < w ∧ w < u) := fun hh => lt_asymm hh.1 hh.2
  simp [triangle, hn]

theorem triangle_collapsed02 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v, u} : Finset V) ∈ A) : triangle tau u v u h = 0 := by
  have hn : ¬ (u < v ∧ v < u) := fun hh => lt_asymm hh.1 hh.2
  simp [triangle, hn]

theorem triangle_collapsed12 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v : V) (h : ({u, v, v} : Finset V) ∈ A) : triangle tau u v v h = 0 := by
  have hn : ¬ (v < u ∧ u < v) := fun hh => lt_asymm hh.1 hh.2
  simp [triangle, hn]

theorem coeff_flat_on_face {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (s : Finset V) (hs : s ∈ A) (u v w : V) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    coeff tau u v * coeff tau v w = coeff tau u w := by
  apply coeff_flat
  exact (A.isRelLowerSet_faces hs).2
    (Finset.insert_subset_iff.mpr ⟨hu, Finset.insert_subset_iff.mpr
      ⟨hv, Finset.singleton_subset_iff.mpr hw⟩⟩) (Finset.insert_nonempty _ _)

theorem triangle_boundary_012 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : u < v) (hbc : v < w) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]

theorem triangle_boundary_021 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : u < w) (hbc : w < v) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  have hf012 := coeff_flat_on_face tau _ h u v w (by simp) (by simp) (by simp)
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]
  abel

theorem triangle_boundary_102 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : v < u) (hbc : u < w) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  have hi01 := coeff_inverse_mul tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]
  abel

theorem triangle_boundary_120 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : v < w) (hbc : w < u) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  have hf012 := coeff_flat_on_face tau _ h u v w (by simp) (by simp) (by simp)
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]
  abel

theorem triangle_boundary_201 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : w < u) (hbc : u < v) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  have hf012 := coeff_flat_on_face tau _ h u v w (by simp) (by simp) (by simp)
  have hi02 := coeff_inverse_mul tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]
  abel

theorem triangle_boundary_210 {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) (hab : w < v) (hbc : v < u) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hac := lt_trans hab hbc
  have hba := not_lt_of_gt hab
  have hcb := not_lt_of_gt hbc
  have hca := not_lt_of_gt hac
  have hf012 := coeff_flat_on_face tau _ h u v w (by simp) (by simp) (by simp)
  have hf021 := coeff_flat_on_face tau _ h u w v (by simp) (by simp) (by simp)
  simp [*, triangle, edge, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    smul_sub, smul_add]
  abel

theorem triangle_boundary {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u v w : V) (h : ({u, v, w} : Finset V) ∈ A) :
    boundaryTwo A (coeff tau) (triangle tau u v w h) =
      coeff tau u v • edge tau v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
        edge tau u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
        edge tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hd0 := coeff_diagonal tau u (vertex_mem_of_face A _ h u (by simp))
  have hi01 := coeff_inverse_mul tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp))
  rcases lt_trichotomy u v with huv | rfl | hvu
  · rcases lt_trichotomy v w with hvw | rfl | hwv
    · exact triangle_boundary_012 tau u v w h huv hvw
    · simp [triangle_collapsed12, edge_collapsed]
    · rcases lt_trichotomy u w with huw | rfl | hwu
      · exact triangle_boundary_021 tau u v w h huw hwv
      · rw [triangle_collapsed02, map_zero, edge_reverse tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp))]
        simp [edge_collapsed, smul_smul, hi01]
      · exact triangle_boundary_201 tau u v w h hwu huv
  · simp [triangle_collapsed01, edge_collapsed, hd0]
  · rcases lt_trichotomy u w with huw | rfl | hwu
    · exact triangle_boundary_102 tau u v w h hvu huw
    · rw [triangle_collapsed02, map_zero, edge_reverse tau u v (pair_mem_of_face A _ h _ _ (by simp) (by simp))]
      simp [edge_collapsed, smul_smul, hi01]
    · rcases lt_trichotomy v w with hvw | rfl | hwv
      · exact triangle_boundary_120 tau u v w h hvw hwu
      · simp [triangle_collapsed12, edge_collapsed]
      · exact triangle_boundary_210 tau u v w h hwv hvu



/-- A supplied vertex gauge gives a flat unit transport. This is useful for
negative witnesses, but is not an assertion that all transports are exact. -/
def gaugeTransport (A : PreAbstractSimplicialComplex V) (p : V → Kˣ) : Transport (K := K) A where
  unit u v := (p u)⁻¹ * p v
  flat u v w _ := by simp [mul_assoc]

section Maps
variable {U : Type*} [LinearOrder U]

omit [LinearOrder U] in
theorem image_mem {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (s : Finset U) (hs : s ∈ A) : s.image f ∈ B :=
  hf ⟨s, hs, rfl⟩

/-- Literal pullback along a face-preserving map, allowing collapsed vertices. -/
def pullback {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) : Transport (K := K) A where
  unit u v := tau.unit (f u) (f v)
  flat u v w h := tau.flat _ _ _ (by
    simpa using image_mem f hf {u, v, w} h)

def mapVertex {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (u : Vertex A) : Vertex B :=
  ⟨f u.val, by simpa using image_mem f hf {u.val} u.property⟩

def vertexMap {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) : (Vertex A →₀ K) →ₗ[K] Vertex B →₀ K :=
  Finsupp.lmapDomain K K (mapVertex f hf)

def edgeMap {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) :
    (Edge A →₀ K) →ₗ[K] Edge B →₀ K :=
  Finsupp.linearCombination K fun e => edge tau (f e.src) (f e.dst) (by
    simpa using image_mem f hf {e.src, e.dst} e.face)

def triangleMap {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) :
    (Triangle A →₀ K) →ₗ[K] Triangle B →₀ K :=
  Finsupp.linearCombination K fun t => triangle tau (f t.v0) (f t.v1) (f t.v2) (by
    simpa using image_mem f hf {t.v0, t.v1, t.v2} t.face)

theorem map_boundary_one {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) :
    (boundaryOne B (coeff tau)).comp (edgeMap tau f hf) =
      (vertexMap f hf).comp (boundaryOne A (coeff (pullback tau f hf))) := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.comp_apply, edgeMap, Finsupp.linearCombination_single, map_smul,
    edge_boundary]
  simp [vertexMap, Finsupp.lmapDomain_apply, boundaryOne, VoltageChains.baseOne,
    Finsupp.mapDomain_sub, incidence, mapVertex, coeff, pullback, point]

theorem map_boundary_two {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) :
    (boundaryTwo B (coeff tau)).comp (triangleMap tau f hf) =
      (edgeMap tau f hf).comp (boundaryTwo A (coeff (pullback tau f hf))) := by
  apply Finsupp.lhom_ext
  intro t c
  simp only [LinearMap.comp_apply, triangleMap, Finsupp.linearCombination_single, map_smul,
    triangle_boundary]
  simp [edgeMap, boundaryTwo, VoltageChains.baseTwo, incidence, face01, face02, face12,
    coeff, pullback, smul_sub, smul_add, smul_smul]

end Maps

/-- A sign-only reversal loses the first-vertex coefficient transport. -/
theorem missing_edge_transport_rejected [CharZero K] :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let p : Fin 2 → Kˣ := fun u => if u = 0 then 1 else -1
    let tau := gaugeTransport A p
    let e : Edge A := ⟨0, 1, by decide, Finset.insert_nonempty _ _⟩
    edge tau 1 0 (Finset.insert_nonempty _ _) ≠ -Finsupp.single e 1 := by
  dsimp only
  intro he
  let e : Edge (⊤ : PreAbstractSimplicialComplex (Fin 2)) :=
    ⟨0, 1, by decide, Finset.insert_nonempty _ _⟩
  have hc := congrArg (fun x : Edge (⊤ : PreAbstractSimplicialComplex (Fin 2)) →₀ K => x e) he
  norm_num [edge, coeff, gaugeTransport, e, Finsupp.single_apply] at hc

/-- The first-vertex transport matters also for sorting a triangle. -/
theorem missing_triangle_transport_rejected [CharZero K] :
    let A : PreAbstractSimplicialComplex (Fin 3) := ⊤
    let p : Fin 3 → Kˣ := fun u => if u = 0 then 1 else -1
    let tau := gaugeTransport A p
    let t : Triangle A := ⟨0, 1, 2, by decide, by decide, Finset.insert_nonempty _ _⟩
    triangle tau 1 0 2 (Finset.insert_nonempty _ _) ≠ -Finsupp.single t 1 := by
  dsimp only
  intro he
  let t : Triangle (⊤ : PreAbstractSimplicialComplex (Fin 3)) :=
    ⟨0, 1, 2, by decide, by decide, Finset.insert_nonempty _ _⟩
  have hc := congrArg (fun x : Triangle (⊤ : PreAbstractSimplicialComplex (Fin 3)) →₀ K => x t) he
  norm_num [triangle, coeff, gaugeTransport, t, Finsupp.single_apply] at hc

end D2RelationGap.SimplicialTransport
