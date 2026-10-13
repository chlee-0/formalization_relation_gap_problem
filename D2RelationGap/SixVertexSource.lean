import D2RelationGap.VoltageTower
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
An explicit six-vertex, ten-facet candidate finite Moore source.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the tower.
The facet table is the explicit diagnostic in the reviewed AC-0004 draft d0c79a4.
Geometric RP2 identification and refined character-detecting maps remain open.
-/
noncomputable section
namespace D2RelationGap.SixVertexSource
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops IntegerHeights

def facets : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5}, {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5}}

def source : PreAbstractSimplicialComplex (Fin 6) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨q, hq, hsq⟩ := hs.2
    exact ⟨ht, q, hq, hts.trans hsq⟩

theorem pair_face (u v : Fin 6) : ({u,v} : Finset (Fin 6)) ∈ source := by
  change ({u,v} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {u,v} ⊆ t
  fin_cases u <;> fin_cases v <;> decide

theorem singleton_face (v : Fin 6) : ({v} : Finset (Fin 6)) ∈ source := by
  simpa using pair_face v v

def base : Vertex source := ⟨0, singleton_face 0⟩
def paths (v : Vertex source) : Path source 0 v.val := single (pair_face 0 v.val)

def cell (i : Fin 10) : Triangle source :=
  match i with
  | 0 => ⟨0, 1, 2, by decide, by decide, by
      change ({0,1,2} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,1,2} ⊆ t
      decide⟩
  | 1 => ⟨0, 1, 3, by decide, by decide, by
      change ({0,1,3} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,1,3} ⊆ t
      decide⟩
  | 2 => ⟨0, 2, 4, by decide, by decide, by
      change ({0,2,4} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,2,4} ⊆ t
      decide⟩
  | 3 => ⟨0, 3, 5, by decide, by decide, by
      change ({0,3,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,3,5} ⊆ t
      decide⟩
  | 4 => ⟨0, 4, 5, by decide, by decide, by
      change ({0,4,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,4,5} ⊆ t
      decide⟩
  | 5 => ⟨1, 2, 5, by decide, by decide, by
      change ({1,2,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {1,2,5} ⊆ t
      decide⟩
  | 6 => ⟨1, 3, 4, by decide, by decide, by
      change ({1,3,4} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {1,3,4} ⊆ t
      decide⟩
  | 7 => ⟨1, 4, 5, by decide, by decide, by
      change ({1,4,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {1,4,5} ⊆ t
      decide⟩
  | 8 => ⟨2, 3, 4, by decide, by decide, by
      change ({2,3,4} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {2,3,4} ⊆ t
      decide⟩
  | 9 => ⟨2, 3, 5, by decide, by decide, by
      change ({2,3,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {2,3,5} ⊆ t
      decide⟩

def edgeChain (u v : Fin 6) : Edge source →₀ ℚ :=
  edge (PathChains.trivialTransport (K := ℚ) source) u v (pair_face u v)

def fillingCoefficients (u v : Fin 6) : Fin 10 → ℚ :=
  match u, v with
  | 1, 2 => ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1, 3 => ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1, 4 => ![(1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ)]
  | 1, 5 => ![(1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ)]
  | 2, 3 => ![(-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ)]
  | 2, 4 => ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  | 2, 5 => ![(-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ)]
  | 3, 4 => ![(1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-1/2 : ℚ)]
  | 3, 5 => ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  | 4, 5 => ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
  | _, _ => 0

def doubledFilling (e : Edge source) : Triangle source →₀ ℚ :=
  ∑ i : Fin 10, (2 * fillingCoefficients e.src e.dst i) • Finsupp.single (cell i) 1

def filling (e : Edge source) : Triangle source →₀ ℚ := (1/2 : ℚ) • doubledFilling e

def edgeCell (u v : Fin 6) (h : u < v) : Edge source := ⟨u, v, h, pair_face u v⟩

theorem doubled_boundary_01 :
    ordinaryTwo source (doubledFilling (edgeCell 0 1 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 1 (by decide)) 1 - edgeChain 0 1 + edgeChain 0 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_02 :
    ordinaryTwo source (doubledFilling (edgeCell 0 2 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 2 (by decide)) 1 - edgeChain 0 2 + edgeChain 0 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_03 :
    ordinaryTwo source (doubledFilling (edgeCell 0 3 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 3 (by decide)) 1 - edgeChain 0 3 + edgeChain 0 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_04 :
    ordinaryTwo source (doubledFilling (edgeCell 0 4 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 4 (by decide)) 1 - edgeChain 0 4 + edgeChain 0 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_05 :
    ordinaryTwo source (doubledFilling (edgeCell 0 5 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 5 (by decide)) 1 - edgeChain 0 5 + edgeChain 0 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_12 :
    ordinaryTwo source (doubledFilling (edgeCell 1 2 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 2 (by decide)) 1 - edgeChain 0 2 + edgeChain 0 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_13 :
    ordinaryTwo source (doubledFilling (edgeCell 1 3 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 3 (by decide)) 1 - edgeChain 0 3 + edgeChain 0 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_14 :
    ordinaryTwo source (doubledFilling (edgeCell 1 4 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 4 (by decide)) 1 - edgeChain 0 4 + edgeChain 0 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  abel

theorem doubled_boundary_15 :
    ordinaryTwo source (doubledFilling (edgeCell 1 5 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 5 (by decide)) 1 - edgeChain 0 5 + edgeChain 0 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  abel

theorem doubled_boundary_23 :
    ordinaryTwo source (doubledFilling (edgeCell 2 3 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 3 (by decide)) 1 - edgeChain 0 3 + edgeChain 0 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  abel

theorem doubled_boundary_24 :
    ordinaryTwo source (doubledFilling (edgeCell 2 4 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 4 (by decide)) 1 - edgeChain 0 4 + edgeChain 0 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_25 :
    ordinaryTwo source (doubledFilling (edgeCell 2 5 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 5 (by decide)) 1 - edgeChain 0 5 + edgeChain 0 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  abel

theorem doubled_boundary_34 :
    ordinaryTwo source (doubledFilling (edgeCell 3 4 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 3 4 (by decide)) 1 - edgeChain 0 4 + edgeChain 0 3) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  abel

theorem doubled_boundary_35 :
    ordinaryTwo source (doubledFilling (edgeCell 3 5 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 3 5 (by decide)) 1 - edgeChain 0 5 + edgeChain 0 3) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_45 :
    ordinaryTwo source (doubledFilling (edgeCell 4 5 (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 4 5 (by decide)) 1 - edgeChain 0 5 + edgeChain 0 4) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    fillingCoefficients, cell, Fin.sum_univ_succ, edgeChain, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_filling_boundary (e : Edge source) :
    ordinaryTwo source (doubledFilling e) =
      (2 : ℚ) • (Finsupp.single e 1 - edgeChain 0 e.dst + edgeChain 0 e.src) := by
  rcases e with ⟨u, v, huv, hface⟩
  fin_cases u <;> fin_cases v <;> norm_num at huv
  · exact doubled_boundary_01
  · exact doubled_boundary_02
  · exact doubled_boundary_03
  · exact doubled_boundary_04
  · exact doubled_boundary_05
  · exact doubled_boundary_12
  · exact doubled_boundary_13
  · exact doubled_boundary_14
  · exact doubled_boundary_15
  · exact doubled_boundary_23
  · exact doubled_boundary_24
  · exact doubled_boundary_25
  · exact doubled_boundary_34
  · exact doubled_boundary_35
  · exact doubled_boundary_45

/-- The actual rational filling, including its necessary factor one half. -/
theorem filling_boundary (e : Edge source) :
    ordinaryTwo source (filling e) = Finsupp.single e 1 - edgeChain 0 e.dst + edgeChain 0 e.src := by
  rw [filling, map_smul, doubled_filling_boundary, smul_smul]
  norm_num

theorem edge_eq_iff (e d : Edge source) : e = d ↔ e.src = d.src ∧ e.dst = d.dst := by
  constructor
  · intro he; cases he; exact ⟨rfl, rfl⟩
  · rintro ⟨hs, hd⟩; exact Edge.ext hs hd

def treeSection : (Vertex source →₀ ℚ) →ₗ[ℚ] (Edge source →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun v => edgeChain 0 v.val)

def cycleFilling : (Edge source →₀ ℚ) →ₗ[ℚ] (Triangle source →₀ ℚ) :=
  Finsupp.linearCombination ℚ filling

/-- A contracting identity on actual ordinary degree-one chains. -/
theorem contracting_identity : (ordinaryTwo source).comp cycleFilling =
    LinearMap.id - treeSection.comp (ordinaryOne source) := by
  apply Finsupp.lhom_ext
  intro e c
  simp [cycleFilling, treeSection, filling_boundary, ordinaryOne, boundaryOne,
    VoltageChains.baseOne, incidence, smul_add, smul_sub]
  abel

/-- Exactness is proved for this actual finite source, not assumed as an interface. -/
theorem ordinary_chain_exactness :
    (ordinaryTwo source).range = (ordinaryOne source).ker := by
  apply le_antisymm (VoltageExistence.ordinary_range_le_kernel source)
  intro z hz
  have hh := DFunLike.congr_fun contracting_identity z
  change ordinaryTwo source (cycleFilling z) = z - treeSection (ordinaryOne source z) at hh
  have hzero : ordinaryOne source z = 0 := hz
  rw [hzero, map_zero, sub_zero] at hh
  exact ⟨cycleFilling z, hh⟩

def vertexEquiv : Vertex source ≃ Fin 6 where
  toFun v := v.val
  invFun v := ⟨v, singleton_face v⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := rfl

theorem active_vertex_count : Nat.card (Vertex source) = 6 := by
  rw [Nat.card_congr vertexEquiv]
  exact Nat.card_fin 6

/-- Omitting the common rational half doubles the actual nonstar cycle boundary. -/
theorem missing_half_rejected :
    ordinaryTwo source ((2 : ℚ) • filling (edgeCell 1 4 (by decide))) ≠
      Finsupp.single (edgeCell 1 4 (by decide)) 1 - edgeChain 0 4 + edgeChain 0 1 := by
  intro he
  rw [map_smul, filling_boundary] at he
  have hh := congrArg (fun z => z (edgeCell 1 4 (by decide))) he
  norm_num [edgeChain, edge, PathChains.trivialTransport, gaugeTransport,
    coeff, Finsupp.single_apply, edge_eq_iff, edgeCell] at hh

/-- A triangle omitted from the explicit table is not a face of the source. -/
theorem missing_triangle_face_rejected : ¬ ({0, 1, 4} : Finset (Fin 6)) ∈ source := by
  change ¬ (({0,1,4} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,1,4} ⊆ t)
  decide


def complex : AbstractSimplicialComplex (Fin 6) where
  toPreAbstractSimplicialComplex := source
  singleton_mem := singleton_face

theorem facet_card (t : Finset (Fin 6)) (ht : t ∈ facets) : t.card = 3 := by
  simp only [facets, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem dimension_at_most_two : SimplicialImages.AtMostTwo source := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hs.2
  exact (Finset.card_le_card hst).trans (le_of_eq (facet_card t ht))

def signUnit (u v : Fin 6) : ℚˣ :=
  match u, v with
  | 1,4 | 4,1 | 1,5 | 5,1 | 2,3 | 3,2 | 2,5 | 5,2 | 3,4 | 4,3 => -1
  | _, _ => 1

theorem sign_flat_012 (u v w : Fin 6)
    (hu : u ∈ ({0,1,2} : Finset (Fin 6)))
    (hv : v ∈ ({0,1,2} : Finset (Fin 6)))
    (hw : w ∈ ({0,1,2} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_013 (u v w : Fin 6)
    (hu : u ∈ ({0,1,3} : Finset (Fin 6)))
    (hv : v ∈ ({0,1,3} : Finset (Fin 6)))
    (hw : w ∈ ({0,1,3} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_024 (u v w : Fin 6)
    (hu : u ∈ ({0,2,4} : Finset (Fin 6)))
    (hv : v ∈ ({0,2,4} : Finset (Fin 6)))
    (hw : w ∈ ({0,2,4} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_035 (u v w : Fin 6)
    (hu : u ∈ ({0,3,5} : Finset (Fin 6)))
    (hv : v ∈ ({0,3,5} : Finset (Fin 6)))
    (hw : w ∈ ({0,3,5} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_045 (u v w : Fin 6)
    (hu : u ∈ ({0,4,5} : Finset (Fin 6)))
    (hv : v ∈ ({0,4,5} : Finset (Fin 6)))
    (hw : w ∈ ({0,4,5} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_125 (u v w : Fin 6)
    (hu : u ∈ ({1,2,5} : Finset (Fin 6)))
    (hv : v ∈ ({1,2,5} : Finset (Fin 6)))
    (hw : w ∈ ({1,2,5} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_134 (u v w : Fin 6)
    (hu : u ∈ ({1,3,4} : Finset (Fin 6)))
    (hv : v ∈ ({1,3,4} : Finset (Fin 6)))
    (hw : w ∈ ({1,3,4} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_145 (u v w : Fin 6)
    (hu : u ∈ ({1,4,5} : Finset (Fin 6)))
    (hv : v ∈ ({1,4,5} : Finset (Fin 6)))
    (hw : w ∈ ({1,4,5} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_234 (u v w : Fin 6)
    (hu : u ∈ ({2,3,4} : Finset (Fin 6)))
    (hv : v ∈ ({2,3,4} : Finset (Fin 6)))
    (hw : w ∈ ({2,3,4} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_235 (u v w : Fin 6)
    (hu : u ∈ ({2,3,5} : Finset (Fin 6)))
    (hv : v ∈ ({2,3,5} : Finset (Fin 6)))
    (hw : w ∈ ({2,3,5} : Finset (Fin 6))) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals rcases hw with rfl | rfl | rfl
  all_goals norm_num [signUnit]

theorem sign_flat_on_facet (t : Finset (Fin 6)) (ht : t ∈ facets)
    (u v w : Fin 6) (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) :
    signUnit u v * signUnit v w = signUnit u w := by
  simp only [facets, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sign_flat_012 u v w hu hv hw
  · exact sign_flat_013 u v w hu hv hw
  · exact sign_flat_024 u v w hu hv hw
  · exact sign_flat_035 u v w hu hv hw
  · exact sign_flat_045 u v w hu hv hw
  · exact sign_flat_125 u v w hu hv hw
  · exact sign_flat_134 u v w hu hv hw
  · exact sign_flat_145 u v w hu hv hw
  · exact sign_flat_234 u v w hu hv hw
  · exact sign_flat_235 u v w hu hv hw

def signTransport : Transport (K := ℚ) source where
  unit := signUnit
  flat := by
    intro u v w h
    obtain ⟨t, ht, hst⟩ := h.2
    exact sign_flat_on_facet t ht u v w (hst (by simp)) (hst (by simp)) (hst (by simp))

/-- Routes use actual source edges; the empty route at zero is the constant path. -/
def route (u : Fin 6) (xs : List (Fin 6)) : Path source u 0 :=
  match xs with
  | [] => match u with
    | 0 => .refl 0 (singleton_face 0)
    | v => single (pair_face v 0)
  | v :: vs => .cons (pair_face u v) (route v vs)

def generatorPath : Path source 0 0 := route 0 [1,4]
def generatorClass : Loop source base := Quotient.mk _ generatorPath

theorem generator_value : value signTransport generatorPath = -1 := by
  norm_num [value, generatorPath, route, single, signTransport, signUnit]

/-- A literal eighteen-move contraction, not a group-equality oracle. -/
def square_null_moves : Moves (append generatorPath generatorPath) (.refl 0 (singleton_face 0)) := by
  change Moves (route 0 [1,4,0,1,4]) (route 0 [])
  let m0 : Moves (route 0 [1,4,0,1,4]) (route 0 [2,1,4,0,1,4]) := Moves.symm (Moves.triangle (u := 0) (v := 2) (w := 1) (by change ({0,2,1} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,2,1} ⊆ t; decide) (route 1 [4,0,1,4]))
  let m1 : Moves (route 0 [2,1,4,0,1,4]) (route 0 [2,5,1,4,0,1,4]) := Moves.prepend (pair_face 0 2) (Moves.symm (Moves.triangle (u := 2) (v := 5) (w := 1) (by change ({2,5,1} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {2,5,1} ⊆ t; decide) (route 1 [4,0,1,4])))
  let m2 : Moves (route 0 [2,5,1,4,0,1,4]) (route 0 [2,5,4,1,4,0,1,4]) := Moves.prepend (pair_face 0 2) (Moves.prepend (pair_face 2 5) (Moves.symm (Moves.triangle (u := 5) (v := 4) (w := 1) (by change ({5,4,1} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {5,4,1} ⊆ t; decide) (route 1 [4,0,1,4]))))
  let m3 : Moves (route 0 [2,5,4,1,4,0,1,4]) (route 0 [2,5,4,0,1,4]) := Moves.prepend (pair_face 0 2) (Moves.prepend (pair_face 2 5) (Moves.prepend (pair_face 5 4) (Moves.backtrack (pair_face 4 1) (route 4 [0,1,4]))))
  let m4 : Moves (route 0 [2,5,4,0,1,4]) (route 0 [4,2,5,4,0,1,4]) := Moves.symm (Moves.triangle (u := 0) (v := 4) (w := 2) (by change ({0,4,2} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {0,4,2} ⊆ t; decide) (route 2 [5,4,0,1,4]))
  let m5 : Moves (route 0 [4,2,5,4,0,1,4]) (route 0 [4,2,5,0,4,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 2) (Moves.prepend (pair_face 2 5) (Moves.symm (Moves.triangle (u := 5) (v := 0) (w := 4) (by change ({5,0,4} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {5,0,4} ⊆ t; decide) (route 4 [0,1,4])))))
  let m6 : Moves (route 0 [4,2,5,0,4,0,1,4]) (route 0 [4,2,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 2) (Moves.prepend (pair_face 2 5) (Moves.prepend (pair_face 5 0) (Moves.backtrack (pair_face 0 4) (route 0 [1,4])))))
  let m7 : Moves (route 0 [4,2,5,0,1,4]) (route 0 [4,3,2,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.symm (Moves.triangle (u := 4) (v := 3) (w := 2) (by change ({4,3,2} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {4,3,2} ⊆ t; decide) (route 2 [5,0,1,4])))
  let m8 : Moves (route 0 [4,3,2,5,0,1,4]) (route 0 [4,3,5,2,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 3) (Moves.symm (Moves.triangle (u := 3) (v := 5) (w := 2) (by change ({3,5,2} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {3,5,2} ⊆ t; decide) (route 2 [5,0,1,4]))))
  let m9 : Moves (route 0 [4,3,5,2,5,0,1,4]) (route 0 [4,3,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 3) (Moves.prepend (pair_face 3 5) (Moves.backtrack (pair_face 5 2) (route 5 [0,1,4]))))
  let m10 : Moves (route 0 [4,3,5,0,1,4]) (route 0 [4,1,3,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.symm (Moves.triangle (u := 4) (v := 1) (w := 3) (by change ({4,1,3} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {4,1,3} ⊆ t; decide) (route 3 [5,0,1,4])))
  let m11 : Moves (route 0 [4,1,3,5,0,1,4]) (route 0 [4,1,3,0,5,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 1) (Moves.prepend (pair_face 1 3) (Moves.symm (Moves.triangle (u := 3) (v := 0) (w := 5) (by change ({3,0,5} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {3,0,5} ⊆ t; decide) (route 5 [0,1,4])))))
  let m12 : Moves (route 0 [4,1,3,0,5,0,1,4]) (route 0 [4,1,3,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 1) (Moves.prepend (pair_face 1 3) (Moves.prepend (pair_face 3 0) (Moves.backtrack (pair_face 0 5) (route 0 [1,4])))))
  let m13 : Moves (route 0 [4,1,3,0,1,4]) (route 0 [4,1,0,3,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 1) (Moves.symm (Moves.triangle (u := 1) (v := 0) (w := 3) (by change ({1,0,3} : Finset (Fin 6)).Nonempty ∧ ∃ t ∈ facets, {1,0,3} ⊆ t; decide) (route 3 [0,1,4]))))
  let m14 : Moves (route 0 [4,1,0,3,0,1,4]) (route 0 [4,1,0,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 1) (Moves.prepend (pair_face 1 0) (Moves.backtrack (pair_face 0 3) (route 0 [1,4]))))
  let m15 : Moves (route 0 [4,1,0,1,4]) (route 0 [4,1,4]) := Moves.prepend (pair_face 0 4) (Moves.prepend (pair_face 4 1) (Moves.backtrack (pair_face 1 0) (route 1 [4])))
  let m16 : Moves (route 0 [4,1,4]) (route 0 [4]) := Moves.prepend (pair_face 0 4) (Moves.backtrack (pair_face 4 1) (route 4 []))
  let m17 : Moves (route 0 [4]) (route 0 []) := Moves.backtrack (pair_face 0 4) (route 0 [])
  exact Moves.trans m0 (Moves.trans m1 (Moves.trans m2 (Moves.trans m3 (Moves.trans m4 (Moves.trans m5 (Moves.trans m6 (Moves.trans m7 (Moves.trans m8 (Moves.trans m9 (Moves.trans m10 (Moves.trans m11 (Moves.trans m12 (Moves.trans m13 (Moves.trans m14 (Moves.trans m15 (Moves.trans m16 (m17)))))))))))))))))

theorem generator_square : generatorClass ^ 2 = 1 := by
  rw [pow_two]
  change Quotient.mk _ (append generatorPath generatorPath) = Quotient.mk _ (.refl 0 (singleton_face 0))
  exact Quotient.sound ⟨square_null_moves⟩

theorem generator_nonidentity : generatorClass ≠ 1 := by
  intro he
  have hh := congrArg (holonomy signTransport base) he
  change value signTransport generatorPath = 1 at hh
  rw [generator_value] at hh
  have hq := congrArg (fun x : ℚˣ => (x : ℚ)) hh
  norm_num at hq

/-- The actual source loop is a nontrivial involution in the DEFINED loop group.
No equivalence of this group with geometric pi1 or original G is asserted. -/
theorem distinguished_involution : generatorClass ^ 2 = 1 ∧ generatorClass ≠ 1 :=
  ⟨generator_square, generator_nonidentity⟩

theorem generator_null_rejected :
    ¬ Nonempty (Moves generatorPath (.refl 0 (singleton_face 0))) := by
  rintro ⟨m⟩
  exact generator_nonidentity (Quotient.sound ⟨m⟩)

/-- A proved obstruction for maps out of THIS actual source, with detection
still explicit. No character-detecting map into an original presentation is supplied. -/
theorem no_detecting_injective_image_boundary {V K : Type*} [LinearOrder V] [Field K]
    (f : Fin 6 → V) (tau : Transport (K := K) (source.map f))
    (hdetect : holonomy (pullback tau f (le_refl _)) base generatorClass ≠ 1) :
    ¬ Function.Injective (boundaryTwo (source.map f) (coeff tau)) := by
  intro h2
  exact hdetect (VoltageTower.source_holonomy_trivial source base paths
    ordinary_chain_exactness V f tau h2 generatorClass)

theorem source_map_id : source.map (id : Fin 6 → Fin 6) = source := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  constructor
  · rintro ⟨t, ht, he⟩
    change t.image id = s at he
    simp only [Finset.image_id] at he
    exact he ▸ ht
  · intro hs
    exact ⟨s, hs, by simp⟩

/-- This actual source rejects omission of target weighted d2 injectivity,
while ordinary rational source exactness and nontrivial sign holonomy hold. -/
theorem sign_boundary_not_injective :
    ¬ Function.Injective (boundaryTwo source (coeff signTransport)) := by
  let tau : Transport (K := ℚ) (source.map (id : Fin 6 → Fin 6)) := {
    unit := signUnit
    flat := by
      intro u v w h
      rw [source_map_id] at h
      exact signTransport.flat u v w h }
  have hd : holonomy (pullback tau id (le_refl _)) base generatorClass ≠ 1 := by
    change value signTransport generatorPath ≠ 1
    rw [generator_value]
    intro he
    have hq := congrArg (fun x : ℚˣ => (x : ℚ)) he
    norm_num at hq
  have hn := no_detecting_injective_image_boundary id tau hd
  change ¬ Function.Injective (boundaryTwo (source.map (id : Fin 6 → Fin 6)) (coeff signTransport)) at hn
  rw [source_map_id] at hn
  exact hn

end D2RelationGap.SixVertexSource
