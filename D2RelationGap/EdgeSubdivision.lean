import D2RelationGap.SourceExpansion

/-!
A literal edge subdivision of the checked six-vertex source.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Arbitrary refinement/target maps and geometric adequacy are open.
-/
noncomputable section
namespace D2RelationGap.EdgeSubdivision
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops IntegerHeights SourceExpansion

def old (v : Fin 6) : Fin 7 := Fin.castLE (by decide) v

def splitFacet (t : Finset (Fin 6)) : Finset (Finset (Fin 7)) :=
  if 0 ∈ t ∧ 1 ∈ t then
    {insert 6 ((t.erase 0).image old), insert 6 ((t.erase 1).image old)}
  else {t.image old}

def facets : Finset (Finset (Fin 7)) := SixVertexSource.facets.biUnion splitFacet

theorem facets_eq : facets =
  {{1,2,6},{0,2,6},{1,3,6},{0,3,6},{0,2,4},{0,3,5},
   {0,4,5},{1,2,5},{1,3,4},{1,4,5},{2,3,4},{2,3,5}} := by decide

def source : PreAbstractSimplicialComplex (Fin 7) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨q,hq,hsq⟩ := hs.2
    exact ⟨ht,q,hq,hts.trans hsq⟩

instance faceDecidable (s : Finset (Fin 7)) : Decidable (s ∈ source) := by
  change Decidable (s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t)
  infer_instance

theorem singleton_face (v : Fin 7) : ({v} : Finset (Fin 7)) ∈ source := by
  fin_cases v <;> decide

def complex : AbstractSimplicialComplex (Fin 7) where
  toPreAbstractSimplicialComplex := source
  singleton_mem := singleton_face

theorem removed_edge : ({0,1} : Finset (Fin 7)) ∉ source := by decide

theorem wrong_split_triangle_rejected : ({0,1,6} : Finset (Fin 7)) ∉ source := by decide

theorem facet_card (t : Finset (Fin 7)) (ht : t ∈ facets) : t.card = 3 := by
  rw [facets_eq] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem dimension_at_most_two : SimplicialImages.AtMostTwo source := by
  intro s hs
  obtain ⟨t,ht,hst⟩ := hs.2
  exact (Finset.card_le_card hst).trans (le_of_eq (facet_card t ht))

def collapse (v : Fin 7) : Fin 6 := ⟨v.val % 6, Nat.mod_lt _ (by decide)⟩

theorem collapse_old (v : Fin 6) : collapse (old v) = v := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt v.isLt

theorem collapse_facet (t : Finset (Fin 7)) (ht : t ∈ facets) :
    t.image collapse ∈ SixVertexSource.source := by
  rw [facets_eq] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change (Finset.image collapse _).Nonempty ∧
    ∃ q ∈ SixVertexSource.facets, Finset.image collapse _ ⊆ q
  all_goals decide

theorem collapse_face : source.map collapse ≤ SixVertexSource.source := by
  rintro s ⟨t,ht,rfl⟩
  obtain ⟨q,hq,htq⟩ := ht.2
  exact (SixVertexSource.source.isRelLowerSet_faces (collapse_facet q hq)).2
    (Finset.image_subset_image htq) (ht.1.image collapse)


theorem collapse_boundary_one :
    (ordinaryOne SixVertexSource.source).comp (emap collapse collapse_face) =
      (vertexMap (K := ℚ) collapse collapse_face).comp (ordinaryOne source) :=
  ordinary_map_one collapse collapse_face

theorem collapse_boundary_two :
    (ordinaryTwo SixVertexSource.source).comp (tmap collapse collapse_face) =
      (emap collapse collapse_face).comp (ordinaryTwo source) :=
  ordinary_map_two collapse collapse_face

theorem old_inclusion_not_face_map : ¬ SixVertexSource.source.map old ≤ source := by
  intro h
  have he := image_mem old h _ (SixVertexSource.pair_face 0 1)
  have he' : ({0,1} : Finset (Fin 7)) ∈ source := by simpa [old] using he
  exact removed_edge he'

/-- A root-to-vertex tree; vertex one requires the two new edges. -/
def base : Vertex source := ⟨0,singleton_face 0⟩

def toRoot : (v : Fin 7) → Path source v 0
  | 0 => Path.refl 0 (singleton_face 0)
  | 1 => Path.cons (by decide : ({1,6} : Finset (Fin 7)) ∈ source)
      (single (by decide : ({6,0} : Finset (Fin 7)) ∈ source))
  | 2 => single (by decide)
  | 3 => single (by decide)
  | 4 => single (by decide)
  | 5 => single (by decide)
  | 6 => single (by decide)

def paths (v : Vertex source) : Path source 0 v.val := reverse (toRoot v.val)

def rootChain : Fin 7 → Edge source →₀ ℚ
  | 0 => 0
  | 1 => oedge source 0 6 (by decide) - oedge source 1 6 (by decide)
  | 2 => oedge source 0 2 (by decide)
  | 3 => oedge source 0 3 (by decide)
  | 4 => oedge source 0 4 (by decide)
  | 5 => oedge source 0 5 (by decide)
  | 6 => oedge source 0 6 (by decide)

def cell (i : Fin 12) : Triangle source :=
  match i with
  | 0 => ⟨1,2,6,by decide,by decide,by decide⟩
  | 1 => ⟨0,2,6,by decide,by decide,by decide⟩
  | 2 => ⟨1,3,6,by decide,by decide,by decide⟩
  | 3 => ⟨0,3,6,by decide,by decide,by decide⟩
  | 4 => ⟨0,2,4,by decide,by decide,by decide⟩
  | 5 => ⟨0,3,5,by decide,by decide,by decide⟩
  | 6 => ⟨0,4,5,by decide,by decide,by decide⟩
  | 7 => ⟨1,2,5,by decide,by decide,by decide⟩
  | 8 => ⟨1,3,4,by decide,by decide,by decide⟩
  | 9 => ⟨1,4,5,by decide,by decide,by decide⟩
  | 10 => ⟨2,3,4,by decide,by decide,by decide⟩
  | 11 => ⟨2,3,5,by decide,by decide,by decide⟩

def doubledCoefficients (e : Edge source) : Fin 12 → ℚ :=
  match e.src, e.dst with
  | 1,2 => ![2,-2,0,0,0,0,0,0,0,0,0,0]
  | 1,3 => ![0,0,2,-2,0,0,0,0,0,0,0,0]
  | 1,4 => ![1,-1,1,-1,1,1,-1,-1,-1,1,1,-1]
  | 1,5 => ![1,-1,1,-1,1,1,1,-1,-1,-1,1,-1]
  | 2,3 => ![-1,1,1,-1,1,-1,1,1,-1,-1,1,1]
  | 2,4 => ![0,0,0,0,2,0,0,0,0,0,0,0]
  | 2,5 => ![-1,1,1,-1,1,1,1,1,-1,-1,1,-1]
  | 2,6 => ![0,2,0,0,0,0,0,0,0,0,0,0]
  | 3,4 => ![1,-1,-1,1,1,1,-1,-1,1,1,1,-1]
  | 3,5 => ![0,0,0,0,0,2,0,0,0,0,0,0]
  | 3,6 => ![0,0,0,2,0,0,0,0,0,0,0,0]
  | 4,5 => ![0,0,0,0,0,0,2,0,0,0,0,0]
  | _,_ => 0

def doubledFilling (e : Edge source) : Triangle source →₀ ℚ :=
  ∑ i : Fin 12, doubledCoefficients e i • Finsupp.single (cell i) 1

def filling (e : Edge source) : Triangle source →₀ ℚ := (1/2 : ℚ) • doubledFilling e

def edgeCell (u v : Fin 7) (h : u < v) (hf : ({u,v} : Finset (Fin 7)) ∈ source) : Edge source :=
  ⟨u,v,h,hf⟩

theorem doubled_boundary_02 :
    ordinaryTwo source (doubledFilling (edgeCell 0 2 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 2 (by decide) (by decide)) 1 -
        rootChain 2 + rootChain 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_03 :
    ordinaryTwo source (doubledFilling (edgeCell 0 3 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 3 (by decide) (by decide)) 1 -
        rootChain 3 + rootChain 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_04 :
    ordinaryTwo source (doubledFilling (edgeCell 0 4 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 4 (by decide) (by decide)) 1 -
        rootChain 4 + rootChain 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_05 :
    ordinaryTwo source (doubledFilling (edgeCell 0 5 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 5 (by decide) (by decide)) 1 -
        rootChain 5 + rootChain 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_06 :
    ordinaryTwo source (doubledFilling (edgeCell 0 6 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 0 6 (by decide) (by decide)) 1 -
        rootChain 6 + rootChain 0) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_12 :
    ordinaryTwo source (doubledFilling (edgeCell 1 2 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 2 (by decide) (by decide)) 1 -
        rootChain 2 + rootChain 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_13 :
    ordinaryTwo source (doubledFilling (edgeCell 1 3 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 3 (by decide) (by decide)) 1 -
        rootChain 3 + rootChain 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_14 :
    ordinaryTwo source (doubledFilling (edgeCell 1 4 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 4 (by decide) (by decide)) 1 -
        rootChain 4 + rootChain 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_15 :
    ordinaryTwo source (doubledFilling (edgeCell 1 5 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 5 (by decide) (by decide)) 1 -
        rootChain 5 + rootChain 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_16 :
    ordinaryTwo source (doubledFilling (edgeCell 1 6 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 1 6 (by decide) (by decide)) 1 -
        rootChain 6 + rootChain 1) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_23 :
    ordinaryTwo source (doubledFilling (edgeCell 2 3 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 3 (by decide) (by decide)) 1 -
        rootChain 3 + rootChain 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_24 :
    ordinaryTwo source (doubledFilling (edgeCell 2 4 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 4 (by decide) (by decide)) 1 -
        rootChain 4 + rootChain 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_25 :
    ordinaryTwo source (doubledFilling (edgeCell 2 5 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 5 (by decide) (by decide)) 1 -
        rootChain 5 + rootChain 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_26 :
    ordinaryTwo source (doubledFilling (edgeCell 2 6 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 2 6 (by decide) (by decide)) 1 -
        rootChain 6 + rootChain 2) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_34 :
    ordinaryTwo source (doubledFilling (edgeCell 3 4 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 3 4 (by decide) (by decide)) 1 -
        rootChain 4 + rootChain 3) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]
  all_goals abel

theorem doubled_boundary_35 :
    ordinaryTwo source (doubledFilling (edgeCell 3 5 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 3 5 (by decide) (by decide)) 1 -
        rootChain 5 + rootChain 3) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_36 :
    ordinaryTwo source (doubledFilling (edgeCell 3 6 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 3 6 (by decide) (by decide)) 1 -
        rootChain 6 + rootChain 3) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_boundary_45 :
    ordinaryTwo source (doubledFilling (edgeCell 4 5 (by decide) (by decide))) =
      (2 : ℚ) • (Finsupp.single (edgeCell 4 5 (by decide) (by decide)) 1 -
        rootChain 5 + rootChain 4) := by
  classical
  norm_num [doubledFilling, ordinaryTwo, map_sum, boundaryTwo_single,
    doubledCoefficients, cell, Fin.sum_univ_succ, rootChain, oedge, edge, coeff,
    PathChains.trivialTransport, gaugeTransport, face01, face02, face12,
    edgeCell, smul_add, smul_sub, two_smul, neg_smul]

theorem doubled_filling_boundary (e : Edge source) :
    ordinaryTwo source (doubledFilling e) =
      (2 : ℚ) • (Finsupp.single e 1 - rootChain e.dst + rootChain e.src) := by
  obtain ⟨u,v,hord,hface⟩ := e
  fin_cases u <;> fin_cases v <;> norm_num at hord
  · exact False.elim ((by decide : ¬ ({0,1} : Finset (Fin 7)) ∈ source) hface)
  · exact doubled_boundary_02
  · exact doubled_boundary_03
  · exact doubled_boundary_04
  · exact doubled_boundary_05
  · exact doubled_boundary_06
  · exact doubled_boundary_12
  · exact doubled_boundary_13
  · exact doubled_boundary_14
  · exact doubled_boundary_15
  · exact doubled_boundary_16
  · exact doubled_boundary_23
  · exact doubled_boundary_24
  · exact doubled_boundary_25
  · exact doubled_boundary_26
  · exact doubled_boundary_34
  · exact doubled_boundary_35
  · exact doubled_boundary_36
  · exact doubled_boundary_45
  · exact False.elim ((by decide : ¬ ({4,6} : Finset (Fin 7)) ∈ source) hface)
  · exact False.elim ((by decide : ¬ ({5,6} : Finset (Fin 7)) ∈ source) hface)

theorem filling_boundary (e : Edge source) :
    ordinaryTwo source (filling e) = Finsupp.single e 1 - rootChain e.dst + rootChain e.src := by
  rw [filling, map_smul, doubled_filling_boundary, smul_smul]
  norm_num

def treeSection : (Vertex source →₀ ℚ) →ₗ[ℚ] Edge source →₀ ℚ :=
  Finsupp.linearCombination ℚ (fun v => rootChain v.val)

def cycleFilling : (Edge source →₀ ℚ) →ₗ[ℚ] Triangle source →₀ ℚ :=
  Finsupp.linearCombination ℚ filling

theorem contracting_identity : (ordinaryTwo source).comp cycleFilling =
    LinearMap.id - treeSection.comp (ordinaryOne source) := by
  apply Finsupp.lhom_ext
  intro e c
  simp [cycleFilling, filling_boundary, treeSection, ordinaryOne, boundaryOne,
    VoltageChains.baseOne, incidence, smul_sub]
  abel

theorem ordinary_chain_exactness : (ordinaryTwo source).range = (ordinaryOne source).ker := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w,rfl⟩ := hz
    change ordinaryOne source (ordinaryTwo source w) = 0
    have hb := unit_boundary_chain (PathChains.trivialTransport (K := ℚ) source)
    rw [ordinary_coeff] at hb
    exact LinearMap.congr_fun hb w
  · intro z hz
    refine ⟨cycleFilling z, ?_⟩
    have h := LinearMap.congr_fun contracting_identity z
    simpa [show ordinaryOne source z = 0 from hz] using h

def vertexEquiv : Vertex source ≃ Fin 7 where
  toFun := Subtype.val
  invFun := fun v => ⟨v,singleton_face v⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem active_vertex_count : Nat.card (Vertex source) = 7 := by
  simpa using Nat.card_congr vertexEquiv

def signTransport : Transport (K := ℚ) source := pullback SixVertexSource.signTransport collapse collapse_face


theorem sign_boundary_two_natural :
    (boundaryTwo SixVertexSource.source (coeff SixVertexSource.signTransport)).comp
      (triangleMap SixVertexSource.signTransport collapse collapse_face) =
      (edgeMap SixVertexSource.signTransport collapse collapse_face).comp
        (boundaryTwo source (coeff signTransport)) :=
  map_boundary_two SixVertexSource.signTransport collapse collapse_face

def route (u : Fin 7) (xs : List (Fin 7)) : Path source u 0 :=
  match xs with
  | [] => toRoot u
  | v :: vs => if h : ({u,v} : Finset (Fin 7)) ∈ source then .cons h (route v vs) else toRoot u

def generatorPath : Path source 0 0 := route 0 [6,1,4]
def generatorClass : Loop source base := Quotient.mk _ generatorPath

theorem generator_value : value signTransport generatorPath = -1 := by
  have h06 : ({0,6} : Finset (Fin 7)) ∈ source := by decide
  have h61 : ({6,1} : Finset (Fin 7)) ∈ source := by decide
  have h14 : ({1,4} : Finset (Fin 7)) ∈ source := by decide
  norm_num [generatorPath, route, h06, h61, h14, toRoot, single, value,
    signTransport, pullback, SixVertexSource.signTransport, SixVertexSource.signUnit, collapse]

/-- A literal twenty-one-move square contraction on the subdivided faces. -/
def square_null_moves : Moves (append generatorPath generatorPath)
    (Path.refl 0 (singleton_face 0)) := by
  change Moves (route 0 [6,1,4,0,6,1,4]) (route 0 [])
  let m0 : Moves (route 0 [6,1,4,0,6,1,4]) (route 0 [2,6,1,4,0,6,1,4]) := Moves.symm (Moves.triangle (u := 0) (v := 2) (w := 6) (by decide) (route 6 [1,4,0,6,1,4]))
  let m1 : Moves (route 0 [2,6,1,4,0,6,1,4]) (route 0 [2,1,4,0,6,1,4]) := Moves.prepend (by decide : ({0,2} : Finset (Fin 7)) ∈ source) (Moves.triangle (u := 2) (v := 6) (w := 1) (by decide) (route 1 [4,0,6,1,4]))
  let m2 : Moves (route 0 [2,1,4,0,6,1,4]) (route 0 [2,5,1,4,0,6,1,4]) := Moves.prepend (by decide : ({0,2} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 2) (v := 5) (w := 1) (by decide) (route 1 [4,0,6,1,4])))
  let m3 : Moves (route 0 [2,5,1,4,0,6,1,4]) (route 0 [2,5,4,1,4,0,6,1,4]) := Moves.prepend (by decide : ({0,2} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({2,5} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 5) (v := 4) (w := 1) (by decide) (route 1 [4,0,6,1,4]))))
  let m4 : Moves (route 0 [2,5,4,1,4,0,6,1,4]) (route 0 [2,5,4,0,6,1,4]) := Moves.prepend (by decide : ({0,2} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({2,5} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({5,4} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (route 4 [0,6,1,4]))))
  let m5 : Moves (route 0 [2,5,4,0,6,1,4]) (route 0 [4,2,5,4,0,6,1,4]) := Moves.symm (Moves.triangle (u := 0) (v := 4) (w := 2) (by decide) (route 2 [5,4,0,6,1,4]))
  let m6 : Moves (route 0 [4,2,5,4,0,6,1,4]) (route 0 [4,2,5,0,4,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,2} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({2,5} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 5) (v := 0) (w := 4) (by decide) (route 4 [0,6,1,4])))))
  let m7 : Moves (route 0 [4,2,5,0,4,0,6,1,4]) (route 0 [4,2,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,2} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({2,5} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({5,0} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (route 0 [6,1,4])))))
  let m8 : Moves (route 0 [4,2,5,0,6,1,4]) (route 0 [4,3,2,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 4) (v := 3) (w := 2) (by decide) (route 2 [5,0,6,1,4])))
  let m9 : Moves (route 0 [4,3,2,5,0,6,1,4]) (route 0 [4,3,5,2,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,3} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 3) (v := 5) (w := 2) (by decide) (route 2 [5,0,6,1,4]))))
  let m10 : Moves (route 0 [4,3,5,2,5,0,6,1,4]) (route 0 [4,3,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,3} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({3,5} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({5,2} : Finset (Fin 7)) ∈ source) (route 5 [0,6,1,4]))))
  let m11 : Moves (route 0 [4,3,5,0,6,1,4]) (route 0 [4,1,3,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 4) (v := 1) (w := 3) (by decide) (route 3 [5,0,6,1,4])))
  let m12 : Moves (route 0 [4,1,3,5,0,6,1,4]) (route 0 [4,1,3,0,5,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({1,3} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 3) (v := 0) (w := 5) (by decide) (route 5 [0,6,1,4])))))
  let m13 : Moves (route 0 [4,1,3,0,5,0,6,1,4]) (route 0 [4,1,3,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({1,3} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({3,0} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({0,5} : Finset (Fin 7)) ∈ source) (route 0 [6,1,4])))))
  let m14 : Moves (route 0 [4,1,3,0,6,1,4]) (route 0 [4,1,6,3,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 1) (v := 6) (w := 3) (by decide) (route 3 [0,6,1,4]))))
  let m15 : Moves (route 0 [4,1,6,3,0,6,1,4]) (route 0 [4,1,6,0,3,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({1,6} : Finset (Fin 7)) ∈ source) (Moves.symm (Moves.triangle (u := 6) (v := 0) (w := 3) (by decide) (route 3 [0,6,1,4])))))
  let m16 : Moves (route 0 [4,1,6,0,3,0,6,1,4]) (route 0 [4,1,6,0,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({1,6} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({6,0} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({0,3} : Finset (Fin 7)) ∈ source) (route 0 [6,1,4])))))
  let m17 : Moves (route 0 [4,1,6,0,6,1,4]) (route 0 [4,1,6,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({1,6} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({6,0} : Finset (Fin 7)) ∈ source) (route 6 [1,4]))))
  let m18 : Moves (route 0 [4,1,6,1,4]) (route 0 [4,1,4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.prepend (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({1,6} : Finset (Fin 7)) ∈ source) (route 1 [4])))
  let m19 : Moves (route 0 [4,1,4]) (route 0 [4]) := Moves.prepend (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (Moves.backtrack (by decide : ({4,1} : Finset (Fin 7)) ∈ source) (route 4 []))
  let m20 : Moves (route 0 [4]) (route 0 []) := Moves.backtrack (by decide : ({0,4} : Finset (Fin 7)) ∈ source) (route 0 [])
  exact Moves.trans m0 (Moves.trans m1 (Moves.trans m2 (Moves.trans m3 (Moves.trans m4 (Moves.trans m5 (Moves.trans m6 (Moves.trans m7 (Moves.trans m8 (Moves.trans m9 (Moves.trans m10 (Moves.trans m11 (Moves.trans m12 (Moves.trans m13 (Moves.trans m14 (Moves.trans m15 (Moves.trans m16 (Moves.trans m17 (Moves.trans m18 (Moves.trans m19 (m20))))))))))))))))))))

theorem generator_square : generatorClass ^ 2 = 1 := by
  rw [pow_two]
  change Quotient.mk _ (append generatorPath generatorPath) = Quotient.mk _ (Path.refl 0 (singleton_face 0))
  exact Quotient.sound ⟨square_null_moves⟩

theorem generator_nonidentity : generatorClass ≠ 1 := by
  intro he
  have hh := congrArg (holonomy signTransport base) he
  change value signTransport generatorPath = 1 at hh
  rw [generator_value] at hh
  have hq := congrArg (fun x : ℚˣ => (x : ℚ)) hh
  norm_num at hq


/-- Collapse inserts only a stutter at the root into the old generator. -/
def collapse_generator_moves : Moves (mapPath collapse collapse_face generatorPath)
    SixVertexSource.generatorPath := by
  have h06 : ({0,6} : Finset (Fin 7)) ∈ source := by decide
  have h61 : ({6,1} : Finset (Fin 7)) ∈ source := by decide
  have h14 : ({1,4} : Finset (Fin 7)) ∈ source := by decide
  simp only [generatorPath, route, dite_eq_left h06, dite_eq_left h61, dite_eq_left h14, toRoot]
  change Moves (Path.cons (SixVertexSource.pair_face 0 0) SixVertexSource.generatorPath)
    SixVertexSource.generatorPath
  exact Moves.stutter (SixVertexSource.singleton_face 0) SixVertexSource.generatorPath

theorem collapse_generator_class :
    mapClass collapse collapse_face generatorClass = SixVertexSource.generatorClass := by
  change Quotient.mk _ (mapPath collapse collapse_face generatorPath) =
    Quotient.mk _ SixVertexSource.generatorPath
  exact Quotient.sound ⟨collapse_generator_moves⟩

theorem distinguished_involution : generatorClass ^ 2 = 1 ∧ generatorClass ≠ 1 :=
  ⟨generator_square,generator_nonidentity⟩

theorem generator_null_rejected : ¬ Nonempty (Moves generatorPath (Path.refl 0 (singleton_face 0))) := by
  rintro ⟨m⟩
  exact generator_nonidentity (Quotient.sound ⟨m⟩)

def edgeEquiv : Edge source ≃ {p : Fin 7 × Fin 7 // p.1 < p.2 ∧ ({p.1,p.2} : Finset (Fin 7)) ∈ source} where
  toFun e := ⟨(e.src,e.dst),e.ordered,e.face⟩
  invFun p := ⟨p.val.1,p.val.2,p.property.1,p.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem edge_count : Nat.card (Edge source) = 18 := by
  rw [Nat.card_congr edgeEquiv, Nat.card_eq_fintype_card]
  decide

def triangleEquiv : Triangle source ≃ {p : Fin 7 × Fin 7 × Fin 7 //
    p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1,p.2.1,p.2.2} : Finset (Fin 7)) ∈ source} where
  toFun t := ⟨(t.v0,t.v1,t.v2),t.ordered01,t.ordered12,t.face⟩
  invFun p := ⟨p.val.1,p.val.2.1,p.val.2.2,p.property.1,p.property.2.1,p.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem triangle_count : Nat.card (Triangle source) = 12 := by
  rw [Nat.card_congr triangleEquiv, Nat.card_eq_fintype_card]
  decide

theorem missing_half_rejected :
    ordinaryTwo source ((2 : ℚ) • filling (edgeCell 1 4 (by decide) (by decide))) ≠
      Finsupp.single (edgeCell 1 4 (by decide) (by decide)) 1 - rootChain 4 + rootChain 1 := by
  intro he
  rw [map_smul, filling_boundary] at he
  have hh := congrArg (fun z => z (edgeCell 1 4 (by decide) (by decide))) he
  norm_num [rootChain, oedge, edge, ordinary_coeff, Finsupp.single_apply, Edge.ext_iff, edgeCell] at hh

theorem no_detecting_injective_image_boundary {V K : Type*} [LinearOrder V] [Field K]
    (f : Fin 7 → V) (tau : Transport (K := K) (source.map f))
    (hdetect : holonomy (pullback tau f (le_refl _)) base generatorClass ≠ 1) :
    ¬ Function.Injective (boundaryTwo (source.map f) (coeff tau)) := by
  intro h2
  exact hdetect (VoltageTower.source_holonomy_trivial source base paths ordinary_chain_exactness V f tau h2 generatorClass)

end D2RelationGap.EdgeSubdivision
