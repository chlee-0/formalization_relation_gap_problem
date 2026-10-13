import D2RelationGap.StellarSubdivision

/-!
Actual triangle attachments along two existing edges and ordinary cycle spans.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Complete finite target-witness maps and geometric adequacy
remain open; the statements here concern the actual defined ordinary chains.
-/
noncomputable section
namespace D2RelationGap.TriangleAttachment
open OrientedSimplices SimplicialTransport SourceExpansion IntegerHeights EdgePaths
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- All old faces remain. The third edge may already exist. -/
def attachment (A : PreAbstractSimplicialComplex V) (u v w : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ A ∨ s.Nonempty ∧ s ⊆ {u,v,w}}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rcases hs with hs | hs
      · exact (A.isRelLowerSet_faces hs).1
      · exact hs.1
    · intro t hts ht
      rcases hs with hs | hs
      · exact Or.inl ((A.isRelLowerSet_faces hs).2 hts ht)
      · exact Or.inr ⟨ht,hts.trans hs.2⟩

theorem inclusion (A : PreAbstractSimplicialComplex V) (u v w : V) : A ≤ attachment A u v w :=
  fun _ hs => Or.inl hs

theorem triangle_face (A : PreAbstractSimplicialComplex V) (u v w : V) :
    ({u,v,w} : Finset V) ∈ attachment A u v w :=
  Or.inr ⟨Finset.insert_nonempty _ _, Finset.Subset.refl _⟩

theorem vertex_old (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (x : Vertex (attachment A u v w)) : ({x.val} : Finset V) ∈ A := by
  rcases x.property with hx | hx
  · exact hx
  · have hm : x.val = u ∨ x.val = v ∨ x.val = w := by simpa using hx.2 (by simp)
    rcases hm with hu | hv | hw
    · rw [hu]; exact vertex_mem_of_face A _ huv u (by simp)
    · rw [hv]; exact vertex_mem_of_face A _ huv v (by simp)
    · rw [hw]; exact vertex_mem_of_face A _ hvw w (by simp)

def vertexProjection (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    Vertex (attachment A u v w) → Vertex A := fun x => ⟨x.val,vertex_old A u v w huv hvw x⟩

def verticesEquiv (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    Vertex (attachment A u v w) ≃ Vertex A where
  toFun := vertexProjection A u v w huv hvw
  invFun := vertexInclusion (inclusion A u v w)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem active_vertex_count (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    Nat.card (Vertex (attachment A u v w)) = Nat.card (Vertex A) :=
  Nat.card_congr (verticesEquiv A u v w huv hvw)

theorem vertices_finite (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    [Finite (Vertex A)] : Finite (Vertex (attachment A u v w)) :=
  Finite.of_equiv _ (verticesEquiv A u v w huv hvw).symm

theorem dimension_at_most_two (A : PreAbstractSimplicialComplex V) (u v w : V)
    (h : SimplicialImages.AtMostTwo A) : SimplicialImages.AtMostTwo (attachment A u v w) := by
  intro s hs
  rcases hs with hs | hs
  · exact h s hs
  · exact (Finset.card_le_card hs.2).trans (by
      have hh := Finset.card_insert_le u ({v,w} : Finset V)
      have hp : ({v,w} : Finset V).card ≤ 2 := by
        exact (Finset.card_insert_le v {w}).trans (by simp)
      omega)

/-- A genuinely new edge has both detour edges in the original source. -/
theorem detour_faces (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (e : Edge (attachment A u v w)) (he : ¬ ({e.src,e.dst} : Finset V) ∈ A) :
    ({e.src,v} : Finset V) ∈ A ∧ ({v,e.dst} : Finset V) ∈ A := by
  have hsub : ({e.src,e.dst} : Finset V) ⊆ {u,v,w} := (e.face.resolve_left he).2
  have hs : e.src = u ∨ e.src = v ∨ e.src = w := by simpa using hsub (by simp)
  have hd : e.dst = u ∨ e.dst = v ∨ e.dst = w := by simpa using hsub (by simp)
  have hvv : ({v,v} : Finset V) ∈ A := by
    simpa using vertex_mem_of_face A _ huv v (by simp)
  constructor
  · rcases hs with hs | hs | hs
    · simpa [hs] using huv
    · simpa [hs] using hvv
    · simpa [hs,Finset.pair_comm] using hvw
  · rcases hd with hd | hd | hd
    · simpa [hd,Finset.pair_comm] using huv
    · simpa [hd] using hvv
    · simpa [hd] using hvw

/-- Projection of a new edge is its two-edge ordinary detour; no retraction on faces is assumed. -/
def projectEdge (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (e : Edge (attachment A u v w)) : Edge A →₀ ℚ := by
  classical
  exact if he : ({e.src,e.dst} : Finset V) ∈ A then Finsupp.single ⟨e.src,e.dst,e.ordered,he⟩ 1
  else oedge A e.src v (detour_faces A u v w huv hvw e he).1 +
    oedge A v e.dst (detour_faces A u v w huv hvw e he).2

def projectOne (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    (Edge (attachment A u v w) →₀ ℚ) →ₗ[ℚ] Edge A →₀ ℚ :=
  Finsupp.linearCombination ℚ (projectEdge A u v w huv hvw)

def projectZero (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    (Vertex (attachment A u v w) →₀ ℚ) →ₗ[ℚ] Vertex A →₀ ℚ :=
  Finsupp.lmapDomain ℚ ℚ (vertexProjection A u v w huv hvw)

theorem ordinary_edge_boundary (A : PreAbstractSimplicialComplex V) (x y : V)
    (h : ({x,y} : Finset V) ∈ A) :
    ordinaryOne A (oedge A x y h) =
      point y (vertex_mem_of_face A _ h y (by simp)) -
      point x (vertex_mem_of_face A _ h x (by simp)) := by
  have hh := edge_boundary (PathChains.trivialTransport (K := ℚ) A) x y h
  rw [ordinary_coeff,one_smul] at hh
  exact hh

theorem project_boundary (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    (ordinaryOne A).comp (projectOne A u v w huv hvw) =
      (projectZero A u v w huv hvw).comp (ordinaryOne (attachment A u v w)) := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.comp_apply,projectOne,Finsupp.linearCombination_single,map_smul]
  by_cases he : ({e.src,e.dst} : Finset V) ∈ A
  · simp [projectEdge,he,ordinaryOne,boundaryOne,VoltageChains.baseOne,
      incidence,projectZero,Finsupp.lmapDomain_apply,Finsupp.mapDomain_sub,vertexProjection]
  · rw [projectEdge,dite_eq_right he,map_add,ordinary_edge_boundary,ordinary_edge_boundary]
    simp [ordinaryOne,boundaryOne,VoltageChains.baseOne,incidence,
      projectZero,Finsupp.lmapDomain_apply,Finsupp.mapDomain_sub,vertexProjection,point,smul_sub]

theorem correction_face (A : PreAbstractSimplicialComplex V) (u v w : V)
    (e : Edge (attachment A u v w)) (he : ¬ ({e.src,e.dst} : Finset V) ∈ A) :
    ({e.src,v,e.dst} : Finset V) ∈ attachment A u v w := by
  refine Or.inr ⟨Finset.insert_nonempty _ _, ?_⟩
  have hs := (e.face.resolve_left he).2
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hs ⊢
  exact ⟨hs.1, by simp, hs.2⟩

/-- A triangle correcting exactly the newly adjoined edge. Old edges need no correction. -/
def correctionEdge (A : PreAbstractSimplicialComplex V) (u v w : V)
    (e : Edge (attachment A u v w)) : Triangle (attachment A u v w) →₀ ℚ := by
  classical
  exact if he : ({e.src,e.dst} : Finset V) ∈ A then 0
  else otriangle (attachment A u v w) e.src v e.dst (correction_face A u v w e he)

def correction (A : PreAbstractSimplicialComplex V) (u v w : V) :
    (Edge (attachment A u v w) →₀ ℚ) →ₗ[ℚ] Triangle (attachment A u v w) →₀ ℚ :=
  Finsupp.linearCombination ℚ (correctionEdge A u v w)

theorem include_oedge {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (x y : V) (h : ({x,y} : Finset V) ∈ A) :
    includeEdges (K := ℚ) hAB (oedge A x y h) = oedge B x y (hAB h) := by
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · simp [includeEdges,Finsupp.lmapDomain_apply,edgeInclusion,oedge,edge,hlt]
  · simp [oedge,edge]
  · simp only [oedge,edge,dite_eq_right (not_lt_of_gt hgt),dite_eq_left hgt,
      ordinary_coeff,one_smul,map_neg]
    simp [includeEdges,Finsupp.lmapDomain_apply,edgeInclusion]

theorem correction_identity (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) :
    (ordinaryTwo (attachment A u v w)).comp (correction A u v w) =
      (includeEdges (K := ℚ) (inclusion A u v w)).comp (projectOne A u v w huv hvw) - LinearMap.id := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,correction,
    projectOne,Finsupp.linearCombination_single,map_smul]
  by_cases he : ({e.src,e.dst} : Finset V) ∈ A
  · simp [correctionEdge,projectEdge,he,includeEdges,Finsupp.lmapDomain_apply,edgeInclusion]
  · rw [correctionEdge,dite_eq_right he,ordinary_triangle_boundary,projectEdge,dite_eq_right he]
    rw [map_add,include_oedge,include_oedge]
    have hh : oedge (attachment A u v w) e.src e.dst e.face = Finsupp.single e 1 := by
      simp [oedge,edge,e.ordered]
    rw [hh]
    simp only [smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
    abel

/-- An explicit ordinary cycle-span statement, not a homology or target-map surrogate. -/
def CycleSpan (A : PreAbstractSimplicialComplex V) (g : Edge A →₀ ℚ) : Prop :=
  ∀ z : Edge A →₀ ℚ, ordinaryOne A z = 0 →
    ∃ c : ℚ, ∃ b : Triangle A →₀ ℚ, z = c • g + ordinaryTwo A b

theorem cycle_span_preserved (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (g : Edge A →₀ ℚ) (hspan : CycleSpan A g) :
    CycleSpan (attachment A u v w) (includeEdges (inclusion A u v w) g) := by
  intro z hz
  have hp : ordinaryOne A (projectOne A u v w huv hvw z) = 0 := by
    have hh := LinearMap.congr_fun (project_boundary A u v w huv hvw) z
    simpa [hz] using hh
  obtain ⟨c,b,hb⟩ := hspan _ hp
  refine ⟨c,includeTriangles (inclusion A u v w) b - correction A u v w z,?_⟩
  have hi := LinearMap.congr_fun (inclusion_boundary_two (inclusion A u v w) (fun _ _ => (1 : ℚ))) b
  have hc := LinearMap.congr_fun (correction_identity A u v w huv hvw) z
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply] at hi hc
  change includeEdges (inclusion A u v w) (ordinaryTwo A b) =
    ordinaryTwo (attachment A u v w) (includeTriangles (inclusion A u v w) b) at hi
  rw [hb,map_add,map_smul,hi] at hc
  rw [map_sub,hc]
  abel



/-- Vanishing ordinary cycle span is precisely degree-one chain exactness. -/
theorem zero_span_iff_exactness (A : PreAbstractSimplicialComplex V) :
    CycleSpan A 0 ↔ (ordinaryTwo A).range = (ordinaryOne A).ker := by
  constructor
  · intro hs
    apply le_antisymm (VoltageExistence.ordinary_range_le_kernel A)
    intro z hz
    obtain ⟨c,b,hb⟩ := hs z hz
    exact ⟨b,by simpa using hb.symm⟩
  · intro hex z hz
    have hm : z ∈ (ordinaryTwo A).range := by rw [hex]; exact hz
    obtain ⟨b,hb⟩ := hm
    exact ⟨0,b,by simpa using hb.symm⟩

theorem ordinary_exactness_preserved (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) :
    (ordinaryTwo (attachment A u v w)).range = (ordinaryOne (attachment A u v w)).ker := by
  apply (zero_span_iff_exactness _).mp
  simpa only [map_zero] using cycle_span_preserved A u v w huv hvw 0 ((zero_span_iff_exactness A).mpr hex)

/-- The generator can be killed by a proved nonzero rational multiple boundary.
The boundary witness must actually be constructed; a zero multiple does not suffice. -/
theorem exactness_of_boundary_multiple (A : PreAbstractSimplicialComplex V)
    (g : Edge A →₀ ℚ) (hspan : CycleSpan A g) (n : ℚ) (hn : n ≠ 0)
    (b : Triangle A →₀ ℚ) (hb : ordinaryTwo A b = n • g) :
    (ordinaryTwo A).range = (ordinaryOne A).ker := by
  apply (zero_span_iff_exactness A).mp
  intro z hz
  obtain ⟨c,d,hd⟩ := hspan z hz
  refine ⟨0,(c/n) • b + d,?_⟩
  rw [map_add,map_smul,hb,smul_smul,div_mul_cancel₀ c hn]
  simpa using hd

/-- An actual finite square-null source-loop derivation supplies the multiple filling.
CycleSpan and the derivation are not assumed for an unconstructed refined source. -/
theorem exactness_of_square_moves (A : PreAbstractSimplicialComplex V) (r : Vertex A)
    (p : Path A r.val r.val) (hspan : CycleSpan A (PathChains.chain (PathChains.trivialTransport (K := ℚ) A) p))
    (m : Moves (append p p) (.refl r.val r.property)) :
    (ordinaryTwo A).range = (ordinaryOne A).ker := by
  apply exactness_of_boundary_multiple A _ hspan 2 (by norm_num)
    (PathChains.filling (PathChains.trivialTransport (K := ℚ) A) m)
  have hb := PathChains.filling_boundary (PathChains.trivialTransport (K := ℚ) A) m
  rw [ordinary_coeff,PathChains.chain_append,trivial_value] at hb
  simpa [PathChains.chain,two_smul] using hb

/-- The original vertex function extends exactly when its mapped triangle is an actual face. -/
theorem mapped_face (A : PreAbstractSimplicialComplex V) (B : PreAbstractSimplicialComplex W)
    (u v w : V) (f : V → W) (hf : A.map f ≤ B)
    (ht : ({f u,f v,f w} : Finset W) ∈ B) : (attachment A u v w).map f ≤ B := by
  rintro s ⟨t,htA,rfl⟩
  rcases htA with htA | htA
  · exact image_mem f hf t htA
  · apply (B.isRelLowerSet_faces ht).2
    · simpa only [Finset.image_insert,Finset.image_singleton] using Finset.image_subset_image htA.2
    · exact Finset.image_nonempty.mpr htA.1

theorem identity_face_map {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) : A.map id ≤ B := by
  rintro s ⟨t,ht,rfl⟩
  simpa using hAB ht

/-- Existing source paths are retained literally, and so are their target values. -/
theorem retained_path_value {K : Type*} [Field K]
    (A : PreAbstractSimplicialComplex V) (B : PreAbstractSimplicialComplex W)
    (u v w : V) (f : V → W) (hf : A.map f ≤ B) (ht : ({f u,f v,f w} : Finset W) ∈ B)
    (tau : Transport (K := K) B) {x y : V} (p : Path A x y) :
    value tau (mapPath f (mapped_face A B u v w f hf ht)
      (mapPath id (identity_face_map (inclusion A u v w)) p)) = value tau (mapPath f hf p) := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,value,id_eq] using congrArg (fun q => tau.unit _ _ * q) ih

/-- The shortcut is an actual finite triangle move, including reordered/collapsed vertices. -/
def shortcut_moves (A : PreAbstractSimplicialComplex V) (u v w : V) {z : V}
    (p : Path (attachment A u v w) w z) := Moves.triangle (triangle_face A u v w) p

def rootPaths (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val) :
    ∀ x : Vertex (attachment A u v w), Path (attachment A u v w) r.val x.val :=
  fun x => mapPath id (identity_face_map (inclusion A u v w)) (paths (vertexProjection A u v w huv hvw x))

/-- A source cone gives a computed ordinary chain contraction. Used below to
check that filling an old cycle can destroy the converse to attachment preservation. -/
theorem cone_exactness (A : PreAbstractSimplicialComplex V) (r : V)
    (hr : ({r} : Finset V) ∈ A)
    (hc : EdgeContiguous A (fun _ => r)) :
    (ordinaryTwo A).range = (ordinaryOne A).ker := by
  have hf : A.map (fun _ => r) ≤ A := by
    rintro s ⟨t,ht,rfl⟩
    have hne := (A.isRelLowerSet_faces ht).1
    have heq : t.image (fun _ => r) = {r} := by
      ext x
      simp only [Finset.mem_image,Finset.mem_singleton]
      constructor
      · rintro ⟨y,hy,hxy⟩; exact hxy.symm
      · intro hx
        obtain ⟨y,hy⟩ := hne
        exact ⟨y,hy,hx.symm⟩
    change t.image (fun _ => r) ∈ A
    rw [heq]; exact hr
  have hzero : emap (fun _ => r) hf = 0 := by
    apply Finsupp.lhom_ext
    intro e c
    simp [emap_single,oedge,edge]
  apply (zero_span_iff_exactness A).mp
  intro z hz
  refine ⟨0,-prismOne A (fun _ => r) hc z,?_⟩
  have hh := LinearMap.congr_fun (prism_identity A (fun _ => r) hf hc) z
  rw [hzero] at hh
  simpa [hz] using (congrArg Neg.neg hh).symm

/-- Filling the unfilled three-cycle destroys ordinary H1; exactness does not reflect. -/
theorem exactness_reflection_rejected :
    (ordinaryTwo (attachment cycleComplex (0 : Fin 3) 1 2)).range =
      (ordinaryOne (attachment cycleComplex (0 : Fin 3) 1 2)).ker ∧
    (ordinaryTwo cycleComplex).range ≠ (ordinaryOne cycleComplex).ker := by
  have heq : attachment cycleComplex (0 : Fin 3) 1 2 = ⊤ := by
    ext s
    constructor
    · intro hs
      rcases hs with hs | hs
      · exact hs.1
      · exact hs.1
    · intro hs
      exact Or.inr ⟨hs,by
        have hfull : ({0,1,2} : Finset (Fin 3)) = Finset.univ := by decide
        rw [hfull]; exact Finset.subset_univ _⟩
  constructor
  · rw [heq]
    exact cone_exactness ⊤ 0 (Finset.singleton_nonempty _) (fun x y _ => Finset.insert_nonempty _ _)
  · exact IntegerHeights.omitted_chain_exactness_rejected



/-- A literal two-edge source for checking the added edge and correction sign. -/
def twoEdgePath : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0,1} ∨ s ⊆ {1,2})}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    exact ⟨ht,hs.2.elim (fun h => Or.inl (hts.trans h)) (fun h => Or.inr (hts.trans h))⟩

theorem twoEdgePath_01 : ({0,1} : Finset (Fin 3)) ∈ twoEdgePath := by
  exact ⟨Finset.insert_nonempty _ _, Or.inl (Finset.Subset.refl _)⟩
theorem twoEdgePath_12 : ({1,2} : Finset (Fin 3)) ∈ twoEdgePath := by
  exact ⟨Finset.insert_nonempty _ _, Or.inr (Finset.Subset.refl _)⟩
theorem twoEdgePath_missing_02 : ({0,2} : Finset (Fin 3)) ∉ twoEdgePath := by
  change ¬ (({0,2} : Finset (Fin 3)).Nonempty ∧ (({0,2} : Finset (Fin 3)) ⊆ {0,1} ∨ ({0,2} : Finset (Fin 3)) ⊆ {1,2}))
  decide

def newEdge : Edge (attachment twoEdgePath 0 1 2) :=
  ⟨0,2,by decide,Or.inr ⟨Finset.insert_nonempty _ _,by simp⟩⟩

theorem reversed_correction_sign_rejected :
    ordinaryTwo (attachment twoEdgePath 0 1 2)
        (-correctionEdge twoEdgePath 0 1 2 newEdge) ≠
      includeEdges (inclusion twoEdgePath 0 1 2)
        (projectEdge twoEdgePath 0 1 2 twoEdgePath_01 twoEdgePath_12 newEdge) - Finsupp.single newEdge 1 := by
  intro hh
  have hc := LinearMap.congr_fun
    (correction_identity twoEdgePath 0 1 2 twoEdgePath_01 twoEdgePath_12) (Finsupp.single newEdge 1)
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,correction,
    projectOne,Finsupp.linearCombination_single,one_smul] at hc
  rw [← hc,map_neg] at hh
  have hval := congrArg (fun z : Edge (attachment twoEdgePath 0 1 2) →₀ ℚ => z newEdge) hh
  have hn : ¬ ({newEdge.src,newEdge.dst} : Finset (Fin 3)) ∈ twoEdgePath := twoEdgePath_missing_02
  rw [correctionEdge,dite_eq_right hn] at hval
  rw [ordinary_triangle_boundary] at hval
  norm_num [oedge,edge,ordinary_coeff,newEdge,Finsupp.single_apply,Edge.ext_iff] at hval

theorem missing_target_triangle_rejected :
    ¬ (attachment cycleComplex (0 : Fin 3) 1 2).map id ≤ cycleComplex := by
  intro hf
  have ht := image_mem id hf _ (triangle_face cycleComplex (0 : Fin 3) 1 2)
  change ({0,1,2} : Finset (Fin 3)).Nonempty ∧ ({0,1,2} : Finset (Fin 3)).card ≤ 2 at ht
  norm_num at ht

/-- A zero multiple can be a boundary in a complex with nonexact ordinary chains. -/
theorem zero_multiple_rejected :
    (∃ b : Triangle cycleComplex →₀ ℚ,
      ordinaryTwo cycleComplex b = (0 : ℚ) • PathChains.chain (PathChains.trivialTransport cycleComplex) cycleLoop) ∧
    (ordinaryTwo cycleComplex).range ≠ (ordinaryOne cycleComplex).ker := by
  exact ⟨⟨0,by simp⟩,IntegerHeights.omitted_chain_exactness_rejected⟩



/-- The existing computed stellar lifts preserve an arbitrary ordinary cycle span,
not only the special span by zero. -/
theorem cycle_span_stellar_preserved (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u < v) (g : Edge A →₀ ℚ) (hspan : CycleSpan A g) :
    CycleSpan (StellarSubdivision.subdivision A u v)
      (StellarSubdivision.edgeLift A u v (ne_of_lt huv) (PathChains.trivialTransport A) g) := by
  let tau := PathChains.trivialTransport (K := ℚ) A
  let C := StellarSubdivision.subdivision A u v
  have hcoeff : coeff (StellarSubdivision.transport A u v tau) = (fun _ _ => (1 : ℚ)) := by
    change coeff (StellarSubdivision.transport A u v (PathChains.trivialTransport A)) = _
    rw [StellarSubdivision.transport_trivial,ordinary_coeff]
  intro z hz
  let c := edgeMap tau StellarSubdivision.collapse (StellarSubdivision.collapse_face A u v) z
  have hp : ordinaryOne A c = 0 := by
    have hh := LinearMap.congr_fun (map_boundary_one tau StellarSubdivision.collapse
      (StellarSubdivision.collapse_face A u v)) z
    change boundaryOne A (coeff tau) c =
      vertexMap StellarSubdivision.collapse (StellarSubdivision.collapse_face A u v)
        (boundaryOne C (coeff (StellarSubdivision.transport A u v tau)) z) at hh
    rw [ordinary_coeff,hcoeff] at hh
    change ordinaryOne A c = vertexMap StellarSubdivision.collapse
      (StellarSubdivision.collapse_face A u v) (ordinaryOne C z) at hh
    have hzC : ordinaryOne C z = 0 := hz
    simpa only [hzC,map_zero] using hh
  obtain ⟨a,b,hb⟩ := hspan c hp
  refine ⟨a,StellarSubdivision.twoLift A u v huv tau b - StellarSubdivision.oneHomotopy A u v (ne_of_lt huv) tau z,?_⟩
  have h2 := LinearMap.congr_fun (StellarSubdivision.twoLift_boundary A u v huv tau) b
  have hh := LinearMap.congr_fun (StellarSubdivision.homotopy_identity A u v (ne_of_lt huv) tau) z
  rw [ordinary_coeff,hcoeff] at h2
  rw [hcoeff] at hh
  simp only [LinearMap.comp_apply] at h2
  simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.id_apply] at hh
  change ordinaryTwo C (StellarSubdivision.twoLift A u v huv tau b) =
    StellarSubdivision.edgeLift A u v (ne_of_lt huv) tau (ordinaryTwo A b) at h2
  change ordinaryTwo C (StellarSubdivision.oneHomotopy A u v (ne_of_lt huv) tau z) +
    StellarSubdivision.zeroHomotopy A u v (ne_of_lt huv) tau (ordinaryOne C z) =
    StellarSubdivision.edgeLift A u v (ne_of_lt huv) tau c - z at hh
  rw [hz,map_zero,add_zero,hb,map_add,map_smul,← h2] at hh
  rw [map_sub,hh]
  abel

/-- This consumes an actual source span, finite square derivation and detecting map.
Constructing those jointly for an arbitrary target is still a separate obligation. -/
theorem no_detecting_square_source_image {K : Type*} [Field K]
    (A : PreAbstractSimplicialComplex V) [Finite (Vertex A)]
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (p : Path A r.val r.val) (hspan : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p))
    (m : Moves (append p p) (.refl r.val r.property))
    (f : V → W) (tau : Transport (K := K) (A.map f))
    (hdetect : value (pullback tau f (le_refl _)) p ≠ 1) :
    ¬ Function.Injective (boundaryTwo (A.map f) (coeff tau)) := by
  intro h2
  exact hdetect (VoltageTower.source_holonomy_trivial A r paths
    (exactness_of_square_moves A r p hspan m) W f tau h2 (Quotient.mk _ p))

/-- Dropping both existing-edge hypotheses can add active vertices. -/
theorem missing_existing_edges_rejected :
    ∃ x : Vertex (attachment (⊥ : PreAbstractSimplicialComplex (Fin 3)) 0 1 2),
      ({x.val} : Finset (Fin 3)) ∉ (⊥ : PreAbstractSimplicialComplex (Fin 3)) := by
  exact ⟨⟨0,Or.inr ⟨Finset.singleton_nonempty _,by simp⟩⟩,by intro h; exact h⟩

end D2RelationGap.TriangleAttachment
